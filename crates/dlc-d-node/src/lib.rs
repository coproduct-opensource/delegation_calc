//! DLC-D node — the trusted shell around the verified RSM transition core.
//!
//! Design: `spec/r6-1-node-design.md`. Roadmap: `spec/dlc-d-roadmap.md` §2 (R6.1).
//!
//! # The one property this crate exists to preserve
//!
//! **Every state transition of a running node is a call into a function that the
//! R2 correspondence already proved refines the Lean model.** The shell
//! schedules; it never computes state.
//!
//! Concretely, a [`Node`]'s entire model state is one
//! [`dlc_core::rsm::GlobalConfig`] and the only two ways it ever changes are
//!
//!   * `view = dlc_core::rsm::commit(&view, cmd)` — covered by
//!     `DLCD.Transport.rust_capability_safety`;
//!   * `view = dlc_core::rsm::world_step(&view)` — covered by
//!     `DLCD.Transport.rust_world_step_correct` (and `rust_deliver_correct`,
//!     since the replica vector is a singleton).
//!
//! and the decision that gates a commit is `dlc_d_rsm::consensus::decided`,
//! covered by `DLCD.TransportConsensus.rust_consensus_agreement`. There is no
//! store field, no `applied` counter and no log vector owned by this crate; a
//! `tests/purity.rs` grep test fails the build if one appears.
//!
//! # Why the node's view is a whole `GlobalConfig`
//!
//! The natural shape — "my `Replica` plus my copy of the log" — forces the shell
//! to write `replica.store` / `replica.applied` itself, which is exactly what
//! would void the property above. Holding a `GlobalConfig` whose `replicas`
//! vector has exactly one element (this node) lets `commit` and `world_step` be
//! used *verbatim*: on a singleton replica vector, `world_step` is precisely
//! `deliver` for this replica, by its own definition. The cost is a one-element
//! `Vec`; the benefit is that the deployed transition surface is the corresponded
//! surface with no adapter in between.
//!
//! # What is trusted
//!
//! Everything in this crate: the event loop, the transport, the leader's ballot
//! bookkeeping, the slot matching, the drain loop. See `spec/r6-1-node-design.md`
//! §5 for the enumerated TCB. The capability slot (`Command::cap`) is CARRIED,
//! not checked — authorization is a `Prop`-layer obligation and R6.2's surface is
//! what discharges it.

#![forbid(unsafe_code)]
#![deny(missing_docs)]

pub mod auth;
pub mod authdemo;
pub mod codec;
pub mod demo;
pub mod net;
pub mod netauth;
pub mod proto;

use dlc_core::rsm::{commit, world_step, Command, FailureBudget, GlobalConfig, Replica};
use dlc_core::syntax::Term;
use dlc_d_rsm::consensus::decided;

/// A replication message. Crash-only single-decree consensus per slot: the
/// leader proposes, followers vote, a quorum decides, the leader broadcasts the
/// commit.
///
/// This is an in-process message type, NOT a wire format: R6.1a introduces no
/// new encoding (`spec/r6-1-node-design.md` §4 — the replication protocol is not
/// Tamarin-modelled yet, and `CLAUDE.md` bans wire-format changes that outrun
/// the models).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Msg {
    /// Leader → all: take `cmd` for slot `slot`.
    Propose {
        /// The log slot being decided.
        slot: u32,
        /// The proposed command.
        cmd: Command,
    },
    /// Follower → leader: replica `from` votes for `cmd` at `slot`.
    Vote {
        /// The log slot being voted on.
        slot: u32,
        /// The voting replica's id — the ballot index.
        from: u32,
        /// The command voted for.
        cmd: Command,
    },
    /// Leader → all: `cmd` is decided for `slot`; append it.
    Commit {
        /// The decided log slot.
        slot: u32,
        /// The decided command.
        cmd: Command,
    },
}

/// Where an outgoing message goes. `Peers` excludes the sender — a node never
/// delivers to itself, it acts directly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dest {
    /// Every node in the cluster except this one.
    Peers,
    /// One specific replica id.
    To(u32),
}

/// An outgoing message with its destination — what a [`Node`] handler returns.
/// The shell's transport is responsible for delivery; the node itself performs
/// no I/O.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Out {
    /// Delivery target.
    pub dest: Dest,
    /// The message.
    pub msg: Msg,
}

/// One replica: its verified model view plus the shell's protocol bookkeeping.
///
/// The `view` is the model state and is only ever replaced wholesale by
/// [`dlc_core::rsm::commit`] / [`dlc_core::rsm::world_step`]. `ballot` and
/// `proposing` are leader-side shell state — they are not model state and no
/// guarantee is stated about them.
pub struct Node {
    id: u32,
    leader: u32,
    cluster: u32,
    /// The verified model state: a `GlobalConfig` whose replica vector is
    /// exactly `[self]`.
    view: GlobalConfig,
    /// Leader-side ballot for the slot currently in flight, indexed by replica
    /// id — the exact shape `rust_consensus_agreement` quantifies over.
    ballot: Vec<Option<Command>>,
    /// The command the leader currently has in flight, if any.
    proposing: Option<Command>,
}

impl Node {
    /// Create a replica of a `cluster`-sized cluster with `leader` as the static
    /// leader, starting from `init` under the declared failure contract.
    ///
    /// There is no leader election (roadmap §5 backlog): a crashed leader stalls
    /// the cluster regardless of budget, and that is disclosed, not hidden.
    pub fn new(id: u32, cluster: u32, leader: u32, init: Term, budget: FailureBudget) -> Node {
        Node {
            id,
            leader,
            cluster,
            view: GlobalConfig {
                replicas: vec![Replica {
                    id,
                    store: init,
                    applied: 0,
                }],
                log: Vec::new(),
                budget,
            },
            ballot: vec![None; cluster as usize],
            proposing: None,
        }
    }

    /// This replica's id.
    pub fn id(&self) -> u32 {
        self.id
    }

    /// Whether this replica is the (static) leader.
    pub fn is_leader(&self) -> bool {
        self.id == self.leader
    }

    /// The verified model view — a `GlobalConfig` with a singleton replica
    /// vector. Read-only: the shell has no way to mutate it except through the
    /// verified transitions.
    pub fn view(&self) -> &GlobalConfig {
        &self.view
    }

    /// This replica's store (its model register value).
    pub fn store(&self) -> &Term {
        &self.view.replicas[0].store
    }

    /// How many committed slots this replica has applied.
    pub fn applied(&self) -> u32 {
        self.view.replicas[0].applied
    }

    /// This replica's committed log.
    pub fn log(&self) -> &[Command] {
        &self.view.log
    }

    /// The declared failure contract, and whether it still holds.
    pub fn budget(&self) -> &FailureBudget {
        &self.view.budget
    }

    /// The next undecided slot — the log is append-only and gap-free, so this is
    /// exactly its length.
    pub fn next_slot(&self) -> u32 {
        self.view.log.len() as u32
    }

    /// Client submission (leader only): start single-decree consensus on `cmd`
    /// for the next slot. The leader votes for its own proposal, so a
    /// single-node cluster decides immediately.
    ///
    /// Returns the messages to send. A non-leader returns nothing.
    pub fn submit(&mut self, cmd: Command) -> Vec<Out> {
        if !self.is_leader() || self.proposing.is_some() {
            return Vec::new();
        }
        let slot = self.next_slot();
        self.ballot = vec![None; self.cluster as usize];
        self.ballot[self.id as usize] = Some(cmd.clone());
        self.proposing = Some(cmd.clone());

        let mut out = vec![Out {
            dest: Dest::Peers,
            msg: Msg::Propose {
                slot,
                cmd: cmd.clone(),
            },
        }];
        // A one-node cluster is already a quorum of itself.
        out.extend(self.decide_if_quorum(slot, &cmd));
        out
    }

    /// Handle one inbound message, returning the messages to send.
    pub fn handle(&mut self, msg: Msg) -> Vec<Out> {
        match msg {
            // Followers vote for whatever the leader proposes for the slot they
            // are waiting on. Crash-fault model, not Byzantine.
            Msg::Propose { slot, cmd } => {
                if slot != self.next_slot() {
                    return Vec::new();
                }
                vec![Out {
                    dest: Dest::To(self.leader),
                    msg: Msg::Vote {
                        slot,
                        from: self.id,
                        cmd,
                    },
                }]
            }

            // Leader tallies. Votes for an already-decided slot are stale (the
            // log has moved on) and are dropped by the slot check.
            Msg::Vote { slot, from, cmd } => {
                if !self.is_leader() || slot != self.next_slot() {
                    return Vec::new();
                }
                if (from as usize) < self.ballot.len() {
                    self.ballot[from as usize] = Some(cmd.clone());
                }
                self.decide_if_quorum(slot, &cmd)
            }

            // Everyone appends the decided command — through the verified
            // `commit`, at the next slot only (append-only, gap-free).
            Msg::Commit { slot, cmd } => {
                if slot != self.next_slot() {
                    return Vec::new();
                }
                self.apply_commit(cmd);
                Vec::new()
            }
        }
    }

    /// Leader-side decision gate: is `cmd` decided for `slot` by the verified
    /// quorum predicate? If so, apply locally and tell the peers.
    ///
    /// The decision is `dlc_d_rsm::consensus::decided` over a ballot indexed by
    /// replica id — the deployed decision is the one
    /// `TransportConsensus.rust_consensus_agreement` talks about.
    fn decide_if_quorum(&mut self, slot: u32, cmd: &Command) -> Vec<Out> {
        if !decided(&self.ballot, cmd) {
            return Vec::new();
        }
        self.proposing = None;
        self.ballot = vec![None; self.cluster as usize];
        self.apply_commit(cmd.clone());
        vec![Out {
            dest: Dest::Peers,
            msg: Msg::Commit {
                slot,
                cmd: cmd.clone(),
            },
        }]
    }

    /// The ONLY state transition in this crate: append through the verified
    /// `commit`, then drain the committed log through the verified `world_step`.
    ///
    /// Both are whole-view replacements produced by `dlc_core::rsm`. Nothing
    /// here reads or writes a store, an `applied` counter or a log entry
    /// directly.
    fn apply_commit(&mut self, cmd: Command) {
        self.view = commit(&self.view, cmd);
        // Drain: `world_step` delivers exactly one committed slot per call.
        while (self.applied() as usize) < self.view.log.len() {
            self.view = world_step(&self.view);
        }
    }
}

/// Assemble per-node singleton views into the model's global configuration.
///
/// The Lean model's `worldStep` steps every replica at once; a cluster steps its
/// nodes independently. They agree because `DLCD.worldStep g = { g with replicas
/// := g.replicas.map (deliver g.log) }` and `deliver` reads only `(log, own
/// replica)` — so a node's local advance is its own component of the model's
/// map. This function makes that assembly explicit so it can be *tested* against
/// `dlc_core::rsm::world_step` rather than merely asserted in prose
/// (`spec/r6-1-node-design.md` §2.1).
///
/// `log` and `budget` are taken from the first view: the assembly is meaningful
/// exactly when the nodes share a committed log, which is what the consensus
/// layer must provide.
pub fn assemble(views: &[GlobalConfig]) -> GlobalConfig {
    let mut replicas: Vec<Replica> = Vec::new();
    for v in views {
        for r in &v.replicas {
            replicas.push(r.clone());
        }
    }
    GlobalConfig {
        replicas,
        log: views[0].log.clone(),
        budget: views[0].budget.clone(),
    }
}
