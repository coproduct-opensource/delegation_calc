//! The transport and the event loop — the trusted shell proper.
//!
//! R6.1a runs each replica as an independent `tokio` task communicating over
//! in-process unbounded channels. There is **no wire encoding here**: the
//! replication protocol is not Tamarin-modelled yet, and `CLAUDE.md` bans
//! wire-format changes that outrun the models. R6.1b is Tamarin + ProVerif for
//! the replication protocol, then a socket carrier whose payload encoding reuses
//! `dlc_protocol::wire` verbatim (`spec/r6-1-node-design.md` §4).
//!
//! What the in-process transport *does* faithfully exercise: independent tasks,
//! asynchronous interleaving, quorum-gated decisions, crash faults, and
//! convergence. What it does not: an adversarial network. That limit is stated,
//! not dressed up.
//!
//! Fair delivery — the model's `FailureBudget::fair_delivery` assumption — is
//! *provided* here by the channel (loss-free, FIFO), not proved. It is item 3 of
//! the enumerated TCB.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};
use std::time::Duration;

use dlc_core::rsm::{Command, FailureBudget, GlobalConfig};
use dlc_core::syntax::Term;
use tokio::sync::mpsc::{unbounded_channel, UnboundedSender};
use tokio::task::JoinSet;

use crate::{Dest, Msg, Node};

/// How a cluster run is configured.
#[derive(Clone, Debug)]
pub struct ClusterConfig {
    /// Number of replicas.
    pub size: u32,
    /// The static leader's id.
    pub leader: u32,
    /// Shared initial store.
    pub init: Term,
    /// Commands the leader will drive through consensus, in order.
    pub workload: Vec<Command>,
    /// Replicas that never start — crash faults. A crashed replica's channel is
    /// closed, so sends to it fail and are dropped (crash-stop semantics).
    pub crashed: Vec<u32>,
    /// The declared failure contract.
    pub budget: FailureBudget,
    /// How long to wait before declaring the run stalled. A stall is a legitimate
    /// outcome (it is what over-budget crashes must produce), so the timeout is
    /// part of the harness, not an error path.
    pub settle: Duration,
}

/// What a cluster run produced.
#[derive(Clone, Debug)]
pub struct ClusterOutcome {
    /// Final model view per live replica, keyed by replica id.
    pub views: BTreeMap<u32, GlobalConfig>,
    /// True if every live replica applied the whole workload.
    pub complete: bool,
}

impl ClusterOutcome {
    /// The live replicas' stores, in id order.
    pub fn stores(&self) -> Vec<Term> {
        self.views
            .values()
            .map(|v| v.replicas[0].store.clone())
            .collect()
    }

    /// Every live replica holds the same store. Note this is true of a *stalled*
    /// cluster too — which is the point: losing liveness must not cost safety.
    pub fn converged(&self) -> bool {
        let mut it = self.views.values();
        match it.next() {
            None => true,
            Some(first) => it.all(|v| v.replicas[0].store == first.replicas[0].store),
        }
    }

    /// How many slots the live replicas have committed (max over replicas).
    pub fn committed(&self) -> usize {
        self.views.values().map(|v| v.log.len()).max().unwrap_or(0)
    }
}

/// Run a cluster to completion (or to a stall) and report the final state.
///
/// Each live replica is a task owning its [`Node`]; the leader drives the
/// workload one slot at a time, submitting the next command once the previous is
/// applied locally (single-decree per slot). Every state change is published to
/// a shared snapshot map so a *stalled* run can still be inspected — otherwise
/// the over-budget scenario would have nothing to assert on.
pub async fn run_cluster(cfg: ClusterConfig) -> ClusterOutcome {
    let n = cfg.size as usize;
    let expected = cfg.workload.len();

    let mut senders: Vec<Option<UnboundedSender<Msg>>> = Vec::with_capacity(n);
    let mut receivers = Vec::with_capacity(n);
    for id in 0..cfg.size {
        if cfg.crashed.contains(&id) {
            // A crashed replica has no channel: sends to it fail and are dropped.
            senders.push(None);
            receivers.push(None);
        } else {
            let (tx, rx) = unbounded_channel::<Msg>();
            senders.push(Some(tx));
            receivers.push(Some(rx));
        }
    }
    let senders = Arc::new(senders);
    let snapshots: Arc<Mutex<BTreeMap<u32, GlobalConfig>>> = Arc::new(Mutex::new(BTreeMap::new()));

    let mut tasks = JoinSet::new();
    for (id, rx) in receivers.into_iter().enumerate() {
        let Some(mut rx) = rx else { continue };
        let id = id as u32;
        let senders = Arc::clone(&senders);
        let snapshots = Arc::clone(&snapshots);
        let cfg = cfg.clone();

        tasks.spawn(async move {
            let mut node = Node::new(
                id,
                cfg.size,
                cfg.leader,
                cfg.init.clone(),
                cfg.budget.clone(),
            );
            let mut next_cmd = 0usize;
            publish(&snapshots, &node);

            // The leader opens the first slot — and, if it is a quorum of itself
            // (a one-node cluster), the rest of the workload immediately.
            let outs = drive(&mut node, &mut next_cmd, &cfg.workload);
            dispatch(&senders, id, outs);
            publish(&snapshots, &node);

            while (node.applied() as usize) < expected {
                let Some(msg) = rx.recv().await else { break };
                let outs = node.handle(msg);
                dispatch(&senders, id, outs);
                publish(&snapshots, &node);

                // Leader: once the in-flight slot lands locally, open the next.
                let outs = drive(&mut node, &mut next_cmd, &cfg.workload);
                dispatch(&senders, id, outs);
                publish(&snapshots, &node);
            }
        });
    }

    // A stall is a legitimate outcome, so bound the wait rather than joining
    // unconditionally.
    let settled = tokio::time::timeout(cfg.settle, async {
        while tasks.join_next().await.is_some() {}
    })
    .await
    .is_ok();
    tasks.abort_all();

    let views = snapshots.lock().expect("snapshot mutex").clone();
    let complete = settled
        && views
            .values()
            .all(|v| v.replicas[0].applied as usize == expected);
    ClusterOutcome { views, complete }
}

/// Leader-side workload driver: open the next slot whenever the previous one has
/// landed locally (single-decree per slot — at most one proposal in flight).
///
/// It loops rather than submitting once because `submit` can decide immediately
/// when the leader is a quorum of itself (a one-node cluster), in which case the
/// next slot is already open by the time it returns. A non-leader drives nothing.
fn drive(node: &mut Node, next_cmd: &mut usize, workload: &[Command]) -> Vec<crate::Out> {
    let mut outs = Vec::new();
    while node.is_leader()
        && *next_cmd < workload.len()
        && node.log().len() == *next_cmd
        && (node.applied() as usize) == *next_cmd
    {
        outs.extend(node.submit(workload[*next_cmd].clone()));
        *next_cmd += 1;
    }
    outs
}

/// Deliver a handler's outgoing messages. Sends to a crashed replica fail and
/// are dropped — that IS crash-stop.
fn dispatch(senders: &[Option<UnboundedSender<Msg>>], from: u32, outs: Vec<crate::Out>) {
    for out in outs {
        match out.dest {
            Dest::Peers => {
                for (id, tx) in senders.iter().enumerate() {
                    if id as u32 == from {
                        continue;
                    }
                    if let Some(tx) = tx {
                        let _ = tx.send(out.msg.clone());
                    }
                }
            }
            Dest::To(id) => {
                if let Some(Some(tx)) = senders.get(id as usize) {
                    let _ = tx.send(out.msg.clone());
                }
            }
        }
    }
}

/// Publish a node's model view so a stalled run is still inspectable.
fn publish(snapshots: &Arc<Mutex<BTreeMap<u32, GlobalConfig>>>, node: &Node) {
    snapshots
        .lock()
        .expect("snapshot mutex")
        .insert(node.id(), node.view().clone());
}
