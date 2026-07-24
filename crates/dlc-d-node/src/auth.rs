//! The authenticated node — `proto`'s checks gating a running consensus, with
//! the Lean-transported decision predicate still making the call.
//!
//! Design: `spec/r6-1b-replication-protocol.md` §6.2. This is where the
//! authenticated protocol layer ([`crate::proto`]) and the verified transition
//! core ([`dlc_core::rsm`]) meet on a live decision path.
//!
//! # The load-bearing design decision: two proof chains, both live
//!
//! There are two independently-verified decision surfaces, and this node keeps
//! BOTH on the path rather than replacing one with the other:
//!
//!   * `dlc_d_rsm::consensus::decided` — the strict-majority tally, transported
//!     to Lean as `DLCD.TransportConsensus.rust_consensus_agreement`. It makes
//!     the leader's DECISION.
//!   * `crate::proto::{verify_proposal, verify_vote, verify_commit}` — the
//!     Ed25519 authentication whose properties Tamarin + ProVerif prove. It
//!     gates what is ALLOWED to reach the decision (and, on a follower, what is
//!     allowed to be applied).
//!
//! So authentication decides *admissibility* and the verified predicate decides
//! *agreement*. A forged vote never reaches `decided`; a forged commit never
//! reaches `commit`/`world_step`. Neither proof is weakened to accommodate the
//! other.
//!
//! # Identity
//!
//! A replica is its Ed25519 public key; its `u32` ballot index is its position
//! in the roster. The ballot stays `u32`-indexed because that is the exact shape
//! `rust_consensus_agreement` reasons about — authentication maps a verified
//! signer's key to that index, it does not change the index space.
//!
//! # Model state
//!
//! As in [`crate::Node`], the entire model state is a `GlobalConfig` with a
//! singleton replica vector, and it is only ever replaced by
//! `dlc_core::rsm::commit` / `world_step`. The `purity.rs` tripwire scans this
//! file too.

use dlc_core::rsm::{commit, world_step, Command, FailureBudget, GlobalConfig, Replica};
use dlc_core::syntax::Term;
use dlc_d_rsm::consensus::decided;

use crate::proto::{
    self, propose, verify_commit, verify_proposal, verify_vote, vote, Capability, Commit, Proposal,
    PubKey, QuorumCert, Roster, Vote,
};

/// An authenticated replication message. Unlike R6.1a's [`crate::Msg`], every
/// variant carries signatures the receiver checks (`proto`), so this IS a wire
/// message shape — the one the Tamarin/ProVerif models cover.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthMsg {
    /// Leader → all: a signed proposal (carries the capability credential).
    Propose(Proposal),
    /// Follower → leader: a signed vote.
    Vote(Vote),
    /// Leader → all: the decided command plus its quorum certificate.
    Commit(Commit),
}

/// Delivery target for an outgoing authenticated message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dest {
    /// Every node except this one.
    Peers,
    /// One specific replica, by roster index.
    To(u32),
}

/// An outgoing authenticated message with its destination.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Out {
    /// Where it goes.
    pub dest: Dest,
    /// The message.
    pub msg: AuthMsg,
}

/// One authenticated replica.
pub struct AuthNode {
    /// This replica's signing seed.
    seed: [u8; 32],
    /// This replica's public key (derived from `seed`).
    pk: PubKey,
    /// The committee. Membership is pinned; index = position.
    roster: Roster,
    /// This replica's roster index.
    idx: u32,
    /// The static leader's roster index.
    leader_idx: u32,
    /// The verified model state — a singleton-replica `GlobalConfig`.
    view: GlobalConfig,
    /// Leader-side ballot for the in-flight slot, indexed by roster position —
    /// the shape `rust_consensus_agreement` quantifies over. A slot is filled
    /// only by a `proto`-verified vote.
    ballot: Vec<Option<Command>>,
    /// The command + collected votes the leader currently has in flight.
    proposing: Option<(Command, Vec<Vote>)>,
}

impl AuthNode {
    /// Create an authenticated replica. `roster` pins the committee; `seed` is
    /// this replica's key and must correspond to `roster[idx]`.
    pub fn new(
        seed: [u8; 32],
        roster: Roster,
        idx: u32,
        leader_idx: u32,
        init: Term,
        budget: FailureBudget,
    ) -> Option<AuthNode> {
        let pk = dlc_crypto::ed25519::public_key(&seed);
        // The seed must actually be this roster seat's key — otherwise the node
        // would sign votes no one counts.
        if roster.member(idx) != Some(pk) {
            return None;
        }
        let cluster = roster.len();
        Some(AuthNode {
            seed,
            pk,
            roster,
            idx,
            leader_idx,
            view: GlobalConfig {
                replicas: vec![Replica {
                    id: idx,
                    store: init,
                    applied: 0,
                }],
                log: Vec::new(),
                budget,
            },
            ballot: vec![None; cluster],
            proposing: None,
        })
    }

    /// This replica's roster index.
    pub fn idx(&self) -> u32 {
        self.idx
    }

    /// This replica's public key.
    pub fn pk(&self) -> PubKey {
        self.pk
    }

    /// Whether this replica is the static leader.
    pub fn is_leader(&self) -> bool {
        self.idx == self.leader_idx
    }

    /// The verified model view.
    pub fn view(&self) -> &GlobalConfig {
        &self.view
    }

    /// This replica's store.
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

    /// The declared failure contract.
    pub fn budget(&self) -> &FailureBudget {
        &self.view.budget
    }

    /// The next undecided slot (log is append-only and gap-free).
    pub fn next_slot(&self) -> u32 {
        self.view.log.len() as u32
    }

    /// Client submission (leader only): sign and broadcast a proposal for `cmd`,
    /// carrying its capability credential `cap`. The leader votes for its own
    /// proposal, so a one-node cluster decides immediately.
    pub fn submit(&mut self, cmd: Command, cap: Capability) -> Vec<Out> {
        if !self.is_leader() || self.proposing.is_some() {
            return Vec::new();
        }
        let slot = self.next_slot();
        // The leader checks its own capability before proposing (matches the
        // model's Propose rule); if it does not verify, do not propose.
        if !proto::verify_capability(&cap, &cmd) {
            return Vec::new();
        }
        let p = propose(&self.seed, slot, cmd.clone(), cap);
        self.ballot = vec![None; self.roster.len()];
        self.proposing = Some((cmd.clone(), Vec::new()));

        let mut out = vec![Out {
            dest: Dest::Peers,
            msg: AuthMsg::Propose(p),
        }];
        // The leader's own vote — self-authenticated, so it enters the ballot
        // through the same gate as any follower's.
        let own = vote(&self.seed, slot, &cmd);
        out.extend(self.record_vote(slot, own));
        out
    }

    /// Handle one inbound authenticated message.
    pub fn handle(&mut self, msg: AuthMsg) -> Vec<Out> {
        match msg {
            // A follower verifies the proposal — leader membership, leader
            // signature, AND the capability (`cap_check_binds_issuer`) — before
            // it will vote. A proposal that fails any check produces no vote.
            AuthMsg::Propose(p) => {
                if p.slot != self.next_slot() || !verify_proposal(&p, &self.roster) {
                    return Vec::new();
                }
                let v = vote(&self.seed, p.slot, &p.cmd);
                vec![Out {
                    dest: Dest::To(self.leader_idx),
                    msg: AuthMsg::Vote(v),
                }]
            }

            // The leader tallies a vote — but only after `proto` verifies it
            // against the in-flight command. An unverified or off-slot vote never
            // reaches the ballot, so it never reaches `decided`.
            AuthMsg::Vote(v) => {
                if !self.is_leader() {
                    return Vec::new();
                }
                let slot = self.next_slot();
                self.record_vote(slot, v)
            }

            // Any node applies a commit — after `verify_commit` checks the QUORUM
            // CERTIFICATE (not the sender). A forged commit never reaches the
            // verified `commit`/`world_step`.
            AuthMsg::Commit(c) => {
                if c.slot != self.next_slot() || !verify_commit(&c, &self.roster) {
                    return Vec::new();
                }
                self.apply_commit(c.cmd);
                Vec::new()
            }
        }
    }

    /// Leader-side: verify a vote, record it in the ballot at the signer's roster
    /// index, and decide if the verified predicate says a quorum is reached.
    fn record_vote(&mut self, slot: u32, v: Vote) -> Vec<Out> {
        let Some((cmd, _)) = self.proposing.clone() else {
            return Vec::new();
        };
        if slot != self.next_slot() {
            return Vec::new();
        }
        // AUTHENTICATION GATE: the vote must verify against the in-flight command
        // and come from a committee member.
        if !verify_vote(&v, slot, &cmd, &self.roster) {
            return Vec::new();
        }
        let Some(voter_idx) = self.roster.index_of(&v.voter) else {
            return Vec::new();
        };
        // Record in both the u32 ballot (for `decided`) and the vote set (for the
        // certificate). De-dup by signer: a repeated signer must not fill two
        // ballot slots — the same distinctness `verify_qc` enforces.
        if self.ballot[voter_idx as usize].is_none() {
            self.ballot[voter_idx as usize] = Some(cmd.clone());
            if let Some((_, votes)) = self.proposing.as_mut() {
                votes.push(v);
            }
        }

        // DECISION GATE: the Lean-transported strict-majority predicate.
        if !decided(&self.ballot, &cmd) {
            return Vec::new();
        }

        // Decided. Build the certificate from the verified votes, apply locally,
        // and broadcast the commit.
        let votes = self.proposing.take().map(|(_, vs)| vs).unwrap_or_default();
        self.ballot = vec![None; self.roster.len()];
        let qc = QuorumCert { votes };
        let c = Commit {
            slot,
            cmd: cmd.clone(),
            qc,
        };
        // Sanity: the certificate we just built must itself verify — otherwise we
        // would broadcast a commit our own followers would (correctly) reject.
        debug_assert!(verify_commit(&c, &self.roster));
        self.apply_commit(cmd);
        vec![Out {
            dest: Dest::Peers,
            msg: AuthMsg::Commit(c),
        }]
    }

    /// The only model-state transition: append via the verified `commit`, then
    /// drain via the verified `world_step`. Whole-view replacements only.
    fn apply_commit(&mut self, cmd: Command) {
        self.view = commit(&self.view, cmd);
        while (self.applied() as usize) < self.view.log.len() {
            self.view = world_step(&self.view);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proto::issue_capability;
    use dlc_core::rsm::apply_prefix;
    use dlc_core::syntax::{Prop, Term};
    use dlc_crypto::ed25519;

    fn seed(n: u8) -> [u8; 32] {
        [n; 32]
    }

    fn dup_cmd() -> Command {
        Command {
            payload: Term::Lam(
                Box::new(Prop::Atom(0)),
                Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
            ),
            cap: Some(Prop::Atom(7)),
        }
    }

    fn init() -> Term {
        Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)))
    }

    fn roster3() -> Roster {
        Roster::new(vec![
            ed25519::public_key(&seed(1)),
            ed25519::public_key(&seed(2)),
            ed25519::public_key(&seed(3)),
        ])
        .expect("distinct")
    }

    fn node(idx: u32) -> AuthNode {
        AuthNode::new(
            seed((idx + 1) as u8),
            roster3(),
            idx,
            0,
            init(),
            FailureBudget::zero(1),
        )
        .expect("seed matches roster seat")
    }

    /// A deterministic in-memory driver: pump messages to completion. No tokio,
    /// so the run is reproducible and the assertions are about the protocol, not
    /// about scheduling. `dead` roster indices are crashed (their messages are
    /// dropped, and they send none).
    fn run(
        mut nodes: Vec<AuthNode>,
        workload: Vec<(Command, Capability)>,
        dead: &[u32],
    ) -> Vec<AuthNode> {
        let n = nodes.len();
        // (dest_idx, msg) queue.
        let mut queue: Vec<(u32, AuthMsg)> = Vec::new();

        let deliver = |queue: &mut Vec<(u32, AuthMsg)>, from: u32, outs: Vec<Out>| {
            for o in outs {
                match o.dest {
                    Dest::Peers => {
                        for j in 0..n as u32 {
                            if j != from {
                                queue.push((j, o.msg.clone()));
                            }
                        }
                    }
                    Dest::To(j) => queue.push((j, o.msg.clone())),
                }
            }
        };

        // Leader opens each slot in turn.
        for (cmd, cap) in workload {
            // Wait until the leader is idle (previous slot committed), then submit.
            let outs = nodes[0].submit(cmd, cap);
            deliver(&mut queue, 0, outs);
            // Drain the queue for this slot.
            let mut steps = 0;
            while let Some((to, msg)) = queue.pop() {
                steps += 1;
                assert!(steps < 10_000, "message storm — protocol not terminating");
                if dead.contains(&to) {
                    continue;
                }
                let outs = nodes[to as usize].handle(msg);
                deliver(&mut queue, to, outs);
            }
        }
        nodes
    }

    /// Three authenticated replicas commit a workload and converge on the changed
    /// store — the whole chain (sign → verify → vote → certify → verify-commit →
    /// apply) on a live decision path.
    #[test]
    fn authenticated_cluster_converges() {
        let nodes = vec![node(0), node(1), node(2)];
        let c = dup_cmd();
        let cap = issue_capability(&seed(9), &c);
        let out = run(nodes, vec![(c.clone(), cap)], &[]);

        let expected = apply_prefix(&init(), &[c]);
        for nd in &out {
            assert_eq!(nd.applied(), 1, "each replica applied the slot");
            assert_eq!(nd.store(), &expected, "converged on the changed store");
            assert_ne!(nd.store(), &init());
        }
    }

    /// A crashed follower (1 of 3, within budget) does not stop progress: 2 of 3
    /// is still a quorum by the verified predicate, and the survivors converge.
    #[test]
    fn one_crash_within_budget_still_commits() {
        let nodes = vec![node(0), node(1), node(2)];
        let c = dup_cmd();
        let cap = issue_capability(&seed(9), &c);
        let out = run(nodes, vec![(c.clone(), cap)], &[2]);

        let expected = apply_prefix(&init(), &[c]);
        for nd in [&out[0], &out[1]] {
            assert_eq!(nd.applied(), 1);
            assert_eq!(nd.store(), &expected);
        }
    }

    /// A vote from a NON-MEMBER key never enters the ballot, so it cannot help
    /// form a quorum. Fed directly to the leader, it must be ignored.
    #[test]
    fn forged_vote_from_non_member_is_ignored() {
        let mut leader = node(0);
        let c = dup_cmd();
        let cap = issue_capability(&seed(9), &c);
        // Leader proposes (and self-votes → 1 ballot slot).
        let _ = leader.submit(c.clone(), cap);
        assert_eq!(leader.applied(), 0, "one vote is not a quorum of three");

        // An outsider (seed 42 is not in the roster) signs a well-formed vote.
        let outsider = vote(&seed(42), 0, &c);
        let outs = leader.handle(AuthMsg::Vote(outsider));
        assert!(
            outs.is_empty(),
            "a non-member vote must not decide anything"
        );
        assert_eq!(
            leader.applied(),
            0,
            "still no quorum — the forged vote was ignored"
        );
    }

    /// A forged commit — a certificate that is one signer repeated — is rejected
    /// by a follower, so the verified core never applies it (the XDC bug, on the
    /// node path).
    #[test]
    fn forged_commit_is_rejected_by_followers() {
        let mut follower = node(1);
        let c = dup_cmd();
        // One signer's vote, tripled into a bogus "quorum".
        let v = vote(&seed(1), 0, &c);
        let qc = QuorumCert {
            votes: vec![v.clone(), v.clone(), v],
        };
        let forged = Commit {
            slot: 0,
            cmd: c,
            qc,
        };
        let outs = follower.handle(AuthMsg::Commit(forged));
        assert!(outs.is_empty());
        assert_eq!(
            follower.applied(),
            0,
            "a single-signer certificate must not be applied"
        );
        assert_eq!(follower.log().len(), 0);
    }

    /// A vote for a DIFFERENT command than the one in flight does not count —
    /// `verify_vote` binds the command, so it cannot be diverted onto another.
    #[test]
    fn vote_for_wrong_command_does_not_count() {
        let mut leader = node(0);
        let (c1, c2) = (
            dup_cmd(),
            Command {
                payload: Term::Var(3),
                cap: None,
            },
        );
        let cap = issue_capability(&seed(9), &c1);
        let _ = leader.submit(c1, cap);
        // A replica-2 vote, but for c2 rather than the in-flight c1.
        let wrong = vote(&seed(2), 0, &c2);
        let outs = leader.handle(AuthMsg::Vote(wrong));
        assert!(outs.is_empty());
        assert_eq!(leader.applied(), 0);
    }

    /// A node whose seed does not match its roster seat is refused at
    /// construction — it would sign votes no one counts.
    #[test]
    fn seed_must_match_roster_seat() {
        // seed 5 is not roster[0] (which is seed 1's key).
        assert!(AuthNode::new(seed(5), roster3(), 0, 0, init(), FailureBudget::zero(1)).is_none());
        assert!(AuthNode::new(seed(1), roster3(), 0, 0, init(), FailureBudget::zero(1)).is_some());
    }
}
