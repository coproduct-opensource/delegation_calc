//! Scenarios for the `cargo run` demo of the AUTHENTICATED node — including a
//! side-by-side that makes the Byzantine safety property VISIBLE: the same
//! equivocating-leader attack diverges under a crash roster and is defeated
//! under a Byzantine roster.
//!
//! This is deliberately not just happy-path convergence. The whole point of the
//! R6.1b arc is the safety property, so the demo exhibits the attack and its
//! defence, matching what `tests/byzantine.rs` proves.

use dlc_core::rsm::{Command, FailureBudget};
use dlc_core::syntax::{Prop, Term};
use dlc_crypto::ed25519;

use crate::auth::{AuthMsg, AuthNode};
use crate::proto::{issue_capability, vote, Capability, Commit, PubKey, QuorumCert, Roster};

/// A deterministic per-index signing seed.
pub fn seed(n: u8) -> [u8; 32] {
    [n; 32]
}

/// The issuer seed (a distinct principal that signs capabilities).
pub fn issuer_seed() -> [u8; 32] {
    seed(200)
}

/// The closed identity initial store `λ_:atom0. x` (closed, as the transport
/// theorems' `ClosedTm` premises require).
pub fn init() -> Term {
    Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)))
}

/// Two OPERATIONALLY DISTINCT commands so divergence is visible in the store:
/// `dup` (`s ↦ ⟨s,s⟩`) and `id` (`s ↦ s`). (A `Prop`-annotation-only difference
/// would reduce identically — see `tests/byzantine.rs`.)
pub fn cmd(dup: bool) -> Command {
    let body = if dup {
        Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))
    } else {
        Term::Var(0)
    };
    Command {
        payload: Term::Lam(Box::new(Prop::Atom(0)), Box::new(body)),
        cap: Some(Prop::Atom(7)),
    }
}

/// A capability for `c`, signed by the issuer.
pub fn cap_for(c: &Command) -> Capability {
    issue_capability(&issuer_seed(), c)
}

/// The public keys for a cluster of `n` replicas (seats `0..n`).
pub fn keys(n: u32) -> Vec<PubKey> {
    (0..n)
        .map(|i| ed25519::public_key(&seed(i as u8)))
        .collect()
}

/// A crash roster of `n` (strict-majority quorum).
pub fn crash_roster(n: u32) -> Roster {
    Roster::new(keys(n)).expect("distinct")
}

/// A Byzantine roster of `n` (`3·card > 2n` quorum).
pub fn byz_roster(n: u32) -> Roster {
    Roster::new_byzantine(keys(n)).expect("distinct")
}

/// Build an honest replica for `roster` at `idx` (leader = 0).
fn node(idx: u32, roster: Roster) -> AuthNode {
    AuthNode::new(
        seed(idx as u8),
        roster,
        idx,
        0,
        init(),
        FailureBudget::zero(1),
    )
    .expect("seed matches seat")
}

/// The outcome of an equivocation scenario: what each honest applier ended on.
pub struct EquivOutcome {
    /// `(replica index, rendered store)` for each honest replica that applied.
    pub applied: Vec<(u32, Term)>,
    /// Whether two honest replicas ended on DIFFERENT stores (safety violation).
    pub diverged: bool,
}

/// Drive an equivocating leader against `roster`, distributing command `a` to the
/// replicas in `to_a` and command `b` to those in `to_b`, then have the leader
/// assemble a certificate for EACH side (pairing its own equivocating vote with
/// the honest votes it received) and deliver each side's commit to its group.
///
/// Returns what the honest appliers ended on. Under a crash roster the two
/// f+1-size certificates both form → divergence; under a Byzantine roster only a
/// side with ≥ a Byzantine quorum of honest votes forms → no divergence.
pub fn equivocation(roster: Roster, to_a: &[u32], to_b: &[u32]) -> EquivOutcome {
    let (a, b) = (cmd(true), cmd(false));

    // The Byzantine leader (seat 0) signs a vote for BOTH commands — the one
    // equivocating act. Honest followers each vote for the single command they
    // were shown.
    let mut votes_a = vec![vote(&seed(0), 0, &a)];
    for &i in to_a {
        votes_a.push(vote(&seed(i as u8), 0, &a));
    }
    let mut votes_b = vec![vote(&seed(0), 0, &b)];
    for &i in to_b {
        votes_b.push(vote(&seed(i as u8), 0, &b));
    }

    let commit_a = Commit {
        slot: 0,
        cmd: a.clone(),
        qc: QuorumCert { votes: votes_a },
    };
    let commit_b = Commit {
        slot: 0,
        cmd: b.clone(),
        qc: QuorumCert { votes: votes_b },
    };

    // Deliver each side's commit to its honest group; each replica applies only
    // if `verify_commit` accepts the certificate under the roster's threshold.
    let mut applied: Vec<(u32, Term)> = Vec::new();
    for &i in to_a {
        let mut nd = node(i, roster.clone());
        nd.handle(AuthMsg::Commit(commit_a.clone()));
        if nd.applied() == 1 {
            applied.push((i, nd.store().clone()));
        }
    }
    for &i in to_b {
        let mut nd = node(i, roster.clone());
        nd.handle(AuthMsg::Commit(commit_b.clone()));
        if nd.applied() == 1 {
            applied.push((i, nd.store().clone()));
        }
    }

    let diverged = applied
        .iter()
        .any(|(_, s1)| applied.iter().any(|(_, s2)| s1 != s2));
    EquivOutcome { applied, diverged }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The demo's headline claim is a CHECKED test, not just console output: the
    /// same equivocation diverges under a crash roster and is defeated under a
    /// Byzantine roster. (The handler-level proof is in `tests/byzantine.rs`;
    /// this pins the exact scenario the binary prints.)
    #[test]
    fn demo_equivocation_diverges_only_under_crash() {
        let crash = equivocation(crash_roster(3), &[1], &[2]);
        assert!(
            crash.diverged,
            "crash roster must diverge under an equivocating leader"
        );
        assert_eq!(crash.applied.len(), 2, "both crash-quorum sides commit");

        let byz = equivocation(byz_roster(4), &[1, 2], &[3]);
        assert!(
            !byz.diverged,
            "Byzantine roster must NOT diverge — the quorum threshold defeats equivocation"
        );
        // Only the c_a side (2 honest + leader = 3 = a Byzantine quorum) commits;
        // the c_b side (1 honest + leader = 2) does not.
        assert_eq!(
            byz.applied.len(),
            2,
            "only the quorum-reaching side's replicas applied"
        );
        assert!(byz.applied.iter().all(|(_, s)| *s == byz.applied[0].1));
    }

    /// Both demo commands are closed and operationally distinct — so divergence
    /// is observable in the store (the `tests/byzantine.rs` lesson).
    #[test]
    fn demo_commands_are_distinct() {
        use dlc_core::rsm::apply_prefix;
        let a = apply_prefix(&init(), &[cmd(true)]);
        let b = apply_prefix(&init(), &[cmd(false)]);
        assert_ne!(a, b, "dup and id must produce different stores");
    }
}
