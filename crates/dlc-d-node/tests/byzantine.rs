//! Byzantine analysis of the authenticated node — what `verify_commit`'s
//! certificate check actually buys, and the claim it does NOT support.
//!
//! This file exists because the R6.1b code and docs claimed, in several places,
//! that checking the quorum certificate rather than the sender makes agreement
//! "survive a Byzantine leader". Writing the adversary down shows that claim is
//! **overstated**, and pins the honest one in its place. Same discipline as the
//! ProVerif cross-check that corrected the capability claim: a property is only
//! as strong as the attack it actually withstands.
//!
//! # The protocol's real fault model
//!
//! The single-decree protocol here is **crash-fault** (n = 2f+1, quorum = f+1),
//! matching `DLCD.Consensus` — NOT the Byzantine model of
//! `DLCD.ByzantineConsensus` (n ≥ 3f+1). Its safety rests on each replica voting
//! at most once per slot, which the honest node enforces with its ballot but
//! which does **not** bind an adversary that holds a key. The Tamarin
//! `slot_agreement` lemma is honest about this: it holds *"unless a key was
//! revealed"*, and a Byzantine leader signing conflicting votes with its own key
//! IS that excluded case.
//!
//! # What the certificate check DOES buy (forgery resistance)
//!
//! `verify_commit` checking the certificate defeats a leader that tries to
//! *fabricate* a decision — announce a commit it never actually collected a
//! quorum for. That is the class of the Nethermind XDC bug, and it is real value
//! (`leader_cannot_fabricate_a_commit`). What it does NOT defeat is a leader that
//! *equivocates* using its own key (`equivocating_leader_can_force_divergence`).

use dlc_core::rsm::{Command, FailureBudget};
use dlc_core::syntax::{Prop, Term};
use dlc_crypto::ed25519;
use dlc_d_node::auth::{AuthMsg, AuthNode};
use dlc_d_node::proto::{vote, Commit, Quorum, QuorumCert, Roster, Vote};

fn seed(n: u8) -> [u8; 32] {
    [n; 32]
}

/// Two OPERATIONALLY DISTINCT commands, so divergence is observable in the store
/// (not just in the command struct). `cmd(1)` = `dup` (`s ↦ ⟨s,s⟩`), `cmd(2)` =
/// `id` (`s ↦ s`). An earlier version differed only in a `Prop` annotation
/// *inside* the lambda, which does not affect reduction, so both produced the
/// same store and the equivocation was invisible — the test caught that.
fn cmd(tag: u32) -> Command {
    let body = if tag == 1 {
        // dup: ⟨x, x⟩
        Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))
    } else {
        // id: x
        Term::Var(0)
    };
    Command {
        payload: Term::Lam(Box::new(Prop::Atom(0)), Box::new(body)),
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
    .unwrap()
}

fn follower(idx: u32) -> AuthNode {
    AuthNode::new(
        seed((idx + 1) as u8),
        roster3(),
        idx,
        0, // leader is idx 0
        init(),
        FailureBudget::zero(1),
    )
    .unwrap()
}

/// ★ THE CORRECTION. A Byzantine leader that signs conflicting votes with its
/// OWN key forces two honest followers to apply different commands at the same
/// slot. So agreement does NOT "survive a Byzantine leader" — the certificate
/// check does not stop equivocation.
///
/// The mechanism, and why the certificate check is powerless against it: with
/// n=3, quorum=2, the leader pairs its own vote with each honest follower's
/// genuine vote. `{leader:c1, f1:c1}` and `{leader:c2, f2:c2}` are each two
/// DISTINCT valid signers, so both certificates pass `verify_qc` — they are not
/// forged, they are genuinely collected. The leader simply voted twice, which
/// its own ballot would forbid but which nothing can forbid an adversary holding
/// the key. This is precisely the "unless a key was revealed" case the Tamarin
/// `slot_agreement` lemma excludes.
#[test]
fn equivocating_leader_can_force_divergence() {
    let (c1, c2) = (cmd(1), cmd(2));
    let mut f1 = follower(1);
    let mut f2 = follower(2);

    // Every vote below is GENUINE — f1 really would vote c1 on receiving a
    // proposal for c1, the leader really signed both. The only Byzantine act is
    // the leader (seed 1) signing two votes for the same slot.
    let qc1 = QuorumCert {
        votes: vec![vote(&seed(1), 0, &c1), vote(&seed(2), 0, &c1)],
    };
    let qc2 = QuorumCert {
        votes: vec![vote(&seed(1), 0, &c2), vote(&seed(3), 0, &c2)],
    };

    // Both certificates are VALID (two distinct signers each) — this is the point.
    assert!(dlc_d_node::proto::verify_qc(&qc1, 0, &c1, &roster3()));
    assert!(dlc_d_node::proto::verify_qc(&qc2, 0, &c2, &roster3()));

    // The leader sends each honest follower the commit it collected for that side.
    f1.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c1.clone(),
        qc: qc1,
    }));
    f2.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c2.clone(),
        qc: qc2,
    }));

    // DIVERGENCE at the same slot — the attack succeeds.
    assert_eq!(f1.applied(), 1);
    assert_eq!(f2.applied(), 1);
    assert_ne!(
        f1.store(),
        f2.store(),
        "the equivocating leader forced two honest replicas to different states — \
         so the protocol is NOT Byzantine-leader-tolerant (it is crash-fault)"
    );
}

/// ★ WHAT THE CERTIFICATE CHECK ACTUALLY BUYS. A leader that has NOT collected a
/// genuine quorum cannot make an honest follower apply anything — it cannot
/// fabricate a decision. This is the real, honest value of checking the
/// certificate rather than trusting the sender, and the class of the XDC bug.
#[test]
fn leader_cannot_fabricate_a_commit() {
    let c = cmd(1);
    let mut f = follower(1);

    // The leader has only its OWN vote (it never gathered a second). It tries to
    // pass off a "quorum" by repeating that one vote.
    let only_its_vote: Vote = vote(&seed(1), 0, &c);
    let fake = QuorumCert {
        votes: vec![only_its_vote.clone(), only_its_vote],
    };
    // One distinct signer is not a quorum of three — verify_qc refuses.
    assert!(!dlc_d_node::proto::verify_qc(&fake, 0, &c, &roster3()));

    // The follower rejects the commit and applies nothing.
    f.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c,
        qc: fake,
    }));
    assert_eq!(f.applied(), 0, "no genuine quorum → nothing applied");
    assert_eq!(f.log().len(), 0);
}

/// ★ THE OTHER HALF OF FORGERY RESISTANCE. An adversary without any honest
/// voter's key cannot manufacture a valid certificate at all: it can only sign
/// as itself, and one non-member (or one member) is never a quorum. Distinct
/// from the above — that was a member fabricating; this is a total outsider.
#[test]
fn outsider_cannot_manufacture_a_certificate() {
    let c = cmd(1);
    let mut f = follower(1);

    // seed 42 is not in the roster. It signs two (byte-different, both valid)
    // votes trying to look like two voters.
    let outsider = vote(&seed(42), 0, &c);
    let fake = QuorumCert {
        votes: vec![outsider.clone(), outsider],
    };
    assert!(!dlc_d_node::proto::verify_qc(&fake, 0, &c, &roster3()));

    f.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c,
        qc: fake,
    }));
    assert_eq!(f.applied(), 0);
}

/// The positive baseline: an HONEST leader (which votes at most once per slot)
/// never equivocates, so honest-key clusters agree. Without this the corrections
/// above could be read as "the protocol is broken" — it is not; it is
/// crash-fault-correct, and only a *compromised* leader breaks agreement.
#[test]
fn honest_key_cluster_agrees() {
    let c = cmd(1);
    let mut f1 = follower(1);
    let mut f2 = follower(2);

    // The one genuine certificate an honest leader would build for c.
    let qc = QuorumCert {
        votes: vec![vote(&seed(1), 0, &c), vote(&seed(2), 0, &c)],
    };
    f1.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c.clone(),
        qc: qc.clone(),
    }));
    f2.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c,
        qc,
    }));

    assert_eq!(f1.applied(), 1);
    assert_eq!(f2.applied(), 1);
    assert_eq!(f1.store(), f2.store(), "honest-key cluster converges");
}

// ===========================================================================
// The FIX: a Byzantine quorum threshold (n≥3f+1, `3·card > 2n`) defeats the
// same equivocation attack — realizing `DLCD.ByzantineConsensus.byz_agreement`
// at the runtime. `Roster::new_byzantine` selects it.
// ===========================================================================

fn seed_n(n: u8) -> [u8; 32] {
    [n; 32]
}

/// A 4-member Byzantine roster (n=4, f=1): quorum needs `3·card > 8`, i.e. ≥ 3
/// distinct signers.
fn byz_roster4() -> Roster {
    Roster::new_byzantine((1u8..=4).map(|i| ed25519::public_key(&seed_n(i))).collect()).unwrap()
}

fn byz_follower(idx: u32) -> AuthNode {
    AuthNode::new(
        seed_n((idx + 1) as u8),
        byz_roster4(),
        idx,
        0,
        init(),
        FailureBudget::zero(1),
    )
    .unwrap()
}

/// ★ THE FIX. The exact equivocation from `equivocating_leader_can_force_
/// divergence`, run against a Byzantine roster, is DEFEATED: the leader cannot
/// assemble two valid certificates, so no honest replica diverges.
///
/// Why (the honest-intersection argument, `byz_quorum_honest_intersect`): a
/// certificate now needs 3 of 4 distinct signers. The Byzantine leader supplies
/// at most its own 1 signature to each side, so each conflicting certificate
/// needs ≥ 2 HONEST signers. There are only 3 honest replicas and each votes
/// once, so 2 + 2 = 4 distinct honest votes are impossible — at most one side
/// reaches quorum. Equivocation is blocked in a single round.
#[test]
fn byzantine_quorum_defeats_equivocation() {
    let (c1, c2) = (cmd(1), cmd(2));

    // The adversary splits the 3 honest replicas as favourably as it can: two
    // toward c1 (idx 1, 2), one toward c2 (idx 3), plus its own equivocating
    // votes. This is the best case for the attacker.
    let qc1 = QuorumCert {
        votes: vec![
            vote(&seed_n(1), 0, &c1), // Byzantine leader
            vote(&seed_n(2), 0, &c1),
            vote(&seed_n(3), 0, &c1),
        ],
    };
    let qc2 = QuorumCert {
        votes: vec![
            vote(&seed_n(1), 0, &c2), // Byzantine leader equivocates
            vote(&seed_n(4), 0, &c2),
        ],
    };

    // c1 reaches the Byzantine quorum (3 distinct); c2 cannot (only 2).
    assert!(dlc_d_node::proto::verify_qc(&qc1, 0, &c1, &byz_roster4()));
    assert!(
        !dlc_d_node::proto::verify_qc(&qc2, 0, &c2, &byz_roster4()),
        "c2 has only 2 of the required 3 distinct signers — no second certificate"
    );

    // Deliver both commits to two honest followers; only the c1 side applies.
    let mut fa = byz_follower(1);
    let mut fb = byz_follower(3);
    fa.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c1.clone(),
        qc: qc1,
    }));
    fb.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c2,
        qc: qc2,
    }));

    // fb REJECTED the forged c2 commit (no quorum) → it applied nothing → NO
    // divergence. fa applied c1.
    assert_eq!(fa.applied(), 1);
    assert_eq!(
        fb.applied(),
        0,
        "the equivocating side never reached quorum"
    );
    assert_ne!(fa.store(), &init());
    assert_eq!(
        fb.store(),
        &init(),
        "the honest replica did not diverge onto c2"
    );
}

/// The reason it works, isolated: two `2f+1` quorums out of `3f+1` cannot BOTH
/// be filled without reusing an honest signer. Even the adversary's most even
/// split (2 vs 1 of the 3 honest, at n=4) leaves the minority side one short.
#[test]
fn two_byzantine_quorums_cannot_both_form() {
    let r = byz_roster4();
    // Best case for the attacker: honest votes split as evenly as possible.
    // With 3 honest, that is 2 and 1 — and 1 (+ the 1 Byzantine) = 2 < 3.
    assert!(r.is_quorum(3), "3 distinct is a Byzantine quorum of 4");
    assert!(!r.is_quorum(2), "2 distinct is not");
    // So the side with only 1 honest voter can never reach 3, whatever the
    // Byzantine leader signs (it is one identity, one distinct signer).
}

/// The threshold boundary, and that it is strictly stronger than crash. Crash
/// would have accepted the 2-signer c2 certificate (2·2 > 4 is false — actually
/// tie); the Byzantine threshold rejects it. Pins `Quorum::reached`.
#[test]
fn byzantine_threshold_is_strictly_stronger() {
    // n = 4.
    assert!(Quorum::Crash.reached(3, 4)); // 6 > 4
    assert!(Quorum::Byzantine.reached(3, 4)); // 9 > 8
                                              // The separating case: 3-of-4 distinct.
                                              // A 2-of-4 that crash *almost* accepts but byzantine firmly rejects:
    assert!(!Quorum::Crash.reached(2, 4)); // 4 > 4 is false (tie is not a majority)
    assert!(!Quorum::Byzantine.reached(2, 4)); // 6 > 8 is false
                                               // n = 3 (crash territory): crash accepts 2, byzantine demands 3.
    assert!(Quorum::Crash.reached(2, 3)); // 4 > 3
    assert!(!Quorum::Byzantine.reached(2, 3)); // 6 > 6 is false
    assert!(Quorum::Byzantine.reached(3, 3)); // 9 > 6
}

/// An honest Byzantine-roster cluster still converges — the stronger threshold
/// does not break the happy path (anti-vacuity for the fix).
#[test]
fn byzantine_honest_cluster_still_converges() {
    let c = cmd(1);
    let qc = QuorumCert {
        votes: vec![
            vote(&seed_n(1), 0, &c),
            vote(&seed_n(2), 0, &c),
            vote(&seed_n(3), 0, &c),
        ],
    };
    let mut fa = byz_follower(1);
    let mut fb = byz_follower(2);
    fa.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c.clone(),
        qc: qc.clone(),
    }));
    fb.handle(AuthMsg::Commit(Commit {
        slot: 0,
        cmd: c,
        qc,
    }));
    assert_eq!(fa.applied(), 1);
    assert_eq!(fb.applied(), 1);
    assert_eq!(fa.store(), fb.store());
}

/// ★ REGRESSION for a latent bug the n=4 tests could not catch. A Byzantine
/// LEADER must decide with the Byzantine threshold, not the crash one. At n=7
/// (f=2) they DIVERGE — crash quorum is 4 (`2·4 > 7`), Byzantine quorum is 5
/// (`3·5 > 14`). The leader collecting only 4 votes must NOT commit, because its
/// followers verify against the Byzantine bar and would reject a 4-vote
/// certificate. `auth.rs` originally used the crash `decided` unconditionally,
/// which coincides at n=4 but would have let a 7-node Byzantine leader commit
/// prematurely (a self-inflicted stall, and a broken threshold). The fix
/// dispatches the leader's decision on the roster's `Quorum` mode.
#[tokio::test]
async fn byzantine_leader_needs_byzantine_quorum() {
    use dlc_d_node::netauth::{run_auth_cluster, AuthClusterConfig};
    use dlc_d_node::proto::{issue_capability, Capability};
    use std::time::Duration;

    let seeds: Vec<[u8; 32]> = (1u8..=7).map(seed_n).collect();
    let roster = Roster::new_byzantine(seeds.iter().map(ed25519::public_key).collect()).unwrap();
    // Sanity: the two thresholds genuinely differ at n=7.
    assert!(Quorum::Crash.reached(4, 7), "crash quorum is 4 at n=7");
    assert!(
        !Quorum::Byzantine.reached(4, 7),
        "Byzantine quorum is NOT 4 at n=7"
    );
    assert!(
        Quorum::Byzantine.reached(5, 7),
        "Byzantine quorum is 5 at n=7"
    );

    let c = cmd(1);
    let cap: Capability = issue_capability(&seed_n(9), &c);

    // ALL 7 honest: 7 votes ≥ the Byzantine quorum of 5, so it commits — the
    // proof the leader is using the RIGHT (reachable) threshold, not that it
    // never commits.
    let o = run_auth_cluster(AuthClusterConfig {
        seeds: seeds.clone(),
        roster: roster.clone(),
        leader: 0,
        init: init(),
        workload: vec![(c.clone(), cap.clone())],
        crashed: vec![],
        budget: FailureBudget::zero(2),
        settle: Duration::from_millis(3_000),
    })
    .await;
    assert!(o.complete, "7 honest votes clear the Byzantine quorum of 5");
    assert!(o.converged());

    // Now crash 3 of 7: only 4 honest remain. 4 < the Byzantine quorum of 5, so
    // the leader must NOT commit — even though 4 IS a crash quorum. This is the
    // case the old crash-`decided` leader would have wrongly committed (then
    // stalled, its 4-vote cert rejected by followers). Correct behaviour: stall
    // cleanly, nothing applied, no divergence.
    let o2 = run_auth_cluster(AuthClusterConfig {
        seeds,
        roster,
        leader: 0,
        init: init(),
        workload: vec![(c, cap)],
        crashed: vec![4, 5, 6],
        budget: FailureBudget::zero(2),
        settle: Duration::from_millis(1_000),
    })
    .await;
    assert!(
        !o2.complete,
        "4 votes must NOT reach the Byzantine quorum of 5"
    );
    assert_eq!(
        o2.committed(),
        0,
        "the leader correctly withheld the commit"
    );
    for v in o2.views.values() {
        assert_eq!(
            v.replicas[0].applied, 0,
            "no replica applied — clean stall, no divergence"
        );
    }
}
