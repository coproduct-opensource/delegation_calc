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
use dlc_d_node::proto::{vote, Commit, QuorumCert, Roster, Vote};

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
