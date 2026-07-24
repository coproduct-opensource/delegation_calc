//! End-to-end: the authenticated protocol (`proto`) drives the VERIFIED
//! transition core (`dlc_core::rsm`).
//!
//! `proto`'s own unit tests prove each check in isolation. This test proves the
//! pieces COMPOSE into one run — issue → propose → verify → vote → certify →
//! verify-commit → apply — and that the thing applied by the verified `commit` /
//! `world_step` is exactly the command the certificate decided. Without it,
//! `proto` would be a library reachable only from its own `#[cfg(test)]` module:
//! green, and calling nothing real.
//!
//! It is the byte-level counterpart of `ensemble_refines_world_step` in
//! `cluster.rs`: that test shows the unauthenticated in-process node refines the
//! model; this one shows the authenticated protocol's accepted output feeds the
//! same verified transitions. The two meet when the live event loop is keyed
//! (the next increment); until then this test is what keeps `proto` wired to the
//! verified core.

use dlc_core::rsm::{
    apply_prefix, commit, world_step, Command, FailureBudget, GlobalConfig, Replica,
};
use dlc_core::syntax::{Prop, Term};
use dlc_crypto::ed25519;
use dlc_d_node::proto::{
    issue_capability, propose, verify_commit, verify_proposal, vote, Capability, Commit, Proposal,
    QuorumCert, Roster, Vote,
};

fn seed(n: u8) -> [u8; 32] {
    [n; 32]
}

/// The demo `dup` command carrying a real capability slot.
fn dup_cmd() -> Command {
    Command {
        payload: Term::Lam(
            Box::new(Prop::Atom(0)),
            Box::new(Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(0)))),
        ),
        cap: Some(Prop::Atom(7)),
    }
}

fn roster3() -> Roster {
    Roster::new(vec![
        ed25519::public_key(&seed(1)),
        ed25519::public_key(&seed(2)),
        ed25519::public_key(&seed(3)),
    ])
    .expect("distinct members")
}

/// One authenticated slot decision, end to end, feeding the verified core.
///
/// Every step is the real `proto` function a networked node would call, and the
/// final store is produced by the verified `commit` + `world_step` — not by a
/// hand-applied command. The assertion pins that the verified transition applied
/// exactly the certified command.
#[test]
fn authenticated_decision_drives_the_verified_core() {
    let r = roster3();
    let c = dup_cmd();

    // 1. Issuer signs a capability; leader proposes; replicas verify BEFORE voting.
    let cap = issue_capability(&seed(9), &c);
    let p: Proposal = propose(&seed(1), 0, c.clone(), cap);
    assert!(verify_proposal(&p, &r), "honest proposal must verify");

    // 2. Two distinct replicas vote (they verified the proposal first).
    let v1: Vote = vote(&seed(1), 0, &c);
    let v2: Vote = vote(&seed(2), 0, &c);
    let qc = QuorumCert {
        votes: vec![v1, v2],
    };

    // 3. A commit is only as good as its certificate — verify_commit takes NO
    //    sender. This is the Byzantine-leader-tolerant check.
    let cm = Commit {
        slot: 0,
        cmd: c.clone(),
        qc,
    };
    assert!(
        verify_commit(&cm, &r),
        "a real quorum certificate must verify"
    );

    // 4. ONLY after the certificate verifies do we touch the verified core:
    //    append via `commit`, advance via `world_step`.
    let g0 = GlobalConfig {
        replicas: vec![
            Replica {
                id: 0,
                store: Term::Var(0),
                applied: 0,
            },
            Replica {
                id: 1,
                store: Term::Var(0),
                applied: 0,
            },
        ],
        log: vec![],
        budget: FailureBudget::zero(1),
    };
    let g1 = commit(&g0, cm.cmd.clone());
    let g2 = world_step(&world_step(&g1)); // both replicas deliver slot 0

    // 5. The verified transition applied exactly the certified command.
    let expected = apply_prefix(&Term::Var(0), &[cm.cmd]);
    assert_eq!(g2.replicas[0].store, expected);
    assert_eq!(g2.replicas[0].store, g2.replicas[1].store);
    assert_ne!(
        g2.replicas[0].store,
        Term::Var(0),
        "the store genuinely changed"
    );
}

/// A forged certificate is rejected, so the verified core is NEVER reached for
/// an unauthorized command. This is the negative half: the gate in front of the
/// verified transitions actually gates.
#[test]
fn forged_certificate_never_reaches_the_core() {
    let r = roster3();
    let c = dup_cmd();

    // One replica's single vote, replicated three times — the XDC forgery.
    let v = vote(&seed(1), 0, &c);
    let qc = QuorumCert {
        votes: vec![v.clone(), v.clone(), v],
    };
    let cm = Commit {
        slot: 0,
        cmd: c,
        qc,
    };

    assert!(
        !verify_commit(&cm, &r),
        "a single-signer certificate must not verify — else the core applies an unauthorized command"
    );
}

/// The capability gate composes with the protocol: a command whose capability
/// was issued for a DIFFERENT command cannot be proposed, so it never reaches a
/// vote, so it never reaches the core.
#[test]
fn unauthorized_capability_stops_at_the_proposal() {
    let r = roster3();
    let real = dup_cmd();
    let other = Command {
        payload: Term::Var(5),
        cap: Some(Prop::Atom(7)),
    };
    // Capability issued for `other`, stapled onto `real`.
    let cap_for_other: Capability = issue_capability(&seed(9), &other);
    let p = propose(&seed(1), 0, real, cap_for_other);
    assert!(
        !verify_proposal(&p, &r),
        "a mismatched capability must fail at verify_proposal, before any vote"
    );
}
