//! The authenticated node over the async byte transport — the whole stack:
//! `proto` auth + Lean-transported `decided` + the `codec` wire frame + tokio.
//!
//! `auth.rs`'s tests prove the protocol on a deterministic harness; `codec.rs`'s
//! tests prove encode/decode preserves verification. This proves them TOGETHER
//! over concurrent tasks: every message crosses the channel as bytes and is
//! decoded before use, so a codec that broke verification, or a protocol bug the
//! async interleaving exposes, shows up here.

use std::time::Duration;

use dlc_core::rsm::{apply_prefix, Command, FailureBudget};
use dlc_core::syntax::{Prop, Term};
use dlc_crypto::ed25519;
use dlc_d_node::netauth::{run_auth_cluster, AuthClusterConfig, AuthOutcome};
use dlc_d_node::proto::{issue_capability, Capability, Roster};

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

fn fst_cmd() -> Command {
    Command {
        payload: Term::Lam(
            Box::new(Prop::Atom(0)),
            Box::new(Term::Fst(Box::new(Term::Var(0)))),
        ),
        cap: Some(Prop::Atom(7)),
    }
}

fn init() -> Term {
    Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)))
}

fn seeds3() -> Vec<[u8; 32]> {
    vec![seed(1), seed(2), seed(3)]
}

fn roster3() -> Roster {
    Roster::new(seeds3().iter().map(ed25519::public_key).collect()).unwrap()
}

/// Sign each workload command's capability with a separate issuer key.
fn with_caps(cmds: Vec<Command>) -> Vec<(Command, Capability)> {
    cmds.into_iter()
        .map(|c| {
            let cap = issue_capability(&seed(9), &c);
            (c, cap)
        })
        .collect()
}

async fn run(
    seeds: Vec<[u8; 32]>,
    crashed: Vec<u32>,
    budget: FailureBudget,
    workload: Vec<Command>,
) -> AuthOutcome {
    run_auth_cluster(AuthClusterConfig {
        seeds,
        roster: roster3(),
        leader: 0,
        init: init(),
        workload: with_caps(workload),
        crashed,
        budget,
        settle: Duration::from_millis(3_000),
    })
    .await
}

/// Three authenticated replicas, multi-slot workload, over the async byte
/// transport: they converge on the model's answer, having exchanged only encoded
/// frames.
#[tokio::test]
async fn authenticated_cluster_converges_over_the_wire() {
    let workload = vec![dup_cmd(), dup_cmd(), fst_cmd()];
    let o = run(seeds3(), vec![], FailureBudget::zero(1), workload.clone()).await;

    assert!(o.complete, "every live replica applied the whole workload");
    assert_eq!(o.views.len(), 3);
    assert!(o.converged());

    let expected = apply_prefix(&init(), &workload);
    assert_eq!(o.stores()[0], expected);
    assert_ne!(o.stores()[0], init(), "the store genuinely changed");
}

/// One crash within budget: 2 of 3 is still a quorum, and the survivors converge
/// over the wire.
#[tokio::test]
async fn one_crash_within_budget_converges_over_the_wire() {
    let mut budget = FailureBudget::zero(1);
    budget.consumed = 1;
    let o = run(seeds3(), vec![2], budget, vec![dup_cmd()]).await;

    assert_eq!(o.views.len(), 2);
    assert!(o.complete);
    assert!(o.converged());
    assert_eq!(o.stores()[0], apply_prefix(&init(), &[dup_cmd()]));
}

/// Over budget (2 of 3 crashed → no quorum possible): the cluster stalls without
/// diverging, over the wire too. The runtime shadow of
/// `budgeted_guarantee_voids_over_budget`, on the authenticated async path.
#[tokio::test]
async fn over_budget_stalls_over_the_wire() {
    let mut budget = FailureBudget::zero(1);
    budget.consumed = 2;
    let o = run(seeds3(), vec![1, 2], budget, vec![dup_cmd()]).await;

    assert_eq!(o.views.len(), 1, "one survivor");
    assert!(!o.complete);
    assert_eq!(o.committed(), 0, "no quorum, nothing committed");
    // Safety kept: the survivor sits on the untouched initial store.
    let v = o.views.values().next().unwrap();
    assert_eq!(v.replicas[0].store, init());
    assert_eq!(v.replicas[0].applied, 0);
}

/// A Byzantine-quorum roster (n=4, `3·card > 2n`) runs to convergence over the
/// async byte transport with an HONEST leader — so the stronger threshold works
/// end-to-end through the real node, not just in the direct-handler tests. Its
/// equivocation defence is proven in `byzantine.rs`; this shows the happy path
/// is intact when the node actually drives it.
#[tokio::test]
async fn byzantine_roster_converges_over_the_wire() {
    let seeds: Vec<[u8; 32]> = (1u8..=4).map(seed).collect();
    let roster = Roster::new_byzantine(seeds.iter().map(ed25519::public_key).collect()).unwrap();
    let workload = vec![dup_cmd(), fst_cmd()];

    let o = run_auth_cluster(AuthClusterConfig {
        seeds,
        roster,
        leader: 0,
        init: init(),
        workload: with_caps(workload.clone()),
        crashed: vec![],
        budget: FailureBudget::zero(1),
        settle: Duration::from_millis(3_000),
    })
    .await;

    assert!(o.complete, "honest Byzantine-roster cluster completes");
    assert_eq!(o.views.len(), 4);
    assert!(o.converged());
    assert_eq!(o.stores()[0], apply_prefix(&init(), &workload));
}
