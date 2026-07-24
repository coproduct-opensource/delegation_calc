//! The scenarios of `spec/r6-1-node-design.md` §6, as tests.
//!
//! Positive convergence is not enough on its own: a cluster that converged on
//! its *initial* store would pass a naive test while demonstrating nothing, and
//! a cluster that "tolerates" a crash it never actually experienced would too.
//! So each test pins the store it converged ON, and the over-budget test asserts
//! the failure mode is a STALL, not divergence.

use std::time::Duration;

use dlc_core::rsm::{apply_prefix, world_step, FailureBudget};
use dlc_d_node::demo;
use dlc_d_node::net::{run_cluster, ClusterConfig, ClusterOutcome};
use dlc_d_node::{assemble, Node};

fn settle() -> Duration {
    Duration::from_millis(2_000)
}

async fn run(size: u32, crashed: Vec<u32>, budget: FailureBudget) -> ClusterOutcome {
    run_cluster(ClusterConfig {
        size,
        leader: 0,
        init: demo::init(),
        workload: demo::workload(),
        crashed,
        budget,
        settle: settle(),
    })
    .await
}

/// The model's answer for the demo workload — what a correct cluster must land on.
fn model_store() -> dlc_core::syntax::Term {
    apply_prefix(&demo::init(), &demo::workload())
}

// ---------------------------------------------------------------------------
// §6 scenario 1 — convergence, on the CHANGED store.
// ---------------------------------------------------------------------------

#[tokio::test]
async fn cluster_converges_on_the_changed_store() {
    let o = run(3, vec![], FailureBudget::zero(1)).await;

    assert!(
        o.complete,
        "every live replica should apply the whole workload"
    );
    assert!(o.converged(), "replicas must agree");
    assert_eq!(o.views.len(), 3);
    assert_eq!(o.committed(), demo::workload().len());

    let store = o.stores()[0].clone();
    // Converged on the MODEL's answer …
    assert_eq!(store, model_store());
    // … and that answer is genuinely not the initial store (anti-vacuity: a
    // cluster agreeing on `init` would pass a weaker assertion trivially).
    assert_ne!(store, demo::init());

    // Every replica applied every slot.
    for v in o.views.values() {
        assert_eq!(v.replicas[0].applied as usize, demo::workload().len());
        assert_eq!(v.log.len(), demo::workload().len());
    }
}

/// Log ORDER is observable in the final store, so the total order the consensus
/// layer provides is load-bearing rather than decorative.
#[test]
fn log_order_is_observable() {
    let forward = apply_prefix(&demo::init(), &demo::workload());
    let mut permuted = demo::workload();
    permuted.reverse();
    let backward = apply_prefix(&demo::init(), &permuted);
    assert_ne!(forward, backward);
}

// ---------------------------------------------------------------------------
// §6 scenario 2 — a crash INSIDE the declared budget: progress continues.
// ---------------------------------------------------------------------------

#[tokio::test]
async fn quorum_survives_one_crash_within_budget() {
    let mut budget = FailureBudget::zero(1);
    budget.consumed = 1;
    assert!(budget.within_contract(), "1 ≤ f=1 is within contract");

    let o = run(3, vec![2], budget).await;

    assert_eq!(o.views.len(), 2, "the crashed replica never starts");
    assert!(
        o.complete,
        "2 of 3 is still a quorum — the cluster makes progress"
    );
    assert!(o.converged());
    assert_eq!(o.stores()[0], model_store());
    assert_ne!(o.stores()[0], demo::init());
}

// ---------------------------------------------------------------------------
// §6 scenario 3 — the BITE. Over budget: stall, with safety intact.
// ---------------------------------------------------------------------------

/// Over the declared budget the cluster must lose LIVENESS and keep SAFETY: no
/// quorum forms, so nothing is decided, so no replica moves — and crucially the
/// survivors do NOT diverge. This is the runtime shadow of
/// `DLCD.budgeted_guarantee_voids_over_budget` (behaviour void exactly over
/// budget), and it must fail in that specific way: a test that merely observed
/// "not complete" would also pass if the cluster had committed different logs on
/// different replicas, which is the outcome that would actually matter.
#[tokio::test]
async fn over_budget_stalls_without_diverging() {
    let mut budget = FailureBudget::zero(2);
    budget.consumed = 3;
    assert!(!budget.within_contract(), "3 > f=2 is over contract");

    let o = run(5, vec![2, 3, 4], budget).await;

    assert_eq!(o.views.len(), 2, "two survivors");
    // LIVENESS LOST: 2 of 5 is not a quorum (2*2 > 5 is false), so nothing commits.
    assert!(!o.complete);
    assert_eq!(o.committed(), 0, "no slot may be decided without a quorum");
    // SAFETY KEPT: the survivors agree, and agree on the untouched initial store.
    assert!(o.converged(), "a stalled cluster must not diverge");
    for v in o.views.values() {
        assert_eq!(v.replicas[0].store, demo::init());
        assert_eq!(v.replicas[0].applied, 0);
        assert!(v.log.is_empty());
    }
}

/// The leader alone cannot commit: a single node in a 3-cluster is not a quorum,
/// so the verified decision predicate refuses and the store never moves. Without
/// this, "the cluster stalled" could be an artifact of the transport rather than
/// of the quorum rule.
#[tokio::test]
async fn leader_alone_cannot_commit() {
    let mut budget = FailureBudget::zero(1);
    budget.consumed = 2;
    let o = run(3, vec![1, 2], budget).await;

    assert_eq!(o.views.len(), 1);
    assert_eq!(o.committed(), 0);
    let v = o.views.values().next().unwrap();
    assert_eq!(v.replicas[0].store, demo::init());
}

/// A single-replica cluster IS a quorum of itself, so it commits — the boundary
/// on the other side of `is_quorum`. Without it, `leader_alone_cannot_commit`
/// could be passing because the leader path is broken rather than because the
/// quorum rule bites.
#[tokio::test]
async fn singleton_cluster_is_its_own_quorum() {
    let o = run(1, vec![], FailureBudget::zero(0)).await;
    assert!(o.complete);
    assert_eq!(o.committed(), demo::workload().len());
    assert_eq!(o.stores()[0], model_store());
}

// ---------------------------------------------------------------------------
// §2.1 — the ensemble of local views refines the model's `world_step`.
// ---------------------------------------------------------------------------

/// Each node advances its own singleton view; the model steps every replica at
/// once. Assembling the nodes' views must reproduce the model exactly: stepping
/// the assembled *lagging* configuration equals the assembled *stepped* one.
///
/// This is the seam between "each node is correct" and "the cluster is the
/// model" — a scheduling bug in the shell shows up here and nowhere else.
#[test]
fn ensemble_refines_world_step() {
    let cmds = demo::workload();

    // Two nodes that have committed the same log but applied nothing yet.
    let mut a = Node::new(0, 2, 0, demo::init(), FailureBudget::zero(1));
    let mut b = Node::new(1, 2, 0, demo::init(), FailureBudget::zero(1));

    // Drive both through the same committed sequence via the real handlers.
    for (slot, c) in cmds.iter().enumerate() {
        let slot = slot as u32;
        a.handle(dlc_d_node::Msg::Commit {
            slot,
            cmd: c.clone(),
        });
        b.handle(dlc_d_node::Msg::Commit {
            slot,
            cmd: c.clone(),
        });
    }

    // The assembled cluster state.
    let ensemble = assemble(&[a.view().clone(), b.view().clone()]);

    // The model, run independently from the same start over the same log.
    let mut model = ensemble.clone();
    model.replicas[0].store = demo::init();
    model.replicas[0].applied = 0;
    model.replicas[1].store = demo::init();
    model.replicas[1].applied = 0;
    for _ in 0..cmds.len() {
        model = world_step(&model);
    }

    assert_eq!(ensemble, model, "the assembled cluster must BE the model");
    // And non-vacuously: the state actually moved.
    assert_ne!(ensemble.replicas[0].store, demo::init());
    assert_eq!(ensemble.replicas[0].store, ensemble.replicas[1].store);
}

/// A live cluster's assembled state is the model's, too — the same check over
/// states produced by the async event loop rather than by direct handler calls.
#[tokio::test]
async fn live_cluster_ensemble_refines_the_model() {
    let o = run(3, vec![], FailureBudget::zero(1)).await;
    assert!(o.complete);

    let views: Vec<_> = o.views.values().cloned().collect();
    let ensemble = assemble(&views);

    let mut model = ensemble.clone();
    for r in model.replicas.iter_mut() {
        r.store = demo::init();
        r.applied = 0;
    }
    for _ in 0..demo::workload().len() {
        model = world_step(&model);
    }

    assert_eq!(ensemble, model);
}
