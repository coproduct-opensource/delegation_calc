//! `cargo run -p dlc-d-node` — a DLC-D cluster, running.
//!
//! Three scenarios, in order: healthy convergence, a crash inside the declared
//! failure budget, and a crash outside it. The third is the important one: over
//! budget the cluster must **stall with its safety intact**, not diverge. That is
//! the runtime shadow of `DLCD.budgeted_guarantee_voids_over_budget` — behaviour
//! is void exactly over budget.
//!
//! Nothing printed here is a proof. What the run demonstrates is that the
//! deployed transitions are the verified ones (`spec/r6-1-node-design.md` §0) and
//! that the failure envelope behaves as declared.

use std::time::Duration;

use dlc_core::rsm::{apply_prefix, FailureBudget};
use dlc_d_node::demo;
use dlc_d_node::net::{run_cluster, ClusterConfig, ClusterOutcome};

#[tokio::main(flavor = "current_thread")]
async fn main() {
    println!("DLC-D node — trusted shell over the verified RSM transition core");
    println!("  transitions: dlc_core::rsm::{{commit, world_step}} (R2-corresponded)");
    println!("  decisions:   dlc_d_rsm::consensus::decided");
    println!("  transport:   in-process channels (TRUSTED — see spec/r6-1-node-design.md §5)\n");

    // ---------------------------------------------------------------- healthy
    let outcome = run(3, vec![], FailureBudget::zero(1)).await;
    report("3 replicas, no faults, budget f=1", &outcome);

    // ------------------------------------------------- one crash, IN budget
    let mut budget = FailureBudget::zero(1);
    budget.consumed = 1;
    let outcome = run(3, vec![2], budget).await;
    report("3 replicas, 1 crashed (consumed 1 ≤ f=1)", &outcome);

    // ---------------------------------------------- three crashes, OVER budget
    let mut budget = FailureBudget::zero(2);
    budget.consumed = 3;
    let outcome = run(5, vec![2, 3, 4], budget).await;
    report("5 replicas, 3 crashed (consumed 3 > f=2)", &outcome);
}

async fn run(size: u32, crashed: Vec<u32>, budget: FailureBudget) -> ClusterOutcome {
    run_cluster(ClusterConfig {
        size,
        leader: 0,
        init: demo::init(),
        workload: demo::workload(),
        crashed,
        budget,
        settle: Duration::from_millis(500),
    })
    .await
}

fn report(title: &str, o: &ClusterOutcome) {
    let expected = demo::workload().len();
    let model = apply_prefix(&demo::init(), &demo::workload());

    println!("── {title}");
    println!("   within contract : {}", contract(o));
    println!(
        "   live replicas   : {:?}",
        o.views.keys().collect::<Vec<_>>()
    );
    println!("   committed slots : {} of {expected}", o.committed());
    println!("   converged       : {}", o.converged());
    println!("   complete        : {}", o.complete);

    let stores = o.stores();
    match stores.first() {
        None => println!("   store           : (no live replica)\n"),
        Some(s) => {
            println!("   store           : {}", render(s));
            println!("   == model prefix : {}", *s == model);
            println!("   != initial store: {}\n", *s != demo::init());
        }
    }
}

fn contract(o: &ClusterOutcome) -> bool {
    o.views
        .values()
        .next()
        .map(|v| v.budget.within_contract())
        .unwrap_or(false)
}

/// A compact rendering of a store term — enough to see convergence at a glance.
fn render(t: &dlc_core::syntax::Term) -> String {
    use dlc_core::syntax::Term;
    match t {
        Term::Var(i) => format!("x{i}"),
        Term::Lam(_, b) => format!("λ.{}", render(b)),
        Term::Pair(a, b) => format!("⟨{}, {}⟩", render(a), render(b)),
        Term::Fst(a) => format!("π₁ {}", render(a)),
        Term::Snd(a) => format!("π₂ {}", render(a)),
        Term::App(f, a) => format!("({} {})", render(f), render(a)),
        other => format!("{other:?}"),
    }
}
