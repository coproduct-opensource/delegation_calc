//! `cargo run -p dlc-d-node` — the AUTHENTICATED DLC-D node, running.
//!
//! What this demonstrates, in order:
//!   1. an authenticated cluster converging over the async byte transport;
//!   2. a crash within budget still committing; over budget stalling (safety);
//!   3. THE SAFETY PROPERTY, made visible: the same equivocating-leader attack
//!      DIVERGES under a crash roster and is DEFEATED under a Byzantine roster.
//!
//! Nothing printed here is a proof — the proofs are in Lean (`rust_byz_agreement`
//! et al.) and the symbolic models. What the run shows is that the deployed node
//! is the authenticated one, that every state transition goes through the
//! R2-corresponded `commit`/`world_step`, and that the Byzantine threshold
//! behaves as the theorem says.

use std::time::Duration;

use dlc_core::rsm::{apply_prefix, FailureBudget};
use dlc_core::syntax::Term;
use dlc_d_node::authdemo;
use dlc_d_node::netauth::{run_auth_cluster, AuthClusterConfig, AuthOutcome};

#[tokio::main(flavor = "current_thread")]
async fn main() {
    println!("DLC-D — the authenticated node, over the verified RSM transition core");
    println!("  transitions: dlc_core::rsm::{{commit, world_step}}   (R2-corresponded)");
    println!("  decision:    dlc_d_rsm::consensus::{{decided, byz_decided}}  (transported)");
    println!("  wire:        Ed25519 proposals / votes / quorum certificates (Tamarin+ProVerif)");
    println!("  transport:   in-process byte channels (TRUSTED — spec/r6-1-node-design.md §5)\n");

    // 1 ─ authenticated convergence (crash roster, n=3).
    let o = run(authdemo::crash_roster(3), 3, vec![], FailureBudget::zero(1)).await;
    report("crash roster n=3, no faults", &o);

    // 2 ─ crash within budget still commits; over budget stalls.
    let mut b = FailureBudget::zero(1);
    b.consumed = 1;
    let o = run(authdemo::crash_roster(3), 3, vec![2], b).await;
    report("crash roster n=3, 1 crashed (within budget)", &o);

    let mut b = FailureBudget::zero(1);
    b.consumed = 2;
    let o = run(authdemo::crash_roster(3), 3, vec![1, 2], b).await;
    report("crash roster n=3, 2 crashed (over budget → stall)", &o);

    // 3 ─ Byzantine roster (n=4) converges when honest.
    let o = run(authdemo::byz_roster(4), 4, vec![], FailureBudget::zero(1)).await;
    report("Byzantine roster n=4, no faults", &o);

    // 4 ─ THE SAFETY PROPERTY, side by side.
    println!("── equivocating leader: crash roster vs Byzantine roster");
    println!("   (leader seat 0 signs conflicting votes for two distinct commands)\n");

    // Crash n=3: leader pairs its equivocating vote with f1 (→c_a) and f2 (→c_b).
    // Both {leader,f1} and {leader,f2} are a crash quorum of 2 → both commit.
    let crash = authdemo::equivocation(authdemo::crash_roster(3), &[1], &[2]);
    print_equiv("crash roster n=3 (quorum 2)", &crash);

    // Byzantine n=4: leader shows c_a to {1,2} and c_b to {3}. {leader,1,2}=3 is a
    // Byzantine quorum; {leader,3}=2 is NOT → only the c_a side commits.
    let byz = authdemo::equivocation(authdemo::byz_roster(4), &[1, 2], &[3]);
    print_equiv("Byzantine roster n=4 (quorum 3)", &byz);

    println!(
        "   verdict: crash roster DIVERGED = {}; Byzantine roster DIVERGED = {}",
        crash.diverged, byz.diverged
    );
    println!("   → the Byzantine quorum threshold is what defeats equivocation");
    println!("     (rust_byz_agreement, spec/r6-1b-replication-protocol.md §6.5)");
}

async fn run(
    roster: dlc_d_node::proto::Roster,
    n: u32,
    crashed: Vec<u32>,
    budget: FailureBudget,
) -> AuthOutcome {
    let workload = vec![(authdemo::cmd(true), authdemo::cap_for(&authdemo::cmd(true)))];
    let seeds: Vec<[u8; 32]> = (0..n).map(|i| authdemo::seed(i as u8)).collect();
    run_auth_cluster(AuthClusterConfig {
        seeds,
        roster,
        leader: 0,
        init: authdemo::init(),
        workload,
        crashed,
        budget,
        settle: Duration::from_millis(500),
    })
    .await
}

fn report(title: &str, o: &AuthOutcome) {
    let model = apply_prefix(&authdemo::init(), &[authdemo::cmd(true)]);
    println!("── {title}");
    println!(
        "   live replicas : {:?}",
        o.views.keys().collect::<Vec<_>>()
    );
    println!("   committed     : {} slot(s)", o.committed());
    println!("   converged     : {}", o.converged());
    println!("   complete      : {}", o.complete);
    match o.stores().first() {
        None => println!("   store         : (no live replica)\n"),
        Some(s) => {
            println!("   store         : {}", render(s));
            println!("   == model      : {}\n", *s == model);
        }
    }
}

fn print_equiv(title: &str, o: &authdemo::EquivOutcome) {
    println!("   {title}:");
    for (i, s) in &o.applied {
        println!("       replica {i} applied {}", render(s));
    }
    if o.applied.is_empty() {
        println!("       (no replica applied)");
    }
    println!(
        "       diverged: {}  ({})\n",
        o.diverged,
        if o.diverged {
            "SAFETY VIOLATED — two honest replicas disagree"
        } else {
            "safe — no two honest replicas disagree"
        }
    );
}

/// A compact rendering of a store term — enough to see convergence at a glance.
fn render(t: &Term) -> String {
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
