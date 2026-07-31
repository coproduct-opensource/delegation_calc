//! `cargo run -p dlc-d-ledger` — **the governed replicated ledger, running.**
//!
//! One service, one attribute, four enforcement layers, in the order a real deployment meets
//! them:
//!
//!   1. **Build time.** The envelope's violations are `rustc` errors — the ledger you are
//!      running could not have compiled with an ungranted tool, an illegal flow, an
//!      over-budget composition, or a widening delegation (`tests/ui/`, each pinned).
//!   2. **Certificate.** The same demanded-vs-granted fact is decided by the VERIFIED checker,
//!      whose acceptance means a real typing derivation exists (`rust_infer_sound`).
//!   3. **Run time.** The typed witness is minted only from a real Ed25519 credential over the
//!      tool's cap atom — the same atom the certificate demands.
//!   4. **Replication.** The commands run on the authenticated cluster whose every transition
//!      is the R2-corresponded `commit`/`world_step`.
//!
//! Nothing printed here is a proof. The proofs are in Lean; this shows the deployed path is the
//! one they are about — and the same chain is enforcing tool calls in `nucleus` today
//! (`spec/nucleus-admission-integration.md`).

use dlc_core::rsm::apply_prefix;
use dlc_d::{Cap, Invoke, Tool as _};
use dlc_d_ledger::{
    admit_credit, budget, credit, init, teller_credit, treasury_credential, Credit, Seize, Teller,
};
use dlc_d_node::authdemo;
use dlc_d_node::netauth::{run_auth_cluster, AuthClusterConfig};
use dlc_d_node::proto::issue_capability;

#[tokio::main(flavor = "current_thread")]
async fn main() {
    println!("DLC-D — the governed replicated ledger");
    println!("  envelope:    cap = Invoke<Credit> @ Treasury, flow = Ledger <= Audit,");
    println!("               budget = Faults<1>, delegate = attenuate_only");
    println!("  transitions: dlc_core::rsm::{{commit, world_step}}   (R2-corresponded)");
    println!("  transport:   in-process byte channels (TRUSTED — the honest TCB)\n");

    // ── 1 ── Runtime admission: the witness comes FROM a verified credential.
    println!("── 1. runtime admission (Ed25519 over the tool's cap atom, fail-closed)");
    let (keyring, issuer, credential) = treasury_credential(Credit::NAME);
    let cap = match admit_credit(&keyring, &issuer, &credential) {
        Ok(c) => {
            println!(
                "   Treasury credential for \"{}\" → ADMITTED, witness minted",
                Credit::NAME
            );
            c
        }
        Err(e) => {
            eprintln!("   the demo's own credential failed to verify: {e:?}");
            std::process::exit(1);
        }
    };

    // The same issuer's credential for a DIFFERENT tool cannot mint this witness.
    let (_, _, seize_credential) = treasury_credential(Seize::NAME);
    match admit_credit(&keyring, &issuer, &seize_credential) {
        Err(_) => println!(
            "   Treasury credential for \"{}\" → REFUSED for Credit (tool-bound signature)\n",
            Seize::NAME
        ),
        Ok(_) => {
            eprintln!("   FAIL: a wrong-tool credential minted a Credit witness");
            std::process::exit(1);
        }
    }

    // ── 2 ── The governed calls. Each REQUIRES its witness: delete the argument and this
    // program does not compile (tests/ui/missing_witness.rs pins that error).
    println!("── 2. governed writes (each demands its capability witness at the type level)");
    let root_cmd = credit(2, cap);
    let delegated_cmd = teller_credit(1, Cap::<Invoke<Credit>, Teller>::unchecked());
    println!("   Treasury credit(2) and Teller credit(1) built");
    println!("   (the Teller's authority is a NARROWING delegation of the Treasury's:");
    println!("    delegating a tool the Treasury lacks fails to compile)\n");

    // ── 3 ── Replication on the verified transition core.
    println!("── 3. replication (authenticated cluster, n=4 Byzantine roster)");
    let issuer_seed = authdemo::issuer_seed();
    let workload = vec![
        (root_cmd.clone(), issue_capability(&issuer_seed, &root_cmd)),
        (
            delegated_cmd.clone(),
            issue_capability(&issuer_seed, &delegated_cmd),
        ),
    ];
    let cfg = AuthClusterConfig {
        seeds: (0..4).map(|i| authdemo::seed(i as u8)).collect(),
        roster: authdemo::byz_roster(4),
        leader: 0,
        init: init(),
        workload: workload.clone(),
        crashed: vec![],
        budget: budget(),
        settle: std::time::Duration::from_millis(500),
    };
    let outcome = run_auth_cluster(cfg).await;

    let expected = apply_prefix(&init(), &[root_cmd, delegated_cmd]);
    let stores = outcome.stores();
    println!("   committed slots: {}", outcome.committed());
    println!("   replicas converged: {}", outcome.converged());
    let matches_model = stores.iter().all(|s| *s == expected);
    println!("   every replica's store == the model's applyPrefix: {matches_model}");

    if !(outcome.converged() && matches_model && outcome.committed() == 2) {
        eprintln!("\nFAIL: the governed ledger did not replicate as the model says.");
        std::process::exit(1);
    }

    println!("\n── what this run showed");
    println!("   • authority verified at run time (real signature, tool-bound, fail-closed)");
    println!("   • two governed writes, one issued by a NARROWED delegate");
    println!("   • replicated through the R2-corresponded transition core, every replica");
    println!("     agreeing with the model's own applyPrefix");
    println!("   • and the violations that would break any of it are compile errors:");
    println!("     ungranted tool, illegal flow, over-budget, widening delegation,");
    println!("     missing witness — each pinned in tests/ui/");
    println!("\n   Compilation is the proof. The same admission chain is enforcing tool");
    println!("   calls on nucleus's live kernel path today.");
}
