//! # A governed agent tool — the `#[dlc_d::agent_service]` fabric, running.
//!
//! Run it: `cargo run --example governed_agent -p dlc-d`
//!
//! This is a tool-invoking agent whose authority envelope is enforced **by the compiler and the
//! verified checker**, not by a runtime monitor. The three governance guarantees below are checked
//! before the program runs; there is *zero* runtime governance overhead.
//!
//! Contrast with the 2026 state of the art, which governs at runtime and measures it empirically:
//! IBCT (0.049 ms/verify, 100 % rejection over 600 attacks), Governed MCP (kernel-level logit
//! primitives), PAuth (NL slices). Those *check at runtime*; this **compiles the proof**.

use dlc_d::{agent_service, Cap, FlowsInto, Invoke};

// ── Capability vocabulary ────────────────────────────────────────────────────────────────────
// The tool this service may invoke, and the issuer that may grant that authority. `Tool` gives
// SendEmail its stable credential name (defaults to the ident; pin with #[tool(name = "…")] so
// a Rust rename can never invalidate issued credentials).
#[derive(dlc_d::Tool)]
struct SendEmail;
struct Ops;

// The grant declaration: `Ops` grants `SendEmail` and nothing else. Demanding an ungranted tool
// (e.g. `cap = Invoke<DeleteAll> @ Ops`) fails `cargo build` — the demanded-vs-granted gate.
dlc_d::grants! { Ops: SendEmail }

// ── Information-flow lattice ─────────────────────────────────────────────────────────────────
// User data may be recorded into the audit log (`UserData ⊑ AuditLog`), but NOT the reverse — the
// declared edge below is the only permitted flow.
struct UserData;
struct AuditLog;
impl FlowsInto<AuditLog> for UserData {}

/// The governed tool. Its `#[agent_service]` envelope declares:
/// - `cap = Invoke<SendEmail> @ Ops` — only a holder of the `Invoke<SendEmail>` capability granted
///   by `Ops` may call this (admission control). The macro appends a `Cap<Invoke<SendEmail>, Ops>`
///   parameter, so an unauthorized call is a compile error (`E0061`).
/// - `flow = UserData <= AuditLog` — the write respects the label lattice (isolation). An illegal
///   flow (e.g. `AuditLog <= UserData`) is a compile error (`E0277`).
/// - `budget = Faults<1>` — the declared failure envelope.
///
/// And the macro emits a hidden `#[cfg(test)] #[test]` that validates an admission *certificate*
/// (a `dlc_core` typing problem) with the **verified checker** `decide_pure`; a green `cargo test`
/// means, by the machine-checked `rust_infer_sound`, a real typing derivation exists — so the macro
/// is out of the trusted computing base.
#[agent_service(cap = Invoke<SendEmail> @ Ops, flow = UserData <= AuditLog, budget = Faults<1>)]
fn send_email_tool(recipient: &str) -> String {
    format!(
        "SendEmail → {recipient}  (authorized: Invoke<SendEmail>@Ops; flow UserData ⊑ AuditLog)"
    )
}

fn main() {
    // ── The U3 gated mint: the capability witness comes FROM the verified credential ─────────
    // Ops signs a real Ed25519 credential over SendEmail's cap atom, and `Cap::admit` mints the
    // typed witness ONLY because that credential verifies (verify-then-authorize, fail-closed).
    // The atom the signature covers is the SAME `cap_atom(SendEmail::NAME)` the emitted Tier-2
    // certificate demands — one function, one name: compile-time and runtime verdicts are about
    // the same fact. (`Cap::unchecked()` exists for tests/bootstrap, and is named for what it is.)
    let cap = {
        use dlc_core::judgment::KeyRing;
        use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
        use dlc_core::syntax::Signature;
        use dlc_d::runtime::{admit, cap_atom};
        use dlc_d::Tool as _;

        // Ops issues a capability for the SendEmail tool (signs its cap atom).
        let seed = [5u8; 32];
        let pk = dlc_crypto::ed25519::public_key(&seed);
        let ops = Principal::Atom(PrincipalId(pk));
        let keyring = KeyRing {
            entries: vec![KeyRecord {
                principal: PrincipalId(pk),
                alg: 0,
                public_key: pk.to_vec(),
            }],
        };
        let mut msg = b"dlc-d/cap-invoke:".to_vec();
        msg.extend_from_slice(&cap_atom(SendEmail::NAME).to_le_bytes());
        let sig = Signature {
            alg: 0,
            bytes: dlc_crypto::ed25519::sign(&seed, &msg).to_vec(),
        };

        // The credential is refused for any OTHER tool (fail-closed tool-binding)…
        assert!(admit(&keyring, &ops, "DeleteAll", &sig).is_err());
        println!("runtime admission — Ops-signed credential REFUSES DeleteAll, MINTS Cap<Invoke<SendEmail>, Ops> (Ed25519, fail-closed)\n");
        // …and for SendEmail it mints the witness the governed call below requires.
        Cap::<Invoke<SendEmail>, Ops>::admit(&keyring, &ops, &sig)
            .expect("a genuine Ops-signed SendEmail credential must mint")
    };

    let outcome = send_email_tool("alice@example.com", cap);

    println!("── governed agent run ──────────────────────────────────────────────");
    println!("{outcome}");
    println!();
    println!("Guarantees checked by the compiler + the verified checker (0 runtime cost):");
    println!("  • admission   — an unauthorized call is a type error (E0061: missing");
    println!(
        "                  `Cap<Invoke<SendEmail>, Ops>`).            [tests/ui/missing_cap.rs]"
    );
    println!("  • isolation   — an illegal flow is a type error (E0277:");
    println!("                  `AuditLog: FlowsInto<UserData>` unsatisfied). [tests/ui/illegal_flow.rs]");
    println!(
        "  • budget      — composing this Faults<1> service where more tolerance is required is"
    );
    println!(
        "                  a compile error (E0080 const-eval).           [tests/ui/over_budget.rs]"
    );
    println!("  • admission   — `cargo test` validates an auto-emitted certificate with the");
    println!("    proof         VERIFIED checker (decide_pure → rust_infer_sound); the macro is");
    println!("                  out of the TCB — a bogus certificate is rejected.");
    println!();
    println!("Prior art governs at RUNTIME and measures it; this COMPILES the proof:");
    println!(
        "  ACP model-checks 3 invariants · IBCT rejects 600 attacks empirically (0.049 ms/call) ·"
    );
    println!("  dlc_d: green build ⟹ every invocation is says-authorized + illegal flow is a type error.");
}
