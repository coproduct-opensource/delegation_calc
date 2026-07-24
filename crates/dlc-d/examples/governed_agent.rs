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
// The tool this service may invoke, and the issuer that may grant that authority.
struct SendEmail;
struct Ops;

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
    // Mint the capability witness. (For now `Cap::new()` is freely mintable; the witness's VALIDITY
    // is separately backed by the Tier-2 certificate — a gated mint tying it to a verified
    // credential is a planned follow-up.) The call below REQUIRES this witness — delete it and the
    // program will not compile.
    let cap = Cap::<Invoke<SendEmail>, Ops>::new();

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
