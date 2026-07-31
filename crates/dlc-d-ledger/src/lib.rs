//! **The governed replicated ledger** — DLC-D's R6.3 slice: the authority envelope is a *type*,
//! and the service runs on the verified transition core.
//!
//! Everything about this service's authority is declared in one attribute. What that buys, and
//! exactly where each guarantee is decided:
//!
//! | Envelope axis | Violation | Decided by | Fixture |
//! |---|---|---|---|
//! | `cap = Invoke<Credit> @ Treasury` | caller presents no witness | `rustc` E0061 | `ui/missing_witness.rs` |
//! | ″ | issuer never granted the tool | `rustc` E0277 + the **verified checker** re-decides it | `ui/ungranted_tool.rs` |
//! | `flow = Ledger <= Audit` | illegal cross-agent flow | `rustc` E0277 | `ui/illegal_flow.rs` |
//! | `budget = Faults<1>` | composed into a stricter envelope | const-eval E0080 | `ui/over_budget.rs` |
//! | `delegate = attenuate_only` | delegation widens authority | `rustc` E0277 at the delegation | `ui/widening_delegation.rs` |
//!
//! **Scope of the budget axis, stated exactly:** `budget = Faults<f>` anchors the envelope as a
//! TYPE; the breach is decided where envelopes are *composed*
//! (`dlc_d::assert_tolerates::<F, G>()`), not by the axis alone. Write that composition as a
//! `const` item — the eagerly-evaluated form, which is also what the macro emits: the same
//! assertion called inside `fn main()` was observed to compile silently in one crate context, so
//! the item form is the one that reliably bites.
//!
//! The `cap` axis is decided **twice from one `grants!` declaration** — a build-time trait gate
//! and a certificate the verified checker (`dlc_core::decide::decide_pure`) validates, whose
//! acceptance means (by the machine-checked `rust_infer_sound`) a real typing derivation exists.
//! At run time the same authority is a real Ed25519 credential over the same cap atom
//! ([`dlc_d::Cap::admit`]), so the compile-time and runtime verdicts are about one fact.
//!
//! # What is NOT claimed
//!
//! The ledger's *replication* guarantees (agreement, convergence, capability-safety) are the
//! model-level theorems transported to the deployed reducer under R2's three conditions; this
//! crate exercises the deployed path, it does not re-prove it. `Cap::unchecked` still exists for
//! bootstrap. The transport under the cluster is in-process (`spec/r6-1-node-design.md` §5, the
//! honest TCB). Delegation here is grant-set subsumption in fragment F, not `Term::Attenuate`.

use dlc_core::rsm::{Command, FailureBudget};
use dlc_core::syntax::{Prop, Term};
use dlc_d::{Cap, Invoke};

// ── The authority vocabulary ────────────────────────────────────────────────────────────────
// Tools carry STABLE credential names: renaming the Rust type cannot invalidate issued
// credentials (`Tool::NAME` is what grants, certificates, and the runtime credential all key on).

/// The ledger's credit operation.
#[derive(dlc_d::Tool)]
#[tool(name = "ledger-credit")]
pub struct Credit;

/// A ledger operation this demo's issuer deliberately never grants.
#[derive(dlc_d::Tool)]
#[tool(name = "ledger-seize")]
pub struct Seize;

/// The issuing authority.
pub struct Treasury;
/// A delegate holding a NARROWED subset of the Treasury's authority.
pub struct Teller;

/// Confidentiality labels: ledger state may flow into the audit log, never the reverse.
pub struct Ledger;
/// The audit sink.
pub struct Audit;
impl dlc_d::FlowsInto<Audit> for Ledger {}

// The Treasury grants exactly `Credit` — NOT `Seize`. Every gate below is decided against this
// one declaration.
dlc_d::grants! { Treasury: Credit }

// The Teller is delegated a subset of what the Treasury holds. Delegating `Seize` here would
// fail to compile (`tests/ui/widening_delegation.rs`) — misdelegation can only narrow.
dlc_d::delegates! { Treasury => Teller: Credit }

// ── The governed service ────────────────────────────────────────────────────────────────────

/// **The governed ledger write.** Its authority envelope is the attribute: only a holder of
/// `Cap<Invoke<Credit>, Treasury>` can call it, ledger data may only flow to the audit sink, the
/// service tolerates one fault, and its issuer's authority is narrowing-only.
///
/// The body is ordinary Rust — it builds the replicated command that the verified transition
/// core will apply.
#[dlc_d::agent_service(
    cap = Invoke<Credit> @ Treasury,
    flow = Ledger <= Audit,
    budget = Faults<1>,
    delegate = attenuate_only
)]
pub fn credit(amount: u32) -> Command {
    Command {
        payload: credit_payload(amount),
        cap: Some(Prop::Atom(dlc_d::runtime::cap_atom(
            <Credit as dlc_d::Tool>::NAME,
        ))),
    }
}

/// The same write, issued by the DELEGATE rather than the root — the narrowing chain, exercised.
#[dlc_d::agent_service(
    cap = Invoke<Credit> @ Teller,
    flow = Ledger <= Audit,
    budget = Faults<1>,
    delegate = attenuate_only
)]
pub fn teller_credit(amount: u32) -> Command {
    credit_payload_command(amount)
}

fn credit_payload_command(amount: u32) -> Command {
    Command {
        payload: credit_payload(amount),
        cap: Some(Prop::Atom(dlc_d::runtime::cap_atom(
            <Credit as dlc_d::Tool>::NAME,
        ))),
    }
}

/// The store transformer this command applies: a closed term, as the transport theorems'
/// `ClosedTm` premises require. `amount` distinguishes commands operationally (so replication is
/// observable), applied as a nesting depth over the store.
fn credit_payload(amount: u32) -> Term {
    let mut body = Term::Var(0);
    for _ in 0..amount.min(3) {
        body = Term::Pair(Box::new(body), Box::new(Term::Var(0)));
    }
    Term::Lam(Box::new(Prop::Atom(0)), Box::new(body))
}

/// The ledger's initial store — the closed identity.
#[must_use]
pub fn init() -> Term {
    Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)))
}

/// The declared failure envelope, matching the `budget = Faults<1>` axis.
#[must_use]
pub fn budget() -> FailureBudget {
    FailureBudget::zero(1)
}

/// Mint the Treasury's runtime credential for a tool, and the keyring that trusts it.
///
/// Demo issuance: a fixed seed stands in for the Treasury's key management. What matters is that
/// [`admit_credit`] below verifies a REAL Ed25519 signature over the tool's cap atom.
#[must_use]
pub fn treasury_credential(
    tool: &str,
) -> (
    dlc_core::judgment::KeyRing,
    dlc_core::principal::Principal,
    dlc_core::syntax::Signature,
) {
    use dlc_core::principal::{KeyRecord, Principal, PrincipalId};
    let seed = [0x7a; 32];
    let pk = dlc_crypto::ed25519::public_key(&seed);
    let mut msg = b"dlc-d/cap-invoke:".to_vec();
    msg.extend_from_slice(&dlc_d::runtime::cap_atom(tool).to_le_bytes());
    let sig = dlc_core::syntax::Signature {
        alg: 0,
        bytes: dlc_crypto::ed25519::sign(&seed, &msg).to_vec(),
    };
    let keyring = dlc_core::judgment::KeyRing {
        entries: vec![KeyRecord {
            principal: PrincipalId(pk),
            alg: 0,
            public_key: pk.to_vec(),
        }],
    };
    (keyring, Principal::Atom(PrincipalId(pk)), sig)
}

/// **The runtime half of the same authority**: mint the typed witness from a verified credential.
/// Fails closed — a credential signed for another tool cannot mint this witness, because the
/// signature covers that tool's cap atom, not `Credit`'s.
///
/// # Errors
/// [`dlc_d::runtime::AdmitError::Unauthorized`] when the credential does not verify for `Credit`.
pub fn admit_credit(
    keyring: &dlc_core::judgment::KeyRing,
    issuer: &dlc_core::principal::Principal,
    sig: &dlc_core::syntax::Signature,
) -> Result<Cap<Invoke<Credit>, Treasury>, dlc_d::runtime::AdmitError> {
    Cap::<Invoke<Credit>, Treasury>::admit(keyring, issuer, sig)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn governed_credit_builds_a_command() {
        // The witness is required by the type — this is the Tier-1 admission gate.
        let cmd = credit(2, Cap::<Invoke<Credit>, Treasury>::unchecked());
        assert!(cmd.cap.is_some(), "the command carries its capability");
        assert_ne!(
            credit_payload(1),
            credit_payload(2),
            "distinct amounts must be operationally distinct (replication is observable)"
        );
    }

    #[test]
    fn delegated_credit_runs_under_the_narrowed_authority() {
        let cmd = teller_credit(1, Cap::<Invoke<Credit>, Teller>::unchecked());
        assert!(cmd.cap.is_some());
    }

    /// The runtime mint is gated on a REAL signature, and it is tool-bound.
    #[test]
    fn runtime_admission_is_tool_bound() {
        let (kr, issuer, good) = treasury_credential(<Credit as dlc_d::Tool>::NAME);
        assert!(
            admit_credit(&kr, &issuer, &good).is_ok(),
            "a genuine Treasury credential for Credit must mint the witness"
        );

        // A credential the Treasury signed for a DIFFERENT tool cannot mint a Credit witness:
        // refused by the Ed25519 verification, not by bookkeeping.
        let (_, _, wrong_tool) = treasury_credential(<Seize as dlc_d::Tool>::NAME);
        assert!(
            admit_credit(&kr, &issuer, &wrong_tool).is_err(),
            "a credential for another tool must not mint this witness"
        );
    }
}
