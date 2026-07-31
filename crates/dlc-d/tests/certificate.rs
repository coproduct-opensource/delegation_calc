//! **Tier-2 pipeline (proof-carrying code).** The `#[agent_service]` macro's admission obligation is
//! discharged not by trusting the macro but by emitting a *certificate* — a `dlc_core` typing problem
//! — that the **verified checker** validates. `dlc_core::decide::decide_pure` accepting the
//! certificate means, by the machine-checked `rust_infer_sound` (green build ⟹ `Nonempty Deriv`), that
//! a real typing derivation exists. The macro is therefore *out of the TCB*: a wrong certificate is
//! rejected (see `bogus_certificate_rejected`), so a green run is sound regardless of macro
//! correctness (spec/r6.2-agent-service-envelope.md §3.4).
//!
//! This file hand-writes certificates to prove the pipeline end-to-end against the real checker.
//! The macro emits the demanded-vs-granted form of the same obligation
//! (`dlc_d::obligation::cap_problem`); the `cap_obligation` module below is the golden suite for
//! that constructor — including the anti-vacuity witness that the obligation is a NON-CONSTANT
//! function of the envelope and grants declarations (a one-byte perturbation of either flips the
//! verified checker to reject).
//!
//! **Fence.** The certificate proves *typeability* in the verified propositional fragment F. The
//! signature/crypto realization of the `says`-credential is a separate layer (`runtime::admit`,
//! tied to this obligation from U3 onward). A macro that emits NO certificate is caught only by
//! this golden suite, not by the checker.

use dlc_core::decide::decide_pure;
use dlc_core::judgment::{Ctx, TypingProblem};
use dlc_core::syntax::{Prop, Term};

/// The admission certificate for a capability `cap`: the store-transformer `λx:atom_cap. x`, which
/// the calculus types at `atom_cap ⊃ atom_cap` — the commit-I payload requirement `M : φ ⊃ φ`, in
/// the verified fragment F (`Lam`, `Var`). `decide_pure` accepting it ⟹ (by `rust_infer_sound`) a
/// real `Deriv` exists.
fn store_transformer_certificate(cap: u32) -> TypingProblem {
    TypingProblem {
        ctx: Ctx::empty(),
        term: Term::Lam(Box::new(Prop::Atom(cap)), Box::new(Term::Var(0))),
        prop: Prop::Imp(Box::new(Prop::Atom(cap)), Box::new(Prop::Atom(cap))),
    }
}

#[test]
fn admission_certificate_validates() {
    let problem = store_transformer_certificate(0x00C0_FFEE);
    assert!(
        decide_pure(&problem),
        "the admission certificate must type-check in the verified checker"
    );
}

#[test]
fn bogus_certificate_rejected() {
    // Claims `atom 1 ⊃ atom 2`, but `λx:atom_1. x` is typed `atom 1 ⊃ atom 1`. The checker — the
    // trust anchor, NOT the macro — rejects the mismatch, so a wrong emitter cannot forge soundness.
    let problem = TypingProblem {
        ctx: Ctx::empty(),
        term: Term::Lam(Box::new(Prop::Atom(1)), Box::new(Term::Var(0))),
        prop: Prop::Imp(Box::new(Prop::Atom(1)), Box::new(Prop::Atom(2))),
    };
    assert!(
        !decide_pure(&problem),
        "a mistyped certificate must be rejected by the verified checker"
    );
}

#[test]
fn wrong_context_certificate_rejected() {
    // `Var(0)` in the empty context has no type; the certificate is rejected.
    let problem = TypingProblem {
        ctx: Ctx::empty(),
        term: Term::Var(0),
        prop: Prop::Atom(0),
    };
    assert!(
        !decide_pure(&problem),
        "an unbound-variable certificate must be rejected"
    );
}

/// Golden suite for the macro-emitted demanded-vs-granted obligation. Same constructor the
/// emitted certificate test calls, so what is proven here is a fact about the REAL obligation,
/// not a test-only twin.
mod cap_obligation {
    use dlc_core::decide::decide_pure;
    use dlc_d::obligation::{cap_problem, demanded_atom};

    /// Ops' grant list as `IssuerGrants::GRANTS` would carry it.
    const OPS_GRANTS: &[&str] = &["SendEmail", "NetRead"];

    #[test]
    fn granted_pair_accepted() {
        assert!(
            decide_pure(&cap_problem(OPS_GRANTS, "Ops", "SendEmail")),
            "a declared grant must discharge the demand"
        );
    }

    /// ★ The anti-vacuity witness: the obligation is a non-constant function of the grants
    /// declaration. One byte of drift in the granted tool name and the VERIFIED CHECKER — not
    /// string comparison in test code — rejects the admission.
    #[test]
    fn one_byte_grant_perturbation_rejected() {
        let typo: &[&str] = &["SendEmajl", "NetRead"];
        assert!(
            !decide_pure(&cap_problem(typo, "Ops", "SendEmail")),
            "a one-byte perturbation of the granted tool must be rejected by the checker"
        );
    }

    /// The complementary witness: non-constant in the ENVELOPE side too.
    #[test]
    fn ungranted_tool_rejected() {
        assert!(
            !decide_pure(&cap_problem(OPS_GRANTS, "Ops", "DeleteAll")),
            "demanding a tool the issuer never granted must be rejected"
        );
    }

    #[test]
    fn empty_grants_list_rejected() {
        assert!(
            !decide_pure(&cap_problem(&[], "Ops", "SendEmail")),
            "an issuer with no grants must fail closed (no credential to present)"
        );
    }

    /// ★ U3 divergence guard: the atom the certificate GOAL demands is the atom the runtime
    /// credential message signs over — extracted from the REAL emitted problem, not asserted
    /// about the source. If `cap_atom` is ever re-duplicated (the pre-inc4 state) and the copies
    /// drift, this REDs.
    #[test]
    fn same_atom_as_runtime() {
        for name in ["SendEmail", "DeleteAll", "a", ""] {
            let p = cap_problem(OPS_GRANTS, "Ops", name);
            assert_eq!(
                demanded_atom(&p),
                Some(dlc_d::runtime::cap_atom(name)),
                "certificate goal atom and runtime credential atom must be the same value"
            );
        }
    }
}
