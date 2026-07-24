//! **Tier-2 pipeline (proof-carrying code).** The `#[agent_service]` macro's admission obligation is
//! discharged not by trusting the macro but by emitting a *certificate* — a `dlc_core` typing problem
//! — that the **verified checker** validates. `dlc_core::decide::decide_pure` accepting the
//! certificate means, by the machine-checked `rust_infer_sound` (green build ⟹ `Nonempty Deriv`), that
//! a real typing derivation exists. The macro is therefore *out of the TCB*: a wrong certificate is
//! rejected (see `bogus_certificate_rejected`), so a green run is sound regardless of macro
//! correctness (spec/r6.2-agent-service-envelope.md §3.4).
//!
//! This file hand-writes the certificate to prove the pipeline end-to-end against the real checker;
//! the next increment has the macro *emit* an equivalent generated check from the parsed envelope.
//!
//! **Fence.** The certificate proves *typeability* (the commit-I store-transformer `M : φ ⊃ φ`, in the
//! verified propositional fragment F). The signature/crypto realization of the `says`-credential is a
//! separate layer (Phase 2). Validation runs at `cargo test` time here; a build-time gate (build.rs)
//! is the §4 follow-up.

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
