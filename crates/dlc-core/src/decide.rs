//! T1 — Decidable proof-checking algorithm.
//!
//! `decide_pure` is a *checker*, not a searcher. Given a term and a claimed
//! proposition, it walks the term's structure and confirms each constructor's
//! typing rule is satisfied. Linear in `|M|`, with the per-step lookup in `Γ`
//! that grounds T1's `O(|M| · log |Γ|)` bound (the `log` factor materializes
//! once we upgrade `Ctx::additive` from `Vec<Prop>` to a sorted indexed map
//! at M1.Q4).
//!
//! Q2 deliverable: the propositional fragment. Handles:
//!   * `var-A`, `var-L`     — variable lookup
//!   * `imp-I` / `imp-E`    — implication
//!   * `says-I` / `says-E`  — affirmation (cryptographic check stubbed; T2
//!                            closure brings the keyring-threading version
//!                            in `dlc-crypto::decide_with_keyring`)
//!
//! Out of fragment (Q3+): modal `□_O`, `◇_τ`, IFC labels, linear `⊗`/`⊸`,
//! `delegate`, `attenuate`, `discharge`, IFC propagation. The function
//! returns `false` for any term mentioning these constructors — *correct*
//! per the Q2 fragment definition, not a bug.

use alloc::boxed::Box;

use crate::judgment::{Ctx, TypingProblem};
use crate::syntax::{Prop, Term};

/// Decide whether `problem.term` proves `problem.prop` in `problem.ctx`,
/// restricted to the propositional fragment.
///
/// Returns `true` iff the term is well-typed at the claimed proposition.
pub fn decide_pure(problem: &TypingProblem) -> bool {
    match infer(&problem.ctx, &problem.term) {
        Some(inferred) => inferred == problem.prop,
        None => false,
    }
}

/// Infer the proposition for `term` in `ctx`, in the propositional fragment.
/// Returns `None` if the term uses constructors outside the fragment or if
/// any sub-derivation fails.
pub fn infer(ctx: &Ctx, term: &Term) -> Option<Prop> {
    match term {
        // var-A: look up the de-Bruijn index in the additive context. The
        // linear context is consulted only when the additive lookup fails.
        Term::Var(i) => {
            let idx = *i as usize;
            if let Some(phi) = ctx.additive.get(idx) {
                Some(phi.clone())
            } else if ctx.linear.len() == 1 && idx == 0 {
                // var-L: a linear variable can be discharged only from a
                // singleton linear context. (Multi-element linear contexts
                // require explicit context splitting in elimination rules.)
                Some(ctx.linear[0].clone())
            } else {
                None
            }
        }

        // imp-I: extend the additive context and infer the body.
        Term::Lam(phi, body) => {
            let extended = ctx.clone().cons_a((**phi).clone());
            let psi = infer(&extended, body)?;
            Some(Prop::Imp(Box::new((**phi).clone()), Box::new(psi)))
        }

        // imp-E: f must have type φ ⊃ ψ; x must have type φ.
        Term::App(f, x) => {
            let f_ty = infer(ctx, f)?;
            let x_ty = infer(ctx, x)?;
            match f_ty {
                Prop::Imp(phi, psi) => {
                    if *phi == x_ty {
                        Some(*psi)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        }

        // says-I: produce `p says φ` from a proof of `φ`. Signature
        // verification belongs to `Γ ⊢_K` (T2), not here.
        Term::Sign(p, m, _sig) => {
            let phi = infer(ctx, m)?;
            Some(Prop::Says(p.clone(), Box::new(phi)))
        }

        // Out-of-fragment constructors. Returning None is the *correct*
        // behavior for the Q2 propositional fragment.
        Term::Verify(_, _, _)
        | Term::Delegate(_, _)
        | Term::Attenuate(_, _)
        | Term::Discharge(_, _)
        | Term::LiftLabel(_, _)
        | Term::Declassify(_, _, _)
        | Term::Now(_)
        | Term::WithinIntro(_, _) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::principal::{Principal, PrincipalId};
    use crate::syntax::Signature;
    use alloc::vec;

    fn atom(n: u32) -> Prop {
        Prop::Atom(n)
    }

    fn imp(a: Prop, b: Prop) -> Prop {
        Prop::Imp(Box::new(a), Box::new(b))
    }

    fn problem(ctx: Ctx, term: Term, prop: Prop) -> TypingProblem {
        TypingProblem { ctx, term, prop }
    }

    /// var-A: look up the only hypothesis in a singleton additive context.
    #[test]
    fn var_lookup_additive() {
        let ctx = Ctx::empty().cons_a(atom(0));
        let prob = problem(ctx, Term::Var(0), atom(0));
        assert!(decide_pure(&prob));
    }

    /// var-A miss: wrong index.
    #[test]
    fn var_lookup_miss() {
        let ctx = Ctx::empty().cons_a(atom(0));
        let prob = problem(ctx, Term::Var(1), atom(0));
        assert!(!decide_pure(&prob));
    }

    /// var-L: singleton linear context.
    #[test]
    fn var_lookup_linear() {
        let ctx = Ctx::empty().cons_l(atom(7));
        let prob = problem(ctx, Term::Var(0), atom(7));
        assert!(decide_pure(&prob));
    }

    /// imp-I: λ. 0 : A ⊃ A (the polymorphic identity at proposition A).
    #[test]
    fn imp_i_identity() {
        let id_term = Term::Lam(Box::new(atom(0)), Box::new(Term::Var(0)));
        let id_type = imp(atom(0), atom(0));
        let prob = problem(Ctx::empty(), id_term, id_type);
        assert!(decide_pure(&prob));
    }

    /// imp-E: identity applied to a hypothesis returns the hypothesis.
    #[test]
    fn imp_e_identity_application() {
        // Context: x:A
        let ctx = Ctx::empty().cons_a(atom(0));
        // Term: (λy:A. y) x  --> y has prop A in the extended ctx
        let id = Term::Lam(Box::new(atom(0)), Box::new(Term::Var(0)));
        let app = Term::App(Box::new(id), Box::new(Term::Var(0)));
        let prob = problem(ctx, app, atom(0));
        assert!(decide_pure(&prob));
    }

    /// imp-E failure: function expects A but argument has type B.
    #[test]
    fn imp_e_type_mismatch() {
        let ctx = Ctx::empty().cons_a(atom(1)); // x : B
        let id_for_a = Term::Lam(Box::new(atom(0)), Box::new(Term::Var(0)));
        let bad = Term::App(Box::new(id_for_a), Box::new(Term::Var(0)));
        let prob = problem(ctx, bad, atom(0));
        assert!(!decide_pure(&prob));
    }

    /// says-I: signing a proof of A produces `p says A`.
    #[test]
    fn says_i_basic() {
        let p = Principal::Atom(PrincipalId([3u8; 32]));
        let ctx = Ctx::empty().cons_a(atom(0));
        let sig = Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        };
        let term = Term::Sign(p.clone(), Box::new(Term::Var(0)), sig);
        let claimed = Prop::Says(p, Box::new(atom(0)));
        let prob = problem(ctx, term, claimed);
        assert!(decide_pure(&prob));
    }

    /// Out-of-fragment: `now(_)` returns false (correct for Q2).
    #[test]
    fn out_of_fragment_now_rejected() {
        let term = Term::Now(crate::time::TimeBound { epoch_ms: 0 });
        let prob = problem(Ctx::empty(), term, atom(0));
        assert!(!decide_pure(&prob));
    }
}
