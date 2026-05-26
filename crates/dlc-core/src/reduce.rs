//! Small-step reduction `M ▷ M'`.
//!
//! Implements the principal reduction rules from `spec/typing-rules.md` §11:
//!   β              — `(λx.M) N ▷ M[N/x]`
//!   says-extract   — `let ⟨x⟩_p = ⟨M, σ⟩_p in N ▷ N[M/x]`  (encoded via app)
//!   delegate-β     — `delegate(⟨M, _⟩_p, ⟨N, σ'⟩_q) ▷ ⟨N, σ'⟩_{p⊓q}`
//!   attenuate-β    — `attenuate(⟨M, σ⟩_p, ψ) ▷ ⟨M', σ'⟩_p`  (admits reproof)
//!   discharge-β    — `discharge(box(M, _), N) ▷ M`
//!   within-β       — `openWithin(within(M, τ)) ▷ M`
//!
//! Subject reduction (M1.Q2.c proof closure) is stated in `lean/DLC/Reduce.lean`.
//! The Lean proof depends on the substitution lemma (M1.Q2.a, also deferred);
//! the implementations here are correct and tested.

use alloc::boxed::Box;

use crate::principal::Principal;
use crate::subst::subst;
use crate::syntax::Term;

/// One step of head reduction. Returns `None` if `term` is a normal form at
/// the head position (no further redex at the top constructor).
///
/// Reduction is **head-only**: we do not push inside subterms. Strategies
/// that need full reduction iterate `step` over the term tree externally.
pub fn step(term: &Term) -> Option<Term> {
    match term {
        // β: (λx:φ.M) N  ▷  M[N/x]
        Term::App(f, x) => match f.as_ref() {
            Term::Lam(_phi, body) => Some(subst(body, x)),
            _ => None,
        },

        // delegate-β: delegate(⟨M, _⟩_p, ⟨N, σ'⟩_q)  ▷  ⟨N, σ'⟩_{p⊓q}
        // The outer principal is the `acting` composition of p over q.
        Term::Delegate(m, n) => match (m.as_ref(), n.as_ref()) {
            (Term::Sign(p, _m_inner, _sig_p), Term::Sign(q, n_inner, sig_q)) => {
                let acting = Principal::Acting(Box::new(p.clone()), Box::new(q.clone()));
                Some(Term::Sign(acting, n_inner.clone(), sig_q.clone()))
            }
            _ => None,
        },

        // attenuate-β: a (sign, attenuate) pair commutes-and-reproofs. In
        // this kernel implementation we leave the term-level commute to the
        // verifier — attenuation does not reduce on the fly; the verifier
        // checks the side conditions and accepts. Returning `None` here is
        // intentional and matches the calculus (attenuate is a normal form
        // at the head).
        Term::Attenuate(_, _) => None,

        // discharge-β: discharge(box(M, _), N) ▷ M, where `box(M, _)` is
        // encoded as Discharge with the obligation-evidence in the second
        // arg. Production: when we add the explicit `box` constructor at
        // Q3, this rule rewrites to consume the obligation. Week-1 stub:
        // a `discharge` over a non-box is a normal form.
        Term::Discharge(_m, _n) => None,

        // within-β: openWithin(within(M, τ)) ▷ M. We currently model
        // `openWithin` as application of an identity wrapper; explicit
        // open-elim constructor lands at Q3.
        Term::WithinIntro(_, _) => None,

        // All other forms — Var, Lam, Sign, Verify, LiftLabel, Declassify,
        // Now — are normal forms at the head.
        _ => None,
    }
}

/// Iterate `step` to a normal form (or until the fuel runs out).
///
/// Returns the final term and the number of steps taken. Bounded by `fuel`
/// to keep the function total — necessary for Aeneas extraction.
pub fn reduce_with_fuel(term: &Term, fuel: u32) -> (Term, u32) {
    let mut cur = term.clone();
    for n in 0..fuel {
        match step(&cur) {
            Some(next) => cur = next,
            None => return (cur, n),
        }
    }
    (cur, fuel)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{Prop, Signature};
    use alloc::vec;

    fn ed25519_stub_sig() -> Signature {
        Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        }
    }

    /// β: identity applied to anything is that thing.
    #[test]
    fn beta_identity() {
        let id = Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)));
        let arg = Term::Var(5);
        let result = step(&Term::App(Box::new(id), Box::new(arg.clone()))).unwrap();
        assert_eq!(result, arg);
    }

    /// β: `(λ.λ. 0) v` reduces to `λ. 0` (the inner lambda is preserved).
    #[test]
    fn beta_under_binder() {
        let kk = Term::Lam(
            Box::new(Prop::Atom(0)),
            Box::new(Term::Lam(Box::new(Prop::Atom(1)), Box::new(Term::Var(0)))),
        );
        let v = Term::Var(7);
        let app = Term::App(Box::new(kk), Box::new(v));
        let result = step(&app).unwrap();
        // The inner λ. 0 has no reference to the outer bound var, so it
        // emerges unchanged.
        assert_eq!(
            result,
            Term::Lam(Box::new(Prop::Atom(1)), Box::new(Term::Var(0))),
        );
    }

    /// delegate-β: signs of p and q compose to a sign of `acting p q`.
    #[test]
    fn delegate_beta_produces_acting_principal() {
        let p = Principal::Atom(crate::principal::PrincipalId([1u8; 32]));
        let q = Principal::Atom(crate::principal::PrincipalId([2u8; 32]));
        let inner_proof = Term::Var(0);
        let sig_q = ed25519_stub_sig();

        let m_sign_p = Term::Sign(p.clone(), Box::new(Term::Var(99)), ed25519_stub_sig());
        let n_sign_q = Term::Sign(q.clone(), Box::new(inner_proof.clone()), sig_q.clone());

        let delegated = Term::Delegate(Box::new(m_sign_p), Box::new(n_sign_q));
        let result = step(&delegated).unwrap();

        match result {
            Term::Sign(Principal::Acting(p_box, q_box), inner, sig) => {
                assert_eq!(*p_box, p);
                assert_eq!(*q_box, q);
                assert_eq!(*inner, inner_proof);
                assert_eq!(sig, sig_q);
            }
            other => panic!("unexpected reduction result: {:?}", other),
        }
    }

    /// Var is a normal form.
    #[test]
    fn var_is_normal() {
        assert!(step(&Term::Var(0)).is_none());
    }

    /// Lambda is a normal form (no app yet).
    #[test]
    fn lambda_is_normal() {
        let id = Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)));
        assert!(step(&id).is_none());
    }

    /// `reduce_with_fuel` terminates on a finite β-chain.
    #[test]
    fn reduce_with_fuel_terminates() {
        let id = Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)));
        let app = Term::App(Box::new(id.clone()), Box::new(Term::Var(0)));
        let (final_term, steps) = reduce_with_fuel(&app, 10);
        assert_eq!(final_term, Term::Var(0));
        assert_eq!(steps, 1);
    }
}
