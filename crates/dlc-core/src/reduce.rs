//! Small-step reduction `M ▷ M'`.
//!
//! Implements `spec/typing-rules.md` §11 and mirrors
//! `lean/DLC/Reduce.lean::step` case-for-case: eight head redexes (β,
//! and-Eₗ/ᵣ-β, or-E-β, let-tensor, says-extract, sf-extract-β,
//! delegate-β) plus the 2026-07 CONGRUENCE rules — when an elimination
//! form's head rule does not fire, reduction descends into the
//! scrutinee/function position (call-by-name, one deterministic
//! position per form). Without congruence, nested eliminations were
//! stuck and progress failed; see spec §11 and
//! `spec/t3-two-run-design-2026-07.md` (FINDING).
//!
//! Frozen forms (`verify`, `attenuate`, `declassify`, `discharge`,
//! `liftLabel`, `withinIntro`) do not reduce: they are checked by the
//! verifier layers, not computed. discharge-β awaits the
//! obligation-carrying constructor (T4 non-vacuity package).

use alloc::boxed::Box;

use crate::principal::Principal;
use crate::subst::{shift, subst};
use crate::syntax::Term;

/// One deterministic step of reduction, or `None` for values, frozen
/// forms, and terms stuck on a frozen scrutinee.
///
/// The congruence arms spell out `match step(x) { Some(..) => .., None
/// => None }` instead of `Option::map` DELIBERATELY: closures are the
/// weak spot of the Charon/Aeneas pipeline this crate must stay
/// translatable under (the committed `lean/DLC/Aeneas/DlcCore` tree is
/// generated from exactly this shape), so the clippy lint is
/// suppressed rather than obeyed.
#[allow(clippy::manual_map)]
pub fn step(term: &Term) -> Option<Term> {
    match term {
        // β: (λx:φ.M) N ▷ M[N/x]; ξ-app in the function position.
        Term::App(f, x) => match f.as_ref() {
            Term::Lam(_phi, body) => Some(subst(body, x)),
            _ => match step(f) {
                Some(f2) => Some(Term::App(Box::new(f2), x.clone())),
                None => None,
            },
        },

        // and-Eₗ-β: π₁ ⟨a, _⟩ ▷ a; ξ-fst.
        Term::Fst(m) => match m.as_ref() {
            Term::Pair(a, _) => Some(a.as_ref().clone()),
            _ => match step(m) {
                Some(m2) => Some(Term::Fst(Box::new(m2))),
                None => None,
            },
        },

        // and-Eᵣ-β: π₂ ⟨_, b⟩ ▷ b; ξ-snd.
        Term::Snd(m) => match m.as_ref() {
            Term::Pair(_, b) => Some(b.as_ref().clone()),
            _ => match step(m) {
                Some(m2) => Some(Term::Snd(Box::new(m2))),
                None => None,
            },
        },

        // or-E-β: case (inl a) ▷ left[a/x] (inr symmetric); ξ-case.
        Term::Case(s, l, r) => match s.as_ref() {
            Term::Inl(_, a) => Some(subst(l, a)),
            Term::Inr(_, a) => Some(subst(r, a)),
            _ => match step(s) {
                Some(s2) => Some(Term::Case(Box::new(s2), l.clone(), r.clone())),
                None => None,
            },
        },

        // let-tensor: `let x⊗y = a⊗b in body ▷ body[a/x, b/y]` with the
        // intermediate-context shift on `a` (see Lean `step` for the
        // detailed de-Bruijn justification); ξ-lettensor.
        Term::LetTensor(s, body) => match s.as_ref() {
            Term::TensorIntro(a, b) => Some(subst(&subst(body, &shift(a, 1, 0)), b)),
            _ => match step(s) {
                Some(s2) => Some(Term::LetTensor(Box::new(s2), body.clone())),
                None => None,
            },
        },

        // says-extract: `let ⟨x⟩_p = ⟨m, σ⟩_p in body ▷ body[m/x]` when
        // the principals agree (a signed value under the wrong principal
        // is stuck — typing rules it out); ξ-letsays.
        Term::LetSays(p, s, body) => match s.as_ref() {
            Term::Sign(p2, m, _sig) => {
                if p == p2 {
                    Some(subst(body, m))
                } else {
                    None
                }
            }
            _ => match step(s) {
                Some(s2) => Some(Term::LetSays(p.clone(), Box::new(s2), body.clone())),
                None => None,
            },
        },

        // sf-extract-β: `sfExtract ⟨m, σ⟩_p ▷ m`; ξ-sfextract.
        Term::SfExtract(m) => match m.as_ref() {
            Term::Sign(_, inner, _) => Some(inner.as_ref().clone()),
            _ => match step(m) {
                Some(m2) => Some(Term::SfExtract(Box::new(m2))),
                None => None,
            },
        },

        // delegate-β: delegate(⟨M, _⟩_p, ⟨N, σ'⟩_q) ▷ ⟨N, σ'⟩_{p⊓q};
        // ξ-delegate: left position first, then right once left is a sign.
        Term::Delegate(m, n) => match (m.as_ref(), n.as_ref()) {
            (Term::Sign(p, _m_inner, _sig_p), Term::Sign(q, n_inner, sig_q)) => {
                let acting = Principal::Acting(Box::new(p.clone()), Box::new(q.clone()));
                Some(Term::Sign(acting, n_inner.clone(), sig_q.clone()))
            }
            (Term::Sign(_, _, _), _) => match step(n) {
                Some(n2) => Some(Term::Delegate(m.clone(), Box::new(n2))),
                None => None,
            },
            _ => match step(m) {
                Some(m2) => Some(Term::Delegate(Box::new(m2), n.clone())),
                None => None,
            },
        },

        // Frozen forms and values: Var, Lam, Sign, Pair, Inl, Inr,
        // TensorIntro, Now, WithinIntro, Verify, Attenuate, Discharge,
        // LiftLabel, Declassify. Also `Command` (DLC-D, R1 increment 1): a
        // STUCK non-value — its `command-β` reduction is deferred to a later
        // increment, so it does not step.
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

    /// Congruence: nested projections now evaluate — the FINDING case.
    #[test]
    fn nested_projection_evaluates() {
        // fst (fst (pair (pair a b) c)) ▷ fst (pair a b) ▷ a
        let a = Term::Var(1);
        let b = Term::Var(2);
        let c = Term::Var(3);
        let inner = Term::Pair(Box::new(a.clone()), Box::new(b));
        let outer = Term::Pair(Box::new(inner), Box::new(c));
        let m = Term::Fst(Box::new(Term::Fst(Box::new(outer))));
        let (final_term, steps) = reduce_with_fuel(&m, 10);
        assert_eq!(final_term, a);
        assert_eq!(steps, 2);
    }

    /// Congruence in function position: ((λ.λ.0) v) w needs ξ-app first.
    #[test]
    fn xi_app_reduces_function_position() {
        let kk = Term::Lam(
            Box::new(Prop::Atom(0)),
            Box::new(Term::Lam(Box::new(Prop::Atom(1)), Box::new(Term::Var(0)))),
        );
        let inner_app = Term::App(Box::new(kk), Box::new(Term::Var(7)));
        let outer = Term::App(Box::new(inner_app), Box::new(Term::Var(9)));
        let (final_term, steps) = reduce_with_fuel(&outer, 10);
        assert_eq!(final_term, Term::Var(9));
        assert_eq!(steps, 2);
    }

    /// Frozen scrutinee stays stuck: letSays over an attenuate does not step.
    #[test]
    fn frozen_scrutinee_is_stuck() {
        let p = Principal::Atom(crate::principal::PrincipalId([1u8; 32]));
        let frozen = Term::Attenuate(Box::new(Term::Var(0)), Box::new(Prop::Top));
        let m = Term::LetSays(p, Box::new(frozen), Box::new(Term::Var(0)));
        assert!(step(&m).is_none());
    }
}
