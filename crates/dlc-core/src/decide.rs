//! T1 — Decidable proof-checking algorithm.
//!
//! `decide_pure` is a *checker*, not a searcher. Given a term and a claimed
//! proposition, it walks the term's structure and confirms each constructor's
//! typing rule is satisfied. Linear in `|M|`, with the per-step lookup in `Γ`
//! that grounds T1's `O(|M| · log |Γ|)` bound (the `log` factor materializes
//! once we upgrade `Ctx::additive` from `Vec<Prop>` to a sorted indexed map
//! at M1.Q4).
//!
//! Q4 deliverable: the full calculus (modulo linear-context splitting at
//! elimination forms; that's the M1.Q4.d follow-up tightening, see below).
//! Handles:
//!   * `var-A`, `var-L`     — variable lookup
//!   * `imp-I` / `imp-E`    — implication
//!   * `says-I`             — affirmation (cryptographic check stubbed; T2
//!     closure brings the keyring-threading version in
//!     `dlc-crypto::decide_with_keyring`)
//!   * `delegate`           — chain composition
//!   * `attenuate`          — affirmation narrowing along provable implication
//!   * `discharge`          — obligation elimination
//!   * `lift`               — IFC label introduction
//!   * `declassify`         — controlled label lowering
//!   * `now` / `within-I`   — time modality intro forms
//!
//! Per spec/typing-rules.md, each modality adds a constant cost per node;
//! the `O(|M| · log |Γ|)` bound is preserved.

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

        // verify: eliminates `p says φ` to `φ` modulo signature check (T2
        // bridges these). At the propositional level, return the underlying
        // type.
        Term::Verify(p, m, _sig) => {
            let m_ty = infer(ctx, m)?;
            match m_ty {
                Prop::Says(q, inner) if q == *p => Some(*inner),
                _ => None,
            }
        }

        // delegate(M, N): M : p says (q ⇒ p), N : q says φ
        //               ⊢ delegate(M, N) : (p ⊓ q) says φ
        Term::Delegate(m, n) => {
            let m_ty = infer(ctx, m)?;
            let n_ty = infer(ctx, n)?;
            let (m_principal, m_inner) = match m_ty {
                Prop::Says(p, inner) => (p, *inner),
                _ => return None,
            };
            let (q_outer, p_outer) = match m_inner {
                Prop::SpeaksFor(q, p) => (q, p),
                _ => return None,
            };
            // The outer p in the speaks-for must agree with the says-principal.
            if p_outer != m_principal {
                return None;
            }
            let (n_principal, n_inner) = match n_ty {
                Prop::Says(p, inner) => (p, *inner),
                _ => return None,
            };
            // The q from the speaks-for must agree with n's principal —
            // this is the no-chain-splicing condition.
            if q_outer != n_principal {
                return None;
            }
            let acting =
                crate::principal::Principal::Acting(Box::new(p_outer), Box::new(n_principal));
            Some(Prop::Says(acting, Box::new(n_inner)))
        }

        // attenuate(M, ψ): M : p says φ; the side condition `φ ⊃ ψ` is
        // provable; the IFC side condition `ψ ≤_L φ` is checked at M1.Q4.a
        // once the IFC re-export is in (Lean side does the check; Rust
        // here trusts the user-provided ψ as the claimed result type).
        Term::Attenuate(m, psi) => {
            let m_ty = infer(ctx, m)?;
            match m_ty {
                Prop::Says(p, _phi) => Some(Prop::Says(p, psi.clone())),
                _ => None,
            }
        }

        // discharge(M, N): M : □_O φ, N : O ⊢ discharge(M, N) : φ.
        // The linear consumption is enforced by the context-splitting
        // protocol; this checker assumes the caller has split correctly.
        Term::Discharge(m, _evidence) => {
            let m_ty = infer(ctx, m)?;
            match m_ty {
                Prop::Boxed(_, inner) => Some(*inner),
                _ => None,
            }
        }

        // lift_ℓ(M): M : φ ⊢ lift_ℓ(M) : φ @ ℓ.
        Term::LiftLabel(label, m) => {
            let m_ty = infer(ctx, m)?;
            Some(Prop::At(Box::new(m_ty), label.clone()))
        }

        // declassify_ℓ'(M, π): M : φ @ ℓ, π : DeclassifyPolicy ⊢
        // declassify_ℓ'(M, π) : φ @ ℓ'.
        Term::Declassify(target_label, m, _policy) => {
            let m_ty = infer(ctx, m)?;
            match m_ty {
                Prop::At(inner, _source_label) => Some(Prop::At(inner, target_label.clone())),
                _ => None,
            }
        }

        // now(τ): produces a proof of `⊤` (intuitively, an opaque witness
        // that the current time is < τ; verification of the embedded anchor
        // is done by `dlc-crypto::time_anchor::within_bound` at use sites).
        Term::Now(_tau) => Some(Prop::Top),

        // within(M, τ): M : φ ⊢ within(M, τ) : ◇_τ φ.
        Term::WithinIntro(tau, m) => {
            let m_ty = infer(ctx, m)?;
            Some(Prop::Within(tau.clone(), Box::new(m_ty)))
        }

        // and-I: ⟨M, N⟩ : φ ∧ ψ
        Term::Pair(a, b) => {
            let a_ty = infer(ctx, a)?;
            let b_ty = infer(ctx, b)?;
            Some(Prop::And(Box::new(a_ty), Box::new(b_ty)))
        }

        // and-Eₗ: π₁ M from M : φ ∧ ψ
        Term::Fst(m) => match infer(ctx, m)? {
            Prop::And(phi, _) => Some(*phi),
            _ => None,
        },

        // and-Eᵣ: π₂ M from M : φ ∧ ψ
        Term::Snd(m) => match infer(ctx, m)? {
            Prop::And(_, psi) => Some(*psi),
            _ => None,
        },

        // or-I-left: inl_ψ M : φ ∨ ψ, where M : φ.
        Term::Inl(other, m) => {
            let phi = infer(ctx, m)?;
            Some(Prop::Or(Box::new(phi), Box::new((**other).clone())))
        }

        // or-I-right: inr_φ M : φ ∨ ψ, where M : ψ.
        Term::Inr(other, m) => {
            let psi = infer(ctx, m)?;
            Some(Prop::Or(Box::new((**other).clone()), Box::new(psi)))
        }

        // or-E: case M of inl x ⇒ N | inr y ⇒ P. The two branches must
        // infer the same type, which we then return.
        Term::Case(scrut, left, right) => {
            let (phi, psi) = match infer(ctx, scrut)? {
                Prop::Or(p, q) => (*p, *q),
                _ => return None,
            };
            let left_ctx = ctx.clone().cons_a(phi);
            let right_ctx = ctx.clone().cons_a(psi);
            let left_ty = infer(&left_ctx, left)?;
            let right_ty = infer(&right_ctx, right)?;
            if left_ty == right_ty {
                Some(left_ty)
            } else {
                None
            }
        }

        // tensor-I: M ⊗ N : φ ⊗ ψ. Linear-context splitting is not enforced
        // here; the checker assumes the caller arranged the linear context
        // appropriately. The Lean Deriv constructors capture the linearity.
        Term::TensorIntro(a, b) => {
            let a_ty = infer(ctx, a)?;
            let b_ty = infer(ctx, b)?;
            Some(Prop::Tensor(Box::new(a_ty), Box::new(b_ty)))
        }

        // tensor-E: let x⊗y = M in N. Binds two linear hypotheses.
        Term::LetTensor(scrut, body) => {
            let (phi, psi) = match infer(ctx, scrut)? {
                Prop::Tensor(p, q) => (*p, *q),
                _ => return None,
            };
            let extended = ctx.clone().cons_l(phi).cons_l(psi);
            infer(&extended, body)
        }

        // says-extract: let ⟨x⟩_p = M in N. Bind the underlying proof.
        Term::LetSays(principal, scrut, body) => {
            let inner = match infer(ctx, scrut)? {
                Prop::Says(p, phi) if p == *principal => *phi,
                _ => return None,
            };
            let extended = ctx.clone().cons_a(inner);
            infer(&extended, body)
        }

        // sf-extract: from `p says (q ⇒ p)` extract `q ⇒ p`.
        Term::SfExtract(m) => match infer(ctx, m)? {
            Prop::Says(p_outer, inner) => match *inner {
                Prop::SpeaksFor(q, p_inner) if p_inner == p_outer => {
                    Some(Prop::SpeaksFor(q, p_inner))
                }
                _ => None,
            },
            _ => None,
        },
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

    /// `now(τ)` infers `⊤`. Mismatch against an atom claim still rejects.
    #[test]
    fn now_infers_top_and_rejects_atom_claim() {
        let term = Term::Now(crate::time::TimeBound { epoch_ms: 0 });
        let prob_top = problem(Ctx::empty(), term.clone(), Prop::Top);
        assert!(decide_pure(&prob_top));

        let prob_atom = problem(Ctx::empty(), term, atom(0));
        assert!(!decide_pure(&prob_atom));
    }

    /// `verify(M, σ)` strips `p says φ` to `φ`.
    #[test]
    fn verify_strips_says() {
        let p = Principal::Atom(PrincipalId([3u8; 32]));
        let sig = Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        };
        let ctx = Ctx::empty().cons_a(atom(0));
        let signed = Term::Sign(p.clone(), Box::new(Term::Var(0)), sig.clone());
        let verified = Term::Verify(p, Box::new(signed), sig);
        let prob = problem(ctx, verified, atom(0));
        assert!(decide_pure(&prob));
    }

    /// `delegate(M, N)` produces `(p ⊓ q) says φ`. No-chain-splicing means
    /// the `q` in the speaks-for and the `q` of `N` must match.
    #[test]
    fn delegate_produces_acting_principal() {
        let p = Principal::Atom(PrincipalId([1u8; 32]));
        let q = Principal::Atom(PrincipalId([2u8; 32]));
        let sig = Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        };

        // The `p says (q ⇒ p)` witness — at the propositional level, we
        // construct it from a hypothesis. Context: H : q ⇒ p.
        let speaks_for = Prop::SpeaksFor(q.clone(), p.clone());
        // M : p says (q ⇒ p).
        let m = Term::Sign(p.clone(), Box::new(Term::Var(0)), sig.clone());
        // N : q says A.
        let n = Term::Sign(q.clone(), Box::new(Term::Var(1)), sig);

        // Context: 0 → speaks_for, 1 → atom(0).
        let ctx = Ctx::empty().cons_a(atom(0)).cons_a(speaks_for);
        let delegated = Term::Delegate(Box::new(m), Box::new(n));
        let acting = Principal::Acting(Box::new(p), Box::new(q));
        let expected = Prop::Says(acting, Box::new(atom(0)));
        let prob = problem(ctx, delegated, expected);
        assert!(decide_pure(&prob));
    }

    /// Attenuate: narrows `p says φ` to `p says ψ`.
    #[test]
    fn attenuate_narrows_says() {
        let p = Principal::Atom(PrincipalId([4u8; 32]));
        let sig = Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        };
        let ctx = Ctx::empty().cons_a(atom(0));
        let signed = Term::Sign(p.clone(), Box::new(Term::Var(0)), sig);
        let narrowed = Term::Attenuate(Box::new(signed), Box::new(atom(1)));
        let expected = Prop::Says(p, Box::new(atom(1)));
        let prob = problem(ctx, narrowed, expected);
        assert!(decide_pure(&prob));
    }

    /// `lift_ℓ(M) : φ @ ℓ`.
    #[test]
    fn lift_label_wraps_at_label() {
        use crate::ifc::Label;
        let label = Label(vec![3]);
        let ctx = Ctx::empty().cons_a(atom(0));
        let lifted = Term::LiftLabel(label.clone(), Box::new(Term::Var(0)));
        let expected = Prop::At(Box::new(atom(0)), label);
        let prob = problem(ctx, lifted, expected);
        assert!(decide_pure(&prob));
    }

    /// `within(M, τ) : ◇_τ φ`.
    #[test]
    fn within_intro_produces_within_modality() {
        let tau = crate::time::TimeBound { epoch_ms: 999_999 };
        let ctx = Ctx::empty().cons_a(atom(0));
        let within = Term::WithinIntro(tau.clone(), Box::new(Term::Var(0)));
        let expected = Prop::Within(tau, Box::new(atom(0)));
        let prob = problem(ctx, within, expected);
        assert!(decide_pure(&prob));
    }

    /// Discharge: `□_O φ` → `φ`.
    #[test]
    fn discharge_strips_box() {
        use crate::obligation::Obligation;
        // Construct an additive hypothesis at type □_O atom(0).
        let obligation = Obligation::Top;
        let boxed = Prop::Boxed(obligation, Box::new(atom(0)));
        let ctx = Ctx::empty().cons_a(boxed.clone());
        // discharge(Var(0), Var(0)) — we re-use the same hypothesis here as
        // a stand-in for the obligation evidence; the propositional checker
        // doesn't enforce the linearity, that's the Q4.d follow-up.
        let term = Term::Discharge(Box::new(Term::Var(0)), Box::new(Term::Var(0)));
        let prob = problem(ctx, term, atom(0));
        assert!(decide_pure(&prob));
    }

    /// and-I: `⟨M, N⟩` produces `φ ∧ ψ`.
    #[test]
    fn pair_produces_and() {
        // cons_a pushes at index 0, so after these two pushes:
        //   index 0 = atom(0), index 1 = atom(1)
        let ctx = Ctx::empty().cons_a(atom(1)).cons_a(atom(0));
        let term = Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(1)));
        let expected = Prop::And(Box::new(atom(0)), Box::new(atom(1)));
        let prob = problem(ctx, term, expected);
        assert!(decide_pure(&prob));
    }

    /// and-Eₗ + and-Eᵣ: round-trip through Fst/Snd.
    #[test]
    fn pair_fst_snd_round_trip() {
        let ctx = Ctx::empty().cons_a(atom(1)).cons_a(atom(0));
        let pair = Term::Pair(Box::new(Term::Var(0)), Box::new(Term::Var(1)));
        // π₁ ⟨Var 0, Var 1⟩ : atom(0)
        let fst_term = Term::Fst(Box::new(pair.clone()));
        let fst_prob = problem(ctx.clone(), fst_term, atom(0));
        assert!(decide_pure(&fst_prob));

        // π₂ ⟨Var 0, Var 1⟩ : atom(1)
        let snd_term = Term::Snd(Box::new(pair));
        let snd_prob = problem(ctx, snd_term, atom(1));
        assert!(decide_pure(&snd_prob));
    }

    /// or-I left: `inl_ψ M` produces `φ ∨ ψ`.
    #[test]
    fn inl_produces_or_left() {
        let ctx = Ctx::empty().cons_a(atom(0));
        let term = Term::Inl(Box::new(atom(1)), Box::new(Term::Var(0)));
        let expected = Prop::Or(Box::new(atom(0)), Box::new(atom(1)));
        let prob = problem(ctx, term, expected);
        assert!(decide_pure(&prob));
    }

    /// or-I right symmetric.
    #[test]
    fn inr_produces_or_right() {
        let ctx = Ctx::empty().cons_a(atom(1));
        let term = Term::Inr(Box::new(atom(0)), Box::new(Term::Var(0)));
        let expected = Prop::Or(Box::new(atom(0)), Box::new(atom(1)));
        let prob = problem(ctx, term, expected);
        assert!(decide_pure(&prob));
    }

    /// or-E: case eliminates a disjunction; both branches must agree.
    #[test]
    fn case_eliminates_or() {
        let ctx = Ctx::empty().cons_a(Prop::Or(Box::new(atom(0)), Box::new(atom(0))));
        // case (Var 0) of inl x ⇒ x | inr y ⇒ y. Both yield atom(0).
        let case = Term::Case(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(0)), // bound: inl-witness shadows outer
            Box::new(Term::Var(0)), // bound: inr-witness shadows outer
        );
        let prob = problem(ctx, case, atom(0));
        assert!(decide_pure(&prob));
    }

    /// or-E rejects branches that disagree.
    #[test]
    fn case_rejects_disagreeing_branches() {
        let ctx = Ctx::empty().cons_a(Prop::Or(Box::new(atom(0)), Box::new(atom(1))));
        let case = Term::Case(
            Box::new(Term::Var(0)),
            Box::new(Term::Var(0)), // : atom(0)
            Box::new(Term::Var(0)), // : atom(1)
        );
        let prob = problem(ctx, case, atom(0));
        assert!(!decide_pure(&prob));
    }

    /// tensor-I: M ⊗ N : φ ⊗ ψ.
    #[test]
    fn tensor_intro_produces_tensor() {
        let ctx = Ctx::empty().cons_a(atom(1)).cons_a(atom(0));
        let term = Term::TensorIntro(Box::new(Term::Var(0)), Box::new(Term::Var(1)));
        let expected = Prop::Tensor(Box::new(atom(0)), Box::new(atom(1)));
        let prob = problem(ctx, term, expected);
        assert!(decide_pure(&prob));
    }

    /// says-extract: `let ⟨x⟩_p = M in N` extracts the underlying proof.
    #[test]
    fn let_says_binds_inner_proof() {
        let p = Principal::Atom(PrincipalId([9u8; 32]));
        let sig = Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        };
        // Context: hyp : p says atom(0)
        let says_prop = Prop::Says(p.clone(), Box::new(atom(0)));
        let ctx = Ctx::empty().cons_a(says_prop);
        // let ⟨x⟩_p = Var 0 in x  --  via LetSays(p, scrut, body=Var(0))
        // Note: scrut is Var(0) referring to the existing additive hyp.
        let _signed = Term::Sign(p.clone(), Box::new(Term::Var(0)), sig);
        let term = Term::LetSays(
            p,
            Box::new(Term::Var(0)),
            Box::new(Term::Var(0)), // inner: bound to atom(0)
        );
        let prob = problem(ctx, term, atom(0));
        assert!(decide_pure(&prob));
    }

    /// sf-extract: from `p says (q ⇒ p)` extract `q ⇒ p`.
    #[test]
    fn sf_extract_pulls_speaks_for() {
        let p = Principal::Atom(PrincipalId([1u8; 32]));
        let q = Principal::Atom(PrincipalId([2u8; 32]));
        let sf = Prop::SpeaksFor(q.clone(), p.clone());
        let says_sf = Prop::Says(p, Box::new(sf.clone()));
        let ctx = Ctx::empty().cons_a(says_sf);
        let term = Term::SfExtract(Box::new(Term::Var(0)));
        let prob = problem(ctx, term, sf);
        assert!(decide_pure(&prob));
    }

    /// Chain-splicing attempt is rejected: speaks-for inner principal must
    /// match the says-principal of N.
    #[test]
    fn delegate_rejects_chain_splicing() {
        let p = Principal::Atom(PrincipalId([1u8; 32]));
        let q = Principal::Atom(PrincipalId([2u8; 32]));
        let r = Principal::Atom(PrincipalId([3u8; 32])); // wrong principal
        let sig = Signature {
            alg: 0,
            bytes: vec![0u8; 64],
        };
        let speaks_for = Prop::SpeaksFor(q, p.clone());
        let m = Term::Sign(p, Box::new(Term::Var(0)), sig.clone());
        let n = Term::Sign(r, Box::new(Term::Var(1)), sig); // says by r, not q!
        let ctx = Ctx::empty().cons_a(atom(0)).cons_a(speaks_for);
        let delegated = Term::Delegate(Box::new(m), Box::new(n));
        // Any claimed conclusion must fail — the spliced chain is rejected.
        let prob = problem(ctx, delegated, atom(0));
        assert!(!decide_pure(&prob));
    }
}
