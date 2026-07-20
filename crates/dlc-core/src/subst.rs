//! Capture-avoiding substitution on de-Bruijn-indexed terms.
//!
//! The substitution lemma (`Γ ⊢ M : φ` and `Γ, x:ψ ⊢ N : χ` imply
//! `Γ ⊢ N[M/x] : χ`) is stated about these functions in
//! `lean/DLC/Subst.lean`. Production-grade closure of the lemma lands at
//! M1.Q2.a. The functions themselves are correct now.

use alloc::boxed::Box;

use crate::syntax::Term;

/// Shift every free de-Bruijn index in `term` by `delta`, treating indices
/// `< cutoff` as bound (and therefore not shifted). The standard "lift" of
/// the de-Bruijn calculus.
///
/// `delta` may be negative (used when closing a binder); callers must ensure
/// no resulting index goes below zero.
pub fn shift(term: &Term, delta: i32, cutoff: u32) -> Term {
    match term {
        Term::Var(i) => {
            if *i < cutoff {
                Term::Var(*i)
            } else {
                let shifted = (*i as i64) + (delta as i64);
                // Shift below zero would mean a use site escaping its binder,
                // which substitution must never produce. Internal-API
                // contract violation; treat as identity rather than panic to
                // keep `dlc-core` no-panic for Aeneas.
                if shifted < 0 {
                    Term::Var(*i)
                } else {
                    Term::Var(shifted as u32)
                }
            }
        }
        Term::Lam(p, body) => Term::Lam(p.clone(), Box::new(shift(body, delta, cutoff + 1))),
        Term::App(f, x) => Term::App(
            Box::new(shift(f, delta, cutoff)),
            Box::new(shift(x, delta, cutoff)),
        ),
        Term::Sign(p, m, sig) => {
            Term::Sign(p.clone(), Box::new(shift(m, delta, cutoff)), sig.clone())
        }
        Term::Verify(p, m, sig) => {
            Term::Verify(p.clone(), Box::new(shift(m, delta, cutoff)), sig.clone())
        }
        Term::Delegate(m, n) => Term::Delegate(
            Box::new(shift(m, delta, cutoff)),
            Box::new(shift(n, delta, cutoff)),
        ),
        Term::Attenuate(m, psi) => Term::Attenuate(Box::new(shift(m, delta, cutoff)), psi.clone()),
        Term::Boxed(o, m, n) => Term::Boxed(
            o.clone(),
            Box::new(shift(m, delta, cutoff)),
            Box::new(shift(n, delta, cutoff)),
        ),
        Term::Discharge(m, n) => Term::Discharge(
            Box::new(shift(m, delta, cutoff)),
            Box::new(shift(n, delta, cutoff)),
        ),
        Term::LiftLabel(l, m) => Term::LiftLabel(l.clone(), Box::new(shift(m, delta, cutoff))),
        Term::Declassify(l, m, pi) => Term::Declassify(
            l.clone(),
            Box::new(shift(m, delta, cutoff)),
            Box::new(shift(pi, delta, cutoff)),
        ),
        Term::Now(t) => Term::Now(t.clone()),
        Term::WithinIntro(t, m) => Term::WithinIntro(t.clone(), Box::new(shift(m, delta, cutoff))),

        // Additive product
        Term::Pair(a, b) => Term::Pair(
            Box::new(shift(a, delta, cutoff)),
            Box::new(shift(b, delta, cutoff)),
        ),
        Term::Fst(a) => Term::Fst(Box::new(shift(a, delta, cutoff))),
        Term::Snd(a) => Term::Snd(Box::new(shift(a, delta, cutoff))),

        // Additive coproduct
        Term::Inl(p, a) => Term::Inl(p.clone(), Box::new(shift(a, delta, cutoff))),
        Term::Inr(p, a) => Term::Inr(p.clone(), Box::new(shift(a, delta, cutoff))),
        Term::Case(scrut, left, right) => Term::Case(
            Box::new(shift(scrut, delta, cutoff)),
            // `case` branches bind one new variable each
            Box::new(shift(left, delta, cutoff + 1)),
            Box::new(shift(right, delta, cutoff + 1)),
        ),

        // Multiplicative product
        Term::TensorIntro(a, b) => Term::TensorIntro(
            Box::new(shift(a, delta, cutoff)),
            Box::new(shift(b, delta, cutoff)),
        ),
        Term::LetTensor(scrut, body) => Term::LetTensor(
            Box::new(shift(scrut, delta, cutoff)),
            // let-tensor binds two new variables
            Box::new(shift(body, delta, cutoff + 2)),
        ),

        // Says elimination forms
        Term::LetSays(p, scrut, body) => Term::LetSays(
            p.clone(),
            Box::new(shift(scrut, delta, cutoff)),
            Box::new(shift(body, delta, cutoff + 1)),
        ),
        Term::SfExtract(m) => Term::SfExtract(Box::new(shift(m, delta, cutoff))),
    }
}

/// Substitute `value` for the variable at de-Bruijn index 0 in `body`. The
/// substitution shifts `value`'s free variables up by the binder depth at
/// each occurrence (the standard "instantiate" of the locally-nameless / de-
/// Bruijn calculus).
///
/// Use case: `(λx.body) value` β-reduces to `subst(body, value)`.
pub fn subst(body: &Term, value: &Term) -> Term {
    subst_at(body, value, 0)
}

fn subst_at(body: &Term, value: &Term, depth: u32) -> Term {
    match body {
        Term::Var(i) => match (*i).cmp(&depth) {
            // Hit. Lift the value's free indices over the surrounding
            // binders we descended through.
            core::cmp::Ordering::Equal => shift(value, depth as i32, 0),
            // Was a free variable; close one binder by decrementing.
            core::cmp::Ordering::Greater => Term::Var(*i - 1),
            // Bound by an inner binder.
            core::cmp::Ordering::Less => Term::Var(*i),
        },
        Term::Lam(p, inner) => Term::Lam(p.clone(), Box::new(subst_at(inner, value, depth + 1))),
        Term::App(f, x) => Term::App(
            Box::new(subst_at(f, value, depth)),
            Box::new(subst_at(x, value, depth)),
        ),
        Term::Sign(p, m, sig) => {
            Term::Sign(p.clone(), Box::new(subst_at(m, value, depth)), sig.clone())
        }
        Term::Verify(p, m, sig) => {
            Term::Verify(p.clone(), Box::new(subst_at(m, value, depth)), sig.clone())
        }
        Term::Delegate(m, n) => Term::Delegate(
            Box::new(subst_at(m, value, depth)),
            Box::new(subst_at(n, value, depth)),
        ),
        Term::Attenuate(m, psi) => {
            Term::Attenuate(Box::new(subst_at(m, value, depth)), psi.clone())
        }
        Term::Boxed(o, m, n) => Term::Boxed(
            o.clone(),
            Box::new(subst_at(m, value, depth)),
            Box::new(subst_at(n, value, depth)),
        ),
        Term::Discharge(m, n) => Term::Discharge(
            Box::new(subst_at(m, value, depth)),
            Box::new(subst_at(n, value, depth)),
        ),
        Term::LiftLabel(l, m) => Term::LiftLabel(l.clone(), Box::new(subst_at(m, value, depth))),
        Term::Declassify(l, m, pi) => Term::Declassify(
            l.clone(),
            Box::new(subst_at(m, value, depth)),
            Box::new(subst_at(pi, value, depth)),
        ),
        Term::Now(t) => Term::Now(t.clone()),
        Term::WithinIntro(t, m) => {
            Term::WithinIntro(t.clone(), Box::new(subst_at(m, value, depth)))
        }

        Term::Pair(a, b) => Term::Pair(
            Box::new(subst_at(a, value, depth)),
            Box::new(subst_at(b, value, depth)),
        ),
        Term::Fst(a) => Term::Fst(Box::new(subst_at(a, value, depth))),
        Term::Snd(a) => Term::Snd(Box::new(subst_at(a, value, depth))),

        Term::Inl(p, a) => Term::Inl(p.clone(), Box::new(subst_at(a, value, depth))),
        Term::Inr(p, a) => Term::Inr(p.clone(), Box::new(subst_at(a, value, depth))),
        Term::Case(scrut, left, right) => Term::Case(
            Box::new(subst_at(scrut, value, depth)),
            Box::new(subst_at(left, value, depth + 1)),
            Box::new(subst_at(right, value, depth + 1)),
        ),

        Term::TensorIntro(a, b) => Term::TensorIntro(
            Box::new(subst_at(a, value, depth)),
            Box::new(subst_at(b, value, depth)),
        ),
        Term::LetTensor(scrut, body) => Term::LetTensor(
            Box::new(subst_at(scrut, value, depth)),
            Box::new(subst_at(body, value, depth + 2)),
        ),

        Term::LetSays(p, scrut, body) => Term::LetSays(
            p.clone(),
            Box::new(subst_at(scrut, value, depth)),
            Box::new(subst_at(body, value, depth + 1)),
        ),
        Term::SfExtract(m) => Term::SfExtract(Box::new(subst_at(m, value, depth))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::Prop;

    /// Substituting into `λ. 0` (identity) just returns the lambda; the
    /// outer var index 0 is bound, so the substitution targets index 1, which
    /// isn't there.
    #[test]
    fn identity_lambda_unchanged() {
        let id = Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)));
        let value = Term::Var(7);
        let result = subst(&id, &value);
        assert_eq!(
            result,
            Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0))),
        );
    }

    /// `subst(Var(0), value)` returns `value` unshifted (depth 0 entry).
    #[test]
    fn subst_var_zero_returns_value() {
        let value = Term::Var(3);
        let result = subst(&Term::Var(0), &value);
        assert_eq!(result, Term::Var(3));
    }

    /// `subst(Var(1), value)` returns `Var(0)` — the free variable's index
    /// decrements by one because the binder it pointed past has been closed.
    #[test]
    fn subst_free_var_decrements() {
        let result = subst(&Term::Var(1), &Term::Var(99));
        assert_eq!(result, Term::Var(0));
    }

    /// Shifting a closed term by any delta is a no-op.
    #[test]
    fn shift_closed_lambda_is_noop() {
        let id = Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(0)));
        let shifted = shift(&id, 5, 0);
        assert_eq!(shifted, id);
    }

    /// Shift adds delta to free variables only.
    #[test]
    fn shift_increments_free_var() {
        let result = shift(&Term::Var(2), 3, 0);
        assert_eq!(result, Term::Var(5));
    }

    /// Substituting under one binder lifts the value's free indices.
    #[test]
    fn subst_under_binder_lifts_value() {
        // Body: λ. Var(1)  (a use of the outer var-zero, one binder deep)
        let body = Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(1)));
        // Value: a free Var(0)
        let value = Term::Var(0);
        // After subst, body's outer var 0 (i.e. the inner Var(1)) becomes the
        // value lifted by one binder → Var(1).
        let result = subst(&body, &value);
        assert_eq!(
            result,
            Term::Lam(Box::new(Prop::Atom(0)), Box::new(Term::Var(1))),
        );
    }
}
