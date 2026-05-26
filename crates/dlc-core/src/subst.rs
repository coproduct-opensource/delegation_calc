//! Capture-avoiding substitution.
//!
//! Stubbed for Week-1; the substitution lemma (M1.Q2.a) is what is proven about
//! this function in `lean/DLC/Subst.lean`.

use alloc::boxed::Box;

use crate::syntax::Term;

/// Substitute `value` for the variable at de-Bruijn index 0 in `body`,
/// shifting indices appropriately. Stub returns `body` unchanged.
pub fn subst(_body: &Term, _value: &Term) -> Term {
    // M1.Q2.a deliverable. Stubbed for skeleton.
    Term::Var(0)
}

/// Shift de-Bruijn indices in `term` by `delta`.
pub fn shift(_term: &Term, _delta: i32) -> Term {
    Term::Var(0)
}

#[allow(dead_code)]
fn _force_box_dep() -> Box<Term> {
    Box::new(Term::Var(0))
}
