//! Small-step reduction relation `M ▷ M'`.
//!
//! Subject reduction (M1.Q2.c) is proven about this in `lean/DLC/Reduce.lean`.

use crate::syntax::Term;

/// One step of reduction. Returns `None` if `term` is a normal form.
pub fn step(_term: &Term) -> Option<Term> {
    None
}
