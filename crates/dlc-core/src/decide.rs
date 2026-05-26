//! The decidable proof-checker — T1's algorithm.
//!
//! Pure function: takes a context, term, and proposition, returns `true` iff
//! the term proves the proposition in the context. The Aeneas translation of
//! this function is what `lean/DLC/Decidability.lean` proves total and
//! `O(|term| · log |ctx|)`.

use crate::judgment::TypingProblem;

/// Decide whether the given typing problem is derivable in DLC.
///
/// Stub returns `false`. M1.Q2.d closes T1 against this function.
pub fn decide_pure(_problem: &TypingProblem) -> bool {
    false
}
