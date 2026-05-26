//! Typing judgments and contexts.
//!
//! The four mutually recursive judgments of DLC:
//!   - `Γ ⊢ M : φ`            — logical typing
//!   - `Γ ⊢ p says M : p says φ` — affirmation typing
//!   - `Γ ⊢ M ▷ M'`           — small-step reduction
//!   - `Γ ⊢_K M : φ`          — cryptographic typing under keyring K
//!
//! The rules themselves are frozen in `spec/typing-rules.md` and mirrored in
//! `lean/DLC/Judgment.lean`. This module is the Rust counterpart that Aeneas
//! translates back to Lean for the Rust↔Lean bridge.

use alloc::vec::Vec;

use crate::principal::KeyRecord;
use crate::syntax::{Prop, Term};

/// A typing context. Hypotheses are pairs of (variable index, proposition).
/// Linear hypotheses are a multiset; the substructural rules of the calculus
/// enforce single-use.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Context {
    /// Non-linear (additive) hypotheses, available for arbitrary use.
    pub additive: Vec<Prop>,
    /// Linear hypotheses, available for exactly one use.
    pub linear: Vec<Prop>,
}

/// A keyring binds principal identities to their public keys, threading the
/// cryptographic-typing judgment `⊢_K`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KeyRing {
    /// Known public keys, indexed by principal id.
    pub entries: Vec<KeyRecord>,
}

/// A typing problem: "does `term` have proposition `prop` in `ctx`?"
#[derive(Clone, Debug)]
pub struct TypingProblem {
    /// The context.
    pub ctx: Context,
    /// The candidate proof term.
    pub term: Term,
    /// The proposition being claimed.
    pub prop: Prop,
}
