//! Typing judgments and contexts.
//!
//! `Ctx`, `KeyRing`, and `RuleName` mirror the Lean encoding in
//! `lean/DLC/Judgment.lean`. The Rust verifier's case analysis dispatches on
//! `RuleName` so the rule index is stable across both languages.

use alloc::vec::Vec;

use crate::principal::KeyRecord;
use crate::syntax::{Prop, Term};

/// A typing context. Additive hypotheses are re-usable; linear hypotheses are
/// single-use. Substructural rules of DLC enforce single-use via the multiset
/// shape of `linear`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Ctx {
    /// Non-linear (additive) hypotheses, available for arbitrary use.
    pub additive: Vec<Prop>,
    /// Linear hypotheses, available for exactly one use.
    pub linear: Vec<Prop>,
}

impl Ctx {
    /// The empty context.
    pub fn empty() -> Self {
        Self::default()
    }

    /// Push an additive hypothesis.
    pub fn cons_a(mut self, phi: Prop) -> Self {
        self.additive.insert(0, phi);
        self
    }

    /// Push a linear hypothesis.
    pub fn cons_l(mut self, phi: Prop) -> Self {
        self.linear.insert(0, phi);
        self
    }
}

/// A keyring threads the cryptographic-typing judgment `⊢_K`.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KeyRing {
    /// Known public keys, indexed by principal id.
    pub entries: Vec<KeyRecord>,
}

/// A typing problem: "does `term` have proposition `prop` in `ctx`?"
#[derive(Clone, Debug)]
pub struct TypingProblem {
    /// The context.
    pub ctx: Ctx,
    /// The candidate proof term.
    pub term: Term,
    /// The proposition being claimed.
    pub prop: Prop,
}

/// Enumeration of the named typing rules from `spec/typing-rules.md`.
///
/// Stable index used by both the Lean `Deriv` constructors and the Rust
/// verifier's match arms. New rules append; never insert.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RuleName {
    /// `var-A` — additive variable lookup.
    VarA,
    /// `var-L` — linear variable lookup.
    VarL,
    /// `weaken-A` — additive weakening.
    WeakenA,
    /// `imp-I` — implication introduction.
    ImpI,
    /// `imp-E` — implication elimination.
    ImpE,
    /// `and-I` — additive conjunction introduction.
    AndI,
    /// `and-Eₗ` — left projection.
    AndEL,
    /// `and-Eᵣ` — right projection.
    AndER,
    /// `says-I` — affirmation introduction (carries a signature).
    SaysI,
    /// `says-E` — affirmation elimination (let-binds the proof).
    SaysE,
    /// `delegate` — chain composition.
    Delegate,
    /// `attenuate` — narrow an affirmation along provable implication.
    Attenuate,
    /// `lift` — IFC label introduction.
    Lift,
    /// `app-IFC` — application takes the join of labels.
    AppIFC,
    /// `declassify` — controlled label lowering, requires witness.
    Declassify,
    /// `box-I` — obligation-attached proposition introduction.
    BoxI,
    /// `discharge` — consume an obligation.
    Discharge,
    /// `now` — proof of `now < τ` from a time anchor.
    Now,
    /// `within-I` — `◇_τ` introduction.
    WithinI,
    /// `within-E` — `◇_τ` elimination.
    WithinE,
    /// `verify` — cryptographic-typing bridge rule.
    Verify,

    // --- Q4 follow-up: additive and linear connectives ---
    /// `or-I` — disjunction introduction (left or right).
    OrI,
    /// `or-E` — disjunction elimination (case).
    OrE,
    /// `tensor-I` — linear conjunction introduction.
    TensorI,
    /// `tensor-E` — linear conjunction elimination (let-tensor).
    TensorE,
    /// `lolli-I` — linear implication introduction (shares syntax with `imp-I`).
    LolliI,
    /// `lolli-E` — linear implication elimination (shares syntax with `imp-E`).
    LolliE,
    /// `let-tensor` — alias / reduction form of `tensor-E`.
    LetTensor,
    /// `says-extract` — explicit let-binder form of `says-E`.
    SaysExtract,
    /// `sf-extract` — extract a speaks-for from `p says (q ⇒ p)`.
    SfExtract,

    // --- R1 (DLC-D first-classing): distributed constructs ---
    /// `commit-I` — capability-gated replicated write introduction. Types
    /// `command M c ℓ : Replicated (φ ⊃ φ)` from a credential `c : issuer says
    /// capProp` and a store transformer `M : φ ⊃ φ`. Additive this increment
    /// (R1-inc2); the linear seal (`commit-I-L` in `CDerivS`) is deferred.
    CommitI,
}
