/-
DLC — Graded comonad for quantitative obligations.

Lean mirror of `crates/dlc-core/src/graded.rs`. Follows the categorical model
of Petricek-Mycroft-Orchard and the applied work in *Graded Modal Types for
Integrity and Confidentiality* (arXiv 2309.04324).

Pairs a carrier value with a DP budget `(ε, δ)`. The grade-additive law
matches DP's sequential composition theorem.
-/

import DLC.Obligation

namespace DLC

/-- A differential-privacy budget grade. Mirrors
`crate::obligation::DpBudget`. -/
structure DpBudget where
  /-- ε (privacy-loss bound) in micro-units. -/
  epsilonMicros : Nat
  /-- δ (failure probability) in micro-units. -/
  deltaMicros : Nat
  deriving Repr, DecidableEq

namespace DpBudget

/-- The zero budget. -/
def zero : DpBudget := ⟨0, 0⟩

/-- Componentwise add (sequential DP composition). Lean is unbounded
`Nat` so we do not need the `saturating_` qualifier the Rust mirror uses. -/
def saturatingAdd (a b : DpBudget) : DpBudget :=
  ⟨a.epsilonMicros + b.epsilonMicros, a.deltaMicros + b.deltaMicros⟩

/-- Componentwise ≤. -/
def le (a b : DpBudget) : Bool :=
  decide (a.epsilonMicros ≤ b.epsilonMicros ∧ a.deltaMicros ≤ b.deltaMicros)

end DpBudget

/-- A value paired with its consumed grade. -/
structure Graded (α : Type) where
  value : α
  grade : DpBudget
  deriving Repr

namespace Graded

/-- Inject at the zero grade. -/
def pure {α : Type} (a : α) : Graded α := ⟨a, DpBudget.zero⟩

/-- Functor action: map preserves the grade. -/
def map {α β : Type} (f : α → β) (g : Graded α) : Graded β :=
  ⟨f g.value, g.grade⟩

/-- Sequence: append additional consumption. -/
def consume {α : Type} (g : Graded α) (extra : DpBudget) : Graded α :=
  ⟨g.value, g.grade.saturatingAdd extra⟩

end Graded

/-! ## Comonad laws (proven — M1.Q3.b closure).

`pure` is left-identity for `consume zero`; consumption is associative
componentwise. The proofs unfold the definitions and reduce by `Nat`
arithmetic — no axioms, no `sorry`. -/

/-- Identity-of-consume law (grade-side). -/
theorem graded_identity_law :
    ∀ {α : Type} (a : α),
      (Graded.pure a).consume DpBudget.zero = Graded.pure a := by
  intros α a
  simp [Graded.pure, Graded.consume, DpBudget.zero, DpBudget.saturatingAdd]

/-- Associativity of consumption (sequential composition of grades).

The general associativity-of-`saturatingAdd` lemma factors out — it's
what makes the law independent of the carrier `α`. -/
theorem dp_budget_saturating_add_assoc (a b c : DpBudget) :
    (a.saturatingAdd b).saturatingAdd c = a.saturatingAdd (b.saturatingAdd c) := by
  simp [DpBudget.saturatingAdd, Nat.add_assoc]

theorem graded_associativity_law :
    ∀ {α : Type} (a : α) (x y : DpBudget),
      ((Graded.pure a).consume x).consume y =
      (Graded.pure a).consume (x.saturatingAdd y) := by
  intros α a x y
  simp [Graded.pure, Graded.consume,
        DpBudget.zero, DpBudget.saturatingAdd, Nat.add_assoc, Nat.zero_add]

/-! ## Backward-compat aliases.

Previously these laws were stated as `def …Statement : Prop`. We keep the
old names as `abbrev`-pointed-at-the-theorem so anything that referenced
the statement form (none yet, but reserved for the spec / paper) stays
type-checked. -/

/-- @[deprecated graded_identity_law] -/
abbrev GradedIdentityLawStatement : Prop :=
  ∀ {α : Type} (a : α),
    (Graded.pure a).consume DpBudget.zero = Graded.pure a

/-- @[deprecated graded_associativity_law] -/
abbrev GradedAssociativityLawStatement : Prop :=
  ∀ {α : Type} (a : α) (x y : DpBudget),
    ((Graded.pure a).consume x).consume y =
    (Graded.pure a).consume (x.saturatingAdd y)

end DLC
