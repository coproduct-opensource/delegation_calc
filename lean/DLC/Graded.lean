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

/-! ## Comonad laws (statements only — proof closure at M1.Q3.d).

`pure` is left-identity for `consume zero`; consumption is associative
componentwise. Stated here as named `def Statement : Prop` per CLAUDE.md
discipline. -/

/-- Identity-of-consume law (grade-side). -/
def GradedIdentityLawStatement : Prop :=
  ∀ {α : Type} (a : α),
    (Graded.pure a).consume DpBudget.zero = Graded.pure a

/-- Associativity of consumption (sequential composition of grades). -/
def GradedAssociativityLawStatement : Prop :=
  ∀ {α : Type} (a : α) (x y : DpBudget),
    ((Graded.pure a).consume x).consume y =
    (Graded.pure a).consume (x.saturatingAdd y)

end DLC
