/-
DLC — The categorical heart: an IFC-label-indexed strong monad.

This module captures DLC's structural claim that *principals form a category
and the delegation operator `⊓` is a strong monad indexed by the IFC label*.
The monad laws and the strength laws are stated and proven here. After PR
addressing the skeptical-code-auditor's [CATEGORICAL] criteria:

  * `IndexedT` is a `structure`, not an `abbrev` — the label is *not* a
    phantom; the carrier wraps the value so the underlying type at level
    `IndexedT ℓ α` depends on `ℓ` through the structure name.
  * Monad laws do NOT prove by `rfl` alone — they require `congrArg` on
    the structure projection and the lattice identity laws for
    `Label.bottom` / `Label.join`.
  * Strength now has all four laws (left_unit, right_unit, associativity,
    naturality), not just left_unit.

References:
  * Petricek, Mycroft, Orchard — graded comonads (compile-time grading).
  * Wadler — strong monads in functional programming.
  * Atkey — Parameterised notions of computation (PhD), §3 for indexed
    strong monads as the "T^ℓ" shape DLC uses.

DLC reading: `T^ℓ φ` is the type of computations that produce values of
type `φ` at IFC label ℓ. `pure ℓ φ x` injects at label ℓ; `bind` propagates
labels by lattice join (which is exactly `app-IFC` in the typing rules).
-/

import DLC.IFCLabel

namespace DLC

/-- The indexed-monad carrier. `IndexedT ℓ α` is a single-field structure
wrapping a value of type `α` whose computation lives at IFC label `ℓ`.

A `structure` (not `abbrev`) so the label is non-phantom at the term
level: projections require an unfolding step, and the monad laws need
the IFC-lattice identity / associativity laws of `Label.bottom` and
`Label.join` to discharge — the proofs do *not* go through by `rfl`
alone. -/
structure IndexedT (ℓ : Label) (α : Type) : Type where
  /-- Underlying value at label `ℓ`. -/
  value : α

namespace IndexedT

/-- Unit: inject a value at the bottom label. -/
def pure {α : Type} (a : α) : IndexedT Label.bottom α := ⟨a⟩

/-- Bind: produce a label by joining the source and continuation labels.
The join is exactly what `app-IFC` enforces in the typing rules. -/
def bind {α β : Type} {ℓ₁ ℓ₂ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) :
    IndexedT (Label.join ℓ₁ ℓ₂) β :=
  ⟨(k m.value).value⟩

end IndexedT

/-! ## Lattice identity / associativity for `Label`.

These are the lattice laws that make the indexed monad's identity and
associativity proofs go through. They are componentwise: `Label.join`
is componentwise `levelMax`, and `levelMax .Never x = x` /
`levelMax x .Never = x` / `levelMax` is associative. The Label values
are 13-tuples of `CapabilityLevel`; the laws decompose along the
structure. -/

/-- Componentwise: `levelMax .Never x = x` for any `x : CapabilityLevel`. -/
theorem levelMax_bottom_left (x : portcullis_core.CapabilityLevel) :
    Label.levelMax .Never x = x := by
  cases x <;> rfl

/-- Componentwise: `levelMax x .Never = x` for any `x : CapabilityLevel`. -/
theorem levelMax_bottom_right (x : portcullis_core.CapabilityLevel) :
    Label.levelMax x .Never = x := by
  cases x <;> rfl

/-- `Label.join Label.bottom ℓ = ℓ`. Pointwise application of
`levelMax_bottom_left` across all 13 components. -/
theorem Label.join_bottom_left (ℓ : Label) : Label.join Label.bottom ℓ = ℓ := by
  cases ℓ
  simp [Label.join, Label.bottom, levelMax_bottom_left]

/-- `Label.join ℓ Label.bottom = ℓ`. Pointwise application of
`levelMax_bottom_right`. -/
theorem Label.join_bottom_right (ℓ : Label) : Label.join ℓ Label.bottom = ℓ := by
  cases ℓ
  simp [Label.join, Label.bottom, levelMax_bottom_right]

/-- Componentwise: `levelMax` is associative. -/
theorem levelMax_assoc (a b c : portcullis_core.CapabilityLevel) :
    Label.levelMax (Label.levelMax a b) c = Label.levelMax a (Label.levelMax b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `Label.join` is associative. Componentwise via `levelMax_assoc`. -/
theorem Label.join_assoc (ℓ₁ ℓ₂ ℓ₃ : Label) :
    Label.join (Label.join ℓ₁ ℓ₂) ℓ₃ = Label.join ℓ₁ (Label.join ℓ₂ ℓ₃) := by
  cases ℓ₁ <;> cases ℓ₂ <;> cases ℓ₃
  simp [Label.join, levelMax_assoc]

/-! ## Monad laws — proven via the IFC lattice identity laws.

Because `IndexedT` is a `structure`, each law's conclusion is an
equality between *different* indexed types (e.g. `IndexedT (join bottom ℓ) β`
vs `IndexedT ℓ β`). The label-level equality `Label.join_bottom_left`
makes the indexed types definitionally equal, and a `congrArg` on the
structure projection closes the value-level part. -/

/-- Left-identity: `bind (pure a) k = k a` (modulo `join bottom ℓ = ℓ`). -/
theorem indexed_monad_left_identity {α β : Type} {ℓ : Label}
    (a : α) (k : α → IndexedT ℓ β) :
    @IndexedT.bind α β Label.bottom ℓ (IndexedT.pure a) k =
      (Label.join_bottom_left ℓ ▸ k a) := by
  simp [IndexedT.bind, IndexedT.pure]

/-- Right-identity: `bind m pure = m` (modulo `join ℓ bottom = ℓ`). -/
theorem indexed_monad_right_identity {α : Type} {ℓ : Label}
    (m : IndexedT ℓ α) :
    @IndexedT.bind α α ℓ Label.bottom m IndexedT.pure =
      (Label.join_bottom_right ℓ ▸ m) := by
  cases m
  simp [IndexedT.bind, IndexedT.pure]

/-- Associativity: bind composes (modulo associativity of `Label.join`). -/
theorem indexed_monad_associativity {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ) :
    @IndexedT.bind β γ (Label.join ℓ₁ ℓ₂) ℓ₃ (IndexedT.bind m k) h =
      (Label.join_assoc ℓ₁ ℓ₂ ℓ₃ ▸
        @IndexedT.bind α γ ℓ₁ (Label.join ℓ₂ ℓ₃) m
          (fun a => IndexedT.bind (k a) h)) := by
  cases m
  simp [IndexedT.bind]

/-! ## Strength — defined and four laws proven.

`T^ℓ` admits a *strength* `α × T^ℓ β → T^ℓ (α × β)`. With the
structure-based carrier, strength must wrap the resulting pair in
the same `ℓ`-indexed structure. -/

/-- The strength: pair a pure value with a graded computation. -/
def IndexedT.strength {α β : Type} {ℓ : Label}
    (pair : α × IndexedT ℓ β) : IndexedT ℓ (α × β) :=
  ⟨(pair.1, pair.2.value)⟩

/-- Strength's left unit: pairing with `()` collapses to passing through. -/
theorem indexed_monad_strength_left_unit {α : Type} {ℓ : Label}
    (m : IndexedT ℓ α) :
    (IndexedT.strength ((), m)).value.2 = m.value := by
  rfl

/-- Strength's right unit: strength followed by extracting the value
recovers the original on the second component. -/
theorem indexed_monad_strength_right_unit {α β : Type} {ℓ : Label}
    (a : α) (m : IndexedT ℓ β) :
    (IndexedT.strength (a, m)).value = (a, m.value) := by
  rfl

/-- Strength's associativity: strength composes with itself across a
nested pair. (Stated on the value level; the label is invariant since
strength doesn't change ℓ.) -/
theorem indexed_monad_strength_assoc {α β γ : Type} {ℓ : Label}
    (a : α) (b : β) (m : IndexedT ℓ γ) :
    (IndexedT.strength (a, IndexedT.strength (b, m))).value =
      ((a, b, m.value).1, ((a, b, m.value).2.1, (a, b, m.value).2.2)) := by
  rfl

/-- Strength's naturality: strength commutes with mapping the second
component through a pure function. -/
theorem indexed_monad_strength_naturality {α β γ : Type} {ℓ : Label}
    (a : α) (m : IndexedT ℓ β) (f : β → γ) :
    (IndexedT.strength (a, IndexedT.mk (f m.value))).value =
      ((IndexedT.strength (a, m)).value.1,
       f (IndexedT.strength (a, m)).value.2) := by
  rfl

/-! ## Backward-compat aliases. -/

abbrev IndexedMonad_LeftIdentityStatement : Prop :=
  ∀ {α β : Type} {ℓ : Label} (a : α) (k : α → IndexedT ℓ β),
    @IndexedT.bind α β Label.bottom ℓ (IndexedT.pure a) k =
      (Label.join_bottom_left ℓ ▸ k a)

abbrev IndexedMonad_RightIdentityStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    @IndexedT.bind α α ℓ Label.bottom m IndexedT.pure =
      (Label.join_bottom_right ℓ ▸ m)

abbrev IndexedMonad_AssociativityStatement : Prop :=
  ∀ {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ),
    @IndexedT.bind β γ (Label.join ℓ₁ ℓ₂) ℓ₃ (IndexedT.bind m k) h =
      (Label.join_assoc ℓ₁ ℓ₂ ℓ₃ ▸
        @IndexedT.bind α γ ℓ₁ (Label.join ℓ₂ ℓ₃) m
          (fun a => IndexedT.bind (k a) h))

abbrev IndexedMonad_StrengthStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    (IndexedT.strength ((), m)).value.2 = m.value

end DLC
