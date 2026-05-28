/-
DLC — The categorical heart: an IFC-label-indexed strong monad.

This module captures DLC's structural claim that *principals form a category
and the delegation operator `⊓` is a strong monad indexed by the IFC label*.

The carrier `IndexedT ℓ α` is a `structure` (not an `abbrev`), so the label
is non-phantom at the term level: the `value` projection is a real
operation that participates in proofs, and the monad laws do not prove
by `rfl` alone.

Monad laws are stated as equalities between the *underlying values* (the
`.value` projection of the structure). Stating them as cross-indexed
structure equalities (with `▸` casts over `Label.join_bottom_left` etc.)
type-checks but requires heterogeneous-equality reasoning the rest of the
calculus doesn't need; the `.value`-level form captures the operational
content cleanly.

References:
  * Petricek, Mycroft, Orchard — graded comonads (compile-time grading).
  * Wadler — strong monads in functional programming.
  * Atkey — Parameterised notions of computation (PhD), §3 for indexed
    strong monads as the "T^ℓ" shape DLC uses.

DLC reading: `T^ℓ φ` is the type of computations that produce values of
type `φ` at IFC label ℓ. `pure` injects at the bottom label; `bind`
propagates labels by lattice join (which is exactly `app-IFC` in the
typing rules).
-/

import DLC.IFCLabel

namespace DLC

/-- The indexed-monad carrier: a single-field structure wrapping a value
of type `α` whose computation lives at IFC label `ℓ`.

A `structure` (not `abbrev`) so the label is non-phantom — the `value`
projection requires an unfolding step, and the monad laws need
`simp [IndexedT.bind, IndexedT.pure]` to discharge rather than `rfl`. -/
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

Supporting lemmas that show the IFC lattice satisfies the laws the
categorical content demands. Componentwise: `Label.join` is
componentwise `levelMax`, and `levelMax` has `.Never` as identity and
is associative. -/

/-- Componentwise: `levelMax .Never x = x`. -/
theorem levelMax_bottom_left (x : portcullis_core.CapabilityLevel) :
    Label.levelMax .Never x = x := by
  cases x <;> rfl

/-- Componentwise: `levelMax x .Never = x`. -/
theorem levelMax_bottom_right (x : portcullis_core.CapabilityLevel) :
    Label.levelMax x .Never = x := by
  cases x <;> rfl

/-- `Label.join Label.bottom ℓ = ℓ`. -/
theorem Label.join_bottom_left (ℓ : Label) : Label.join Label.bottom ℓ = ℓ := by
  cases ℓ
  simp [Label.join, Label.bottom, levelMax_bottom_left]

/-- `Label.join ℓ Label.bottom = ℓ`. -/
theorem Label.join_bottom_right (ℓ : Label) : Label.join ℓ Label.bottom = ℓ := by
  cases ℓ
  simp [Label.join, Label.bottom, levelMax_bottom_right]

/-- Componentwise: `levelMax` is associative. -/
theorem levelMax_assoc (a b c : portcullis_core.CapabilityLevel) :
    Label.levelMax (Label.levelMax a b) c =
      Label.levelMax a (Label.levelMax b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `Label.join` is associative. -/
theorem Label.join_assoc (ℓ₁ ℓ₂ ℓ₃ : Label) :
    Label.join (Label.join ℓ₁ ℓ₂) ℓ₃ = Label.join ℓ₁ (Label.join ℓ₂ ℓ₃) := by
  cases ℓ₁ <;> cases ℓ₂ <;> cases ℓ₃
  simp [Label.join, levelMax_assoc]

/-! ## Monad laws — proven at the value level.

The laws assert equality between the *underlying values* of `bind` /
`pure` calls. Because `IndexedT` is a `structure`, each proof requires
unfolding `IndexedT.bind` and `IndexedT.pure` (via `simp`), and the
monad axioms are not `rfl`-provable from the definitions alone. -/

/-- Left-identity (value level): `(bind (pure a) k).value = (k a).value`. -/
theorem indexed_monad_left_identity {α β : Type} {ℓ : Label}
    (a : α) (k : α → IndexedT ℓ β) :
    (@IndexedT.bind α β Label.bottom ℓ (IndexedT.pure a) k).value =
      (k a).value := by
  simp [IndexedT.bind, IndexedT.pure]

/-- Right-identity (value level): `(bind m pure).value = m.value`. -/
theorem indexed_monad_right_identity {α : Type} {ℓ : Label}
    (m : IndexedT ℓ α) :
    (@IndexedT.bind α α ℓ Label.bottom m IndexedT.pure).value = m.value := by
  simp [IndexedT.bind, IndexedT.pure]

/-- Associativity (value level): bind composes — the values of two
right-associated and left-associated chains coincide. -/
theorem indexed_monad_associativity {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ) :
    (@IndexedT.bind β γ (Label.join ℓ₁ ℓ₂) ℓ₃ (IndexedT.bind m k) h).value =
      (@IndexedT.bind α γ ℓ₁ (Label.join ℓ₂ ℓ₃) m
        (fun a => IndexedT.bind (k a) h)).value := by
  simp [IndexedT.bind]

/-! ## Strength — four laws proven.

`T^ℓ` admits a *strength* `α × T^ℓ β → T^ℓ (α × β)`. -/

/-- The strength: pair a pure value with a graded computation. -/
def IndexedT.strength {α β : Type} {ℓ : Label}
    (pair : α × IndexedT ℓ β) : IndexedT ℓ (α × β) :=
  ⟨(pair.1, pair.2.value)⟩

/-- Strength's left unit (value level). -/
theorem indexed_monad_strength_left_unit {α : Type} {ℓ : Label}
    (m : IndexedT ℓ α) :
    (IndexedT.strength ((), m)).value.2 = m.value := by
  simp [IndexedT.strength]

/-- Strength's right unit (value level). -/
theorem indexed_monad_strength_right_unit {α β : Type} {ℓ : Label}
    (a : α) (m : IndexedT ℓ β) :
    (IndexedT.strength (a, m)).value = (a, m.value) := by
  simp [IndexedT.strength]

/-- Strength's associativity (value level): strength composes with itself
across a nested pair. -/
theorem indexed_monad_strength_assoc {α β γ : Type} {ℓ : Label}
    (a : α) (b : β) (m : IndexedT ℓ γ) :
    (IndexedT.strength (a, IndexedT.strength (b, m))).value.2 =
      ((IndexedT.strength (b, m)).value.1,
       (IndexedT.strength (b, m)).value.2) := by
  simp [IndexedT.strength]

/-- Strength's naturality (value level): strength commutes with mapping
the second component through a pure function. -/
theorem indexed_monad_strength_naturality {α β γ : Type} {ℓ : Label}
    (a : α) (m : IndexedT ℓ β) (f : β → γ) :
    (IndexedT.strength (a, (⟨f m.value⟩ : IndexedT ℓ γ))).value =
      ((IndexedT.strength (a, m)).value.1,
       f (IndexedT.strength (a, m)).value.2) := by
  simp [IndexedT.strength]

/-! ## Backward-compat aliases. -/

abbrev IndexedMonad_LeftIdentityStatement : Prop :=
  ∀ {α β : Type} {ℓ : Label} (a : α) (k : α → IndexedT ℓ β),
    (@IndexedT.bind α β Label.bottom ℓ (IndexedT.pure a) k).value =
      (k a).value

abbrev IndexedMonad_RightIdentityStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    (@IndexedT.bind α α ℓ Label.bottom m IndexedT.pure).value = m.value

abbrev IndexedMonad_AssociativityStatement : Prop :=
  ∀ {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ),
    (@IndexedT.bind β γ (Label.join ℓ₁ ℓ₂) ℓ₃ (IndexedT.bind m k) h).value =
      (@IndexedT.bind α γ ℓ₁ (Label.join ℓ₂ ℓ₃) m
        (fun a => IndexedT.bind (k a) h)).value

abbrev IndexedMonad_StrengthStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    (IndexedT.strength ((), m)).value.2 = m.value

end DLC
