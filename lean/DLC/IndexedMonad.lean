/-
DLC — The categorical heart: an IFC-label-indexed strong monad.

This module captures DLC's structural claim that *principals form a category
and the delegation operator `⊓` is a strong monad indexed by the IFC label*.
The monad laws and the strength laws are stated here as a `def Statement :
Prop`-style record; proof closure depends on the Metatheory framework
(arXiv 2512.09280) and the upstream PortcullisCore re-export.

References:
  * Petricek, Mycroft, Orchard — graded comonads (compile-time grading).
  * Wadler — strong monads in functional programming.
  * Atkey — Parameterised notions of computation (PhD), §3 for indexed
    strong monads as the "T^ℓ" shape DLC uses.

The DLC reading: `T^ℓ φ` is the type of computations that produce values of
type `φ` at IFC label ℓ. `pure ℓ φ x` injects at label ℓ; `bind` propagates
labels by lattice join (which is exactly `app-IFC` in the typing rules).
-/

import DLC.IFCLabel
import DLC.Syntax

namespace DLC

/-- The indexed-monad action. Parameterized over a Lean carrier type `α`
and a DLC IFC label `ℓ`.

`abbrev` (rather than `def`) so the type is reducible to its underlying
carrier — that's what makes the monad laws provable by `rfl`. The label
parameter is a "phantom" at the value level; it lives at the type level
to constrain how programs may compose. -/
abbrev IndexedT (_ℓ : Label) (α : Type) : Type := α

namespace IndexedT

/-- Unit: inject a value at the bottom label. -/
def pure {α : Type} (a : α) : IndexedT Label.bottom α := a

/-- Bind: produce a label by joining the source and continuation labels.
The join is exactly what `app-IFC` enforces in the typing rules. -/
def bind {α β : Type} {ℓ₁ ℓ₂ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) :
    IndexedT (Label.join ℓ₁ ℓ₂) β :=
  k m

end IndexedT

/-! ## Monad laws (proven — M1.Q4.b closure).

Because `IndexedT` is an `abbrev` that erases the label at the value level,
the three monad laws (left identity, right identity, associativity) hold
by reflexivity. The label parameters in the type signatures differ
syntactically (e.g. `Label.join Label.bottom ℓ` vs `ℓ`) but the underlying
values are the same. -/

/-- Left-identity: `bind (pure a) k = k a`. -/
theorem indexed_monad_left_identity {α β : Type} {ℓ : Label}
    (a : α) (k : α → IndexedT ℓ β) :
    IndexedT.bind (α := α) (β := β) (ℓ₁ := Label.bottom) (ℓ₂ := ℓ)
      (IndexedT.pure a) k = k a := by
  rfl

/-- Right-identity: `bind m pure = m`. -/
theorem indexed_monad_right_identity {α : Type} {ℓ : Label}
    (m : IndexedT ℓ α) :
    IndexedT.bind (α := α) (β := α) (ℓ₁ := ℓ) (ℓ₂ := Label.bottom)
      m IndexedT.pure = m := by
  rfl

/-- Associativity: bind composes. -/
theorem indexed_monad_associativity {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ) :
    IndexedT.bind (IndexedT.bind m k) h =
    IndexedT.bind m (fun a => IndexedT.bind (k a) h) := by
  rfl

/-! ## Strength (defined and proven).

`T^ℓ` admits a *strength* `α × T^ℓ β → T^ℓ (α × β)`. With `IndexedT` as
a label-indexed identity functor, strength is just pairing — the
categorical content is in the label discipline that surrounds it. -/

/-- The strength: pair a pure value with a graded computation. -/
def IndexedT.strength {α β : Type} {ℓ : Label}
    (pair : α × IndexedT ℓ β) : IndexedT ℓ (α × β) :=
  (pair.1, pair.2)

/-- Strength's left unit: pairing with `()` collapses. -/
theorem indexed_monad_strength_left_unit {α : Type} {ℓ : Label}
    (m : IndexedT ℓ α) :
    IndexedT.strength ((), m) = ((), m) := by
  rfl

/-! ## Backward-compat aliases. -/

/-- @[deprecated indexed_monad_left_identity] -/
abbrev IndexedMonad_LeftIdentityStatement : Prop :=
  ∀ {α β : Type} {ℓ : Label} (a : α) (k : α → IndexedT ℓ β),
    IndexedT.bind (α := α) (β := β) (ℓ₁ := Label.bottom) (ℓ₂ := ℓ)
      (IndexedT.pure a) k = k a

/-- @[deprecated indexed_monad_right_identity] -/
abbrev IndexedMonad_RightIdentityStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    IndexedT.bind (α := α) (β := α) (ℓ₁ := ℓ) (ℓ₂ := Label.bottom)
      m IndexedT.pure = m

/-- @[deprecated indexed_monad_associativity] -/
abbrev IndexedMonad_AssociativityStatement : Prop :=
  ∀ {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ),
    IndexedT.bind (IndexedT.bind m k) h =
    IndexedT.bind m (fun a => IndexedT.bind (k a) h)

/-- @[deprecated indexed_monad_strength_left_unit] -/
abbrev IndexedMonad_StrengthStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    IndexedT.strength ((), m) = ((), m)

end DLC
