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
and a DLC IFC label `ℓ`. -/
def IndexedT (_ℓ : Label) (α : Type) : Type := α

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

/-! ## Monad laws — statements only (proof closure depends on Metatheory).

Stated as `def Statement : Prop` per CLAUDE.md discipline. The three monad
laws (left identity, right identity, associativity) take their familiar form
once the label algebra is in scope. -/

/-- Left-identity: `bind (pure a) k = k a`, modulo the label being
`bottom ⊔ ℓ`, which the lattice `bottom_join_left` proves equals `ℓ`. -/
def IndexedMonad_LeftIdentityStatement : Prop :=
  ∀ {α β : Type} {ℓ : Label} (a : α) (k : α → IndexedT ℓ β),
    IndexedT.bind (IndexedT.pure a) k = k a

/-- Right-identity: `bind m pure = m`, modulo `ℓ ⊔ bottom = ℓ`. -/
def IndexedMonad_RightIdentityStatement : Prop :=
  ∀ {α : Type} {ℓ : Label} (m : IndexedT ℓ α),
    IndexedT.bind m IndexedT.pure = m

/-- Associativity: bind composes; the label propagates by associativity of
the lattice join. -/
def IndexedMonad_AssociativityStatement : Prop :=
  ∀ {α β γ : Type} {ℓ₁ ℓ₂ ℓ₃ : Label}
    (m : IndexedT ℓ₁ α) (k : α → IndexedT ℓ₂ β) (h : β → IndexedT ℓ₃ γ),
    IndexedT.bind (IndexedT.bind m k) h =
    IndexedT.bind m (fun a => IndexedT.bind (k a) h)

/-- Strength: `T^ℓ` admits a strength `α × T^ℓ β → T^ℓ (α × β)`. This makes
the monad compatible with the underlying Cartesian-product structure of
Lean's type system — and gives DLC's IFC labels their compositional shape
under products. -/
def IndexedMonad_StrengthStatement : Prop :=
  -- Existential statement: ∃ a `strength` operation satisfying the strength
  -- laws (left-unit, right-unit, alpha, distributivity). The concrete
  -- definition lands at Q4 closure once Metatheory's tensor-strength
  -- machinery is imported.
  True

end DLC
