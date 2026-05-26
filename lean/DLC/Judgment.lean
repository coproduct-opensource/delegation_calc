/-
DLC — Typing judgments.

Four mutually recursive judgments (frozen in `spec/typing-rules.md`):
  Γ ⊢ M : φ            -- logical typing
  Γ ⊢ p says M : p says φ  -- affirmation typing (a special case)
  Γ ⊢ M ▷ M'           -- small-step reduction (DLC.Reduce)
  Γ ⊢_K M : φ          -- cryptographic typing (DLC.Correspondence)

The full inductive `Deriv` lands at M1.Q1.c with the first 10 rules.
-/

import DLC.Syntax
import DLC.Principal

namespace DLC

/-- A typing context: additive hypotheses (re-usable) and a linear multiset
(single-use). At M1.Q1.c the linear context is upgraded from `List` to
Mathlib `Multiset` so the substructural rules are clean. -/
structure Ctx where
  additive : List Prop'
  linear   : List Prop'
  deriving Repr

namespace Ctx

/-- The empty context. -/
def empty : Ctx := { additive := [], linear := [] }

end Ctx

/-- A keyring threads the cryptographic-typing judgment `⊢_K`. -/
structure KeyRing where
  entries : List KeyRecord
  deriving Repr

/-- The derivation predicate. Placeholder: M1.Q1.c populates this with the
first ten typing rules; the full ~40-rule inductive lands by end of Q4. -/
inductive Deriv : Ctx → Term → Prop' → Type where
  -- Stub. Will be inhabited at M1.Q1.c.

end DLC
