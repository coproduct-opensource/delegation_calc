/-
T3 — Non-interference under delegation.

For any IFC label `ℓ_low`, a derivation of `φ @ ℓ_low` from a context whose
hypotheses live only at labels `≥ ℓ_low` cannot transport information from
strictly-higher labels into the conclusion. Generalizes Garg-Pfenning's
constructive-authorization-logic non-interference (CSF '06) to the IFC-
labeled setting.

Proof strategy (M1.Q4.c closure): a logical relation
`R[ℓ_low] : Prop' → Term → Term → Prop`
expressing observational equivalence at label `ℓ_low`. The fundamental
lemma — every well-typed term is related to itself by `R[ℓ_low]` — implies
the non-interference statement.

Load-bearing dependencies for the proof:
  * Subject reduction (M1.Q2.c).
  * Substitution lemma (M1.Q2.a).
  * Galois connections between IFC labels (nucleus's
    `GaloisConnectionProofs.lean`) — `app-IFC` and `declassify` invoke
    these directly.

Per CLAUDE.md, T3 is stated as a `def Statement : Prop`. The first commit
that closes the proof flips this to `theorem t3_non_interference : … := …`.
-/

import DLC.Judgment
import DLC.IFCLabel

namespace DLC

/-! ## The non-interference logical-relation predicate.

Stated abstractly so the closure work can choose the concrete encoding. -/

/-- A binary relation on terms parameterized by the low-label "observer" and
the proposition being projected. The standard logical-relations shape:

  R[ℓ_low](φ, M, M') ⟺
    M and M' produce indistinguishable outputs at any label ≤ ℓ_low.

The relation is defined by structural induction over `φ`; the cases for
`says`, `□_O`, `◇_τ`, and IFC-labeled propositions follow the standard
logical-relations recipe (Garg-Pfenning CSF '06, Tomé Cortiñas-Veltri '22).

For Q4 the relation is *typed* (not inhabited) — the body lands with the
proof closure. -/
def Indistinguishable (_ℓLow : Label) (_φ : Prop') (_M _N : Term) : Prop :=
  -- Body fills in at proof closure. Stated as `Prop`-valued for now so
  -- T3 type-checks.
  True

/-! ## T3 — statement only. -/

/-- T3 — Non-interference under delegation.

Given a context `Γ` whose linear and additive hypotheses all sit at labels
`≥ ℓ_low`, any well-typed term `M : φ` is indistinguishable from itself
under the logical relation at `ℓ_low`. Equivalently: nothing flows from
labels `> ℓ_low` into observations at `ℓ_low`.

The full statement includes a side condition on Γ (label well-formedness)
which lands with the proof — placeholder form here:

  ∀ ℓ_low Γ M φ,
    Deriv Γ M φ →
    ContextHasLabelAtLeast Γ ℓ_low →
    Indistinguishable ℓ_low φ M M

Proof: logical relations over `Deriv`, using the Galois connections imported
from nucleus's `GaloisConnectionProofs.lean`. -/
def T3_NonInterferenceStatement : Prop :=
  ∀ (ℓLow : Label) (Γ : Ctx) (M : Term) (φ : Prop'),
    -- placeholder shape — full form lands at proof closure
    ℓLow = ℓLow ∧ Γ = Γ ∧ M = M ∧ φ = φ

end DLC
