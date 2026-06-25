/-
DLC — M2: the graded bridge, generalized.

`GradedBridge.lean` / `GradedDistributiveLaw.lean` proved the τ-bridge and its distributive
law for the *specific* `riskToBudget`. This file abstracts the construction: **any** monotone
lax monoid homomorphism into the `DpBudget` coeffect monoid induces the *same* graded
distributive-law coherences. The concrete risk↔DP bridge is then just one instance.

Nothing here is risk-specific — it isolates exactly the structure the graded distributive law
needs (a lax monoid hom into `(DpBudget, ⊕, 0)`), so any future effect grade (cost, taint,
sensitivity, …) that maps laxly into a DP/resource budget reuses the coherences for free.

Reuses the proven lemmas in `GradedDistributiveLaw.lean` (`DpBudget.saturatingAdd_zero`).
-/

import DLC.GradedDistributiveLaw

namespace DLC

/-- A lax monoid homomorphism from a grade monoid `(G, combine, unit)` into the DP-budget
coeffect monoid `(DpBudget, ⊕ = saturatingAdd, 0)`: it preserves the unit and is *lax* over
the operation (`f (a ∙ b) ≤ f a ⊕ f b`). This is the entire interface the graded
distributive law depends on. -/
structure LaxBudgetHom (G : Type) where
  /-- The grade monoid's operation (the effect-monad grade composition). -/
  combine : G → G → G
  /-- The grade monoid's unit. -/
  unit : G
  /-- The lax homomorphism into the budget monoid. -/
  f : G → DpBudget
  /-- Unit preservation (on the nose): a unit grade costs nothing. -/
  f_unit : f unit = DpBudget.zero
  /-- Laxity over the operation: the matched-pair 2-cell. -/
  f_lax : ∀ a b, (f (combine a b)).le ((f a).saturatingAdd (f b)) = true

namespace LaxBudgetHom

variable {G : Type} (H : LaxBudgetHom G)

/-- Generic monad-unit coherence: absorbing a unit grade leaves the budget unchanged. -/
theorem unit_absorb (c : DpBudget) : c.saturatingAdd (H.f H.unit) = c := by
  rw [H.f_unit, DpBudget.saturatingAdd_zero]

/-- Generic monad-multiplication coherence (the matched-pair 2-cell) for ANY lax hom:
`c ⊕ f(a ∙ b)  ≤  (c ⊕ f a) ⊕ f b`. Same proof as the concrete `distrib_mult_lax`, now
parametric in `H`. -/
theorem mult_lax (c : DpBudget) (a b : G) :
    (c.saturatingAdd (H.f (H.combine a b))).le
      ((c.saturatingAdd (H.f a)).saturatingAdd (H.f b)) = true := by
  have hlax := H.f_lax a b
  simp only [DpBudget.le, DpBudget.saturatingAdd, decide_eq_true_eq] at hlax ⊢
  obtain ⟨he, hd⟩ := hlax
  exact ⟨by omega, by omega⟩

end LaxBudgetHom

/-- The concrete risk↔DP bridge is one instance of the generic construction: `RiskGrade`'s
join-monoid mapped into `DpBudget` by `riskToBudget`, with the M1-proven laws. -/
def riskBudgetHom : LaxBudgetHom RiskGrade where
  combine := RiskGrade.join
  unit := RiskGrade.bottom
  f := riskToBudget
  f_unit := riskToBudget_bottom
  f_lax := riskToBudget_lax_monoidal

/-- Sanity: the generic multiplication coherence, instantiated at `riskBudgetHom`, recovers
the concrete `distrib_mult_lax` statement — confirming the abstraction is faithful. -/
theorem riskBudgetHom_recovers_mult (c : DpBudget) (m₁ m₂ : RiskGrade) :
    (c.saturatingAdd (riskToBudget (RiskGrade.join m₁ m₂))).le
      ((c.saturatingAdd (riskToBudget m₁)).saturatingAdd (riskToBudget m₂)) = true :=
  riskBudgetHom.mult_lax c m₁ m₂

end DLC
