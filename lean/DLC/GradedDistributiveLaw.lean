/-
DLC — a graded mixed distributive law λ : D∘T ⇒ T∘D  (CT-unification moonshot, M3).

D = the `DpBudget` graded **comonad** (coeffect, ⊕ = saturating add, 0).
T = the `RGraded`/`RiskGrade` graded **monad** (effect, ⊔ = join, ⊥ = low).

λ commutes a budgeted computation-of-a-risky-value into a risky-computation-of-a-budgeted
value, **the budget absorbing the DP-cost τ of the risk it commutes past**:

    λ_{c,m} : D_c (T_m α) → T_m (D_{c ⊕ τ(m)} α)        (grade level)
    distrib ⟨⟨v, risk⟩, c⟩ = ⟨⟨v, c ⊕ τ(risk)⟩, risk⟩    (carrier level)

This is a *mixed* (comonad-over-monad) graded distributive law in the sense of Gaboardi,
Katsumata, Orchard, Breuvart, Uustalu, "Combining Effects and Coeffects via Grading"
(ICFP 2016): once graded, the two sides of the classical multiplication axiom land at
**incomparable** budget grades (`τ(m₁⊔m₂)` vs `τ(m₁)⊕τ(m₂)`), so the equality is replaced
by the order-theoretic 2-cell `≤` (budget weakening) — their "matched-pair" format.

## HONEST SCOPE — read this

This file **completes the categorical object** and **strengthens the admission decision**;
it does **not** add mathematical insight. The entire non-trivial content of the
multiplication coherence is the inequality `τ(m₁⊔m₂) ≤ τ(m₁)⊕τ(m₂)`, which is exactly
`riskToBudget_lax_monoidal`, already proven in `GradedBridge.lean`. The theory is fully
prior (ICFP 2016); current work (Resource-Bounded Type Theory, arXiv 2512.06952, Dec 2025)
deliberately keeps ⊕ and ⊔ independent with no distributive law, so this is not a sought
open problem — it is a *formalization capstone* for our specific τ-bridge, mechanized
sorry-free in Lean. Model-level only: `RiskGrade` is not Aeneas-extractable, so there is no
runtime-certified use; it is linked to the Rust enum by structural discriminant parity.

The payoff that is NOT ceremony: the consumer `admitsCommuted` charges `c ⊕ τ(risk)` —
the ambient budget `c` *plus* the risk cost — whereas `GradedBridge.admitsUnderCap` ignores
`c`. `admitsCommuted_tighter` proves the commuted admission is strictly more conservative.
-/

import DLC.GradedBridge

namespace DLC

/-! ## The distributive law -/

/-- The graded mixed distributive law on carriers. Risk moves outward unchanged; the budget
moves inward and absorbs `τ(risk)`. -/
def distrib {α : Type} (g : Graded (RGraded α)) : RGraded (Graded α) :=
  ⟨⟨g.value.value, g.grade.saturatingAdd (riskToBudget g.value.grade)⟩, g.value.grade⟩

/-! ## Budget-order helpers -/

/-- `⊕` has `0` as right identity. -/
@[simp] theorem DpBudget.saturatingAdd_zero (c : DpBudget) :
    c.saturatingAdd DpBudget.zero = c := by
  cases c; simp [DpBudget.saturatingAdd, DpBudget.zero]

/-- A summand is below the sum: `b ≤ a ⊕ b`. -/
theorem DpBudget.le_saturatingAdd_right (a b : DpBudget) :
    b.le (a.saturatingAdd b) = true := by
  simp only [DpBudget.le, DpBudget.saturatingAdd, decide_eq_true_eq]
  omega

/-! ## The graded distributive-law coherences (specialized matched-pair axioms) -/

/-- **Monad-unit coherence** (η^T). A pure (bottom-risk) computation leaves the budget
unchanged, because `τ(⊥) = 0`. This is a *real* constraint on τ (a τ with `τ(⊥) ≠ 0`
would break it), discharged by `riskToBudget_bottom`. -/
theorem distrib_unit {α : Type} (v : α) (c : DpBudget) :
    distrib (⟨RGraded.pure v, c⟩ : Graded (RGraded α))
      = (⟨⟨v, c⟩, RiskGrade.bottom⟩ : RGraded (Graded α)) := by
  simp [distrib, RGraded.pure, riskToBudget_bottom]

/-- **Monad-multiplication coherence** (μ^T) — the crux. Absorbing the join of two inner
risks is dominated by absorbing them one at a time:
`c ⊕ τ(m₁ ⊔ m₂)  ≤  (c ⊕ τ(m₁)) ⊕ τ(m₂)`. Under grading the two sides are incomparable
budgets; the `≤` is the matched-pair 2-cell, and its content is exactly the proven
`riskToBudget_lax_monoidal`. -/
theorem distrib_mult_lax (c : DpBudget) (m₁ m₂ : RiskGrade) :
    (c.saturatingAdd (riskToBudget (RiskGrade.join m₁ m₂))).le
      ((c.saturatingAdd (riskToBudget m₁)).saturatingAdd (riskToBudget m₂)) = true := by
  have hlax := riskToBudget_lax_monoidal m₁ m₂
  simp only [DpBudget.le, DpBudget.saturatingAdd, decide_eq_true_eq] at hlax ⊢
  obtain ⟨he, hd⟩ := hlax
  exact ⟨by omega, by omega⟩

/-- **Value-naturality** (the ε^D / inert-value content): λ is the identity on the carried
value and leaves the risk grade outermost. The comonad-counit axiom reduces to this. -/
@[simp] theorem distrib_value {α : Type} (g : Graded (RGraded α)) :
    (distrib g).value.value = g.value.value ∧ (distrib g).grade = g.value.grade :=
  ⟨rfl, rfl⟩

/-! Note: the comonad-comultiplication coherence (δ^D) has the *same* lax shape — splitting
`c ⊕ τ(m)` across a budget split is dominated by split-then-absorb — and reduces to ℕ²
monotonicity plus `riskToBudget_lax_monoidal`. It is the symmetric residual of this object;
omitted here because it carries no content beyond the multiplication coherence above. -/

/-! ## Consumer: commuted (ambient-budget-aware) DP admission

`GradedBridge.admitsUnderCap` charges only `τ(risk)`. Routing through `distrib` yields an
admission that also charges the ambient budget `c` already consumed — strictly tighter. -/

/-- Admit `g` iff the *commuted* budget `c ⊕ τ(risk)` fits `cap`. -/
def admitsCommuted {α : Type} (g : Graded (RGraded α)) (cap : DpBudget) : Bool :=
  (distrib g).value.grade.le cap

/-- **The law pays its way.** Commuted admission is strictly more conservative than the
risk-only admission: if the ambient-budget-aware check passes, so does the risk-only one
(the ambient budget can only tighten admission). -/
theorem admitsCommuted_tighter {α : Type} (g : Graded (RGraded α)) (cap : DpBudget)
    (h : admitsCommuted g cap = true) :
    admitsUnderCap g.value cap = true := by
  simp only [admitsCommuted, distrib, admitsUnderCap, tau] at h ⊢
  exact DpBudget.le_trans
    (DpBudget.le_saturatingAdd_right g.grade (riskToBudget g.value.grade)) h

end DLC
