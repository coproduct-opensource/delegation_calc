/-
Multi-step reduction metatheory — T3 rung 2
(`spec/t3-two-run-design-2026-07.md`).

`Reduce.step : Term → Option Term` is a FUNCTION: at most one redex
fires per term, so the reduction system is deterministic by
construction. That gives us confluence-strength results without a
parallel-reduction diamond:

* `Steps` — reflexive-transitive closure of `step`.
* `steps_semiconfluent` — two reduction paths from one term are
  totally ordered: one endpoint reaches the other.
* `Joinable` — ∃ common reduct; reflexive, symmetric, and (the
  payoff, via semi-confluence) TRANSITIVE. Joinability is therefore
  an equivalence on terms, fit to serve as the atom-level relation of
  the redesigned two-run logical relation (rung 3).

This is the first metatheory over `Reduce` in the development; the
ledger's T3 entry tracks it as rung 2 of the ladder.
-/

import DLC.Reduce

namespace DLC

/-! ## Multi-step reduction -/

/-- Reflexive-transitive closure of `step`. -/
inductive Steps : Term → Term → Prop where
  | refl (M : Term) : Steps M M
  | head {M N P : Term} (h : step M = some N) (tail : Steps N P) :
      Steps M P

namespace Steps

/-- One step is a multi-step. -/
theorem single {M N : Term} (h : step M = some N) : Steps M N :=
  .head h (.refl N)

/-- Transitivity — path concatenation. -/
theorem trans {M N P : Term} (h₁ : Steps M N) (h₂ : Steps N P) :
    Steps M P := by
  induction h₁ with
  | refl _ => exact h₂
  | head h _ ih => exact .head h (ih h₂)

end Steps

/-! ## Determinism and semi-confluence -/

/-- `step` is a function, so single-step reduction is deterministic. -/
theorem step_deterministic {M N₁ N₂ : Term}
    (h₁ : step M = some N₁) (h₂ : step M = some N₂) : N₁ = N₂ := by
  rw [h₁] at h₂
  exact Option.some.inj h₂

/-- Semi-confluence for a deterministic system: two reduction paths
from the same term are totally ordered — one endpoint reduces to the
other. Induction on the first path; at each fork both paths must take
the SAME step. -/
theorem steps_semiconfluent {M N₁ N₂ : Term}
    (h₁ : Steps M N₁) (h₂ : Steps M N₂) :
    Steps N₁ N₂ ∨ Steps N₂ N₁ := by
  induction h₁ generalizing N₂ with
  | refl _ => exact .inl h₂
  | head hstep tail ih =>
      cases h₂ with
      | refl _ => exact .inr (.head hstep tail)
      | head hstep' tail' =>
          have := step_deterministic hstep hstep'
          subst this
          exact ih tail'

/-! ## Joinability -/

/-- Two terms are joinable when they share a common reduct. This is
the equality-up-to-computation the rung-3 logical relation uses at
atomic propositions. -/
def Joinable (M N : Term) : Prop :=
  ∃ V, Steps M V ∧ Steps N V

namespace Joinable

theorem refl (M : Term) : Joinable M M :=
  ⟨M, .refl M, .refl M⟩

theorem symm {M N : Term} (h : Joinable M N) : Joinable N M :=
  let ⟨V, hM, hN⟩ := h
  ⟨V, hN, hM⟩

theorem of_steps {M N : Term} (h : Steps M N) : Joinable M N :=
  ⟨N, h, .refl N⟩

/-- Transitivity — THE consequence of determinism. Given common
reducts `V₁` (for `M, N`) and `V₂` (for `N, P`), semi-confluence on
`N`'s two paths orders `V₁` and `V₂`; either way a common reduct for
`M` and `P` exists. -/
theorem trans {M N P : Term}
    (h₁ : Joinable M N) (h₂ : Joinable N P) : Joinable M P := by
  obtain ⟨V₁, hM, hN₁⟩ := h₁
  obtain ⟨V₂, hN₂, hP⟩ := h₂
  rcases steps_semiconfluent hN₁ hN₂ with h | h
  · exact ⟨V₂, hM.trans h, hP⟩
  · exact ⟨V₁, hM, hP.trans h⟩

end Joinable

/-! ## Sanity checks -/

namespace ReduceMetaChecks

/-- β-reduction is a `Steps`. -/
example (φ : Prop') (arg : Term) :
    Steps (Term.app (Term.lam φ (Term.var 0)) arg) (subst (Term.var 0) arg) :=
  Steps.single rfl

/-- Projections of the same pair are joinable with their components:
`fst ⟨a,b⟩` joins `a`. -/
example (a b : Term) : Joinable (Term.fst (Term.pair a b)) a :=
  Joinable.of_steps (Steps.single rfl)

/-- Joinability really is transitive across a shared middle term:
`fst ⟨a,b⟩ ~ a` and `a ~ a` compose. -/
example (a b : Term) : Joinable (Term.fst (Term.pair a b)) a :=
  Joinable.trans
    (Joinable.of_steps (Steps.single rfl))
    (Joinable.refl a)

end ReduceMetaChecks

end DLC
