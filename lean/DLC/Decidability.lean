/-
T1 — Decidability of proof-checking.

The headline statement (proven at M1.Q2.d for the propositional fragment and
extended to the full calculus at M1.Q4.d):

  ∀ Γ M φ, Decidable (Nonempty (Deriv Γ M φ))

with the additional complexity bound

  time(decide_pure Γ M φ) ≤ c · |M| · log |Γ|

stated as a separate theorem against the Aeneas-extracted `decide_pure`.
-/

import DLC.Judgment

namespace DLC

/-- Placeholder. M1.Q2.d replaces with the actual decidability theorem. -/
theorem t1_decidability_stub : True := trivial

end DLC
