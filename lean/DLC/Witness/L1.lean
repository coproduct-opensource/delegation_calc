/-
Non-vacuity witness for L1 (`linear_lever_L1`, `DLC.CtxWellFormed`).

`CtxWellFormed_all` proves the disambiguation invariant for EVERY context,
which invites the obvious objection: an invariant that holds universally may
hold because it says nothing. Two obligations answer it, mirroring what the
2026-07 audit demanded of T3:

1. BOTH BRANCHES REACHABLE — `CtxWellFormed`'s conclusion is a genuine
   disjunction (additive hit / linear singleton at `additive.length`), and
   each disjunct is inhabited by a concrete context. An invariant whose
   every instance took the same branch would be the weaker statement it is
   sometimes mistaken for.
2. THE DOMAIN RESTRICTION IS LOAD-BEARING — `ctxLookup_eq_checker_additive`
   and `ctxLookup_eq_checker_empty_additive` carry hypotheses, and those
   hypotheses cannot be dropped: `ctxLookup_ne_checker_witness` exhibits a
   concrete `Γ, i` on which `ctxLookup` and the shipped checker DISAGREE.
   The agreement results are therefore restricted, not universal — which is
   precisely why the ledger status is `proven_fragment` and not `proven`.
-/

import DLC.CtxWellFormed

namespace DLC.Witness

open DLC

/-! ## 1. Both disjuncts of the invariant are inhabited. -/

/-- Additive-hit context: one additive slot, no linear slot. -/
abbrev ΓA : Ctx := { additive := [Prop'.atom 0], linear := [] }

/-- Linear-hit context: one additive slot, plus the linear singleton that
disambiguation places at index `additive.length = 1`. -/
abbrev ΓL : Ctx := { additive := [Prop'.atom 0], linear := [Prop'.atom 1] }

/-- LEFT disjunct is reachable: index 0 of `ΓA` is an in-range additive hit. -/
example :
    (0 < ΓA.additive.length ∧ ΓA.additive[0]? = some (Prop'.atom 0)) ∨
    (0 = ΓA.additive.length ∧ ΓA.linear = [Prop'.atom 0]) :=
  CtxWellFormed_all ΓA 0 (Prop'.atom 0) rfl

/-- …and it really is the LEFT one — the right disjunct is false here,
since `0 ≠ 1`. -/
example : ¬ (0 = ΓA.additive.length ∧ ΓA.linear = [Prop'.atom 0]) := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-- RIGHT disjunct is reachable: in `ΓL` the linear singleton sits at index
`additive.length = 1`, which no additive slot occupies. -/
example :
    (1 < ΓL.additive.length ∧ ΓL.additive[1]? = some (Prop'.atom 1)) ∨
    (1 = ΓL.additive.length ∧ ΓL.linear = [Prop'.atom 1]) :=
  CtxWellFormed_all ΓL 1 (Prop'.atom 1)
    (ctxLookup_varL [Prop'.atom 0] (Prop'.atom 1))

/-- …and it really is the RIGHT one — the left disjunct is false here,
since index 1 is out of range for a one-element additive context. -/
example : ¬ (1 < ΓL.additive.length ∧ ΓL.additive[1]? = some (Prop'.atom 1)) := by
  rintro ⟨h, -⟩
  exact absurd h (by decide)

/-! ## 2. The checker-agreement hypotheses are load-bearing.

`ctxLookup_eq_checker_additive` needs its `Γ.additive[i]? = some φ`
premise and `ctxLookup_eq_checker_empty_additive` needs `Γ.additive = []`.
Neither can be weakened to an unconditional equality, because the two
functions genuinely diverge — `decide.rs` consults the linear context only
at index 0, where `additive[0]` shadows it. -/

/-- The divergence, restated here as the witness obligation: agreement with
the shipped checker is NOT universal. -/
example : ∃ (Γ : Ctx) (i : Nat), ctxLookup Γ i ≠ decideLean Γ (Term.var i) :=
  ctxLookup_ne_checker_witness

/-- The same fact at the concrete context, so the counterexample is visible
rather than existentially hidden: `ctxLookup` resolves the linear var that
the checker refuses. -/
example : ctxLookup ΓL 1 = some (Prop'.atom 1) :=
  ctxLookup_varL [Prop'.atom 0] (Prop'.atom 1)

example : decideLean ΓL (Term.var 1) = none := by
  unfold decideLean; rfl

/-- POSITIVE, on the supported domain: where the premise DOES hold, the
agreement theorem delivers a real equality. -/
example : ctxLookup ΓA 0 = decideLean ΓA (Term.var 0) :=
  ctxLookup_eq_checker_additive ΓA 0 (Prop'.atom 0) rfl

end DLC.Witness
