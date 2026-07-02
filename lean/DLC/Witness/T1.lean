/-
Non-vacuity witness for T1 (propositional-fragment decidability).

The ledger (scripts/ledger.sh) refuses to report T1 as
`proven_fragment` unless this file builds. It demonstrates that the
proven decidability content is non-degenerate:

* the decision procedure ACCEPTS a real well-typed term,
* the decision procedure REJECTS a real ill-typed term, and the
  completeness theorem turns that rejection into an underivability
  proof — i.e. the theorems distinguish inhabited from uninhabited
  judgments, which is exactly what a tautological placeholder cannot
  do.
-/

import DLC.Decidability

namespace DLC.Witness

/-- Positive: the identity at `atom 0` checks, at the expected type. -/
example :
    decideLean Ctx.empty (Term.lam (Prop'.atom 0) (Term.var 0)) =
      some (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) := rfl

/-- Positive: the judgment itself is inhabited (constructively). -/
example :
    PropDeriv [] (Term.lam (Prop'.atom 0) (Term.var 0))
      (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) :=
  PropDeriv.impI [] (Prop'.atom 0) (Prop'.atom 0) (Term.var 0)
    (PropDeriv.varA [Prop'.atom 0] 0 (Prop'.atom 0) rfl)

/-- Negative: an unbound variable does not check in the empty context. -/
example : decideLean Ctx.empty (Term.var 0) = none := rfl

/-- Negative, through the completeness theorem: the judgment for the
unbound variable is UNINHABITED. If a derivation existed, completeness
would force `decideLean` to return `some`, contradicting the `none`
above. This is the non-vacuity content: T1's theorems separate
derivable from underivable. -/
example : ¬ Nonempty (PropDeriv [] (Term.var 0) (Prop'.atom 0)) := by
  intro ⟨d⟩
  have h := t1_propositional_completeness [] (Term.var 0) (Prop'.atom 0) d
  have h0 : decideLean { additive := [], linear := [] } (Term.var 0) = none := rfl
  rw [h0] at h
  cases h

/-- Negative: a type MISMATCH is also rejected — the identity at
`atom 0` is not derivable at `atom 1 ⊃ atom 1`. -/
example :
    ¬ Nonempty (PropDeriv [] (Term.lam (Prop'.atom 0) (Term.var 0))
        (Prop'.imp (Prop'.atom 1) (Prop'.atom 1))) := by
  intro ⟨d⟩
  have h := t1_propositional_completeness [] _ _ d
  have h0 : decideLean { additive := [], linear := [] }
      (Term.lam (Prop'.atom 0) (Term.var 0)) =
      some (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) := rfl
  rw [h0] at h
  injection Option.some.inj h with h1 _
  injection h1 with h2
  exact absurd h2 (by decide)

end DLC.Witness
