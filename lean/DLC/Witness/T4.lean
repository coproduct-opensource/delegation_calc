/-
Non-vacuity witness for T4 (`t4_no_new_obligation`,
`DLC/ObligationSoundness.lean`).

Until the R0-R5 ladder (`spec/t4-obligation-design-2026-07.md`) this file
COULD NOT EXIST. `pendingObligations` was provably the constant `[]` --
`pendingObligations_eq_nil`, now deleted -- because no `Term` constructor
carried an `Obligation`. T4 was a real ~180-line induction over an empty
list: true, and empty.

Two obligations, mirroring what the 2026-07 audit demanded of T3:

1. POSITIVE INSTANCE -- a concrete term whose obligation list is NON-EMPTY,
   and a concrete reduction on which T4's conclusion says something. The
   ledger gates T4's status on exactly this (`scripts/ledger.sh` refuses
   `proven*` without a witness module that builds).
2. THE REDUCTION IS LOAD-BEARING -- discharge-beta genuinely REMOVES the
   obligation. Shown by exhibiting an obligation that is pending before the
   step and absent after it. A T4 that held because nothing ever changed
   would be the vacuity in a new costume.
-/

import DLC.ObligationSoundness

namespace DLC.Witness

open DLC

/-! ## 1. Obligations can be non-empty. -/

/-- A concrete obligation: principal-independent, so the witness does not
drag in key material. -/
abbrev Ow : Obligation := Obligation.top

/-- Obligation evidence. Its typing is checked by `Deriv.boxI`, not by
`pendingObligations`, so any closed term serves here. -/
abbrev Ev : Term := Term.now { epochMs := 0 }

/-- The payload: a proof carrying no obligations of its own, so the box's
own obligation is the ONLY one in the list and the arithmetic is visible. -/
abbrev Payload : Term := Term.var 0

/-- `box_Ow(Payload, Ev)` -- the introduction form the ladder added. -/
abbrev Boxed : Term := Term.boxed Ow Payload Ev

/-- POSITIVE: the obligation list is exactly `[Ow]`. Before R5 this was
`[]` for every term in the language. -/
example : pendingObligations Boxed = [Ow] := by
  simp [pendingObligations]

/-- …and therefore non-empty, which is the property the ledger's witness
requirement is about. -/
example : pendingObligations Boxed ≠ [] := by
  simp [pendingObligations]

/-! ## 2. The reduction is load-bearing.

`discharge-beta` destroys the box, so the obligation leaves the list. If
reduction never changed the obligation list, T4's non-introduction claim
would hold for an uninteresting reason. -/

/-- The redex: `discharge(box_Ow(Payload, Ev), Ev)`. -/
abbrev Redex : Term := Term.discharge Boxed Ev

/-- It steps, and to the payload -- discharge-beta fires. -/
example : step Redex = some Payload := by
  simp [step]

/-- BEFORE: the redex has `Ow` pending. -/
example : Ow ∈ pendingObligations Redex := by
  simp [pendingObligations]

/-- AFTER: the contractum does NOT. The step discharged it. -/
example : Ow ∉ pendingObligations Payload := by
  simp [pendingObligations]

/-- T4 applied to this concrete step. The theorem says the contractum
introduces no obligation absent from the redex; here the contractum has
none at all, and the redex had one. Non-introduction holds, and holds
non-trivially: the direction that could have failed is the one where a
step INVENTS an obligation, and this exhibits a step that instead
CONSUMES one. -/
example (o : Obligation) :
    o ∈ pendingObligations Payload → o ∈ pendingObligations Redex :=
  t4_no_new_obligation Redex Payload (by simp [step]) o

/-! ## 3. The multiset direction that is NOT yet proven.

Recorded so the witness does not overstate what T4 covers.
`t4_no_new_obligation` is the non-introduction inequality only. The full
accounting

  `obligations(M') = obligations(M) − discharged + introduced`

is not proven; this file exhibits one instance of the `discharged` side
(`Ow` leaves) but proves no general equation. T4's ledger status must stay
`proven_fragment` at most, and must name the fragment. -/

/-- The instance of the discharged side, stated concretely: this step
removes exactly `Ow` and adds nothing. -/
example :
    pendingObligations Redex = Ow :: pendingObligations Payload := by
  simp [pendingObligations]

end DLC.Witness
