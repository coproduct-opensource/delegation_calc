/-
Non-vacuity witness for the T3 first rung (two-run intro-fragment NI,
`DLC.NonInterferenceTwoRun`).

Two obligations, mirroring what the 2026-07 audit demanded of any
future T3 claim:

1. POSITIVE INSTANCE — a concrete intro-only derivation with a high
   hypothesis and an observable conclusion, on which the two-run
   theorem yields literal equality of the two runs.
2. TYPING IS LOAD-BEARING — the two-run CONCLUSION is falsifiable for
   a term that references the high hypothesis (which the typing +
   observability hypotheses rule out). The retired reflexivity "T3"
   held for ill-typed garbage; this one does not.
-/

import DLC.NonInterferenceTwoRun

namespace DLC.Witness

open DLC

/-- A label strictly above bottom: `read_files := Always`. -/
abbrev ℓHigh : Label :=
  { Label.bottom with read_files := .Always }

/-- The observer sits at bottom. -/
abbrev ℓLow : Label := Label.bottom

/-- `ℓHigh ⋠ ℓLow` — computable, so `rfl`. -/
theorem high_not_le : Label.le ℓHigh ℓLow = false := rfl

/-- A high hypothesis type: an atom lifted to `ℓHigh`. -/
abbrev ψHigh : Prop' := Prop'.at (Prop'.atom 7) ℓHigh

theorem ψHigh_not_observable : ¬ Observable ℓLow ψHigh := by
  intro h
  have h1 : Label.le ℓHigh ℓLow = true := h.1
  rw [high_not_le] at h1
  cases h1

/-- Context: slot 0 is HIGH, slot 1 is a low atom. -/
abbrev Γw : List Prop' := [ψHigh, Prop'.atom 0]

/-- The witness term: pairs the LOW hypothesis with a `now` — an
intro-only derivation whose conclusion is observable. -/
abbrev Mw : Term := Term.pair (Term.var 1) (Term.now { epochMs := 0 })

abbrev φw : Prop' := Prop'.and (Prop'.atom 0) Prop'.top

def dw : IntroDeriv Γw Mw φw :=
  .andI Γw (Prop'.atom 0) Prop'.top (Term.var 1) (Term.now { epochMs := 0 })
    (.varA Γw 1 (Prop'.atom 0) rfl)
    (.now Γw { epochMs := 0 })

theorem φw_observable : Observable ℓLow φw :=
  ⟨trivial, trivial⟩

/-- POSITIVE: the two runs of `Mw` under any two instantiations of the
high hypothesis are literally equal — instantiated at two visibly
different terms. -/
example :
    substAt Mw (Term.now { epochMs := 1 }) 0 =
    substAt Mw (Term.now { epochMs := 2 }) 0 :=
  t3_intro_two_run ℓLow dw φw_observable ψHigh_not_observable
    (Term.now { epochMs := 1 }) (Term.now { epochMs := 2 })

/-- LOAD-BEARING: for a term that DOES reference the high slot, the
two-run conclusion is FALSE — so the theorem's hypotheses are doing
real work (this is exactly what the retired reflexivity "T3" could
not say). -/
example :
    substAt (Term.var 0) (Term.now { epochMs := 1 }) 0 ≠
    substAt (Term.var 0) (Term.now { epochMs := 2 }) 0 := by
  intro h
  simp only [substAt, if_pos rfl, shift] at h
  injection h with h1
  injection h1 with h2
  exact absurd h2 (by decide)

end DLC.Witness
