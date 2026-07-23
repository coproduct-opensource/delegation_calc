import DLCD.Rsm
import DLC.Graded

/-! # DLC-D Phase R1, stage E, increment E1 — `FaultGrade` graded comonad + `BudgetedGuarantee`

The **type-level failure-budget contract**. This module turns the DLC-D failure
model (`DLCD.FailureBudget`) from a *runtime `Prop` contract* — a
`withinContract = true` hypothesis the liveness guarantees carry — into a genuine
**graded-comonad-indexed guarantee**, so that "crossing the fault budget voids the
guarantee" is expressed as an *uninhabited type at an over-budget grade*, not
merely a `Prop` you fail to supply.

Per the approved design (`spec/r1-stageE-failurebudget-grade-design.md`, option
**c'**), this is a **graded comonad OVER THE GUARANTEE** (`Graded⟨FaultGrade⟩`),
NOT a `Prop'`/`CDeriv` term modality (options a/b, rejected as vacuous +
maximal-cost) and NOT a CARVe resource dimension. The calculus is untouched:
**no** `Prop'`/`CDeriv` constructor, **no** redex, **no** `LRel` clause, so
SR/NI/progress and the 49 axiom snapshots are undisturbed. E1 is PURELY ADDITIVE.

## What E1 delivers
- **`FaultGrade := Nat`** — the distilled 1-D consumable grade (`zero`,
  `saturatingAdd`, preorder `≤`), with the grade laws (identity, associativity,
  `+`-monotonicity). The associativity law is *derived from* `Graded.lean`'s
  `DLC.dp_budget_saturating_add_assoc` via the monoid embedding
  `FaultGrade.toDpBudget` (the δ=0 projection of `Graded⟨DpBudget⟩`), so the
  reuse is load-bearing, not prose (design §2, route 2 with route-1 witness).
- **`BudgetedGuarantee f b G : Prop`** — the guarantee delivered *at a grade*
  `b` under the tolerated bound `f`, with a threshold-gated counit `extract`.
  Its `charged : b ≤ f` field is the counit's availability side; at the
  over-budget grade `f ⊕ 1` that field is uninhabitable, so the whole type is
  **empty for every payload `G`** — the type-level voiding
  (`budgeted_guarantee_voids_over_budget`).
- A **bridge** to the runtime contract: `FailureBudget.toFaultGrade` (the
  consumable grade) and `FailureBudget.threshold` (the mislabeled `.le` guard
  clarified), with `withinContract ↔ threshold ∧ fairDelivery`. The existing
  `FailureBudget` is NOT modified — the bridge is additive.
- **Anti-vacuity witnesses** (the teeth): an in-budget `BudgetedGuarantee 1 0 …`
  on the real `RsmAntiVacuity` run whose `extract` FIRES and yields the genuinely
  *changed* converged store; and a concrete over-budget refutation
  `¬ BudgetedGuarantee 0 1 …` proving the void is real (not vacuously-true).

## Prior art (Mandate 0 — web-searched 2026-07-23, reused from the design doc)
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, *Combining Effects and
  Coeffects via Grading* (ICFP 2016): coeffects = graded monoidal **comonads**;
  a resource demand is a grade in a pre-ordered semiring — the model
  `Graded.lean`'s `DpBudget` already instantiates.
  https://kar.kent.ac.uk/57480/1/bieffects.pdf
- Orchard, Liepelt, Eades III, *Quantitative Program Reasoning with Graded Modal
  Types* (Granule, ICFP 2019): a graded modality `□_r A` over a resource algebra;
  the canonical "resource with a bounded usage grade" system.
  https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018): the
  grade **preorder is distinct from any threshold check** — the separation this
  module makes between `FaultGrade.le` (grade order) and `threshold`
  (`consumed ≤ maxFaults`). https://bentnib.org/quantitative-type-theory.pdf
- Mannucci, Thuro, *Resource-Bounded Type Theory* (arXiv 2512.06952, 2025): a
  graded *feasibility* modality with a **counit** — "extract the value once
  within budget" — the exact shape of `BudgetedGuarantee.extract`.
  https://arxiv.org/abs/2512.06952
-/

namespace DLCD

open DLC

/-! ## 1. The distilled 1-D fault grade.

`FaultGrade` is the grade carrier read off `FailureBudget.consumed` (§2 of the
design: `maxFaults`/`fairDelivery` are NOT grade data — the threshold and the
qualitative fairness flag are kept separate). As unbounded `Nat` the `saturating_`
qualifier is a no-op (as in `Graded.lean`'s `DpBudget`), but the name is retained
to match the graded-comonad template. -/

/-- The consumable crash-fault grade: the number of crash faults charged against
the contract. The 1-D projection of `DpBudget`'s `(ε, δ)`. -/
abbrev FaultGrade : Type := Nat

namespace FaultGrade

/-- The zero grade: no faults charged. -/
def zero : FaultGrade := 0

/-- Charge additional faults — the graded-comonad `+` (sequential composition of
grades). `Nat` is unbounded so this is `Nat.add`; the name matches `DpBudget`. -/
def saturatingAdd (a b : FaultGrade) : FaultGrade := a + b

/-- The grade PREORDER (Atkey LICS'18: distinct from the threshold guard). -/
def le (a b : FaultGrade) : Bool := decide (a ≤ b)

/-- Embed the 1-D fault grade into the 2-D DP budget as the δ=0 projection.
`toDpBudget` is a monoid homomorphism (`toDpBudget_zero`, `toDpBudget_add`),
which makes the reuse of `Graded.lean` concrete: `FaultGrade`'s grade laws are
the ε-component of `DpBudget`'s already-discharged laws (design §2, route 1). -/
def toDpBudget (g : FaultGrade) : DLC.DpBudget := ⟨g, 0⟩

theorem toDpBudget_zero : toDpBudget zero = DLC.DpBudget.zero := rfl

theorem toDpBudget_add (a b : FaultGrade) :
    toDpBudget (saturatingAdd a b)
      = (toDpBudget a).saturatingAdd (toDpBudget b) := by
  simp [toDpBudget, saturatingAdd, DLC.DpBudget.saturatingAdd]

end FaultGrade

/-! ### The grade laws (identity, associativity, monotonicity).

Route 2 of design §2 (a 1-D restatement, the *same* `simp [saturatingAdd, …]`
scripts as `Graded.lean`), except associativity is *derived* from
`DLC.dp_budget_saturating_add_assoc` through the `toDpBudget` embedding, so the
`Graded⟨DpBudget⟩` reuse is load-bearing rather than prose. -/

/-- Identity law: `zero` is a right unit for `saturatingAdd` (mirrors
`DLC.graded_identity_law`'s grade side). -/
theorem faultgrade_identity_law (a : FaultGrade) :
    FaultGrade.saturatingAdd a FaultGrade.zero = a := by
  simp [FaultGrade.saturatingAdd, FaultGrade.zero]

/-- Associativity of grade composition — **derived from** `Graded.lean`'s
`DLC.dp_budget_saturating_add_assoc` (the ε-component, via the `toDpBudget`
monoid hom). This is the reuse the design names in §2. -/
theorem faultgrade_saturating_add_assoc (a b c : FaultGrade) :
    FaultGrade.saturatingAdd (FaultGrade.saturatingAdd a b) c
      = FaultGrade.saturatingAdd a (FaultGrade.saturatingAdd b c) := by
  have h := DLC.dp_budget_saturating_add_assoc
    (FaultGrade.toDpBudget a) (FaultGrade.toDpBudget b) (FaultGrade.toDpBudget c)
  have he := congrArg DLC.DpBudget.epsilonMicros h
  simpa [FaultGrade.toDpBudget, FaultGrade.saturatingAdd,
         DLC.DpBudget.saturatingAdd] using he

/-- The `+` is monotone in the grade preorder (the semiring's monotone-`+`
requirement — Gaboardi ICFP'16). -/
theorem faultgrade_add_le_monotone {a₁ a₂ b₁ b₂ : FaultGrade}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    FaultGrade.saturatingAdd a₁ b₁ ≤ FaultGrade.saturatingAdd a₂ b₂ :=
  Nat.add_le_add ha hb

/-- The grade preorder is reflexive (it is `Nat.le`). -/
theorem faultgrade_le_refl (a : FaultGrade) : a ≤ a := Nat.le_refl a

/-- …and transitive. -/
theorem faultgrade_le_trans {a b c : FaultGrade} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    a ≤ c := Nat.le_trans h₁ h₂

/-! ## 2. `BudgetedGuarantee` — the graded-comonad-indexed guarantee.

`BudgetedGuarantee f b G` delivers the raw guarantee `G` *at grade `b`* under the
tolerated fault bound `f`. The `charged : b ≤ f` field is the graded counit's
availability side (RBTT / Granule): the guarantee is extractable ONLY within
budget. Off-budget (`b = f ⊕ 1`) the field `f + 1 ≤ f` is uninhabitable, so the
whole type is empty — the type-level voiding. A `Prop` (design ruling Q5): the
liveness payload `G` is itself a `Prop`, and the `charged`-empty voiding is a
clean `Prop` refutation. -/

/-- The failure-budget-graded guarantee. `f = maxFaults` is the tolerated bound;
`b` is the fault grade charged by the delivery schedule; `G` is the raw liveness
conclusion. -/
structure BudgetedGuarantee (f b : FaultGrade) (G : Prop) : Prop where
  /-- The counit's availability side: the guarantee is delivered ONLY within
  budget. At an over-budget grade this field is uninhabitable — that is the
  type-level void. -/
  charged : b ≤ f
  /-- The delivered guarantee. -/
  guarantee : G

namespace BudgetedGuarantee

/-- **The graded counit.** Within budget (guaranteed by the `charged` field the
value already carries) extract the raw guarantee `G`. This is the
`extract`/counit of the graded comonad — total on the in-budget index, and
*untypable* off it because no value of the over-budget type exists. -/
theorem extract {f b : FaultGrade} {G : Prop} (g : BudgetedGuarantee f b G) : G :=
  g.guarantee

/-- The counit's availability witness: a delivered budgeted guarantee proves the
schedule stayed within budget. -/
theorem withinBudget {f b : FaultGrade} {G : Prop}
    (g : BudgetedGuarantee f b G) : b ≤ f :=
  g.charged

/-- Deliver a guarantee at the **zero grade** (no faults charged). The counit is
trivially available (`0 ≤ f`). Mirrors `Graded.pure`. -/
theorem deliver {f : FaultGrade} {G : Prop} (hG : G) :
    BudgetedGuarantee f FaultGrade.zero G :=
  ⟨Nat.zero_le f, hG⟩

/-- **Thread a further fault-round onto the grade** (the graded-comonad
`consume`, sequencing via `saturatingAdd`). The guarantee is preserved and the
grade advances; the counit stays available exactly while the *new* grade is still
within budget (`hle`). Mirrors `Graded.consume`. -/
theorem consume {f b : FaultGrade} {G : Prop}
    (g : BudgetedGuarantee f b G) (extra : FaultGrade)
    (hle : FaultGrade.saturatingAdd b extra ≤ f) :
    BudgetedGuarantee f (FaultGrade.saturatingAdd b extra) G :=
  ⟨hle, g.guarantee⟩

end BudgetedGuarantee

/-- **The over-budget void — a `Nat` fact.** One fault past the bound cannot be
within budget: `¬ (f ⊕ 1 ≤ f)`. -/
theorem over_budget_empty (f : FaultGrade) :
    ¬ (FaultGrade.saturatingAdd f 1 ≤ f) :=
  -- `saturatingAdd f 1` is defeq `Nat.succ f`, so this is `Nat.not_succ_le_self`.
  Nat.not_succ_le_self f

/-- **THE TYPE-LEVEL FAILURE-BUDGET CONTRACT (headline).** At the over-budget
grade `f ⊕ 1`, the guarantee type is GENUINELY UNINHABITED — for EVERY payload
`G`, including a provable one — because its `charged` field `f + 1 ≤ f` is empty.
Crossing the fault budget makes the guarantee *type* void, not merely a `Prop`
you fail to supply; this is the graded counit's unavailability off-budget. The
in-budget inhabitation (`FaultGradeAntiVacuity.budgeted_converge`) shows the void
is a genuine boundary, not `BudgetedGuarantee` being empty everywhere. -/
theorem budgeted_guarantee_voids_over_budget {f : FaultGrade} {G : Prop} :
    ¬ BudgetedGuarantee f (FaultGrade.saturatingAdd f 1) G :=
  fun g => over_budget_empty f g.charged

/-! ## 3. Bridge to the runtime `FailureBudget` contract (additive).

`FailureBudget` (in `DLCD.Rsm`) is NOT modified — these are additive appendages
in the same namespace. `FailureBudget.le` is mislabeled: it computes the
THRESHOLD guard `consumed ≤ maxFaults`, not the grade preorder. The bridge
clarifies the two concerns the grade literature (Atkey LICS'18) keeps apart. -/

namespace FailureBudget

/-- Distil the consumable GRADE out of the runtime contract: the crash faults
charged so far. -/
def toFaultGrade (fb : FailureBudget) : FaultGrade := fb.consumed

/-- The THRESHOLD guard as a `Prop` (the counit-availability condition): the
charged grade has not exceeded the tolerated bound. This is what the mislabeled
`FailureBudget.le` actually computes. -/
def threshold (fb : FailureBudget) : Prop := fb.consumed ≤ fb.maxFaults

/-- `threshold` is exactly the (mislabeled) boolean `le`, decoded. -/
theorem threshold_iff_le (fb : FailureBudget) :
    fb.threshold ↔ fb.le = true := by
  simp [threshold, FailureBudget.le]

/-- The threshold guard, restated on the distilled grade: `toFaultGrade ≤
maxFaults`. Ties the grade to the counit gate. -/
theorem threshold_eq_grade_le (fb : FailureBudget) :
    fb.threshold ↔ fb.toFaultGrade ≤ fb.maxFaults := Iff.rfl

/-- The enforced runtime predicate decomposes into the **threshold guard** and
the **fair-delivery** assumption — the two concerns the grade reformulation keeps
separate (the threshold gates the counit; fairness stays a qualitative premise). -/
theorem withinContract_iff (fb : FailureBudget) :
    fb.withinContract = true ↔ fb.threshold ∧ fb.fairDelivery = true := by
  simp only [FailureBudget.withinContract, FailureBudget.le, threshold,
             Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Runtime contract feeds the graded guarantee.** A within-contract budget
supplies the counit's availability side (`toFaultGrade ≤ maxFaults`), so any
proof of the payload `G` may be delivered as a `BudgetedGuarantee maxFaults
(toFaultGrade) G`. This is where the old `withinContract = true` hypothesis
re-enters as the graded guarantee's `charged` field. -/
theorem budgetedGuarantee_of_withinContract {fb : FailureBudget} {G : Prop}
    (hc : fb.withinContract = true) (hG : G) :
    BudgetedGuarantee fb.maxFaults fb.toFaultGrade G :=
  ⟨((withinContract_iff fb).mp hc).1, hG⟩

end FailureBudget

/-! ## 4. Anti-vacuity — the increment's teeth.

Two witnesses on the concrete `RsmAntiVacuity` run:
- **in-budget** — a real `BudgetedGuarantee 1 0 …` whose `extract` FIRES and
  yields the genuinely *changed* converged store (a non-trivial `Prop`, not
  `True`);
- **over-budget** — a concrete refutation `¬ BudgetedGuarantee 0 1 …` proving the
  over-budget guarantee type is really uninhabited (the void is not vacuously
  true). -/

namespace FaultGradeAntiVacuity

/-- The tolerated bound for the witness run: a 1-resilient contract. -/
def f : FaultGrade := 1

/-- The real liveness/convergence payload: the two replicas' stores converge to
the CHANGED value `⟨var 0, var 0⟩`, genuinely distinct from the initial store.
A non-trivial `Prop` (proved by `RsmAntiVacuity.converged_store_changed`), NOT
`True`. -/
abbrev ConvergedPayload : Prop :=
  RsmAntiVacuity.r1.store = Term.pair (Term.var 0) (Term.var 0) ∧
    RsmAntiVacuity.r1.store ≠ RsmAntiVacuity.init

/-- **In-budget delivery.** A concrete `BudgetedGuarantee 1 0` whose payload is
the real converged-and-changed fact, delivered at the unspent grade `b = 0 ≤ 1`. -/
theorem budgeted_converge : BudgetedGuarantee f FaultGrade.zero ConvergedPayload :=
  BudgetedGuarantee.deliver RsmAntiVacuity.converged_store_changed

/-- **The counit FIRES within budget:** `extract` recovers the real converged
fact from the in-budget guarantee. -/
theorem in_budget_extract_fires : ConvergedPayload :=
  budgeted_converge.extract

/-- …and the extracted fact is genuinely the CHANGED store — the payload was not
vacuous. -/
theorem in_budget_delivers_changed_store :
    RsmAntiVacuity.r1.store = Term.pair (Term.var 0) (Term.var 0) ∧
      RsmAntiVacuity.r1.store ≠ RsmAntiVacuity.init :=
  in_budget_extract_fires

/-- **Over-budget refutation (concrete `f = 0`, `b = 1`).** The over-budget
guarantee type is genuinely uninhabited — even for the real converged payload —
so the type-level voiding is not vacuously true the other way. -/
theorem over_budget_refutation : ¬ BudgetedGuarantee 0 1 ConvergedPayload :=
  -- `FaultGrade.saturatingAdd 0 1` is defeq `1`, so the headline void applies
  -- directly at the concrete `f = 0`.
  budgeted_guarantee_voids_over_budget (f := 0) (G := ConvergedPayload)

/-- The concrete `Nat` void behind the refutation: `¬ (1 ≤ 0)`. -/
theorem over_budget_empty_concrete : ¬ ((1 : FaultGrade) ≤ 0) := by decide

end FaultGradeAntiVacuity

end DLCD
