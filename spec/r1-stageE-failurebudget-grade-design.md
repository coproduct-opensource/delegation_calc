# R1 stage E — `FailureBudget` as a linear/consumable GRADE

**Status:** PROPOSAL (design only; no `.lean`/`.rs` edits). Gated on review.
**Branch:** `dlc-d/phase0-carve` (HEAD `8807bbb`).
**Scope:** turn the DLC-D failure model (`DLCD.FailureBudget`) from a *runtime
Prop contract* — a `withinContract = true` hypothesis the liveness guarantees
carry — into a genuine **type-level grade** threaded through the guarantee
layer, so that "crossing the fault budget voids the guarantee" is expressed as
an *uninhabited/uneliminable type at an over-budget grade*, not merely a `Prop`
you fail to supply. The unifying construct the original plan called "the
failure model as a linear type."

The headline recommendation, up front, so the tradeoff is visible before the
detail: **do NOT add a graded modality to `Prop'`/`CDeriv` (options a/b below).**
The fault budget is a *distributed-scheduling* resource — replicas spend it by
crashing — not a *term-level* resource that any binder or β-redex consumes. A
modality on the calculus would therefore be the single biggest R1 stage (it
re-founds subject reduction, non-interference and progress, exactly as
inc2/inc3 did for `command`/`replicated`) **and would be semantically vacuous**:
no `Term` ever consumes a fault. The type-level content belongs at the layer
where the budget is real — the DLCD guarantee layer over `GlobalConfig`. Placed
there (option c'), it reuses the already-proven `DpBudget` graded-comonad
template wholesale, touches only the two liveness theorems, and re-founds G1–G4
with **zero** re-proof of SR/NI/progress and **zero** churn to the 49 axiom
snapshots. This is the cheapest design that is *genuinely* type-level rather
than a renamed hypothesis, and the rest of the doc argues exactly that.

---

## 0. Prior art (web-searched 2026-07-23; URLs recorded)

**Graded / coeffect type systems for consumable resources (the grade algebra
+ graded (co)monad this reuses).**
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu, *Combining Effects and
  Coeffects via Grading* (ICFP 2016) — effects = graded monads, coeffects =
  graded monoidal **comonads**; a resource demand is a grade drawn from a
  (pre-ordered) semiring. This is the categorical model `Graded.lean`'s
  `DpBudget`/`Graded` already instantiates.
  https://kar.kent.ac.uk/57480/1/bieffects.pdf
- Orchard, Liepelt, Eades III, *Quantitative Program Reasoning with Graded
  Modal Types* (ICFP 2019) — **Granule**: a linear language with a graded
  modality `□_r A` indexed by a resource algebra (a pre-ordered semiring with
  monotone `+`, `*`), instantiable per-semiring; the canonical "a resource with
  a bounded usage grade" system.
  https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- McBride, *I Got Plenty o' Nuttin'* (2016) — usage over an arbitrary *rig*;
  the rig's **zero marks context present "for contemplation rather than
  consumption"** — precisely CARVe's `Mult.zero`/`zeroed` block. The paper the
  CARVe var rule already descends from.
  https://personal.cis.strath.ac.uk/conor.mcbride/pub/Rig.pdf
- Atkey, *Syntax and Semantics of Quantitative Type Theory* (LICS 2018) —
  usage-vector judgements over the semiring `Q`; a grade `0` variable is
  contemplation-only, and the **grade preorder is distinct from any threshold
  check** — the separation this proposal makes for `FailureBudget`.
  https://bentnib.org/quantitative-type-theory.pdf
- Mannucci, Thuro, *Resource-Bounded Type Theory: Compositional Cost Analysis
  via Graded Modalities* (arXiv 2512.06952, Dec 2025) — a **graded
  *feasibility* modality with a counit** and a cost-soundness theorem: a bound
  `b` drawn from a resource lattice, the term realizes cost `≤ b`. The counit
  "extract the value once you are within budget" is the exact shape of the
  `BudgetedGuarantee` eliminator proposed in §1.c'.
  https://arxiv.org/abs/2512.06952
- Bounded Linear Logic (Girard–Scedrov–Scott, via the ICFP'19 survey framing):
  the `!` modality replaced by a *family* of modalities parametrized by a
  resource bound — the "modality bounded by `b`" pattern, of which "guarantee
  available while `consumed ≤ f`" is an instance.

**Failure / fault budget as a type-level resource in distributed / session
systems (the closest existing "failure model in the types").**
- Barwell, Scalas, Yoshida et al., *Crash-Stop Failures in Asynchronous
  Multiparty Session Types* (arXiv 2311.11851) — crash-stop faults are typed:
  processes may crash and peers detect + handle it, with type-level reliability
  assumptions bounding how many/where. The prior art that a *crash-fault model*
  can live in a type system. https://arxiv.org/pdf/2311.11851
- *Fault-Tolerant Multiparty Session Types* (FTMPST, arXiv 2204.07728) and
  *…with Global Escape Loops* (arXiv 2510.24203) — reliability annotations on
  interactions. https://arxiv.org/pdf/2204.07728
- The three reliability *levels* — Strongly Reliable / Weakly Reliable /
  Unreliable — are a coarse, 3-point version of exactly a fault **grade**; a
  `FaultGrade : Nat` generalizes that qualitative ladder to a consumable count
  bounded by `f`. (Survey framing, same corpus.)
- Benton-style **mixed linear / graded** logic — *A Mixed Linear and Graded
  Logic: Proofs, Terms, and Models* (arXiv 2401.17199) — layers a *graded*
  modality **on top of** a linear system rather than folding grades into the
  linear context. Direct support for keeping the fault grade in its own
  modality/layer (option c') instead of the CARVe usage vector (option b).
  https://arxiv.org/pdf/2401.17199

**The lens these give us.** A grade is (i) an ordered monoid `(G, +, 0, ≤)`
threaded by a graded (co)monad, plus (ii) — for a *bounded* resource — a
*separate* threshold against which a **counit/eliminator** is gated. The
current `FailureBudget` conflates (i) `consumed` (the grade) with (ii)
`maxFaults` (the threshold) and a qualitative side-flag `fairDelivery`. The
reformulation's whole content is to **separate** them: the grade *indexes* the
guarantee; the threshold *gates its elimination*. That separation is what makes
"over budget" a type-level fact rather than a false `Prop`.

---

## 1. What "`FailureBudget` as a grade" means here — three options, weighed

### The load-bearing fact that decides this (read first)

An audit of where the budget is actually *used as a hypothesis* (not merely
carried as a `GlobalConfig` field):

| Guarantee | Budget role | file |
|---|---|---|
| `command_eventually_written` (G3) | **hypothesis** `hbudget : withinContract = true`, unlocks `fairDelivery` → `hfair` | `Liveness.lean:320` |
| `command_eventually_written_weakfair` (G3) | **hypothesis** `hbudget`, unlocks `WeakFair` | `Termination.lean:300` |
| `distributed_noninterference` (G1) | **none** — budget is only a field of the witness `GlobalConfig`s | `DistributedNI.lean:422` |
| `capability_safety`, `…_by_inversion` (G1) | **none** — config field only | `CapSafety.lean` |
| `single_linearization` (G2) | **none** | `Linearizable.lean` |
| `replicas_converge_via_consensus`, `log_agreement_eq`, CALM (G4) | **none** | `Consensus/MultiDecree/Calm` |
| `SliceWitness` seal | `budget_contract : withinContract = true`, part of the bundle | `Witness.lean:244` |

So the budget is **load-bearing in exactly two theorems**, both about *liveness*
(fair delivery), and in both its only content is: `withinContract = true`
extracts `fairDelivery = true`, which unlocks the fairness premise. In G1/G2/G4
the budget is **inert data**. This asymmetry is the whole design: a type-level
budget need only re-found the two liveness theorems; everywhere else it is
[RE-FOUND] byte-identically because the budget was never in the statement.

It also tells us *where the budget lives*: in the delivery schedule (how many
replicas may crash before fair delivery is lost), **not** in any `Term`. No
command, no β-redex, no binder ever "spends a fault." That kills options (a)
and (b) on semantic grounds before we even count their proof cost.

### Option (a) — a graded modality on propositions `Prop'.budgeted b φ`

Add a constructor `Prop'.budgeted (b : FaultGrade) (φ : Prop')` with `CDeriv`
intro/elim rules that track/consume the grade, mirroring the label modality
`Prop'.at φ ℓ` (inc3) and the `Graded⟨DpBudget⟩` wrapper.

- **Cost.** New `Prop'` constructor ⇒ new `CDeriv` rules ⇒ re-thread
  `cderiv_shift`, `cderiv_substA/L/M`, `cderiv_subject_reduction'`, `cprogress`
  over the new rules (every one is an induction over all constructors); a new
  reduction redex (`budgeted`-intro/elim, e.g. `runBudgeted`) with its own SR
  case; and a **new clause in the DistributedNI logical relation (`LRel`)** so
  NI covers the modality — precisely the inc3 `runCmd`/`liftLabel` playbook,
  but for a construct that then does nothing.
- **Fatal objection — vacuity.** A `Prop'` modality is intro'd/elim'd by
  *terms*, but no term consumes a fault. `budgeted b φ` would be inhabited at
  *any* `b` with no operational event charging it, so the grade index is
  free-floating decoration. To make it non-vacuous you would have to invent a
  reduction rule where some term (a commit?) *spends* budget — but a commit's
  authorization is fault-independent (§6), so that rule would have no
  operational meaning in the RSM model. **Rejected: maximal cost, on the wrong
  layer, vacuous.**

### Option (b) — a fourth resource dimension in the CARVe vector

Extend `Carve.Ctx` entries from `(Prop', Mult)` to `(Prop', Mult, FaultGrade)`,
`MJoin`/`CJoin` to a product resource algebra `Mult × FaultGrade`.

- **Cost.** Touches **every** lemma in `CarveJudgment.lean` (2779 lines, all 11
  constructors × `shift`/`substA`/`substL`/`substM`/SR/progress) plus
  `CarveCtx.lean`. A product-semiring usage vector is standard QTT, so it is
  *possible*, but it is the largest re-proof in the repo.
- **Fatal objection — category error.** The `Mult` vector tracks *variable
  usage* (which binder is consumed, exactly once vs. freely); the fault grade
  tracks *replica crashes*. These are orthogonal concerns living at different
  layers. Conflating them into one vector forces every substitution lemma to
  carry crash-fault arithmetic it never uses. The mixed-linear-graded-logic
  prior art (arXiv 2401.17199) is explicit that grades layer *on top of* the
  linear system, not *inside* its context. **Rejected: maximal cost, category
  error.**

### Option (c') — RECOMMENDED: a graded comonad over the *guarantee*, `Graded⟨FaultGrade⟩`

Keep the calculus untouched. Instantiate the **existing** `DpBudget`
graded-comonad template at the fault grade and wrap the *liveness guarantee* in
it, so the guarantee is delivered **at a grade**, with a threshold-gated
eliminator:

```
FaultGrade            := Nat                         -- the consumable grade
-- reuse Graded.lean's proven monoid: 0, saturatingAdd (= +), le (= ≤)

structure BudgetedGuarantee (f : Nat) (b : FaultGrade) (G : Prop) : Prop where
  -- G is the raw liveness conclusion (∃k, Decided … ∧ ∃m, applied …)
  charged  : b ≤ f          -- the counit is available ONLY within budget
  guarantee : G
-- consume : charge a fault-round, threading the grade (saturatingAdd)
-- extract : {b ≤ f} → BudgetedGuarantee f b G → G     -- the graded counit
```

The **type-level voiding** is real: `BudgetedGuarantee f (f+1) G` has an
uninhabitable `charged : f+1 ≤ f` field, so **there is no term of the
over-budget guarantee type**, and `extract` at `b > f` does not typecheck.
Crossing the budget makes the guarantee *type* empty — not a `Prop` you merely
fail to prove. Sequencing delivery rounds `consume`s the grade via
`saturatingAdd`; the grade preorder `le` is `DpBudget.le`'s naturals-monoid
instance; and this is **structurally the `DpBudget` graded comonad** the plan
named, so its identity/associativity laws (`graded_identity_law`,
`graded_associativity_law`, `dp_budget_saturating_add_assoc`) port directly
(§2).

- **Why this is genuinely type-level, not a renamed hypothesis.** The old
  `hbudget : withinContract = true` is a `Prop` premise: over budget ⇒ you
  cannot *supply* it. Here the guarantee's **type is indexed by the grade**,
  and the over-budget index yields an *empty type*; the eliminator that yields
  the raw fact is gated by `b ≤ f` at the type level; and the grade **threads**
  (each fault-round `consume`s it). That is the graded-comonad counit of the
  Resource-Bounded Type Theory / Granule prior art, not a Boolean flag.
- **Why it is cheapest.** It reuses `Graded.lean` wholesale; it adds **no**
  `Prop'`/`CDeriv` constructor, **no** redex, **no** LRel clause; SR/NI/progress
  are untouched; the 49 axiom snapshots stay byte-identical (new theorems get
  *new* snapshots appended). It re-founds exactly the two liveness theorems and
  leaves G1/G2/G4 alone.

**RECOMMENDATION: option (c').** Trade-off named honestly: this is *not* the
maximal, "biggest R1 stage" construction — options (a)/(b) are, and if you rule
for a calculus-level modality you should expect an inc2+inc3-sized re-founding
of SR/NI/progress. The recommendation is deliberately the *small* design,
because the analysis (§1 audit) shows the type-level content has exactly one
honest home — the guarantee layer — and putting it anywhere else buys a vacuous
modality at maximal cost. Per the stage gate ("if a graded modality would force
re-proving NI from scratch, prefer the lighter reformulation"), c' is the ruling
the gate points to.

---

## 2. The grade algebra — is `FailureBudget` a valid grade? (yes, once distilled)

A grade is an ordered monoid `(G, +, 0, ≤)` with `+` monotone in `≤`. Reading
off `FailureBudget`:

| grade law | current `FailureBudget` | verdict |
|---|---|---|
| carrier `G` | `consumed : Nat` (the grade); `maxFaults`, `fairDelivery` are **not** grade data | `FaultGrade := Nat` |
| unit `0` | `zero f = ⟨f, true, 0⟩` — `consumed = 0` | ✓ |
| `+` | `saturatingAdd b extra = { b with consumed := consumed + extra }` — i.e. `Nat.add` on the grade | ✓ associative, `0` unit |
| preorder `≤` | **absent as a grade order** — `FailureBudget.le` is `consumed ≤ maxFaults`, i.e. the *threshold*, not the grade order | needs the grade preorder `consumed₁ ≤ consumed₂` |

**Finding.** `FailureBudget.le` is mislabelled: it is the **threshold guard**
(`consumed ≤ maxFaults`), not the grade preorder. The distillation cleanly
separates the two concerns the grade literature keeps apart (Atkey LICS'18: the
usage preorder is distinct from any bound):

- **grade preorder** `FaultGrade.le b₁ b₂ := b₁ ≤ b₂` — this is exactly
  `DpBudget.le` restricted to one component (`DpBudget` is `(ℕ², +, 0, ≤)`;
  `FaultGrade` is `(ℕ, +, 0, ≤)`, its 1-D projection).
- **threshold guard** `withinBudget f b := b ≤ f` — the counit-availability
  condition (`BudgetedGuarantee.charged`), plus the qualitative
  `fairDelivery : Bool` kept as a *separate* assumption (it is a
  yes/no premise, not a consumable count; see open Q2 for the 2-D alternative).

**Reuse of `Graded.lean`.** Two faithful routes, both cheap:
1. **Instantiate** `Graded⟨DpBudget⟩` with `deltaMicros := 0` and read the grade
   off `epsilonMicros`. Then *every* law (`graded_identity_law`,
   `dp_budget_saturating_add_assoc`, `graded_associativity_law`) applies with
   **no new proof** — literally the DpBudget comonad. Downside: a spurious
   second component.
2. **Port** to a 1-D `FaultGrade` (cleaner types): the three law proofs are the
   *same* `simp [saturatingAdd, Nat.add_assoc, Nat.zero_add]` scripts as
   `Graded.lean`, three lines each, axiom-clean. Recommended for readability.

Either way the grade laws are **already discharged** in `Graded.lean`; stage E
adds no new grade-algebra proof obligation beyond a 1-D restatement.

---

## 3. How G1–G4 re-found relative to a TYPED budget

Per-guarantee, using the §1 audit. `[RE-FOUND]` = existing statement preserved,
budget hypothesis becomes a grade index (recoverable as an `extract` corollary,
so the *original theorem is retained verbatim*); `[RE-PROVE]` = needs new proof.

- **G1 `distributed_noninterference` — [RE-FOUND], byte-identical.** Takes no
  budget hypothesis (`DistributedNI.lean:422`); budget is a `GlobalConfig`
  field of the witnesses only. Reuses `DLC.t3_two_run_general` (the
  fundamental-lemma non-interference, propositional core). Unchanged.
- **G1 `capability_safety`, `…_by_inversion`, `…_linear`,
  `wellTypedLog_implies_htyped`, `wellTypedCmd_of_command_typing` —
  [RE-FOUND], byte-identical.** Config-field only. Unchanged.
- **G2 `single_linearization` — [RE-FOUND], byte-identical.** No budget
  hypothesis. Unchanged.
- **G3 `command_eventually_written` — [RE-FOUND], re-stated.** Currently
  `(budget) (hbudget : withinContract = true) … → (∃k, Decided) ∧ (∃m, applied)`.
  Re-founded form delivers the conclusion **at a grade**:
  `command_eventually_written_budgeted : … → BudgetedGuarantee f b G_liveness`,
  where `b` is the faults charged by the delivery schedule and `f = maxFaults`.
  The original is recovered *verbatim* as
  `command_eventually_written := fun … => (command_eventually_written_budgeted …).extract h`
  where `h : b ≤ f` comes from the same `withinContract` decode. **The old
  theorem is kept as a one-line corollary — not re-proved, not weakened.** The
  new content: the `hfair`/`WeakFair` premise is threaded as the graded
  guarantee's payload, and `fairDelivery = true` is precisely the counit's
  availability side (it stays a separate premise, or folds in per open Q2).
- **G3 `command_eventually_written_weakfair` — [RE-FOUND], re-stated.** Same
  move over `WeakFair` + `MonotoneVotes`. `weakfair_terminates` (the consensus
  half) is unchanged; only the top-level combinator is re-stated to return a
  `BudgetedGuarantee`.
- **G3 `log_grows_unbounded` — [RE-FOUND], byte-identical.** Uses a fair slot
  schedule, not the `FailureBudget`. Unchanged.
- **G4 `replicas_converge_via_consensus`, `log_agreement_eq`,
  `coordination_free_convergence` — [RE-FOUND], byte-identical.** No budget
  hypothesis. Unchanged.
- **The seal `SliceWitness.dlc_d_slice_witness` — [RE-FOUND], one field
  swapped.** Currently bundles `budget_contract : withinContract = true`. Under
  c' it bundles the *graded* witness (a `BudgetedGuarantee f 0 …` at the unspent
  grade `b = 0 ≤ f`), whose `extract` reproduces `budget_contract`. The bundle
  stays inhabited on the same real 2-replica run.

**Net:** of the ~14 governed guarantees, **12 are [RE-FOUND] byte-identical**
(budget never appeared in their statement) and **2 liveness theorems are
[RE-FOUND] via re-statement** with the originals kept as `extract` corollaries.
**Zero [RE-PROVE].** The type-level "voiding" bites exactly where the budget was
ever load-bearing (§4 anti-vacuity: exhibit the empty over-budget guarantee
type).

---

## 4. Realizability + SR/NI soundness

Because option (c') adds **no** constructor to `Prop'`/`CDeriv`, **no** redex,
and **no** `LRel` clause, the calculus metatheory is entirely undisturbed:

- **Subject reduction — [RE-FOUND], byte-identical.** `cderiv_subject_reduction'`
  induction is unchanged; there is no new β-redex to preserve. No new SR case,
  no re-thread of `cderiv_shift`/`cderiv_substA/L/M`.
- **Non-interference — [RE-FOUND], byte-identical.** `distributed_noninterference`
  and its `LRel` are unchanged; the budget grade lives *above* the logical
  relation, over `GlobalConfig`/delivery, so NI never sees it. This is the
  soundness payoff of choosing the guarantee layer: **NI is not re-proved from
  scratch**, which the stage gate flags as the disqualifier for a modality.
- **Progress — [RE-FOUND], byte-identical.** `cprogress` untouched.
- **Realizability of `BudgetedGuarantee`.** Its realizer is a graded comonad
  value `⟨charged, guarantee⟩` (the `Graded⟨FaultGrade⟩` pair). The counit
  `extract` is the RBTT/Granule feasibility counit — total on the in-budget
  index, undefined (untypable) off it — and its laws are the reused
  `graded_identity_law`/`graded_associativity_law`. Anti-vacuity witness (E1):
  (i) a real in-budget `BudgetedGuarantee f 0 G` whose `extract` yields an
  actual `Decided ∧ applied` fact on the `RsmAntiVacuity` run, and (ii) a
  refutation `¬ ∃ g : BudgetedGuarantee f (f+1) G, True` (the `charged` field is
  `f+1 ≤ f`, empty) — proving the over-budget guarantee type is genuinely
  uninhabited, i.e. the voiding is not vacuous the other way.

**For the record — what option (a) *would* require** (to justify declining it):
a `budgeted`-intro value + `runBudgeted` elim redex; an SR case
`runBudgeted (budgeted b V) ▷ …` closing at the reduct type (inc3-style); an
`LRel (budgeted b φ)` clause and its two-run gate; and a fresh subject-reduction
+ NI induction pass. That is [RE-PROVE] on SR **and** NI — the biggest single
R1 stage — for a modality no term inhabits non-trivially. Declined.

---

## 5. Impact map + staging

### Files

- **NEW `lean/DLCD/FaultGrade.lean`** (E1) — `FaultGrade`, the 1-D grade laws
  (ported from `Graded.lean`, ~3 lines each), `BudgetedGuarantee`, `extract`,
  `consume`, the comonad laws, and the two anti-vacuity witnesses. Self-
  contained; imports `DLCD.Rsm` (+ optionally `DLC.Graded`). **Touches no
  existing theorem** → the 49 snapshots stay byte-identical; E1 adds *new*
  snapshot files only.
- **`lean/DLCD/Liveness.lean`, `lean/DLCD/Termination.lean`** (E2) — *append*
  `command_eventually_written_budgeted` / `_weakfair_budgeted`; keep the
  originals verbatim, redefined as one-line `extract` corollaries (or left
  standing and the budgeted form added alongside — see open Q1).
- **`lean/DLCD/Witness.lean`** (E3, optional) — swap `budget_contract` for the
  graded witness field; bundle stays inhabited.
- **`lean/DLCD/Summary.lean`** — append two `abbrev` re-exports (ledger
  tripwire) for the budgeted forms.
- **`lean/theorem-status.json`** — append `DLCD_command_eventually_written_budgeted`
  etc. (append-only IDs; existing IDs untouched).
- **`lean/expected-axioms/`** — *new* snapshot files for the new theorems;
  all 49 existing snapshots byte-unchanged.
- **`crates/dlc-core/`** — none. (`FailureBudget` has no Rust mirror in
  `dlc-core`; `graded.rs` mirrors `DpBudget` only. The grade is model-side.)
- **`Rsm.FailureBudget`** — **not edited.** Add (E2) a *bridge*
  `FailureBudget.toFaultGrade b := b.consumed` and
  `FailureBudget.threshold b := b.maxFaults` so the config field and all its
  witnesses stay byte-identical; the graded theorems consume the bridge. (Do
  **not** replace `FailureBudget` — see open Q4.)

### Green-to-green sub-steps

- **E1 (minimal first increment)** — `FaultGrade.lean` alone: the distilled
  grade + reused laws + `BudgetedGuarantee`/`extract`/`consume` + the two
  anti-vacuity witnesses (in-budget `extract` fires; over-budget type empty).
  This *stands alone*, compiles green, and **already demonstrates the type-level
  voiding** without touching a single existing guarantee. It is the whole
  type-level claim in miniature. New axiom snapshots appended; 49 untouched;
  `check-claims.sh` green (doc + new model file, no headline claim changes).
- **E2** — re-found the two liveness theorems as budgeted forms + `extract`
  corollaries + the `FailureBudget.toFaultGrade` bridge. Originals preserved.
- **E3** — thread the grade through the `SliceWitness` seal; ledger + status
  append.

### Honest cost

Under the recommended (c') design this is **one of the *smaller* R1 stages**,
not the biggest — *because* it declines the calculus modality. Estimate: E1 is
a day (grade port is near-free; the work is the `BudgetedGuarantee` API +
anti-vacuity); E2 a day (two re-statements + corollaries + bridge + snapshots);
E3 a half-day. **If instead you rule for option (a)** (a `Prop'`/`CDeriv`
modality), it becomes the **biggest** R1 stage by a wide margin — an
inc2+inc3-scale re-founding of SR, NI and progress with new snapshots for every
touched theorem — and I would estimate it at a multiple of every prior R1
increment combined, for a modality that no term inhabits non-trivially. The
recommendation is explicitly to *not* pay that.

---

## 6. Interaction with the first-classed command (`commit-I` / `Term.command`)

**Does a `commit-I` consume budget? — No; recommend commit-I does NOT thread the
grade.** A `commit-I` (`Term.command M c ℓ`, inc3) *authorizes* a write; a
**fault** is a replica **crash**. Committing does not spend the crash-fault
budget: a command is authorized regardless of how many replicas have crashed, so
long as a quorum survives. The two are orthogonal — authorization is a *safety*
property (fault-independent), the budget bounds *liveness* (delivery under
crashes). Threading `FaultGrade` through `commit-I`'s typing would re-introduce
exactly the option-(a) vacuity: the command's type would carry a grade no
reduction charges.

**Where the real interaction is.** `f = maxFaults` bounds the **quorum** size,
and a commit's *eventual decision* requires a quorum — which is precisely the
premise the two liveness theorems (and only they) consume. So the fault grade
indexes the **delivery/liveness** of a committed command, which is exactly where
the (c') `BudgetedGuarantee` already sits. Commit-I stays ungraded (its
authorization is fault-independent); the grade indexes `command_eventually_
written_budgeted`, whose payload is "this committed command is eventually
decided + applied." That is the correct and only load-bearing coupling.

**Optional future hook (not now).** If per-command fault accounting is ever
wanted, `Prop'.replicated φ ℓ` (inc3, already label-indexed) could gain a
*second* fault-grade index `replicated φ ℓ b`, making `commit-I` conclude at a
grade. That is option (a) in miniature and inherits its vacuity unless a real
reduction spends the grade — deferred, likely never (open Q3).

---

## 7. Open questions for ruling

1. **Keep-or-replace the originals.** E2 can either (i) *replace*
   `command_eventually_written` with a one-line `extract` corollary of the
   budgeted form (cleanest; the graded form becomes the primary), or (ii) keep
   both side-by-side (zero risk to the existing snapshot; two theorems to
   maintain). Recommend (i); confirm the snapshot for the corollary is
   acceptable churn on those two files.
2. **1-D grade vs. 2-D `(faults, fairDelivery)`.** `DpBudget` is 2-D `(ε, δ)`.
   Should `fairDelivery` fold into the grade as a second (Boolean-lattice)
   component — giving a `(faults, fairness)` grade that mirrors `(ε, δ)` exactly
   — or stay a separate qualitative premise? Recommend **separate** (fairness is
   a yes/no assumption, not a consumable count), but the 2-D form maximizes
   reuse of `DpBudget` verbatim. Your call on aesthetics vs. reuse.
3. **Ever want a term-level `budgeted` modality (option a)?** i.e. is there a
   future need for a `Prop'`/`CDeriv` fault modality, or is the guarantee-layer
   grade sufficient permanently? If permanently sufficient, we can close the
   "failure-model-as-linear-type" plan item with (c') and never open the
   calculus modality.
4. **Replace vs. bridge `Rsm.FailureBudget`.** Recommend *bridge*
   (`toFaultGrade`/`threshold`) to keep the 49 snapshots and all config
   witnesses byte-identical. Replacing `FailureBudget` outright would touch every
   `GlobalConfig` witness (`Witness`, `DistributedNI`, `CapSafety`, `TypedLog`)
   and their snapshots for no proof benefit. Confirm bridge.
5. **`Prop` vs `Type` for `BudgetedGuarantee`.** The liveness payload is an
   `∃`-statement (`Prop`), so `Prop` suffices and the `charged`-empty voiding is
   a clean `Prop` refutation. Confirm we do not need a `Type`-valued guarantee
   (we would only if a future guarantee must *carry a derivation* through the
   grade, cf. `CJoin` being `Type`-valued).

---

## Appendix — web URLs (Mandate 0)

- Combining Effects and Coeffects via Grading (ICFP'16): https://kar.kent.ac.uk/57480/1/bieffects.pdf
- Granule / Quantitative Program Reasoning with Graded Modal Types (ICFP'19): https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf
- McBride, I Got Plenty o' Nuttin' (2016): https://personal.cis.strath.ac.uk/conor.mcbride/pub/Rig.pdf
- Atkey, Syntax and Semantics of Quantitative Type Theory (LICS'18): https://bentnib.org/quantitative-type-theory.pdf
- Resource-Bounded Type Theory (arXiv 2512.06952): https://arxiv.org/abs/2512.06952
- Crash-Stop Failures in Asynchronous Multiparty Session Types (arXiv 2311.11851): https://arxiv.org/pdf/2311.11851
- Fault-Tolerant Multiparty Session Types (arXiv 2204.07728): https://arxiv.org/pdf/2204.07728
- FTMPST with Global Escape Loops (arXiv 2510.24203): https://arxiv.org/pdf/2510.24203
- A Mixed Linear and Graded Logic (arXiv 2401.17199): https://arxiv.org/pdf/2401.17199
