import DLCD.Consensus

/-! # DLC-D Phase 1.2c — LIVENESS under the `FailureBudget` (the failure-model-as-contract, completed)

Phases 1.0/1.1 delivered the SAFETY half of the failure-model contract:
`replicas_converge_on_prefix` (determinism), `agreement`/`validity`
(single-decree safety), and the `committed_prefix_agree` bridge that earns the
log oracle. Safety says *nothing bad happens* (at most one value decided; equal
prefixes converge). This module adds the **LIVENESS** half — *something good
eventually happens* — and thereby completes the failure model AS a contract:
`FailureBudget.withinContract` (fair delivery ∧ ≤ f faults) now buys not just
consistency but **progress**.

## The liveness statement (informal)

Under the `FailureBudget` contract — i.e. `fairDelivery = true` and the
crash-fault grade not overspent — an issued command:

1. **eventually commits** (a correct quorum's proposed value is `Decided`), and
2. **is eventually applied by every correct replica** (its written value is
   reflected in every correct replica's store).

Formally the two halves are `fair_quorum_decides` (consensus-termination, the
rank argument) and `command_eventually_applied` / `slot_write_observed`
(delivery-liveness), composed in `command_eventually_written`.

## Why fair delivery is an EXPLICIT hypothesis (FLP), not a weakness

The **FLP impossibility** (Fischer–Lynch–Paterson 1985) proves that in a fully
asynchronous network, deterministic consensus is impossible even with a *single*
crash fault: with no bound on message delay an adversarial scheduler can forever
delay the one decisive message. Hence **liveness REQUIRES a fairness / eventual-
synchrony assumption** — it can never be conjured from safety alone. So
`fairDelivery` appears as a genuine, load-bearing hypothesis on every liveness
theorem here (Gate 3, `bite_needs_fairDelivery`, shows a concrete never-fair
execution that never decides). This mirrors the earlier Iris write-once-cell →
replicated-register liveness lift, which used exactly a `no_infinite_descent`
rank descent PLUS an external `ThreadFair`/fair-delivery assumption. Making the
assumption explicit is *correct*, per FLP — not a gap.

## The rank argument (consensus-termination, the hard part)

Termination is proved by a **well-founded `Nat` ranking / progress measure**
(Manna 1974; Cousot–Cousot; the standard liveness proof rule = *conservation*
(≤) + *reduction* (<) of a ranking, under a fairness constraint that forbids
ignoring the progress action forever):

- `rank correct votes` := the number of *correct* replicas that have **not yet
  voted** (`(correct.filter (·.isNone)).card`).
- **Fairness** (the operationalization of `fairDelivery = true`) says: whenever
  some correct replica is still unvoted, the next fairly-scheduled step makes a
  correct replica vote, so the rank **strictly decreases**
  (`rank (run (k+1)) < rank (run k)` while `0 < rank (run k)`).
- `no_infinite_descent`: a `Nat` sequence that strictly decreases whenever
  positive must reach `0` — a `Nat` cannot descend forever (Mathlib
  well-foundedness of `<` on `ℕ`, here as an explicit strong-induction descent
  mirroring the Iris `FairModel.no_infinite_descent`).
- At rank `0` every correct replica has voted the proposal; `correct` is a
  quorum, so the value is `Decided`. ⇒ `fair_quorum_decides`.

## What is PROVED vs FENCED

- **PROVED, fully (no `sorry`):**
  - Delivery-liveness: `deliver` advances `applied` by 1 per step
    (`deliver_applied`, `deliver_applied_exact`, `deliver_applied_ge`), so after
    `i+1` deliveries a replica's `applied > i` and its store reflects
    `applyPrefix … (log.take (i+1))` — the slot-`i` write is observed
    (`slot_write_observed`). Bounded, deterministic, "eventually applied".
  - The **rank-descent CORE** in full: `no_infinite_descent` and
    `fair_run_reaches_zero`, and `fair_quorum_decides` (fair scheduling ⇒ quorum
    eventually forms ⇒ `Decided`) under an explicitly-named fairness predicate.
- **FENCED (the honest residual):** deriving the fairness predicate `hfair`
  (rank strictly decreases per round) from a *concrete message-passing schedule*
  driven by `FailureBudget.fairDelivery` + a ≤ f-crash adversary. We take the
  rank-descent as the operational *meaning* of `fairDelivery = true` (threaded
  through `command_eventually_written`, which extracts `fairDelivery = true`
  from `withinContract` and feeds it to `hfair`), rather than building the full
  asynchronous network model + partial-synchrony (Dwork–Lynch–Stockmeyer) round
  structure that would DISCHARGE it. That protocol-model construction is the
  next increment; nothing here asserts it. This is a precisely-fenced honest
  partial, per the increment's scope.

## Prior art (web-searched 2026-07-22; URLs recorded)
- decentralizedthoughts, *Flavours of State Machine Replication* (termination =
  all correct parties eventually output; liveness only under synchrony):
  https://decentralizedthoughts.github.io/2019-10-25-flavours-of-state-machine-replication/
- decentralizedthoughts, *CAP for two servers & one crash in partial synchrony*
  (why liveness needs a timing assumption):
  https://decentralizedthoughts.github.io/2023-07-09-CAP-two-servers-in-psynch/
- *The FLP Impossibility Result, 40 Years Later* (async + 1 crash ⇒ no
  deterministic consensus ⇒ fairness/eventual-synchrony is mandatory):
  https://www.javacodegeeks.com/2026/04/the-flp-impossibility-result-40-years-later-why-it-still-defines-every-consensus-protocol-you-use.html
- *Proving Program Termination* (CACM; Manna ranking functions / progress
  measures = the standard termination technique):
  https://cacm.acm.org/research/proving-program-termination/
- *Implicit Rankings for Verifying Liveness Properties in First-Order Logic*
  (arXiv 2412.13996; ranking = conservation (≤) + reduction (<)):
  https://arxiv.org/pdf/2412.13996
- Klein et al., *Progress Measures and Stack Assertions for Fair Termination*
  (PODC 1991) — liveness ⇒ fair termination via progress measures:
  https://dl.acm.org/doi/10.1145/135419.135462
- *Liveness Proofs in Veil* (the three ingredients: a progress action, a
  fairness assumption forbidding starving it, and the eventual good):
  https://proofsandintuitions.net/2026/06/24/liveness-proofs-in-veil-part-1/
- Dwork–Lynch–Stockmeyer, *Consensus in the Presence of Partial Synchrony*
  (safety under any asynchrony, termination only once timing bounds hold — the
  clean safety/termination separation this file mirrors).
- ACE / decentralizedthoughts survey (SMR = multi-shot agreement; termination =
  every sequence number eventually output by all correct parties):
  https://decentralizedthoughts.github.io/2019-10-25-flavours-of-state-machine-replication/
-/

namespace DLCD

open DLC

/-! ## 1. DELIVERY-LIVENESS — a committed slot is applied after bounded deliveries.

`deliver` advances `applied` by exactly 1 whenever the replica is not caught up
to the committed log (`applied < log.length`), and is a no-op otherwise. So after
`i+1` deliveries a replica that started at `applied = 0` has `applied = i+1 > i`,
and its store is the deterministic fold of the first `i+1` slots — the slot-`i`
write is the outermost applied command. This is the bounded, deterministic
"eventually applied": no fairness needed for a *single* replica's own deliveries
(fairness is what guarantees the replica is *scheduled*; once scheduled, delivery
is deterministic progress). -/

/-- `deliver` advances `applied` by 1 iff the replica has un-applied committed
slots left, else it is a no-op on `applied`. The clean per-step progress fact. -/
theorem deliver_applied (log : CommittedLog) (r : Replica) :
    (deliver log r).applied = if r.applied < log.length then r.applied + 1 else r.applied := by
  unfold deliver
  cases h : log[r.applied]? with
  | some c =>
      have hlt : r.applied < log.length := by
        have := List.getElem?_eq_some_iff.1 h
        obtain ⟨hlt, _⟩ := this
        exact hlt
      simp [hlt]
  | none =>
      have hge : log.length ≤ r.applied := List.getElem?_eq_none_iff.1 h
      have : ¬ r.applied < log.length := by omega
      simp [this]

/-- Exact progress: from a replica with `r.applied + k ≤ log.length`, after `k`
deliveries `applied = r.applied + k`. (Every one of the `k` steps strictly
advances, because it stays below `log.length`.) -/
theorem deliver_applied_exact (log : CommittedLog) (r : Replica) (k : Nat)
    (h : r.applied + k ≤ log.length) :
    ((deliver log)^[k] r).applied = r.applied + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : r.applied + k ≤ log.length := by omega
      rw [Function.iterate_succ', Function.comp_apply, deliver_applied]
      rw [ih hk]
      have : r.applied + k < log.length := by omega
      simp [this]
      omega

/-- Monotone lower bound on progress, with no caught-up hypothesis: after `k`
deliveries, `applied ≥ min (r.applied + k) log.length`. Used for the "eventually
`applied > i`" statement regardless of the starting position. -/
theorem deliver_applied_ge (log : CommittedLog) (r : Replica) (k : Nat) :
    min (r.applied + k) log.length ≤ ((deliver log)^[k] r).applied := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply, deliver_applied]
      set a' := ((deliver log)^[k] r).applied with ha'
      by_cases hlt : a' < log.length
      · simp only [hlt, if_true]
        omega
      · simp only [hlt, if_false]
        omega

/-- **DELIVERY-LIVENESS (eventually applied).** For any committed slot `i` of the
log, after enough (`i+1`) deliveries the replica's `applied` has passed `i`.
Bounded and deterministic — the number of deliveries is `i+1`. -/
theorem command_eventually_applied (log : CommittedLog) (r : Replica) (i : Nat)
    (hi : i < log.length) :
    ∃ k, i < ((deliver log)^[k] r).applied := by
  refine ⟨i + 1, ?_⟩
  have hge := deliver_applied_ge log r (i + 1)
  omega

/-- `deliver` iterated preserves the prefix invariant (`AppliedPrefix`): if a
replica's store is the fold of its applied prefix, it still is after any number
of deliveries. So the "store reflects the committed prefix" invariant is what the
delivery dynamics maintain, not a vacuous assumption. -/
theorem deliver_iterate_maintains_prefix {init : Term} {log : CommittedLog}
    {r : Replica} (h : AppliedPrefix init log r) (k : Nat) :
    AppliedPrefix init log ((deliver log)^[k] r) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Function.iterate_succ', Function.comp_apply]
      exact deliver_maintains_prefix ih

/-- **The slot-`i` write is observed.** A replica starting caught-up-to-nothing
(`applied = 0`) with the prefix invariant, after exactly `i+1` deliveries has
`applied = i+1` and its store is `applyCommand c (applyPrefix init (log.take i))`
— i.e. slot `i`'s command `c` is the *outermost* applied command, so the value
written at slot `i` is now reflected in the store. Connects delivery-liveness to
*observing the write*. -/
theorem slot_write_observed {init : Term} {log : CommittedLog} {r : Replica}
    (h0 : r.applied = 0) (hinv : AppliedPrefix init log r)
    (i : Nat) (hi : i < log.length) (c : Command) (hc : log[i]? = some c) :
    ∃ k, ((deliver log)^[k] r).applied = i + 1 ∧
         ((deliver log)^[k] r).store = applyCommand c (applyPrefix init (log.take i)) ∧
         AppliedPrefix init log ((deliver log)^[k] r) := by
  refine ⟨i + 1, ?_, ?_, ?_⟩
  · rw [deliver_applied_exact log r (i + 1) (by omega)]
    omega
  · have happlied : ((deliver log)^[i + 1] r).applied = i + 1 := by
      rw [deliver_applied_exact log r (i + 1) (by omega)]; omega
    have hinv' := deliver_iterate_maintains_prefix hinv (i + 1)
    unfold AppliedPrefix at hinv'
    rw [hinv', happlied, applyPrefix_succ init log i c hc]
  · exact deliver_iterate_maintains_prefix hinv (i + 1)

/-! ## 2. CONSENSUS-TERMINATION — the well-founded rank argument.

The FLP-forced fairness assumption is operationalized as a *rank* (progress
measure) that strictly decreases whenever fair delivery schedules a correct
replica's vote. A `Nat` cannot strictly descend forever, so a quorum of correct
replicas eventually all vote and the value is `Decided`. -/

section Termination

variable {n : ℕ} {V : Type*}

/-- **THE RANK / PROGRESS MEASURE.** The number of *correct* replicas that have
not yet cast a vote. Strictly decreases each time fair delivery lets a correct
replica vote; is `0` exactly when every correct replica has voted. -/
def rank (correct : Finset (Fin n)) (votes : Votes n V) : ℕ :=
  (correct.filter (fun r => (votes r).isNone = true)).card

/-- **`no_infinite_descent` (auxiliary, bounded).** A `Nat` sequence `M` that
strictly decreases whenever it is positive reaches `0`, given a bound `N` on its
start. Pure `Nat` descent, by induction on the bound — the analogue of the Iris
`FairModel.no_infinite_descent`. -/
theorem no_infinite_descent_aux :
    ∀ (N : ℕ) (M : ℕ → ℕ), M 0 ≤ N →
      (∀ k, 0 < M k → M (k + 1) < M k) → ∃ k, M k = 0 := by
  intro N
  induction N with
  | zero => intro M h0 _; exact ⟨0, Nat.le_zero.1 h0⟩
  | succ N ih =>
      intro M h0 hfair
      rcases Nat.eq_zero_or_pos (M 0) with hM0 | hpos
      · exact ⟨0, hM0⟩
      · have hstep : M 1 < M 0 := hfair 0 hpos
        have hbound : (fun k => M (k + 1)) 0 ≤ N := by simp; omega
        have hfair' : ∀ k, 0 < (fun k => M (k + 1)) k →
            (fun k => M (k + 1)) (k + 1) < (fun k => M (k + 1)) k := by
          intro k hk; exact hfair (k + 1) hk
        obtain ⟨k, hk⟩ := ih (fun k => M (k + 1)) hbound hfair'
        exact ⟨k + 1, hk⟩

/-- **`no_infinite_descent`.** A `Nat` sequence that strictly decreases while
positive must hit `0`: a `Nat` cannot descend forever. The well-founded core of
the termination argument. -/
theorem no_infinite_descent (M : ℕ → ℕ)
    (hfair : ∀ k, 0 < M k → M (k + 1) < M k) : ∃ k, M k = 0 :=
  no_infinite_descent_aux (M 0) M le_rfl hfair

/-- **Fair scheduling ⇒ the correct set eventually fully votes.** If the rank
(unvoted-correct count) strictly decreases whenever positive — the fair-delivery
assumption — then at some step every correct replica has voted (`rank = 0`). -/
theorem fair_run_reaches_zero (run : ℕ → Votes n V) (correct : Finset (Fin n))
    (hfair : ∀ k, 0 < rank correct (run k) → rank correct (run (k + 1)) < rank correct (run k)) :
    ∃ k, rank correct (run k) = 0 :=
  no_infinite_descent (fun k => rank correct (run k)) hfair

/-- **CONSENSUS-TERMINATION.** Under a correct quorum `correct` (all voting the
proposal `v` — the honesty/validity discipline) and the fair-delivery assumption
(the rank strictly decreases while positive), the value `v` is eventually
`Decided`. Composition: fair scheduling drives `rank` to `0` (`fair_run_reaches_
zero` via `no_infinite_descent`), at which point every correct replica has voted
`v`; since `correct` is a quorum, `v` is `Decided`. The FLP-forced fairness lives
entirely in `hfair`. -/
theorem fair_quorum_decides (run : ℕ → Votes n V) (correct : Finset (Fin n)) (v : V)
    (hq : IsQuorum correct)
    (hhonest : ∀ k r, r ∈ correct → (run k) r ≠ none → (run k) r = some v)
    (hfair : ∀ k, 0 < rank correct (run k) → rank correct (run (k + 1)) < rank correct (run k)) :
    ∃ k, Decided (run k) v := by
  obtain ⟨k, hk⟩ := fair_run_reaches_zero run correct hfair
  refine ⟨k, correct, hq, ?_⟩
  intro r hr
  -- rank = 0 means the filter of unvoted-correct is empty: r has voted.
  have hempty : correct.filter (fun r => ((run k) r).isNone = true) = ∅ :=
    Finset.card_eq_zero.1 hk
  have hne : (run k) r ≠ none := by
    intro hnone
    have hmem : r ∈ correct.filter (fun r => ((run k) r).isNone = true) :=
      Finset.mem_filter.2 ⟨hr, by rw [hnone]; rfl⟩
    rw [hempty] at hmem
    simp at hmem
  exact hhonest k r hr hne

end Termination

/-! ## 3. COMBINE — an issued command is eventually committed AND applied.

`command_eventually_written` composes consensus-termination (§2) with delivery-
liveness (§1). The `FailureBudget` contract is threaded EXPLICITLY: `within
Contract = true` yields `fairDelivery = true`, which is precisely the trigger the
fairness hypothesis `hfair` consumes. So the fairness assumption is not a free
decoration — it is unlocked by, and only by, the contract holding. (Gate 3 shows
that without it, liveness fails.) -/

/-- **THE LIVENESS METATHEOREM.** Under the `FailureBudget` contract
(`withinContract = true` ⇒ fair delivery ∧ ≤ f faults), a command `c` proposed by
a correct quorum under fair delivery is BOTH (1) eventually `Decided` and (2)
eventually applied by a correct replica — its slot-`i` write reflected in the
store. The fairness hypothesis `hfair` is *guarded by* `budget.fairDelivery`, so
the contract is load-bearing: no contract ⇒ no `fairDelivery = true` ⇒ `hfair`
gives nothing ⇒ no termination. -/
theorem command_eventually_written {n : ℕ}
    (budget : FailureBudget) (hbudget : budget.withinContract = true)
    (run : ℕ → Votes n Command) (correct : Finset (Fin n)) (c : Command)
    (hq : IsQuorum correct)
    (hhonest : ∀ k r, r ∈ correct → (run k) r ≠ none → (run k) r = some c)
    (hfair : budget.fairDelivery = true →
      ∀ k, 0 < rank correct (run k) → rank correct (run (k + 1)) < rank correct (run k))
    {init : Term} {log : CommittedLog} {i : Nat} (hi : i < log.length)
    (hci : log[i]? = some c)
    {r : Replica} (h0 : r.applied = 0) (hinv : AppliedPrefix init log r) :
    (∃ k, Decided (run k) c) ∧
    (∃ m, ((deliver log)^[m] r).applied = i + 1 ∧
          ((deliver log)^[m] r).store = applyCommand c (applyPrefix init (log.take i)) ∧
          AppliedPrefix init log ((deliver log)^[m] r)) := by
  -- The contract holding delivers the FLP-forced fair-delivery flag.
  have hfd : budget.fairDelivery = true := by
    simp only [FailureBudget.withinContract, Bool.and_eq_true] at hbudget
    exact hbudget.1
  refine ⟨?_, ?_⟩
  · exact fair_quorum_decides run correct c hq hhonest (hfair hfd)
  · exact slot_write_observed h0 hinv i hi c hci

/-! ## 4. THE RIGHT-REASON BITE — fairness is LOAD-BEARING (the FLP analogue).

Drop the fairness assumption and liveness FAILS. The concrete never-fair
execution is the *stuck* run in which no replica ever votes (`fun _ => none`):
fair delivery never schedules anyone, the rank never decreases (it is constant
and positive), and the value is never `Decided`. So `fair_quorum_decides` cannot
apply — its `hfair` premise is exactly what this run violates. This is the direct
analogue of the Iris `bite_needs_threadFair` and of FLP: without fairness, a
correct replica can be starved forever. -/

namespace LivenessBite

variable {n : ℕ} {V : Type*}

/-- The **stuck** ballot: nobody ever votes. -/
def stuck (n : ℕ) (V : Type*) : Votes n V := fun _ => none

/-- **The stuck ballot never decides anything.** `Decided` needs a whole quorum
voting `some v`; but every quorum is nonempty (`quorum_intersect Q Q`), and that
replica voted `none ≠ some v`. So no value is ever chosen. -/
theorem stuck_never_decides {v : V} : ¬ Decided (stuck n V) v := by
  rintro ⟨Q, hQ, hv⟩
  obtain ⟨r, hr⟩ := quorum_intersect hQ hQ
  rw [Finset.mem_inter] at hr
  have : stuck n V r = some v := hv r hr.1
  simp [stuck] at this

/-- **THE BITE, stated as the failure of liveness without fairness.** For the
stuck run: (a) it is never `Decided` at ANY step, and (b) it violates the
fairness premise — its rank is positive (some correct replica unvoted) yet never
decreases — so the ONLY route to a decision (`fair_quorum_decides`, whose `hfair`
this run falsifies) is closed. Fairness is therefore load-bearing: remove it and
a correct proposal is starved forever, exactly as FLP predicts. The hypothesis
`hne` (the correct set is nonempty) is what makes the run's rank genuinely
positive, i.e. that there IS a correct replica to starve. -/
theorem bite_needs_fairDelivery (correct : Finset (Fin n)) (v : V)
    (hne : 0 < correct.card) :
    (∀ _ : ℕ, ¬ Decided (stuck n V) v) ∧
    (0 < rank correct (stuck n V)) := by
  refine ⟨fun _ => stuck_never_decides, ?_⟩
  -- rank = card of the whole `correct` set, since every replica is unvoted.
  have : correct.filter (fun r => ((stuck n V) r).isNone = true) = correct := by
    apply Finset.filter_true_of_mem
    intro r _
    rfl
  unfold rank
  rw [this]
  exact hne

end LivenessBite

/-! ## 5. ANTI-VACUITY — concrete non-vacuous liveness.

Two witnesses: (a) DELIVERY — a real 2-slot-adjacent run where a replica's
`applied` genuinely advances PAST the slot and its store CHANGES to the written
value; (b) TERMINATION — the descent measure genuinely decreases to `0` on an
explicit sequence, and `fair_quorum_decides` genuinely produces a `Decided`. -/

namespace LivenessAntiVacuity

/-! ### (a) Delivery-liveness is non-vacuous: the write is really observed. -/

/-- Starting from `applied = 0` over the one-slot `dup` log, after `1` delivery
`applied = 1 > 0` — the slot-0 command has been applied. -/
theorem delivery_advances_past_slot :
    0 < ((deliver DLCD.RsmAntiVacuity.log)^[1] ⟨0, DLCD.RsmAntiVacuity.init, 0⟩).applied := by
  have h1 : ((deliver DLCD.RsmAntiVacuity.log)^[1] ⟨0, DLCD.RsmAntiVacuity.init, 0⟩).applied = 1 :=
    deliver_applied_exact DLCD.RsmAntiVacuity.log ⟨0, DLCD.RsmAntiVacuity.init, 0⟩ 1 (by decide)
  omega

/-- **The observed value is the CHANGED store**, non-vacuously: after delivering
slot 0 the store is `⟨var 0, var 0⟩` (the `dup` write), genuinely distinct from
the initial `var 0`. The slot-0 write is reflected. -/
theorem write_observed_nonvacuous :
    ((deliver DLCD.RsmAntiVacuity.log)^[1] ⟨0, DLCD.RsmAntiVacuity.init, 0⟩).store
        = Term.pair (Term.var 0) (Term.var 0) ∧
    ((deliver DLCD.RsmAntiVacuity.log)^[1] ⟨0, DLCD.RsmAntiVacuity.init, 0⟩).store
        ≠ DLCD.RsmAntiVacuity.init := by
  refine ⟨rfl, ?_⟩
  intro h
  exact Term.noConfusion h

/-! ### (b) Consensus-termination is non-vacuous. -/

/-- An explicit strictly-descending measure `5, 4, 3, 2, 1, 0, 0, …`: it strictly
decreases while positive, so `no_infinite_descent` yields a real zero — the rank
argument fires on genuine descent, not a vacuous premise. -/
def descM : ℕ → ℕ := fun k => 5 - k

/-- The measure really decreases while positive. -/
theorem descM_fair : ∀ k, 0 < descM k → descM (k + 1) < descM k := by
  intro k hk
  unfold descM at *
  omega

/-- `no_infinite_descent` produces a real zero of the genuinely-descending
measure (at `k = 5`). Non-vacuous: the measure actually counts down. -/
theorem descM_reaches_zero : ∃ k, descM k = 0 := no_infinite_descent descM descM_fair

/-- Concrete descent witness: `descM 5 = 0` while `descM 0 = 5 > 0`. -/
theorem descM_descended : descM 0 = 5 ∧ descM 5 = 0 := by
  unfold descM; decide

/-- A concrete 3-replica population; the whole set `{0,1,2}` is the correct
quorum (`2·3 > 3`). -/
abbrev popN : ℕ := 3

/-- A correct quorum voting the proposal `7` at every step (rank `0` throughout).
This inhabits `fair_quorum_decides` producing a REAL `Decided 7` — the whole
termination pipeline yields a genuine decision, not a vacuous one. -/
def allVote : ℕ → Votes popN ℕ := fun _ _ => some 7

/-- The correct quorum: everyone. -/
def correctAll : Finset (Fin popN) := Finset.univ

theorem correctAll_quorum : IsQuorum correctAll := by
  unfold IsQuorum correctAll; decide

/-- Honesty: every (indeed the only) vote is `some 7`. -/
theorem allVote_honest : ∀ k r, r ∈ correctAll → (allVote k) r ≠ none → (allVote k) r = some 7 := by
  intro k r _ _; rfl

/-- The rank of the all-voted ballot is `0` (nobody is unvoted), so the fairness
premise is (vacuously) satisfied — there is never a positive rank to decrease. -/
theorem allVote_rank_zero (k : ℕ) : rank correctAll (allVote k) = 0 :=
  (by decide : rank correctAll (fun _ : Fin popN => (some 7 : Option ℕ)) = 0)

theorem allVote_fair : ∀ k, 0 < rank correctAll (allVote k) →
    rank correctAll (allVote (k + 1)) < rank correctAll (allVote k) := by
  intro k hk
  rw [allVote_rank_zero] at hk
  omega

/-- **`fair_quorum_decides` inhabited — a genuine decision emerges.** The full
termination theorem, applied to a concrete correct quorum, produces `∃ k,
Decided (allVote k) 7`. Non-vacuous: `7` really is decided. -/
theorem termination_produces_decision : ∃ k, Decided (allVote k) 7 :=
  fair_quorum_decides allVote correctAll 7 correctAll_quorum allVote_honest allVote_fair

/-- And the decision is concretely inhabited: `7` is `Decided` at step `0`. -/
theorem decided7_concrete : Decided (allVote 0) 7 :=
  ⟨correctAll, correctAll_quorum, by intro r _; rfl⟩

end LivenessAntiVacuity

end DLCD
