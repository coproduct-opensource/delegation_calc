import DLCD.Liveness
import DLCD.FaultGrade

/-! # DLC-D Phase 2.a — CONSENSUS TERMINATION derived from schedule WEAK-FAIRNESS

Phase 1.2c (`DLCD.Liveness`) proved consensus-termination (`fair_quorum_decides`)
and the end-to-end liveness metatheorem (`command_eventually_written`) but only
*relative to a raw, per-step rank-decrease assumption* `hfair`:

  `∀ k, 0 < rank Q (run k) → rank Q (run (k+1)) < rank Q (run k)`.

That hypothesis literally asserts the progress measure drops on **every** step —
which is stronger than any realistic scheduler guarantees (a correct replica may
sit un-scheduled for many steps before it finally votes). It is close to the
conclusion in disguise: "the rank goes down" is nearly "termination".

This module replaces that raw assumption with the STANDARD schedule-level
**weak-fairness** predicate `WeakFair` (the TLA⁺ `WF_vars` shape) plus the
standard **non-retraction** invariant `MonotoneVotes` (once a replica has voted,
it stays voted), and PROVES that termination follows. The payload is the
*fairness-transfer* theorem `weakfair_rank_decreases`: a schedule-level fairness
hypothesis about *enabled actions* is transferred onto the *rank* — turning the
former bare assumption into a THEOREM. This is the "transfer fairness from the
schedule to the ranking function" step of the ranking-function liveness method.

## What "enabled" / "weak fairness" mean here (honest fences)

- A correct replica `r ∈ Q` is **enabled** at step `k` iff it has *not yet voted*
  (`sched k r = none`), i.e. it *can still* cast its single-decree vote.
- **`WeakFair sched Q v`** := at every step `k`, every enabled correct replica
  *eventually* casts its vote for `v`: `∀ k r, r ∈ Q → sched k r = none →
  ∃ k' > k, sched k' r = some v`. This is exactly the `WF_vars(A)` pattern
  (Lamport): an action (this replica voting) that is continuously enabled is
  eventually taken. Crucially it is a genuine *scheduling* hypothesis — it says
  nothing about the rank, and it does NOT force a decrease on every step, only
  eventually. Its necessity is the FLP boundary, witnessed by `bite_needs_weakfair`.
- **`MonotoneVotes sched`** := `∀ k r x, sched k r = some x → sched (k+1) r =
  some x`. The standard "votes are not retracted" invariant; explicitly assumed.
  It is what makes the unvoted set shrink monotonically, so that a single new
  vote strictly lowers the rank (rather than being offset by a retraction).

Neither predicate is the conclusion restated: `weakfair_terminates` is *unprovable*
if `WeakFair` is dropped — that is precisely what `bite_needs_weakfair` shows by
exhibiting a `MonotoneVotes` schedule whose sole missing ingredient is weak
fairness and which therefore never decides.

## What is PROVED (no `sorry`)

- `eventual_descent` — a `Nat` sequence in which, whenever positive, some
  *strictly-later* index holds a smaller value, must reach `0`. This is the
  "eventual" strengthening of `Liveness.no_infinite_descent` (which needed a
  decrease on *every* step); it is what a genuine weak-fairness hypothesis feeds.
- `weakfair_rank_decreases` — THE fairness transfer: `WeakFair` + `MonotoneVotes`
  ⇒ whenever the rank is positive, a strictly-later step has a strictly-smaller
  rank. (Take an enabled correct replica; weak fairness makes it vote later;
  non-retraction keeps every other voted replica voted; so the unvoted set is a
  proper subset ⇒ strictly smaller card.)
- `weakfair_terminates` — decision is DERIVED: `WeakFair` + `MonotoneVotes` +
  quorum + honesty ⇒ `∃ k, Decided (sched k) v`. NO raw rank-decrease hypothesis.
- `command_eventually_written_weakfair` — the discharge/bridge: the Phase-1.2c
  end-to-end guarantee (`∃ k, Decided … ∧ eventually-applied …`) re-founded on
  `WeakFair` (guarded by `budget.fairDelivery`, exactly as the old `hfair` was),
  so the whole liveness metatheorem no longer needs the raw assumption. The
  consensus half calls `weakfair_terminates`; the delivery half reuses
  `Liveness.slot_write_observed` unchanged.
- `bite_needs_weakfair` — the FLP-boundary bite (see below).
- `WeakFairAntiVacuity.prog_terminates` — a concrete schedule that *genuinely
  exercises* `WeakFair`'s existential (replicas start unvoted and only vote
  later) and drives a real `Decided 7`, so nothing here is vacuous.

## The right-reason bite (FLP boundary)

`bite_needs_weakfair` fixes `n = 2` (whose only quorum is the whole set) and the
schedule `starve k := fun r => if r = 0 then none else some 7`: replica `0` is
perpetually enabled but NEVER votes, while replica `1` votes. The schedule is
`MonotoneVotes` (nothing is retracted), yet the rank is the constant `1 > 0`, so
no quorum ever forms and `¬ ∃ k, Decided (starve k) v`. And `starve` is exactly
a `WeakFair` *violation* (`starve_not_weakfair`): the enabled replica `0` never
gets its eventual vote. So weak fairness is load-bearing — without it a correct
proposal is starved forever, precisely as FLP predicts. This mirrors
`Liveness.bite_needs_fairDelivery` and the Iris `bite_needs_threadFair`.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Yao–Tao–Gu–Nieh, *Mostly Automated Verification of Liveness Properties for
  Distributed Protocols with Ranking Functions*, POPL 2024 (PACMPL) — the exact
  method used here: reduce liveness to safety via a ranking function whose
  decrease is *transferred from a fairness assumption*; verifies Paxos variants:
  https://dl.acm.org/doi/full/10.1145/3632877 , https://par.nsf.gov/servlets/purl/10477169
- Padon–Hoenicke–Losa–Podelski–Sagiv–Shoham, *Reducing Liveness to Safety in
  First-Order Logic*, POPL 2018 (PACMPL art. 26) — liveness under fairness
  reduced to safety; first mechanized liveness proof of Stoppable Paxos:
  https://dl.acm.org/doi/10.1145/3158114 , https://dl.acm.org/doi/pdf/10.1145/3158114
- Lamport, TLA⁺ weak fairness `WF_vars(A)` — a continuously-enabled action is
  eventually taken (the `WeakFair` shape): https://en.wikipedia.org/wiki/TLA%2B ,
  https://will62794.github.io/my-notes/notes/Liveness_and_Fairness_in_TLA+/Liveness_and_Fairness_in_TLA+.html
- Single-decree Paxos (mwhittaker) — the quorum-vote decision whose termination
  needs a fairness/eventual-synchrony assumption to transfer from execution
  schedules to the decision: https://mwhittaker.github.io/blog/single_decree_paxos/
- FLP (Fischer–Lynch–Paterson 1985) — async + 1 crash ⇒ no deterministic
  consensus ⇒ a fairness assumption is mandatory (the necessity the bite shows).
-/

namespace DLCD

open DLC

section WeakFairness

variable {n : ℕ} {V : Type*}

/-! ## 0. A small `Option` fact tying the rank filter's `isNone = true` to `none`. -/

/-- The rank filter's predicate `(o).isNone = true` is exactly `o = none`. -/
theorem isNone_eq_none {o : Option V} : o.isNone = true ↔ o = none := by
  cases o <;> simp

/-! ## 1. The two schedule-level hypotheses: weak fairness and non-retraction. -/

/-- **WEAK FAIRNESS (the `WF_vars` shape).** At every step `k`, any correct
replica `r ∈ Q` that is still *enabled* (has not voted — `sched k r = none`)
*eventually* casts its vote for `v` at some strictly-later step. This is a
genuine scheduling hypothesis about enabled actions; it mentions neither the
rank nor `Decided`, and it does NOT assert a per-step decrease (only eventual). -/
def WeakFair (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V) : Prop :=
  ∀ k r, r ∈ Q → sched k r = none → ∃ k', k' > k ∧ sched k' r = some v

/-- **NON-RETRACTION (monotone votes).** Once a replica has voted a value, it
keeps that vote forever. The standard single-decree "votes are not retracted"
invariant, stated explicitly because the rank-decrease argument depends on it. -/
def MonotoneVotes (sched : ℕ → Votes n V) : Prop :=
  ∀ k r x, sched k r = some x → sched (k + 1) r = some x

/-- Non-retraction, iterated: a vote at step `k` persists to any later step
`k + d`. Plain induction on the gap `d`. -/
theorem mono_votes_le {sched : ℕ → Votes n V} (hmono : MonotoneVotes sched)
    (s : Fin n) (x : V) (k : ℕ) :
    ∀ d, sched k s = some x → sched (k + d) s = some x := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
      intro h
      have hd := ih h
      have hk : k + (d + 1) = (k + d) + 1 := by omega
      rw [hk]
      exact hmono (k + d) s x hd

/-! ## 2. The "eventual descent" well-foundedness core.

`Liveness.no_infinite_descent` needed the measure to drop on *every* step. A
genuine weak-fairness hypothesis only gives an *eventual* drop — some strictly
later index holds a smaller value. This is still enough to reach `0`: the future
form is what lets the induction shift its origin forward. -/

/-- Bounded auxiliary: if `M 0 ≤ N` and whenever `M` is positive some
strictly-later index holds a smaller value, then `M` reaches `0`. Induction on
the bound `N`; the "strictly later" (`> k`) is essential — it lets us re-root the
sequence at the witnessing index and reapply the same fairness hypothesis. -/
theorem eventual_descent_aux :
    ∀ (N : ℕ) (M : ℕ → ℕ), M 0 ≤ N →
      (∀ k, 0 < M k → ∃ k', k' > k ∧ M k' < M k) → ∃ k, M k = 0 := by
  intro N
  induction N with
  | zero => intro M h0 _; exact ⟨0, Nat.le_zero.1 h0⟩
  | succ N ih =>
      intro M h0 hfair
      rcases Nat.eq_zero_or_pos (M 0) with hM0 | hpos
      · exact ⟨0, hM0⟩
      · obtain ⟨k', hgt, hlt⟩ := hfair 0 hpos
        -- `M k' < M 0 ≤ N+1`, so the re-rooted sequence starts `≤ N`.
        have hbound : (fun j => M (k' + j)) 0 ≤ N := by
          show M (k' + 0) ≤ N
          have : M (k' + 0) = M k' := by rw [Nat.add_zero]
          omega
        have hfair' : ∀ j, 0 < (fun j => M (k' + j)) j →
            ∃ j', j' > j ∧ (fun j => M (k' + j)) j' < (fun j => M (k' + j)) j := by
          intro j hj
          simp only at hj ⊢
          obtain ⟨m, hmgt, hmlt⟩ := hfair (k' + j) hj
          refine ⟨m - k', by omega, ?_⟩
          have hmk : k' + (m - k') = m := by omega
          rw [hmk]; exact hmlt
        obtain ⟨j, hj⟩ := ih (fun j => M (k' + j)) hbound hfair'
        exact ⟨k' + j, hj⟩

/-- **EVENTUAL DESCENT.** A `Nat` sequence in which, whenever positive, some
strictly-later index holds a smaller value must reach `0`. The well-founded core
that a *weak*-fairness hypothesis (eventual, not per-step) feeds. -/
theorem eventual_descent (M : ℕ → ℕ)
    (hfair : ∀ k, 0 < M k → ∃ k', k' > k ∧ M k' < M k) : ∃ k, M k = 0 :=
  eventual_descent_aux (M 0) M le_rfl hfair

/-! ## 3. THE FAIRNESS TRANSFER — schedule weak-fairness ⇒ rank decrease. -/

/-- **THE PAYLOAD — fairness transferred from the schedule onto the rank.** Under
`WeakFair` (enabled correct replicas eventually vote) and `MonotoneVotes` (no
retraction), whenever the rank is positive there is a *strictly-later* step whose
rank is *strictly smaller*. Proof: a positive rank means some correct replica `r`
is enabled (`sched k r = none`); weak fairness makes `r` vote at some `k' > k`;
non-retraction keeps every replica voted at `k` still voted at `k'`, so the
unvoted-correct set at `k'` is a *proper subset* of that at `k` (it loses `r` and
gains nobody) ⇒ strictly smaller cardinality. This turns the former raw
per-step-decrease *assumption* into a *derived* eventual decrease. -/
theorem weakfair_rank_decreases (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V)
    (hwf : WeakFair sched Q v) (hmono : MonotoneVotes sched) :
    ∀ k, 0 < rank Q (sched k) →
      ∃ k', k' > k ∧ rank Q (sched k') < rank Q (sched k) := by
  intro k hk
  -- A positive rank exhibits an enabled correct replica.
  have hpos : 0 < (Q.filter (fun r => (sched k r).isNone = true)).card := hk
  obtain ⟨r, hrmem⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter] at hrmem
  obtain ⟨hrQ, hrnone⟩ := hrmem
  have hkr : sched k r = none := isNone_eq_none.1 hrnone
  -- Weak fairness: `r` votes at a strictly later step.
  obtain ⟨k', hgt, hk'r⟩ := hwf k r hrQ hkr
  refine ⟨k', hgt, ?_⟩
  -- The unvoted-correct set shrinks: `B ⊆ A`, `r ∈ A`, `r ∉ B`.
  have hBA : Q.filter (fun s => (sched k' s).isNone = true)
      ⊆ Q.filter (fun s => (sched k s).isNone = true) := by
    intro s hs
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨hsQ, hsnone⟩ := hs
    refine ⟨hsQ, ?_⟩
    have hk's : sched k' s = none := isNone_eq_none.1 hsnone
    have hks : sched k s = none := by
      cases hopt : sched k s with
      | none => rfl
      | some y =>
          exfalso
          have hle : k ≤ k' := le_of_lt hgt
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
          have hlater : sched k' s = some y := by
            rw [hd]; exact mono_votes_le hmono s y k d hopt
          rw [hk's] at hlater
          simp at hlater
    exact isNone_eq_none.2 hks
  have hrA : r ∈ Q.filter (fun s => (sched k s).isNone = true) :=
    Finset.mem_filter.2 ⟨hrQ, isNone_eq_none.2 hkr⟩
  have hrnB : r ∉ Q.filter (fun s => (sched k' s).isNone = true) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hh⟩
    rw [hk'r] at hh
    simp at hh
  have hss : Q.filter (fun s => (sched k' s).isNone = true)
      ⊂ Q.filter (fun s => (sched k s).isNone = true) :=
    (Finset.ssubset_iff_of_subset hBA).2 ⟨r, hrA, hrnB⟩
  exact Finset.card_lt_card hss

/-- **The rank reaches `0` under weak fairness.** Feed the derived eventual
decrease into `eventual_descent`. -/
theorem weakfair_reaches_zero (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V)
    (hwf : WeakFair sched Q v) (hmono : MonotoneVotes sched) :
    ∃ k, rank Q (sched k) = 0 :=
  eventual_descent (fun k => rank Q (sched k))
    (weakfair_rank_decreases sched Q v hwf hmono)

/-! ## 4. TERMINATION — decision derived from weak fairness (no raw assumption). -/

/-- **CONSENSUS TERMINATION FROM WEAK FAIRNESS.** Under `WeakFair` + non-retraction
+ a quorum `Q` + honesty (correct replicas only ever vote `v`), the value `v` is
eventually `Decided`. The rank descent is *derived* from weak fairness
(`weakfair_reaches_zero`); at rank `0` every correct replica has voted, and since
`Q` is a quorum, `v` is `Decided`. There is NO raw per-step rank-decrease
hypothesis — that is the whole point of this increment. -/
theorem weakfair_terminates (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V)
    (hwf : WeakFair sched Q v) (hmono : MonotoneVotes sched) (hq : IsQuorum Q)
    (hhonest : ∀ k r, r ∈ Q → sched k r ≠ none → sched k r = some v) :
    ∃ k, Decided (sched k) v := by
  obtain ⟨k, hk⟩ := weakfair_reaches_zero sched Q v hwf hmono
  refine ⟨k, Q, hq, ?_⟩
  intro r hr
  unfold rank at hk
  have hempty : Q.filter (fun r => (sched k r).isNone = true) = ∅ :=
    Finset.card_eq_zero.1 hk
  have hne : sched k r ≠ none := by
    intro hnone
    have hmem : r ∈ Q.filter (fun r => (sched k r).isNone = true) :=
      Finset.mem_filter.2 ⟨hr, isNone_eq_none.2 hnone⟩
    rw [hempty] at hmem
    simp at hmem
  exact hhonest k r hr hne

end WeakFairness

/-! ## 5. THE BRIDGE — discharge the raw `hfair` of the Phase-1.2c metatheorem.

`Liveness.command_eventually_written` fed its raw per-step `hfair` into
`fair_quorum_decides` solely to obtain `∃ k, Decided …`. Here we re-derive the
identical end-to-end guarantee with `WeakFair` (+ non-retraction) in place of
`hfair`, guarded by `budget.fairDelivery` exactly as before — so the contract
stays load-bearing while the raw rank-decrease assumption is gone. The consensus
half is `weakfair_terminates`; the delivery half reuses `slot_write_observed`. -/

/-- **THE DISCHARGE / BRIDGE.** The Phase-1.2c liveness metatheorem, re-founded on
`WeakFair` instead of the raw per-step rank-decrease assumption. Under the
`FailureBudget` contract (which supplies `fairDelivery = true`, unlocking
`WeakFair`), a command `c` proposed by a correct quorum is BOTH eventually
`Decided` and eventually applied. Compare `Liveness.command_eventually_written`:
same conclusion, but its `hfair` obligation is now discharged by weak fairness. -/
theorem command_eventually_written_weakfair {n : ℕ}
    (budget : FailureBudget) (hbudget : budget.withinContract = true)
    (run : ℕ → Votes n Command) (correct : Finset (Fin n)) (c : Command)
    (hq : IsQuorum correct)
    (hhonest : ∀ k r, r ∈ correct → (run k) r ≠ none → (run k) r = some c)
    (hwf : budget.fairDelivery = true → WeakFair run correct c)
    (hmono : MonotoneVotes run)
    {init : Term} {log : CommittedLog} {i : Nat} (hi : i < log.length)
    (hci : log[i]? = some c)
    {r : Replica} (h0 : r.applied = 0) (hinv : AppliedPrefix init log r) :
    (∃ k, Decided (run k) c) ∧
    (∃ m, ((deliver log)^[m] r).applied = i + 1 ∧
          ((deliver log)^[m] r).store = applyCommand c (applyPrefix init (log.take i)) ∧
          AppliedPrefix init log ((deliver log)^[m] r)) := by
  have hfd : budget.fairDelivery = true := by
    simp only [FailureBudget.withinContract, Bool.and_eq_true] at hbudget
    exact hbudget.1
  exact ⟨weakfair_terminates run correct c (hwf hfd) hmono hq hhonest,
         slot_write_observed h0 hinv i hi c hci⟩

/-! ## 6. THE RIGHT-REASON BITE — weak fairness is load-bearing (FLP boundary). -/

namespace WeakFairBite

/-- Population `n = 2`: whose *only* quorum is the whole set `{0,1}` (a strict
majority needs `2·card > 2`, i.e. `card = 2`). So starving *one* replica blocks
*every* quorum — the cleanest setting to expose weak fairness as necessary. -/
abbrev N : ℕ := 2

/-- The **starved** schedule: replica `0` is perpetually enabled (never votes),
replica `1` votes `7`. Value-agnostically it never depends on the step, so it is
trivially `MonotoneVotes`, yet it never lets replica `0` vote. -/
def starve : ℕ → Votes N ℕ := fun _ r => if r = 0 then none else some 7

/-- The correct set / candidate quorum: everyone. -/
def Qc : Finset (Fin N) := Finset.univ

/-- Replica `0` is perpetually enabled: it is `none` at *every* step. -/
theorem starve_r0_enabled : ∀ k, starve k 0 = none := by
  intro k; show starve 0 0 = none; decide

/-- `starve` is non-retracting (`MonotoneVotes`): it does not depend on the step,
so no vote is ever withdrawn. So the bite's failure is NOT a retraction artifact
— the *only* missing ingredient is weak fairness. -/
theorem starve_monotone : MonotoneVotes starve := by
  intro k r x h; exact h

/-- The rank is the constant `1`: exactly replica `0` is unvoted, forever. -/
theorem starve_rank_const : ∀ k, rank Qc (starve k) = 1 := by
  intro k; show rank Qc (starve 0) = 1; decide

/-- **No value is ever decided.** The only quorum of `Fin 2` is the whole set,
which contains replica `0`; but `starve k 0 = none ≠ some v`. So `Decided` is
impossible at every step. -/
theorem starve_never_decides : ∀ (k : ℕ) (v : ℕ), ¬ Decided (starve k) v := by
  intro k v hdec
  obtain ⟨Q, hQ, hv⟩ := hdec
  have hle : Q.card ≤ 2 := by
    have := Finset.card_le_card (Finset.subset_univ Q)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hgt : 2 * Q.card > 2 := hQ
  have hcard2 : Q.card = 2 := by omega
  have huniv : Q = Finset.univ :=
    Finset.eq_univ_of_card Q (by rw [Fintype.card_fin]; exact hcard2)
  have h0Q : (0 : Fin N) ∈ Q := huniv ▸ Finset.mem_univ 0
  have hvote := hv 0 h0Q
  rw [starve_r0_enabled k] at hvote
  simp at hvote

/-- **`starve` violates `WeakFair`.** The enabled replica `0` never gets its
eventual vote — precisely the fairness this schedule lacks. -/
theorem starve_not_weakfair : ∀ (v : ℕ), ¬ WeakFair starve Qc v := by
  intro v hwf
  obtain ⟨k', -, hk'⟩ := hwf 0 0 (by decide) (starve_r0_enabled 0)
  rw [starve_r0_enabled k'] at hk'
  simp at hk'

/-- **THE BITE.** For the `MonotoneVotes` schedule `starve`: (a) replica `0` is
perpetually enabled but never votes; (b) the rank is the constant `1 > 0`, so it
never descends; (c) no value is EVER decided; and (d) this is exactly a
`WeakFair` violation. Hence weak fairness is load-bearing: `weakfair_terminates`
would be unprovable without it, because *this* schedule satisfies every other
hypothesis (monotone, and — vacuously, on the whole quorum needed — it cannot be
honest-to-a-decision) yet starves the proposal forever. FLP made concrete. -/
theorem bite_needs_weakfair :
    (∀ k, starve k 0 = none) ∧
    (∀ k, 0 < rank Qc (starve k)) ∧
    (∀ (k : ℕ) (v : ℕ), ¬ Decided (starve k) v) ∧
    (∀ (v : ℕ), ¬ WeakFair starve Qc v) :=
  ⟨starve_r0_enabled,
   fun k => by rw [starve_rank_const k]; exact Nat.one_pos,
   starve_never_decides,
   starve_not_weakfair⟩

end WeakFairBite

/-! ## 7. ANTI-VACUITY — `WeakFair` genuinely fires and drives a real decision.

The bite shows `WeakFair` is *necessary*; this shows it is *satisfiable and
non-vacuous* — a schedule where replicas genuinely start enabled and only vote
later, so `WeakFair`'s existential is really exercised, the rank really descends
`3 → 2 → 1 → 0`, and `weakfair_terminates` yields a real `Decided 7`. -/

namespace WeakFairAntiVacuity

/-- Three replicas; the whole set `{0,1,2}` is the correct quorum (`2·3 > 3`). -/
abbrev N : ℕ := 3

/-- A **staggered** schedule: replica `r` votes `7` from step `r.val` onward and
is enabled (`none`) before that. So replicas `1` and `2` start *unvoted* and only
vote *later* — genuinely exercising `WeakFair`'s "eventually votes" existential. -/
def prog : ℕ → Votes N ℕ := fun k r => if (r : ℕ) ≤ k then some 7 else none

/-- The quorum: everyone. -/
def Qp : Finset (Fin N) := Finset.univ

theorem prog_quorum : IsQuorum Qp := by unfold IsQuorum Qp; decide

/-- `prog` satisfies `WeakFair`: an enabled replica `r` (with `r.val > k`) votes
at the strictly-later step `k' = r.val`. The existential is really used. -/
theorem prog_weakfair : WeakFair prog Qp 7 := by
  intro k r _ hnone
  simp only [prog] at hnone
  by_cases h : (r : ℕ) ≤ k
  · simp [h] at hnone
  · refine ⟨(r : ℕ), by omega, ?_⟩
    simp [prog]

/-- `prog` is non-retracting: once `r.val ≤ k`, also `r.val ≤ k+1`. -/
theorem prog_monotone : MonotoneVotes prog := by
  intro k r x h
  simp only [prog] at h ⊢
  by_cases h' : (r : ℕ) ≤ k
  · rw [if_pos h'] at h
    rw [if_pos (by omega : (r : ℕ) ≤ k + 1)]
    exact h
  · rw [if_neg h'] at h
    simp at h

/-- Honesty: every vote `prog` ever casts is `some 7`. -/
theorem prog_honest :
    ∀ k r, r ∈ Qp → prog k r ≠ none → prog k r = some 7 := by
  intro k r _ hne
  simp only [prog] at hne ⊢
  by_cases h : (r : ℕ) ≤ k
  · rw [if_pos h]
  · rw [if_neg h] at hne
    exact absurd rfl hne

/-- The rank genuinely starts positive (`= 2`, replicas `1,2` unvoted) at step 0
and reaches `0` by step `2` — a real descent, not a vacuous premise. -/
theorem prog_rank_start : rank Qp (prog 0) = 2 := by decide
theorem prog_rank_zero : rank Qp (prog 2) = 0 := by decide

/-- **`weakfair_terminates` inhabited — a genuine decision emerges from weak
fairness.** The full termination pipeline (fairness transfer → eventual descent →
rank `0` → quorum decides), applied to a schedule that really exercises weak
fairness, produces `∃ k, Decided (prog k) 7`. Non-vacuous. -/
theorem prog_terminates : ∃ k, Decided (prog k) 7 :=
  weakfair_terminates prog Qp 7 prog_weakfair prog_monotone prog_quorum prog_honest

end WeakFairAntiVacuity

/-! ## 8. R1 stageE-E2 — the weak-fair liveness guarantee PACKAGED behind the fault-threshold.

The `WeakFair`-founded twin of `command_eventually_written_budgeted`
(`DLCD.Liveness`): an ADDITIVE graded wrapper that delivers §5's
`command_eventually_written_weakfair` conclusion (`∃ k, Decided … ∧ ∃ m, applied
…`) *at a grade* as a `BudgetedGuarantee budget.maxFaults budget.consumed …`.
The bridge is identical: the original's `withinContract = true` is split (via
`FailureBudget.withinContract_iff`) into the **threshold** `consumed ≤ maxFaults`
(the graded counit's availability side = the `charged` field) and **fair
delivery** (the qualitative premise that unlocks `WeakFair`). The engine is the
ORIGINAL `command_eventually_written_weakfair`, applied UNCHANGED after
`withinContract_iff` re-assembles its premise — byte-identical, not re-proved.
Over budget the `charged` field is uninhabitable, so the weak-fair eventual-
decision guarantee is type-level-unavailable (the E1 void on the real `G`). -/

/-- **THE WEAK-FAIR LIVENESS METATHEOREM, DELIVERED AT A GRADE (E2 headline).**
Identical to `command_eventually_written_weakfair` except `withinContract = true`
is split into the **threshold** `budget.consumed ≤ budget.maxFaults` (the counit's
availability side) and **fair delivery** `budget.fairDelivery = true`, and the
conclusion is packaged as a `BudgetedGuarantee budget.maxFaults budget.consumed
G` for §5's exact eventual-decision-and-application `G`. The `charged` field is
the threshold; over budget it is unconstructible, so the guarantee TYPE is empty
(`budgeted_guarantee_voids_over_budget` on the real weak-fair `G`). The consensus
engine `weakfair_terminates` is untouched; the top-level original is applied
verbatim. -/
theorem command_eventually_written_weakfair_budgeted {n : ℕ}
    (budget : FailureBudget)
    (hthreshold : budget.consumed ≤ budget.maxFaults)
    (hfairDelivery : budget.fairDelivery = true)
    (run : ℕ → Votes n Command) (correct : Finset (Fin n)) (c : Command)
    (hq : IsQuorum correct)
    (hhonest : ∀ k r, r ∈ correct → (run k) r ≠ none → (run k) r = some c)
    (hwf : budget.fairDelivery = true → WeakFair run correct c)
    (hmono : MonotoneVotes run)
    {init : Term} {log : CommittedLog} {i : Nat} (hi : i < log.length)
    (hci : log[i]? = some c)
    {r : Replica} (h0 : r.applied = 0) (hinv : AppliedPrefix init log r) :
    BudgetedGuarantee budget.maxFaults budget.consumed
      ((∃ k, Decided (run k) c) ∧
       (∃ m, ((deliver log)^[m] r).applied = i + 1 ∧
             ((deliver log)^[m] r).store = applyCommand c (applyPrefix init (log.take i)) ∧
             AppliedPrefix init log ((deliver log)^[m] r))) :=
  ⟨hthreshold,
   command_eventually_written_weakfair budget
     ((FailureBudget.withinContract_iff budget).mpr ⟨hthreshold, hfairDelivery⟩)
     run correct c hq hhonest hwf hmono hi hci h0 hinv⟩

/-- **The graded form loses nothing — `extract` recovers §5's conclusion.** Given
the threshold, the counit `BudgetedGuarantee.extract` on
`command_eventually_written_weakfair_budgeted` yields back the EXACT original
weak-fair `∃ k, Decided … ∧ ∃ m, applied …` guarantee. Faithful re-founding:
within budget the real liveness conclusion is fully recoverable. -/
theorem command_eventually_written_weakfair_budgeted_extract {n : ℕ}
    (budget : FailureBudget)
    (hthreshold : budget.consumed ≤ budget.maxFaults)
    (hfairDelivery : budget.fairDelivery = true)
    (run : ℕ → Votes n Command) (correct : Finset (Fin n)) (c : Command)
    (hq : IsQuorum correct)
    (hhonest : ∀ k r, r ∈ correct → (run k) r ≠ none → (run k) r = some c)
    (hwf : budget.fairDelivery = true → WeakFair run correct c)
    (hmono : MonotoneVotes run)
    {init : Term} {log : CommittedLog} {i : Nat} (hi : i < log.length)
    (hci : log[i]? = some c)
    {r : Replica} (h0 : r.applied = 0) (hinv : AppliedPrefix init log r) :
    (∃ k, Decided (run k) c) ∧
    (∃ m, ((deliver log)^[m] r).applied = i + 1 ∧
          ((deliver log)^[m] r).store = applyCommand c (applyPrefix init (log.take i)) ∧
          AppliedPrefix init log ((deliver log)^[m] r)) :=
  (command_eventually_written_weakfair_budgeted budget hthreshold hfairDelivery
    run correct c hq hhonest hwf hmono hi hci h0 hinv).extract

end DLCD
