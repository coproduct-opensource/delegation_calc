import DLCD.Termination
import DLCD.MultiDecree

/-! # DLC-D Phase 2.g — MULTI-DECREE LIVENESS (the committed log grows under fairness)

Phase 2.f (`DLCD.MultiDecree`) earned multi-decree **SAFETY**: any two replicas
that build their committed logs from the *same* per-slot ballots agree entry-by-
entry (`log_agreement`, `log_agreement_eq`) — Raft Log Matching / Multi-Paxos
per-slot agreement, obtained by *composing* single-decree safety. But safety is
silent about progress: nothing in 2.f asserts that any slot is ever decided or
that the log ever grows. This module supplies the matching **PROGRESS** property.

It **lifts** the Phase-2.a per-ballot termination theorem
`weakfair_terminates` (`WeakFair` + `MonotoneVotes` + majority quorum + honesty ⇒
`∃ k, Decided (sched k) v`) *across slots*: give each slot its own time-evolving
ballot, assume per-slot weak-fairness, and every slot is eventually `Decided`,
hence the committed log **grows without bound**. This is the standard "fair state
machine replication inherits liveness slot-by-slot from single-shot agreement"
construction (van Renesse–Altinbuken; Decentralized Thoughts single-shot→SMR).

## The lift (COMPOSE, do not re-prove termination)

- `SlotSchedule n := ℕ → ℕ → Votes n Command` — slot `i`, time `t` ↦ that slot's
  single-decree ballot `ss i t : Votes n Command`. Each slot carries its *own*
  evolving ballot (unlike 2.f's static `SlotBallots`, which is a *snapshot*).
- `slot_eventually_decided` — the core lift. For each slot `i`, `weakfair_terminates`
  is invoked **verbatim** on `ss i` to yield `∃ t, Decided (ss i t) (props i)`.
  Termination is NOT reproved: this file imports and applies the 2.a theorem per
  slot; the only new content is the quantifier lift over slots and the log fold.
- `log_grows_unbounded` — THE DELIVERABLE. For ANY target length `L`, there is a
  *snapshot* `sb : SlotBallots n` (each slot sampled at its own decision time) and
  a length-`L` committed log that is `LogConsistent sb` — every one of its `L`
  slots is `Decided`. Induction-free: we materialise the log `[props 0,…,props (L-1)]`
  and discharge consistency from the per-slot decisions. So the log grows to
  arbitrary length under fairness — progress, complementing 2.f's safety.

## How "eventually / growth" is formulated (honest fence)

The mandate is to pick the cleanest TRUE reachability statement. We give TWO,
both genuine (non-vacuously-quantified) reachability claims:

1. **`log_grows_unbounded`**: `∀ L, ∃ sb log, log.length = L ∧ LogConsistent sb log
   ∧ ∀ i < L, SlotDecided sb i (props i)`. The snapshot `sb i := ss i (t i)` is the
   ballot at slot `i`'s *actual* decision time `t i` (extracted by choice from the
   per-slot `∃ t`), so `sb` is a genuinely *reached* configuration, not an oracle.
2. **`log_decided_by_bounded_time`**: `∀ L, ∃ T, ∀ i < L, ∃ t ≤ T,
   Decided (ss i t) (props i)`. Taking `T` as the `Finset.sup` of the finitely-many
   per-slot decision times, ALL of the first `L` slots are decided by one finite
   time bound `T` — the honest "eventually, all of a finite prefix has decided".

`command_eventually_committed` (the optional strengthening) then puts a *proposed*
command at slot `i` into the committed log at position `i`, via the same per-slot
liveness plus the explicit prefix log.

## The right-reason bite — per-slot fairness is load-bearing for GROWTH

`starved_slot_stalls_growth` (namespace `StalledGrowth`): if ONE slot `i₀` is
starved — its ballot is the Command-lift of Phase-2.a's `WeakFairBite.starve`
(replica `0` perpetually enabled, never voting) — then slot `i₀` NEVER decides
(`no_decide_of_r0_none`, the only quorum of `Fin 2` contains the starved replica),
so NO `LogConsistent` log can carry an entry at position `i₀`: the committed log
`length ≤ i₀`. In prefix-ordered application (`Rsm.deliver` applies slot `i₀+1`
only after `i₀`; cf. the single-shot→SMR "array" rule *slot j+1 starts after slot
j reaches agreement*), growth **stalls at `i₀`**. And this is exactly a `WeakFair`
violation — `bite_composes_termination` pulls the FLP cause straight out of
`WeakFairBite.bite_needs_weakfair`. So per-slot weak-fairness is necessary for the
log to grow: drop it at one slot and the log freezes. FLP made concrete, per slot.

## Anti-vacuity — staggered per-slot decisions, real growth to length 2

`StaggeredWitness`: a concrete 2-slot schedule over `Fin 3` where slot `i`'s
ballot has replica `r` vote `cmd i` only from time `r + 3·i` onward (replicas
start *unvoted* and vote *later*, genuinely exercising `WeakFair`'s existential),
and the slots decide at **staggered** times — slot 0 already decided at `t = 2`
while slot 1 is *still undecided* at `t = 2` (`wit_slot1_undecided_at2`), only
deciding by `t = 5`. `wit_all_slots_eventually` drives both decisions *through*
`slot_eventually_decided → weakfair_terminates`, and the committed log grows to
length 2 with the **distinct** commands `cX ≠ cY`. Real stagger, real growth.

## Honest scope — what is FENCED
- This is multi-decree **LIVENESS** under **per-slot weak-fairness** (the `WF_vars`
  shape of 2.a) + **majority quorum**. Weak fairness is the standard, FLP-necessary
  scheduling assumption — its necessity is witnessed by the bite. Without it a slot
  starves forever (FLP) and the log cannot grow.
- **LEADER ELECTION is still deferred** (as in 2.f). Liveness here is per-slot and
  assumes each slot's honest replicas eventually vote its proposal; who proposes
  (leader) and dueling-proposer termination are orthogonal and not modelled.
- Slots are independent decrees; cross-slot *ordering* of application is
  `Rsm.applyPrefix` (already proved) — the bite leans on that prefix order to turn
  "slot `i₀` never decides" into "the applied log stalls at length `i₀`".
- Complementary to 2.f: 2.f = SAFETY (≤1 value per slot, logs match); 2.g = PROGRESS
  (every slot eventually decides, log grows). Neither implies the other.

## Prior art (web-searched 2026-07-22; URLs recorded)
- van Renesse–Altinbuken, *Paxos Made Moderately Complex* — per-slot liveness:
  "if one or more commands have been proposed for a particular slot, some command
  is eventually decided for that slot"; retransmission + `f+1` replicas:
  https://www.cs.cornell.edu/home/rvr/Paxos/paxos.pdf
- Decentralized Thoughts, *From Single-Shot Agreement to State Machine Replication*
  — SMR = an array of single-shot agreement instances, one per slot; the array
  rule "once position `j` reaches agreement, servers start position `j+1`" is the
  prefix-ordered growth the bite exploits:
  https://decentralizedthoughts.github.io/2022-11-19-from-single-shot-to-smr/
- Decentralized Thoughts, *Distributed consensus made simple (for real this time)*
  — termination under fairness/eventual synchrony:
  https://decentralizedthoughts.github.io/2021-09-30-distributed-consensus-made-simple-for-real-this-time/
- Decentralized Thoughts, *Consensus for State Machine Replication* — single-decree
  per slot; prefix completeness ⇒ shared identical prefixes:
  https://decentralizedthoughts.github.io/2019-10-15-consensus-for-state-machine-replication/
- BBCA-LEDGER — "Totality" (if a correct validator decides a slot, all correct
  validators eventually decide that slot): https://arxiv.org/pdf/2306.14757
- Spiegelman et al., *ACE: Abstract Consensus Encapsulation for Liveness Boosting
  of SMR* — composing single-shot agreement per slot into multi-shot SMR liveness:
  https://arxiv.org/pdf/1911.10486
- FLP (Fischer–Lynch–Paterson 1985) — async + 1 crash ⇒ no deterministic
  consensus ⇒ a fairness assumption is mandatory (the bite's necessity).
-/

namespace DLCD

open DLC

/-! ## 0. Small quorum-emptiness facts used by the bite and the witness. -/

/-- If EVERY replica abstains (`b r = none`), nothing is decided: any quorum is
nonempty (`quorum_intersect Q Q`), and that replica cannot have voted. -/
theorem no_decide_of_all_none {n : ℕ} {V : Type*} {b : Votes n V}
    (h : ∀ r, b r = none) (c : V) : ¬ Decided b c := by
  rintro ⟨Q, hQ, hv⟩
  obtain ⟨r, hr⟩ := quorum_intersect hQ hQ
  rw [Finset.mem_inter] at hr
  have hvr := hv r hr.1
  rw [h r] at hvr
  exact absurd hvr (by simp)

/-- Over `Fin 2` the ONLY quorum is the whole set, which contains replica `0`; so
if replica `0` abstains (`b 0 = none`), nothing is decided. This is the per-slot
core of Phase-2.a's `WeakFairBite.starve_never_decides`, stated generically. -/
theorem no_decide_of_r0_none {V : Type*} {b : Votes 2 V}
    (h0 : b 0 = none) (c : V) : ¬ Decided b c := by
  rintro ⟨Q, hQ, hv⟩
  have hle : Q.card ≤ 2 := by
    have := Finset.card_le_card (Finset.subset_univ Q)
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have hgt : 2 * Q.card > 2 := hQ
  have hcard2 : Q.card = 2 := by omega
  have huniv : Q = Finset.univ :=
    Finset.eq_univ_of_card Q (by rw [Fintype.card_fin]; exact hcard2)
  have h0Q : (0 : Fin 2) ∈ Q := huniv ▸ Finset.mem_univ 0
  have hvr := hv 0 h0Q
  rw [h0] at hvr
  exact absurd hvr (by simp)

/-! ## 1. Multi-decree schedules — one time-evolving ballot per slot. -/

section SlotLift

variable {n : ℕ}

/-- **A multi-decree schedule.** Slot `i`, time `t` ↦ that slot's single-decree
ballot `ss i t : Votes n Command`. Each slot has its own *evolving* ballot; this
is the time-indexed refinement of 2.f's static snapshot `SlotBallots`. -/
abbrev SlotSchedule (n : ℕ) := ℕ → ℕ → Votes n Command

/-- The **explicit committed log** of the first `L` proposals `[props 0, …,
props (L-1)]`. Its entry at slot `i` (for `i < L`) is exactly `props i`. -/
def logProps (props : ℕ → Command) (L : ℕ) : CommittedLog :=
  (List.range L).map props

/-- The entry of `logProps` at slot `i`: `some (props i)` when `i < L`. -/
theorem logProps_getElem? (props : ℕ → Command) (L i : ℕ) :
    (logProps props L)[i]? = if i < L then some (props i) else none := by
  by_cases h : i < L
  · rw [if_pos h]
    have hi : i < (logProps props L).length := by
      unfold logProps; rw [List.length_map, List.length_range]; exact h
    rw [List.getElem?_eq_getElem hi]
    congr 1
    unfold logProps
    rw [List.getElem_map, List.getElem_range]
  · rw [if_neg h]
    apply List.getElem?_eq_none
    unfold logProps; rw [List.length_map, List.length_range]; omega

theorem logProps_length (props : ℕ → Command) (L : ℕ) :
    (logProps props L).length = L := by
  unfold logProps; rw [List.length_map, List.length_range]

/-! ## 2. PER-SLOT LIVENESS — the core lift of `weakfair_terminates`. -/

/-- **PER-SLOT LIVENESS.** Under per-slot weak-fairness (each slot's ballot is
`WeakFair` + `MonotoneVotes` + honest toward its proposal) and a majority quorum,
EVERY slot is eventually `Decided`. Proof: for each slot `i`, apply the Phase-2.a
theorem `weakfair_terminates` **verbatim** to the ballot `ss i`. Termination is
not reproved — it is *composed* per slot. -/
theorem slot_eventually_decided (ss : SlotSchedule n) (Q : Finset (Fin n))
    (props : ℕ → Command)
    (hlive : ∀ i, WeakFair (ss i) Q (props i) ∧ MonotoneVotes (ss i) ∧
      (∀ k r, r ∈ Q → (ss i) k r ≠ none → (ss i) k r = some (props i)))
    (hq : IsQuorum Q) :
    ∀ i, ∃ t, Decided (ss i t) (props i) := by
  intro i
  obtain ⟨hwf, hmono, hhonest⟩ := hlive i
  exact weakfair_terminates (ss i) Q (props i) hwf hmono hq hhonest

/-! ## 3. THE LOG-GROWTH THEOREM — every prefix eventually decides ⇒ log grows. -/

/-- **THE DELIVERABLE — the committed log grows without bound under fairness.**
For ANY target length `L`, there is a snapshot `sb` (each slot sampled at its own
decision time) and a length-`L` committed log `logProps props L`, `LogConsistent`
with `sb`, all of whose `L` slots are `Decided`. This is genuine reachability: the
snapshot `sb i := ss i (t i)` uses slot `i`'s *actual* decision time. Progress —
the log-growth complement to 2.f's log-matching safety. -/
theorem log_grows_unbounded (ss : SlotSchedule n) (Q : Finset (Fin n))
    (props : ℕ → Command)
    (hlive : ∀ i, WeakFair (ss i) Q (props i) ∧ MonotoneVotes (ss i) ∧
      (∀ k r, r ∈ Q → (ss i) k r ≠ none → (ss i) k r = some (props i)))
    (hq : IsQuorum Q) :
    ∀ L, ∃ (sb : SlotBallots n) (log : CommittedLog),
      log.length = L ∧ LogConsistent sb log ∧ ∀ i, i < L → SlotDecided sb i (props i) := by
  have hdec : ∀ i, ∃ t, Decided (ss i t) (props i) :=
    slot_eventually_decided ss Q props hlive hq
  choose t ht using hdec
  intro L
  refine ⟨fun i => ss i (t i), logProps props L, logProps_length props L, ?_, ?_⟩
  · intro i c hc
    rw [logProps_getElem?] at hc
    by_cases hi : i < L
    · rw [if_pos hi, Option.some.injEq] at hc
      rw [← hc]
      exact ht i
    · rw [if_neg hi] at hc; exact absurd hc (by simp)
  · intro i _; exact ht i

/-- **BOUNDED-TIME GROWTH — the honest "eventually".** For ANY `L`, there is one
finite time bound `T` (the `Finset.sup` of the first `L` decision times) by which
ALL of the first `L` slots are decided. So "eventually, an `L`-slot prefix has
committed" is a real finite-reachability claim, not a bare `∀`. -/
theorem log_decided_by_bounded_time (ss : SlotSchedule n) (Q : Finset (Fin n))
    (props : ℕ → Command)
    (hlive : ∀ i, WeakFair (ss i) Q (props i) ∧ MonotoneVotes (ss i) ∧
      (∀ k r, r ∈ Q → (ss i) k r ≠ none → (ss i) k r = some (props i)))
    (hq : IsQuorum Q) :
    ∀ L, ∃ T, ∀ i, i < L → ∃ t, t ≤ T ∧ Decided (ss i t) (props i) := by
  have hdec : ∀ i, ∃ t, Decided (ss i t) (props i) :=
    slot_eventually_decided ss Q props hlive hq
  choose t ht using hdec
  intro L
  refine ⟨(Finset.range L).sup t, ?_⟩
  intro i hi
  exact ⟨t i, Finset.le_sup (Finset.mem_range.2 hi), ht i⟩

/-- **A proposed command is eventually committed at its slot.** Under per-slot
liveness, the proposal `props i` sits at position `i` of a committed log that is
`LogConsistent` with the decision-time snapshot, and slot `i` really decided it.
Ties per-slot liveness to prefix application (`logProps` is the committed prefix). -/
theorem command_eventually_committed (ss : SlotSchedule n) (Q : Finset (Fin n))
    (props : ℕ → Command)
    (hlive : ∀ i, WeakFair (ss i) Q (props i) ∧ MonotoneVotes (ss i) ∧
      (∀ k r, r ∈ Q → (ss i) k r ≠ none → (ss i) k r = some (props i)))
    (hq : IsQuorum Q) (i : ℕ) :
    ∃ (sb : SlotBallots n),
      LogConsistent sb (logProps props (i + 1)) ∧
      (logProps props (i + 1))[i]? = some (props i) ∧
      SlotDecided sb i (props i) := by
  have hdec : ∀ j, ∃ t, Decided (ss j t) (props j) :=
    slot_eventually_decided ss Q props hlive hq
  choose t ht using hdec
  refine ⟨fun j => ss j (t j), ?_, ?_, ht i⟩
  · intro j c hc
    rw [logProps_getElem?] at hc
    by_cases hj : j < i + 1
    · rw [if_pos hj, Option.some.injEq] at hc; rw [← hc]; exact ht j
    · rw [if_neg hj] at hc; exact absurd hc (by simp)
  · rw [logProps_getElem?, if_pos (Nat.lt_succ_self i)]

end SlotLift

/-! ## 4. THE RIGHT-REASON BITE — a starved slot stalls log growth. -/

namespace StalledGrowth

/-- A concrete Command used by the starved / decided slots. -/
def someCmd : Command := { payload := Term.var 0 }

/-- `Fin 2`'s only quorum is the whole set. -/
theorem fin2_univ_quorum : IsQuorum (Finset.univ : Finset (Fin 2)) := by
  unfold IsQuorum; decide

/-- **The Command-lift of Phase-2.a's starved schedule.** We MAP the ℕ-valued
`WeakFairBite.starve` (replica `0` perpetually enabled, replica `1` votes) onto
`Command`: replica `0` still abstains at every time. This is exactly the FLP
starvation of 2.a, transported to the multi-decree log's value type. -/
def ssStarved : ℕ → Votes 2 Command :=
  fun t r => (WeakFairBite.starve t r).map (fun _ => someCmd)

/-- Replica `0` abstains at every time — inherited from `starve_r0_enabled`
(genuine composition of the 2.a bite fact). -/
theorem ssStarved_r0 (t : ℕ) : ssStarved t 0 = none := by
  unfold ssStarved
  rw [WeakFairBite.starve_r0_enabled t]
  rfl

/-- The starved slot NEVER decides (only quorum of `Fin 2` contains the abstainer). -/
theorem ssStarved_never_decides (t : ℕ) (c : Command) : ¬ Decided (ssStarved t) c :=
  no_decide_of_r0_none (ssStarved_r0 t) c

/-- The starved slot violates `WeakFair`: the enabled replica `0` never votes. -/
theorem ssStarved_not_weakfair (c : Command) :
    ¬ WeakFair ssStarved WeakFairBite.Qc c := by
  intro hwf
  obtain ⟨k', -, hk'⟩ := hwf 0 0 (by decide) (ssStarved_r0 0)
  rw [ssStarved_r0 k'] at hk'
  simp at hk'

/-- **The FLP cause, pulled straight from 2.a.** `bite_needs_weakfair` is invoked
to expose that the underlying `starve` schedule (a) keeps replica `0` perpetually
enabled and (b) violates `WeakFair` — the very starvation `ssStarved` lifts. So
the stall below is *caused by* the composed 2.a bite, not a fresh phenomenon. -/
theorem bite_composes_termination :
    (∀ k, WeakFairBite.starve k 0 = none) ∧
    (∀ v : ℕ, ¬ WeakFair WeakFairBite.starve WeakFairBite.Qc v) :=
  ⟨WeakFairBite.bite_needs_weakfair.1, WeakFairBite.bite_needs_weakfair.2.2.2⟩

/-- **The stalling snapshot ballots.** Slots `< i₀` are unanimously `someCmd`
(hence decidable); slot `i₀` and beyond are the starved ballot. Growth reaches
`i₀` and then freezes. -/
def sbStall (i₀ : ℕ) : SlotBallots 2 :=
  fun i => if i < i₀ then (fun _ => some someCmd) else ssStarved 0

/-- Slot `i₀` never decides under `sbStall`. -/
theorem sbStall_slot_undecided (i₀ : ℕ) (c : Command) :
    ¬ SlotDecided (sbStall i₀) i₀ c := by
  unfold SlotDecided sbStall
  rw [if_neg (Nat.lt_irrefl i₀)]
  exact ssStarved_never_decides 0 c

/-- **THE STALL.** No `LogConsistent` log can grow past `i₀`: an entry at position
`i₀` would have to be `SlotDecided`, which slot `i₀` never is. So `length ≤ i₀`. -/
theorem sbStall_bounds_log (i₀ : ℕ) (log : CommittedLog)
    (h : LogConsistent (sbStall i₀) log) : log.length ≤ i₀ := by
  by_contra hlt
  have hlt' : i₀ < log.length := Nat.lt_of_not_le hlt
  have hget : log[i₀]? = some log[i₀] := List.getElem?_eq_getElem hlt'
  exact sbStall_slot_undecided i₀ log[i₀] (h i₀ log[i₀] hget)

/-- **Growth genuinely REACHES `i₀`.** The length-`i₀` log `[someCmd, …]` is
`LogConsistent` with `sbStall i₀` (each slot `< i₀` decides `someCmd` via the full
quorum). So the stall is a real halt at `i₀`, not vacuous length `0`. -/
theorem sbStall_reaches_i0 (i₀ : ℕ) :
    LogConsistent (sbStall i₀) (logProps (fun _ => someCmd) i₀) ∧
    (logProps (fun _ => someCmd) i₀).length = i₀ := by
  refine ⟨?_, logProps_length _ i₀⟩
  intro i c hc
  rw [logProps_getElem?] at hc
  by_cases hi : i < i₀
  · rw [if_pos hi, Option.some.injEq] at hc
    rw [← hc]
    unfold SlotDecided sbStall
    rw [if_pos hi]
    exact ⟨Finset.univ, fin2_univ_quorum, by intro r _; rfl⟩
  · rw [if_neg hi] at hc; exact absurd hc (by simp)

/-- **THE BITE — per-slot weak-fairness is load-bearing for log GROWTH.** If slot
`i₀`'s ballot is the starved (FLP) ballot, then: (a) slot `i₀` NEVER decides;
(b) every `LogConsistent` log has `length ≤ i₀` — the committed prefix cannot grow
past the starved slot (prefix-ordered application: slot `i₀+1` applies only after
`i₀`); (c) yet growth genuinely reaches length `i₀` (real halt, not vacuous); and
(d) the cause is a `WeakFair` violation, composed from 2.a's `bite_needs_weakfair`.
Drop per-slot weak-fairness at one slot and the log freezes there forever. -/
theorem starved_slot_stalls_growth (i₀ : ℕ) :
    ∃ (sb : SlotBallots 2),
      (∀ c, ¬ SlotDecided sb i₀ c) ∧
      (∀ log : CommittedLog, LogConsistent sb log → log.length ≤ i₀) ∧
      (LogConsistent sb (logProps (fun _ => someCmd) i₀) ∧
        (logProps (fun _ => someCmd) i₀).length = i₀) ∧
      (∀ c : Command, ¬ WeakFair ssStarved WeakFairBite.Qc c) :=
  ⟨sbStall i₀, sbStall_slot_undecided i₀, sbStall_bounds_log i₀,
   sbStall_reaches_i0 i₀, ssStarved_not_weakfair⟩

end StalledGrowth

/-! ## 5. ANTI-VACUITY — a staggered 2-slot schedule; the log grows to length 2. -/

namespace StaggeredWitness

/-- Three replicas; the whole set is a strict majority (`2·3 > 3`). -/
abbrev N : ℕ := 3

/-- Slot-0 command. -/
def cX : Command := { payload := Term.var 0 }
/-- Slot-1 command — genuinely distinct from `cX`. -/
def cY : Command := { payload := Term.var 1 }

/-- `cX ≠ cY` (distinct payloads) — the grown log is non-trivial. -/
theorem cX_ne_cY : cX ≠ cY := by
  intro h
  have hp : cX.payload = cY.payload := congrArg Command.payload h
  simp [cX, cY] at hp

/-- The per-slot proposal: slot 0 proposes `cX`, every other slot `cY`. -/
def cmd (i : ℕ) : Command := if i = 0 then cX else cY

/-- The whole population quorum. -/
def Qc : Finset (Fin N) := Finset.univ

theorem Qc_quorum : IsQuorum Qc := by unfold IsQuorum Qc; decide

/-- **The staggered schedule.** In slot `i`, replica `r` votes `cmd i` only from
time `r + 3·i` onward and abstains before that. So replicas start *unvoted* and
vote *later* (exercising `WeakFair`'s existential), and slot `i`'s decision window
is offset by `3·i` — later slots decide strictly later. -/
def wit : SlotSchedule N := fun i t r => if (r : ℕ) + 3 * i ≤ t then some (cmd i) else none

/-- Each slot's ballot is `WeakFair`: an enabled replica `r` (with `r+3i > t`)
votes at the strictly-later step `r + 3i`. The existential is really used. -/
theorem wit_weakfair (i : ℕ) : WeakFair (wit i) Qc (cmd i) := by
  intro k r _ hnone
  simp only [wit] at hnone
  by_cases h : (r : ℕ) + 3 * i ≤ k
  · rw [if_pos h] at hnone; exact absurd hnone (by simp)
  · refine ⟨(r : ℕ) + 3 * i, by omega, ?_⟩
    simp only [wit]; rw [if_pos (le_refl _)]

/-- Each slot's ballot is non-retracting. -/
theorem wit_monotone (i : ℕ) : MonotoneVotes (wit i) := by
  intro k r x h
  simp only [wit] at h ⊢
  by_cases h' : (r : ℕ) + 3 * i ≤ k
  · rw [if_pos h'] at h; rw [if_pos (by omega : (r : ℕ) + 3 * i ≤ k + 1)]; exact h
  · rw [if_neg h'] at h; simp at h

/-- Honesty: every vote slot `i` ever casts is `some (cmd i)`. -/
theorem wit_honest (i : ℕ) :
    ∀ k r, r ∈ Qc → wit i k r ≠ none → wit i k r = some (cmd i) := by
  intro k r _ hne
  simp only [wit] at hne ⊢
  by_cases h : (r : ℕ) + 3 * i ≤ k
  · rw [if_pos h]
  · rw [if_neg h] at hne; exact absurd rfl hne

/-- The per-slot liveness hypothesis bundle for `wit`. -/
theorem wit_hlive : ∀ i, WeakFair (wit i) Qc (cmd i) ∧ MonotoneVotes (wit i) ∧
    (∀ k r, r ∈ Qc → wit i k r ≠ none → wit i k r = some (cmd i)) :=
  fun i => ⟨wit_weakfair i, wit_monotone i, wit_honest i⟩

/-- **Every slot is eventually decided — THROUGH the pipeline.** This calls
`slot_eventually_decided`, which invokes `weakfair_terminates` per slot: a genuine
composition, not a hand-rolled decision. -/
theorem wit_all_slots_eventually : ∀ i, ∃ t, Decided (wit i t) (cmd i) :=
  slot_eventually_decided wit Qc cmd wit_hlive Qc_quorum

/-- Slot 0 is decided by time `2` (all of `{0,1,2}` have `r ≤ 2 = r + 0`). -/
theorem wit_slot0_decided : Decided (wit 0 2) cX := by
  refine ⟨Finset.univ, Qc_quorum, ?_⟩
  intro r _
  have hlt : (r : ℕ) < 3 := r.isLt
  show (if (r : ℕ) + 3 * 0 ≤ 2 then some (cmd 0) else none) = some cX
  rw [if_pos (by omega)]
  rfl

/-- **Genuine stagger:** at time `2`, when slot 0 is *already decided*, slot 1 is
STILL undecided — every replica abstains (`r + 3 > 2`). Slot 1 lags slot 0. -/
theorem wit_slot1_undecided_at2 : ¬ Decided (wit 1 2) cY := by
  apply no_decide_of_all_none
  intro r
  show (if (r : ℕ) + 3 * 1 ≤ 2 then some (cmd 1) else none) = none
  rw [if_neg (by omega)]

/-- Slot 1 IS decided by time `5` (`r + 3 ≤ 5` for all `r ≤ 2`) — later than slot 0. -/
theorem wit_slot1_decided : Decided (wit 1 5) cY := by
  refine ⟨Finset.univ, Qc_quorum, ?_⟩
  intro r _
  have hlt : (r : ℕ) < 3 := r.isLt
  show (if (r : ℕ) + 3 * 1 ≤ 5 then some (cmd 1) else none) = some cY
  rw [if_pos (by omega)]
  rfl

/-- The staggered decision-time snapshot: slot 0 at `t = 2`, slot 1 at `t = 5`. -/
def witSb : SlotBallots N := fun i => if i = 0 then wit 0 2 else wit 1 5

/-- **The committed log grows to length 2 with distinct commands.** `[cX, cY]` is
`LogConsistent` with the staggered snapshot — slot 0 (decided at `t = 2`) and
slot 1 (decided at `t = 5`) both carry real majority decisions — and `cX ≠ cY`. -/
theorem wit_log_grows :
    ([cX, cY] : CommittedLog).length = 2 ∧
    LogConsistent witSb [cX, cY] ∧ cX ≠ cY := by
  refine ⟨rfl, ?_, cX_ne_cY⟩
  intro i c hc
  rcases i with _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc
    show Decided (witSb 0) cX
    simp only [witSb, if_pos]
    exact wit_slot0_decided
  · rcases i with _ | i
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      show Decided (witSb 1) cY
      simp only [witSb]
      rw [if_neg (by decide : ¬ (1 : ℕ) = 0)]
      exact wit_slot1_decided
    · simp at hc

/-- **The deliverable, instantiated on the witness.** `log_grows_unbounded`
applied to `wit`: for every `L`, a length-`L` consistent log with all slots
decided — real, non-vacuous log growth driven by the staggered schedule. -/
theorem wit_log_grows_unbounded :
    ∀ L, ∃ (sb : SlotBallots N) (log : CommittedLog),
      log.length = L ∧ LogConsistent sb log ∧ ∀ i, i < L → SlotDecided sb i (cmd i) :=
  log_grows_unbounded wit Qc cmd wit_hlive Qc_quorum

end StaggeredWitness

end DLCD
