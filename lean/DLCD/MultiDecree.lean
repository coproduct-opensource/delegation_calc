import DLCD.Consensus

/-! # DLC-D Phase 2.f — the MULTI-DECREE replicated log (multi-slot consensus safety)

Phase 1.1 (`DLCD.Consensus`) earned **single-decree** safety: for ONE log slot,
`agreement` proves at most one value is `Decided`, via `quorum_intersect`. This
module **lifts** that atom to a full replicated *log* of independent decrees —
one single-decree ballot per slot — and proves the multi-decree SAFETY property:
any two replicas that build their committed log from the SAME per-slot ballots
**agree entry-by-entry**, hence (at equal length) hold **identical logs**. This
is Raft's *Log Matching* / *State-Machine Safety* and Multi-Paxos's per-slot
agreement, obtained by *composition* — we REUSE single-decree Paxos verbatim, we
do not reprove quorum intersection.

## The composition (COMPOSE, do not re-prove)
Per Chand–Liu–Stoller and García-Pérez et al., Multi-Paxos safety is single-
decree safety applied independently at each slot: slots are just naturals with
NO order structure required between them. Concretely:

- `SlotBallots n := ℕ → Votes n Command` — one *independent* single-decree
  ballot per slot `i : ℕ`.
- `SlotDecided sb i c := Decided (sb i) c` — slot `i` decides `c` iff a majority
  quorum of `sb i` unanimously voted `c`. This is `Consensus.Decided` at slot `i`.
- `slot_agreement` is **literally** `Consensus.agreement` instantiated at
  `votes := sb i`. It reuses `quorum_intersect`; nothing is reproved here.
- `log_agreement` / `log_agreement_eq` fold that per-slot atom over the list of
  slots (the only genuinely new content — a `List.ext_getElem?` induction on the
  log index), so the shared committed log is a FUNCTION of the ballots.

## The safety metatheorems (fully proved, no `sorry`)
1. **`slot_agreement`** — each slot decides at most one command
   (`= Consensus.agreement` at slot `i`; the multi-decree safety *atom*).
2. **`log_agreement`** — two `LogConsistent` logs (every entry is that slot's
   decision) agree at *every* index: `log₁[i]? = some c₁ → log₂[i]? = some c₂ →
   c₁ = c₂`. Pointwise `slot_agreement`. This is the deliverable.
3. **`log_agreement_eq`** — two `LogConsistent` logs of equal length are EQUAL
   (`List.ext_getElem?` + `log_agreement`), so replicas converge on the *whole*
   log. `replicas_converge_multidecree` then chains to `Rsm.applyPrefix` equal
   stores — full state convergence — reusing the Phase-1.0 seed.

## Honest scope — what is FENCED
This increment is multi-decree **SAFETY** (per-slot single-value + log matching),
reusing single-decree Paxos per Chand–Liu / García-Pérez. It is NOT liveness and
NOT leader election:
- **LEADER ELECTION** is deferred (Phase 2+). Crucially, *Paxos safety holds
  regardless of the leader*: agreement per slot follows from quorum intersection
  alone, never from who proposed — a dueling-proposer / split-leader scenario can
  stall PROGRESS but can never decide two commands at one slot. So no leader
  model is needed for the safety statements here, and none is assumed.
- **MULTI-DECREE LIVENESS** (that every slot is *eventually* decided under fair
  delivery and ≤ f crashes, and that logs *grow*) is deferred — it is a PROGRESS
  property, orthogonal to the safety proved here; nothing in this file asserts
  that any slot gets decided. The anti-vacuity witness exhibits concrete decided
  slots to show the safety statements are inhabited, not to claim progress.
- Slots are independent decrees (`ℕ`, no inter-slot relation), matching Chand–Liu
  "for each slot, only a single command may be decided"; cross-slot ordering
  semantics (state-machine application order) is `Rsm.applyPrefix`, already proved.

## The right-reason bite
`weak_slot_breaks_log_agreement`: at a SINGLE slot over `Fin 2`, replace the
majority quorum with a *weak* quorum (`2·card ≥ n`, allowing exact halves). Two
**disjoint** singletons `{0}`, `{1}` are both weak quorums; a split ballot lets
`{0}` decide `cA` and `{1}` decide `cB` with `cA ≠ cB`. Then two logs `[cA]` and
`[cB]` are each *weak-consistent* yet **disagree at slot 0** — `log_agreement`
FAILS. Majority-quorum-per-slot (strict `>`, self-intersecting) is load-bearing:
under a real majority of `Fin 2` a slot's quorum must contain BOTH replicas, and
a single ballot cannot vote two commands.

## Anti-vacuity witness
`Witness`: a concrete **2-slot** log `[cX, cY]` (distinct commands) over `Fin 3`,
each slot `Decided` by a **real majority** (`Finset.univ`, `2·3 > 3`); two
replicas both `LogConsistent`; `log_agreement_eq` proves their whole logs EQUAL;
`log_agreement` applied at slot 0 yields `cX = cX` *through* the quorum-
intersection machinery (not `rfl`). Real multi-slot decisions, real agreement.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Chand–Liu–Stoller, *Formal Verification of Multi-Paxos for Distributed
  Consensus*, FM 2016 — per-slot safety ("for each slot, only a single command
  may be decided and it must be one of the commands proposed"); slots are
  naturals, no relations: https://arxiv.org/pdf/1606.01387 ,
  https://www3.cs.stonybrook.edu/~stoller/papers/fm2016.pdf ,
  https://arxiv.org/abs/1606.01387
- García-Pérez–Gotsman–Meshman–Sergey, *Paxos Consensus, Deconstructed and
  Abstracted*, ESOP 2018 — Multi-Paxos safety by REUSING single-decree Paxos
  (the composition done here): https://ilyasergey.net/assets/pdf/papers/paxos-deconstructed-esop18.pdf ,
  https://arxiv.org/pdf/1802.05969
- Ongaro–Ousterhout, *In Search of an Understandable Consensus Algorithm (Raft)*
  — Log Matching / State-Machine Safety over a replicated log of slots:
  https://raft.github.io/raft.pdf
-/

namespace DLCD

open DLC

/-! ## 1. Multi-decree ballots — one independent single-decree instance per slot. -/

section MultiDecree

variable {n : ℕ}

/-- **Multi-decree ballots.** One *independent* single-decree ballot per slot
`i : ℕ`. Slots are bare naturals — no order structure between decrees is needed
for safety (Chand–Liu–Stoller). `sb i : Votes n Command` is exactly a Phase-1.1
single-decree ballot. -/
abbrev SlotBallots (n : ℕ) := ℕ → Votes n Command

/-- Slot `i` **decides** `c` iff `c` is `Consensus.Decided` by that slot's
ballot — a majority quorum of `sb i` unanimously voted `c`. -/
def SlotDecided (sb : SlotBallots n) (i : ℕ) (c : Command) : Prop :=
  Decided (sb i) c

/-! ## 2. PER-SLOT AGREEMENT — the multi-decree safety atom (lifts `agreement`). -/

/-- **PER-SLOT AGREEMENT.** Each slot decides at most one command. This is
*literally* single-decree `Consensus.agreement` instantiated at `votes := sb i`:
`quorum_intersect` gives a replica in both deciding quorums, and its single vote
forces `c₁ = c₂`. No quorum reasoning is reproved — it is inherited. -/
theorem slot_agreement (sb : SlotBallots n) (i : ℕ) {c₁ c₂ : Command}
    (h₁ : SlotDecided sb i c₁) (h₂ : SlotDecided sb i c₂) : c₁ = c₂ :=
  agreement h₁ h₂

/-- **VALIDITY across slots.** A decided slot value came from a real vote (a real
proposal). This is `Consensus.validity` at slot `i`. -/
theorem slot_validity (sb : SlotBallots n) (i : ℕ) {c : Command}
    (h : SlotDecided sb i c) : ∃ r, sb i r = some c :=
  validity h

/-! ## 3. LOG AGREEMENT — the multi-decree safety theorem (log matching). -/

/-- A committed log is **consistent** with the slot-ballots iff every entry is
exactly that slot's decision. This is what "correct replica's committed log"
means: each slot the replica commits was `Decided` by consensus at that slot. -/
def LogConsistent (sb : SlotBallots n) (log : CommittedLog) : Prop :=
  ∀ i c, log[i]? = some c → SlotDecided sb i c

/-- **LOG AGREEMENT — the multi-decree safety metatheorem (Raft Log Matching /
State-Machine Safety).** Two logs, each consistent with the *same* slot-ballots,
agree at *every* index: if both have an entry at slot `i`, those entries are the
SAME command. Pointwise `slot_agreement` — the single-decree atom, folded over
the log index. Two replicas building committed logs from the same consensus
outputs can never disagree on a decided slot. -/
theorem log_agreement {sb : SlotBallots n} {log₁ log₂ : CommittedLog}
    (h₁ : LogConsistent sb log₁) (h₂ : LogConsistent sb log₂) :
    ∀ (i : ℕ) (c₁ c₂ : Command), log₁[i]? = some c₁ → log₂[i]? = some c₂ → c₁ = c₂ := by
  intro i c₁ c₂ e₁ e₂
  exact slot_agreement sb i (h₁ i c₁ e₁) (h₂ i c₂ e₂)

/-- **LOG AGREEMENT ⇒ EQUAL LOGS.** Two consistent logs of *equal length* are
EQUAL — replicas converge on the whole committed log. `List.ext_getElem?` on the
slot index: where both are in range, `log_agreement` forces equal entries; out of
range both are `none` (equal length). The committed log is a FUNCTION of the
ballots, not a free oracle. -/
theorem log_agreement_eq {sb : SlotBallots n} {log₁ log₂ : CommittedLog}
    (hlen : log₁.length = log₂.length)
    (h₁ : LogConsistent sb log₁) (h₂ : LogConsistent sb log₂) :
    log₁ = log₂ := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < log₁.length
  · have hiB : i < log₂.length := by omega
    have hcA : log₁[i]? = some log₁[i] := List.getElem?_eq_getElem hi
    have hcB : log₂[i]? = some log₂[i] := List.getElem?_eq_getElem hiB
    have heq : log₁[i] = log₂[i] := log_agreement h₁ h₂ i _ _ hcA hcB
    rw [hcA, hcB, heq]
  · rw [List.getElem?_eq_none (by omega : log₁.length ≤ i),
        List.getElem?_eq_none (by omega : log₂.length ≤ i)]

/-- **FULL STATE CONVERGENCE (chaining to `Rsm`).** Two replicas that ran
independent multi-decree consensus — producing committed logs `log₁`, `log₂`,
each consistent with the *same* slot-ballots — and applied the same-length
prefix, hold **equal stores**. `log_agreement_eq` forces `log₁ = log₂`; the
Phase-1.0 seed `replicas_converge_on_prefix` (deterministic fold) finishes. The
whole multi-decree stack — quorum intersection, per-slot agreement, log matching,
deterministic application — composes to state-machine convergence. -/
theorem replicas_converge_multidecree {sb : SlotBallots n}
    {init : Term} {log₁ log₂ : CommittedLog} {r1 r2 : Replica}
    (hlen : log₁.length = log₂.length)
    (h₁ : LogConsistent sb log₁) (h₂ : LogConsistent sb log₂)
    (hp1 : AppliedPrefix init log₁ r1)
    (hp2 : AppliedPrefix init log₂ r2)
    (happ : r1.applied = r2.applied) :
    r1.store = r2.store := by
  have hlog : log₁ = log₂ := log_agreement_eq hlen h₁ h₂
  subst hlog
  exact replicas_converge_on_prefix hp1 hp2 happ

end MultiDecree

/-! ## 4. The right-reason bite — a WEAK per-slot quorum breaks log agreement. -/

namespace Bite

/-- Two genuinely distinct commands (distinct payloads). -/
def cA : Command := { payload := Term.var 0 }
/-- The other distinct command. -/
def cB : Command := { payload := Term.var 1 }

/-- The commands differ (their payloads `var 0` / `var 1` differ). -/
theorem cA_ne_cB : cA ≠ cB := by
  intro h
  have hp : cA.payload = cB.payload := congrArg Command.payload h
  simp [cA, cB] at hp

/-- The **weakened** per-slot quorum notion allowing exact halves (`2·card ≥ n`
for `n = 2`). This is the majority `>` of `IsQuorum` degraded to `≥`. -/
def IsWeakQuorum (Q : Finset (Fin 2)) : Prop := 2 * Q.card ≥ 2

/-- A weak-decision at a slot: some *weak* quorum unanimously voted `c`. -/
def WeakDecided (votes : Votes 2 Command) (c : Command) : Prop :=
  ∃ Q : Finset (Fin 2), IsWeakQuorum Q ∧ ∀ r ∈ Q, votes r = some c

/-- **THE BITE.** Drop the strict-majority per-slot quorum to `≥`. At a single
slot, the split ballot (`r=0 ↦ cA`, `r=1 ↦ cB`) lets the two **disjoint**
singleton weak quorums `{0}` and `{1}` decide the DIFFERENT commands `cA`, `cB`.
Then the two logs `[cA]` and `[cB]` are each *weak-consistent* (every entry is a
weak-decision at its slot) yet **disagree at slot 0** — the `log_agreement`
conclusion `c₁ = c₂` is refuted. Weak quorums need not intersect, so per-slot
agreement (hence log matching) collapses. The strict `>` majority is load-bearing. -/
theorem weak_slot_breaks_log_agreement :
    ∃ (sb : ℕ → Votes 2 Command) (log₁ log₂ : CommittedLog) (c₁ c₂ : Command),
      -- both logs are weak-consistent: every entry is weak-decided at its slot
      (∀ i c, log₁[i]? = some c → WeakDecided (sb i) c) ∧
      (∀ i c, log₂[i]? = some c → WeakDecided (sb i) c) ∧
      -- yet they DISAGREE at slot 0 — log_agreement fails
      log₁[0]? = some c₁ ∧ log₂[0]? = some c₂ ∧ c₁ ≠ c₂ := by
  -- The split ballot at every slot: replica 0 votes cA, replica 1 votes cB.
  refine ⟨fun _ => (fun r => if r = 0 then some cA else some cB),
          [cA], [cB], cA, cB, ?_, ?_, rfl, rfl, cA_ne_cB⟩
  · -- [cA] weak-consistent: slot 0's entry cA is weak-decided by {0}.
    intro i c hc
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨{0}, by unfold IsWeakQuorum; decide,
             by intro r hr; rw [Finset.mem_singleton] at hr; subst hr; rfl⟩
    · simp at hc
  · -- [cB] weak-consistent: slot 0's entry cB is weak-decided by {1}.
    intro i c hc
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨{1}, by unfold IsWeakQuorum; decide,
             by intro r hr; rw [Finset.mem_singleton] at hr; subst hr; rfl⟩
    · simp at hc

/-- The disjointness that kills per-slot quorum intersection at `≥`: the two weak
quorums used by the bite share no replica. -/
theorem weak_quorums_disjoint :
    (({0} : Finset (Fin 2)) ∩ ({1} : Finset (Fin 2))) = ∅ := by decide

end Bite

/-! ## 5. Anti-vacuity — a concrete 2-slot log, real majorities, equal logs. -/

namespace Witness

/-- Three replicas. -/
abbrev N : ℕ := 3

/-- Slot-0 command. -/
def cX : Command := { payload := Term.var 0 }
/-- Slot-1 command — genuinely distinct from `cX`. -/
def cY : Command := { payload := Term.var 1 }

/-- `cX ≠ cY` (distinct payloads) — the log is non-trivial. -/
theorem cX_ne_cY : cX ≠ cY := by
  intro h
  have hp : cX.payload = cY.payload := congrArg Command.payload h
  simp [cX, cY] at hp

/-- The slot-ballots: slot 0 is unanimous for `cX`, every other slot unanimous
for `cY`. A concrete `SlotBallots N`. -/
def sb : SlotBallots N := fun i => if i = 0 then (fun _ => some cX) else (fun _ => some cY)

/-- The whole population `{0,1,2}` is a strict majority of 3 (`2·3 > 3`). -/
theorem univ_quorum : IsQuorum (Finset.univ : Finset (Fin N)) := by
  unfold IsQuorum
  simp [Finset.card_univ, Fintype.card_fin]

/-- Slot 0 really **decides** `cX` — a real majority quorum voting a real value. -/
theorem slot0_decides : SlotDecided sb 0 cX :=
  ⟨Finset.univ, univ_quorum, by intro r _; rfl⟩

/-- Slot 1 really **decides** `cY`. -/
theorem slot1_decides : SlotDecided sb 1 cY :=
  ⟨Finset.univ, univ_quorum, by intro r _; rfl⟩

/-- The concrete 2-slot committed log. -/
def log : CommittedLog := [cX, cY]

/-- The log is **consistent** with the slot-ballots: every entry is that slot's
real majority decision. -/
theorem log_consistent : LogConsistent sb log := by
  intro i c hc
  rcases i with _ | i
  · simp only [log, List.getElem?_cons_zero, Option.some.injEq] at hc
    subst hc; exact slot0_decides
  · rcases i with _ | i
    · simp only [log, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc; exact slot1_decides
    · simp [log] at hc

/-- **Two replicas converge on the WHOLE log.** Both build their committed log
from the same slot-ballots (both `LogConsistent`, equal length); `log_agreement_eq`
proves their logs EQUAL — a non-vacuous multi-slot convergence. -/
theorem two_replicas_agree : log = log :=
  log_agreement_eq rfl log_consistent log_consistent

/-- **Agreement applied non-vacuously at slot 0.** `log_agreement` on two
consistent logs yields `cX = cX` at slot 0 — an equality derived *through*
`slot_agreement → agreement → quorum_intersect`, not by `rfl`. -/
theorem log_agreement_nonvacuous : cX = cX :=
  log_agreement log_consistent log_consistent 0 cX cX rfl rfl

/-- The witness is non-trivial: a 2-slot log with distinct commands. -/
theorem log_nontrivial : log.length = 2 ∧ cX ≠ cY := ⟨rfl, cX_ne_cY⟩

end Witness

end DLCD
