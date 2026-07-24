import DLCD.ByzantineConsensus

/-! # DLC-D — MULTI-DECREE BYZANTINE safety (per-slot `byz_agreement`, folded over the log).

The Byzantine twin of `DLCD.MultiDecree.log_agreement`. `MultiDecree` folds crash-fault
`Consensus.agreement` per slot to get log matching (Raft's State-Machine Safety); this folds
`ByzantineConsensus.byz_agreement` per slot to get the SAME log-matching guarantee under a
BYZANTINE minority (`n ≥ 3f+1`, `> 2/3` Byzantine quorums that intersect in an HONEST member).

Multi-decree = per-slot single-decree agreement applied independently at each slot (Chand–Liu–Stoller;
PBFT is the multi-decree reference — Velisarios, Coq, https://vrahli.github.io/articles/velisarios.pdf).
The fold is IDENTICAL to the crash version; only the per-slot atom swaps `agreement → byz_agreement`.
Generic over the decided value `V`; instantiating `V := DLCD.Command` gives the committed-log
(`List Command`) matching for the DLC-D SMR.

Scope: multi-decree Byzantine **SAFETY** (per-slot single-value + log matching). Liveness (every slot
eventually decided) is separate (the view-change models: `models/tamarin/dlcd-viewchange-byz.spthy`,
`models/tla/DlcdViewChange.tla`). Slots are independent decrees (`ℕ`); cross-slot ordering is `Rsm`.
-/

namespace DLCD
namespace ByzantineMultiDecree

section
variable {n f : ℕ} {V : Type*}

/-- **Multi-decree Byzantine ballots.** One independent single-decree Byzantine ballot per slot
`i : ℕ` — `sb i : Fin n → Option V` is exactly a Phase-`ByzantineConsensus` ballot. -/
abbrev ByzSlotBallots (n : ℕ) (V : Type*) := ℕ → (Fin n → Option V)

/-- Slot `i` **Byzantine-decides** `v` iff `v` is certified by a Byzantine quorum of that slot's
ballot (an honest majority of a `> 2/3` supermajority voted `v`). `ByzDecided` at slot `i`. -/
def ByzSlotDecided (B : Finset (Fin n)) (sb : ByzSlotBallots n V) (i : ℕ) (v : V) : Prop :=
  ByzDecided B (sb i) v

/-- **Honest non-equivocation, per slot.** Each honest replica (`∉ B`) casts at most one value in
each slot's ballot — the premise `byz_agreement` needs (a function-vote is automatically consistent;
the Byzantine members of `B` may equivocate freely). -/
def HonestConsistent (B : Finset (Fin n)) (sb : ByzSlotBallots n V) : Prop :=
  ∀ i r, r ∉ B → ∀ w1 w2 : V, sb i r = some w1 → sb i r = some w2 → w1 = w2

/-- **PER-SLOT BYZANTINE AGREEMENT.** Each slot decides at most one value under `≤ f` Byzantine
faults — *literally* `byz_agreement` instantiated at `votes := sb i`. No quorum reasoning is
reproved; the honest-intersection core is inherited. -/
theorem byz_slot_agreement (B : Finset (Fin n)) (sb : ByzSlotBallots n V) (i : ℕ)
    (hn : n ≥ 3 * f + 1) (hB : B.card ≤ f) (hc : HonestConsistent B sb)
    {v₁ v₂ : V} (h₁ : ByzSlotDecided B sb i v₁) (h₂ : ByzSlotDecided B sb i v₂) : v₁ = v₂ :=
  byz_agreement (f := f) hn hB (hc i) h₁ h₂

/-- A log is **Byzantine-consistent** with the slot-ballots iff every entry is that slot's Byzantine
decision — a correct replica commits, at each slot, exactly what Byzantine consensus decided there. -/
def ByzLogConsistent (B : Finset (Fin n)) (sb : ByzSlotBallots n V) (log : List V) : Prop :=
  ∀ (i : ℕ) (v : V), log[i]? = some v → ByzSlotDecided B sb i v

/-- **BYZANTINE LOG AGREEMENT — the multi-decree safety metatheorem (State-Machine Safety under
Byzantine faults).** Two logs, each Byzantine-consistent with the *same* slot-ballots, agree at every
index: if both have an entry at slot `i`, those entries are the SAME value. Pointwise
`byz_slot_agreement` folded over the log index. Two correct replicas building committed logs from the
same Byzantine-consensus outputs never disagree on a decided slot, even with `≤ f` Byzantine replicas
equivocating. -/
theorem byz_log_agreement (B : Finset (Fin n)) {sb : ByzSlotBallots n V} {log₁ log₂ : List V}
    (hn : n ≥ 3 * f + 1) (hB : B.card ≤ f) (hc : HonestConsistent B sb)
    (h₁ : ByzLogConsistent B sb log₁) (h₂ : ByzLogConsistent B sb log₂) :
    ∀ (i : ℕ) (v₁ v₂ : V), log₁[i]? = some v₁ → log₂[i]? = some v₂ → v₁ = v₂ := by
  intro i v₁ v₂ e₁ e₂
  exact byz_slot_agreement (f := f) B sb i hn hB hc (h₁ i v₁ e₁) (h₂ i v₂ e₂)

/-- **BYZANTINE LOG AGREEMENT ⇒ EQUAL LOGS.** Two Byzantine-consistent logs of *equal length* are
EQUAL — correct replicas converge on the whole committed log under `≤ f` Byzantine faults.
`List.ext_getElem?` on the slot index; in range `byz_log_agreement` forces equal entries, out of range
both are `none`. Identical fold to the crash `log_agreement_eq`; the fault model swapped underneath. -/
theorem byz_log_agreement_eq (B : Finset (Fin n)) {sb : ByzSlotBallots n V} {log₁ log₂ : List V}
    (hlen : log₁.length = log₂.length)
    (hn : n ≥ 3 * f + 1) (hB : B.card ≤ f) (hc : HonestConsistent B sb)
    (h₁ : ByzLogConsistent B sb log₁) (h₂ : ByzLogConsistent B sb log₂) :
    log₁ = log₂ := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < log₁.length
  · have hiB : i < log₂.length := by omega
    have hcA : log₁[i]? = some log₁[i] := List.getElem?_eq_getElem hi
    have hcB : log₂[i]? = some log₂[i] := List.getElem?_eq_getElem hiB
    have heq : log₁[i] = log₂[i] := byz_log_agreement (f := f) B hn hB hc h₁ h₂ i _ _ hcA hcB
    rw [hcA, hcB, heq]
  · rw [List.getElem?_eq_none (by omega : log₁.length ≤ i),
        List.getElem?_eq_none (by omega : log₂.length ≤ i)]

end

/-! ## Non-vacuity — a concrete Byzantine multi-decree run (reuses `ByzWitness`). -/

namespace ByzMultiWitness

open ByzWitness

/-- Every slot uses the concrete deciding-`7` ballot (honest replicas vote 7; node 3 equivocates 99). -/
def sb : ByzSlotBallots N ℕ := fun _ => votes

/-- Honest consistency holds at every slot (the ballot is a function). -/
theorem sb_honest : HonestConsistent (n := N) B sb := fun _ => honest_consistent

/-- **PER-SLOT agreement, non-vacuously.** At slot 0, two certificates through the two *different*
Byzantine quorums `{0,1,2}` and `{1,2,3}` are forced equal by `byz_slot_agreement` — a real `7 = 7`
derived *through* the honest intersection (not `rfl`), despite node 3 equivocating. -/
theorem byz_slot_agreement_nonvacuous : (7 : ℕ) = 7 :=
  byz_slot_agreement (f := F) B sb 0 n_bound B_card sb_honest decided7_via_q1 decided7_via_q2

/-- A concrete committed log `[7]` is Byzantine-consistent with `sb`. -/
theorem log_consistent : ByzLogConsistent (n := N) B sb [7] := by
  intro i v hv
  rcases i with _ | i
  · rw [List.getElem?_cons_zero, Option.some.injEq] at hv
    rw [← hv]; exact decided7_via_q1
  · rw [List.getElem?_cons_succ, List.getElem?_nil] at hv
    exact absurd hv (by simp)

/-- **LOG AGREEMENT, non-vacuously.** Two correct replicas each holding the committed log `[7]` agree
at every slot — `byz_log_agreement` applied to the concrete run, forced through per-slot Byzantine
quorum intersection (node 3 equivocating). -/
theorem byz_log_agreement_nonvacuous :
    ∀ (i : ℕ) (v₁ v₂ : ℕ), ([7] : List ℕ)[i]? = some v₁ → ([7] : List ℕ)[i]? = some v₂ → v₁ = v₂ :=
  byz_log_agreement (f := F) B n_bound B_card sb_honest log_consistent log_consistent

end ByzMultiWitness

end ByzantineMultiDecree
end DLCD
