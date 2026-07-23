import DLCD.Rsm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! # DLC-D Phase 1.1 — single-decree consensus SAFETY (discharging the log oracle)

Phase 1.0 (`DLCD.Rsm`) took the totally-ordered `CommittedLog` as an **oracle**:
the shared, per-slot-agreed command sequence was *assumed*, and convergence was
proved *relative* to it (`replicas_converge_on_prefix`). This module **earns**
that assumption for a single slot: it models how one slot's committed `Command`
is *agreed* by consensus, so the shared log is JUSTIFIED rather than postulated.

## The model: one decree, quorums, votes, a decision

We model a SINGLE decree (one log slot) over a finite replica set `Fin n`:

- **Quorum = strict majority.** `IsQuorum Q := 2 * Q.card > n`. Majorities are
  the canonical *self-intersecting* quorum system: any two overlap.
- **Votes.** `votes : Fin n → Option V` — each replica casts at most **one**
  value (single decree; a *function* returns one result per replica).
- **Decision.** `Decided votes v := ∃ Q, IsQuorum Q ∧ ∀ r ∈ Q, votes r = some v`
  — a value is chosen iff a whole quorum voted for it.

## The safety metatheorems (fully proved, no `sorry`)

1. **`quorum_intersect`** — the load-bearing lemma. Two majorities of `Fin n`
   overlap: `IsQuorum Q1 → IsQuorum Q2 → (Q1 ∩ Q2).Nonempty`. Classic `card`
   pigeonhole: `card(Q1)+card(Q2) > n ≥ card(Q1 ∪ Q2)`, and
   `card(Q1∪Q2)+card(Q1∩Q2) = card(Q1)+card(Q2)`, so `card(Q1∩Q2) > 0`.
2. **`agreement`** (the safety metatheorem) — `Decided votes v1 → Decided votes
   v2 → v1 = v2`. A replica in `Q1 ∩ Q2` voted `some v1` AND `some v2`; a
   function returns one value, so `v1 = v2`. Only one value can be chosen.
3. **`validity`** — `Decided votes v → ∃ r, votes r = some v`. The decided value
   came from a real vote (a real proposal), via `quorum_intersect Q Q` giving a
   nonempty quorum. `decided_proposed` sharpens this: if every vote respects a
   `Proposed` predicate, the decided value was `Proposed`.

## Discharging the oracle — the bridge

`committed_prefix_agree` turns per-slot `agreement` into a *well-defined shared
log*: two `CommittedLog`s of equal length, each of whose slots is `Decided` by
the **same** per-slot ballot family `slotVotes`, are **equal**. The committed log
is thus a FUNCTION of the votes — not a free oracle. `replicas_converge_via_
consensus` then feeds this straight into the Phase-1.0 seed: two replicas that
ran *independent* consensus instances (`logA`, `logB`) still converge, because
agreement forces `logA = logB`. The Phase-1.0 shared-`log` assumption is now
EARNED per slot, not assumed.

## Honest scope — what is FENCED

This increment is SAFETY only (agreement + validity + quorum-intersection),
which is the tractable core and is proved in full. **TERMINATION / liveness** —
that a decision *is eventually reached* under fair delivery and ≤ f crashes —
is the LATER liveness increment (the `no_infinite_descent` / well-founded-rank
argument, cf. `FailureBudget.fairDelivery`). It is deliberately NOT attempted
here; nothing in this file asserts progress. The multi-slot induction (lifting
single-slot agreement to the whole log via `slotVotes`) is stated as the bridge
`committed_prefix_agree` and used, but a full multi-slot *protocol* run is out
of scope for 1.1.

## The right-reason bite

Weakening `IsQuorum` to `2 * card ≥ n` (allowing exact-half "quorums") breaks
everything: `weak_agreement_fails` exhibits two **disjoint** half-sets of
`Fin 2`, each a weak "quorum", deciding **different** values — so
`quorum_intersect` and hence `agreement` genuinely fail at `≥`. The strict `>`
is load-bearing.

## Prior art (web-searched 2026-07-22; URLs recorded)
- mwhittaker, *Single-Decree Paxos* (the phase-1/phase-2 quorum decision and the
  intersection argument): https://mwhittaker.github.io/blog/single_decree_paxos/
- Howard–Malkhi–Spiegelman, *Flexible Paxos: Quorum intersection revisited*
  (arXiv:1608.06696) — only *cross-phase* quorums must intersect; majorities are
  one sufficient system: https://arxiv.org/abs/1608.06696 , https://fpaxos.github.io/ ,
  https://drops.dagstuhl.de/storage/00lipics/lipics-vol070-opodis2016/LIPIcs.OPODIS.2016.25/LIPIcs.OPODIS.2016.25.pdf
- decentralizedthoughts, *Consensus for SMR* (single-decree per slot; prefix
  completeness ⇒ correct replicas share identical prefixes):
  https://decentralizedthoughts.github.io/2019-10-15-consensus-for-state-machine-replication/
- Padon–Losa–Sagiv–Shoham et al. / Chand–Liu–Stoller, *Formal verification of
  Multi-Paxos for distributed consensus* (FM 2016) — quorum intersection is the
  invariant that yields agreement:
  https://www3.cs.stonybrook.edu/~stoller/papers/fm2016.pdf
- García-Pérez–Gotsman–Meshman–Sergey, *Paxos Consensus, Deconstructed and
  Abstracted* (ESOP 2018): https://ilyasergey.net/assets/pdf/papers/paxos-deconstructed-esop18.pdf
- Lamport, *The Part-Time Parliament* / *Paxos Made Simple*; *Time, Clocks…*
  (1978) SMR via total order.
-/

namespace DLCD

open DLC

/-! ## 1. Replicas, quorums, and the quorum-intersection lemma. -/

section Consensus

-- The replica population size `n`; replicas are `Fin n`. Values are `V`.
variable {n : ℕ} {V : Type*}

/-- A **quorum** is a strict majority of the `n` replicas. Strict `>` is the
load-bearing choice (see `weak_agreement_fails`): it makes majorities a
self-intersecting quorum system. -/
def IsQuorum (Q : Finset (Fin n)) : Prop := 2 * Q.card > n

/-- **THE KEY LEMMA — quorum intersection.** Any two majorities of `Fin n`
overlap. Pigeonhole on cardinalities: `card(Q1∪Q2) ≤ n < card(Q1)+card(Q2)`
(from the two majorities), and `card(Q1∪Q2)+card(Q1∩Q2) = card(Q1)+card(Q2)`
(inclusion–exclusion), so `card(Q1∩Q2) > 0`, i.e. the intersection is nonempty.
Every safety guarantee below flows from this one fact. -/
theorem quorum_intersect {Q1 Q2 : Finset (Fin n)}
    (h1 : IsQuorum Q1) (h2 : IsQuorum Q2) : (Q1 ∩ Q2).Nonempty := by
  unfold IsQuorum at h1 h2
  rw [← Finset.card_pos]
  -- The union fits inside the whole population of size `n`.
  have hunion : (Q1 ∪ Q2).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (Q1 ∪ Q2))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  -- Inclusion–exclusion for `card`.
  have hkey : (Q1 ∪ Q2).card + (Q1 ∩ Q2).card = Q1.card + Q2.card :=
    Finset.card_union_add_card_inter Q1 Q2
  omega

/-! ## 2. Votes and the decision predicate. -/

/-- A **ballot**: each replica casts at most one value (single decree). -/
abbrev Votes (n : ℕ) (V : Type*) := Fin n → Option V

/-- A value is **decided** iff some quorum unanimously voted for it. This is the
genuinely inhabitable decision predicate (see `ConsensusAntiVacuity.decided7_a`). -/
def Decided (votes : Fin n → Option V) (v : V) : Prop :=
  ∃ Q : Finset (Fin n), IsQuorum Q ∧ ∀ r ∈ Q, votes r = some v

/-! ## 3. AGREEMENT and VALIDITY — the safety core. -/

/-- **AGREEMENT — the safety metatheorem.** At most one value is decided. From
`quorum_intersect`, a replica `r ∈ Q1 ∩ Q2` voted `some v1` (it is in `Q1`) and
`some v2` (it is in `Q2`); `votes r` is a single value, so `v1 = v2`. -/
theorem agreement {votes : Fin n → Option V} {v1 v2 : V}
    (h1 : Decided votes v1) (h2 : Decided votes v2) : v1 = v2 := by
  obtain ⟨Q1, hq1, hv1⟩ := h1
  obtain ⟨Q2, hq2, hv2⟩ := h2
  obtain ⟨r, hr⟩ := quorum_intersect hq1 hq2
  rw [Finset.mem_inter] at hr
  have e1 : votes r = some v1 := hv1 r hr.1
  have e2 : votes r = some v2 := hv2 r hr.2
  rw [e1] at e2
  exact Option.some.inj e2

/-- **VALIDITY.** A decided value came from a real vote. `quorum_intersect Q Q`
shows the deciding quorum is nonempty; that replica's vote is `some v`. -/
theorem validity {votes : Fin n → Option V} {v : V}
    (h : Decided votes v) : ∃ r, votes r = some v := by
  obtain ⟨Q, hq, hv⟩ := h
  obtain ⟨r, hr⟩ := quorum_intersect hq hq
  rw [Finset.mem_inter] at hr
  exact ⟨r, hv r hr.1⟩

/-- **VALIDITY vs proposals.** If every cast vote respects a `Proposed`
predicate (a replica only votes for proposed values), then a decided value was
proposed: `Decided v → Proposed v`. This ties the decision to real proposals,
matching `CapSafety`'s "only authorized commands are decided" discipline. -/
theorem decided_proposed {votes : Fin n → Option V} {Proposed : V → Prop}
    (hvp : ∀ r v, votes r = some v → Proposed v) {v : V}
    (h : Decided votes v) : Proposed v := by
  obtain ⟨r, hr⟩ := validity h
  exact hvp r v hr

end Consensus

/-! ## 4. Discharging the oracle — from per-slot agreement to a shared log.

The Phase-1.0 `CommittedLog` was an oracle. Here each slot `i` carries its own
ballot `slotVotes i`, and a log is *legitimate* iff each of its slots is
`Decided` by that slot's ballot. `committed_prefix_agree` shows any two
legitimate logs of equal length coincide — the committed log is a **function of
the votes**, not a free assumption. -/

section Bridge

variable {n : ℕ}

/-- **THE BRIDGE LEMMA — the shared committed prefix is well-defined.** Two
committed logs of equal length, each of whose slots is the value `Decided` by
the *same* per-slot ballot family `slotVotes`, are **equal**. Per-slot
`agreement` forces the two independent consensus outputs to agree slot-by-slot,
so the shared log the Phase-1.0 seed assumed is now determined by the votes. -/
theorem committed_prefix_agree
    (slotVotes : ℕ → Votes n Command)
    (logA logB : CommittedLog)
    (hlen : logA.length = logB.length)
    (hA : ∀ i c, logA[i]? = some c → Decided (slotVotes i) c)
    (hB : ∀ i c, logB[i]? = some c → Decided (slotVotes i) c) :
    logA = logB := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < logA.length
  · have hiB : i < logB.length := by omega
    have hcA : logA[i]? = some logA[i] := List.getElem?_eq_getElem hi
    have hcB : logB[i]? = some logB[i] := List.getElem?_eq_getElem hiB
    have dA := hA i _ hcA
    have dB := hB i _ hcB
    have heq : logA[i] = logB[i] := agreement dA dB
    rw [hcA, hcB, heq]
  · rw [List.getElem?_eq_none (by omega : logA.length ≤ i),
        List.getElem?_eq_none (by omega : logB.length ≤ i)]

/-- **The oracle discharged for convergence.** Two replicas that ran
*independent* single-decree consensus instances — producing possibly-distinct
committed logs `logA`, `logB` — nevertheless converge, because per-slot
`agreement` (via `committed_prefix_agree`) forces `logA = logB`, and then the
Phase-1.0 seed `replicas_converge_on_prefix` applies. This is exactly the
statement that the Phase-1.0 *shared* log is EARNED, not assumed. -/
theorem replicas_converge_via_consensus
    (slotVotes : ℕ → Votes n Command)
    {init : Term} {logA logB : CommittedLog} {r1 r2 : Replica}
    (hlen : logA.length = logB.length)
    (hA : ∀ i c, logA[i]? = some c → Decided (slotVotes i) c)
    (hB : ∀ i c, logB[i]? = some c → Decided (slotVotes i) c)
    (h1 : AppliedPrefix init logA r1)
    (h2 : AppliedPrefix init logB r2)
    (happ : r1.applied = r2.applied) :
    r1.store = r2.store := by
  have hlog : logA = logB := committed_prefix_agree slotVotes logA logB hlen hA hB
  subst hlog
  exact replicas_converge_on_prefix h1 h2 happ

end Bridge

/-! ## 5. Anti-vacuity — a concrete, non-vacuous decision and agreement.

Three replicas; two genuinely *distinct* overlapping majorities `{0,1}` and
`{1,2}`; a real ballot; a `Decided` value inhabited by real votes; and
`agreement` applied to two decisions from the two different quorums yielding a
real equality. Nothing here is vacuous — the quorums, the decision, and the
intersection are all concretely inhabited. -/

namespace ConsensusAntiVacuity

/-- A three-replica population. -/
abbrev N : ℕ := 3

/-- The ballot: every replica votes for `7`. -/
def votes : Votes N ℕ := fun _ => some 7

/-- First majority: `{0, 1}`. -/
def Q1 : Finset (Fin N) := {0, 1}

/-- Second majority: `{1, 2}` — genuinely different from `Q1`. -/
def Q2 : Finset (Fin N) := {1, 2}

/-- `{0,1}` is a strict majority of 3 (`2·2 > 3`). -/
theorem q1_quorum : IsQuorum Q1 := by unfold IsQuorum Q1; decide

/-- `{1,2}` is a strict majority of 3. -/
theorem q2_quorum : IsQuorum Q2 := by unfold IsQuorum Q2; decide

/-- The two majorities are genuinely distinct sets. -/
theorem quorums_distinct : Q1 ≠ Q2 := by decide

/-- Their intersection is exactly `{1}` — the replica whose single vote forces
agreement. -/
theorem quorums_overlap_at_one : Q1 ∩ Q2 = {1} := by decide

/-- `quorum_intersect` inhabited on the concrete pair: the intersection is
nonempty. -/
theorem quorums_overlap : (Q1 ∩ Q2).Nonempty := quorum_intersect q1_quorum q2_quorum

/-- `7` is decided *via* `Q1` — a real quorum voting a real value. -/
theorem decided7_a : Decided votes 7 := ⟨Q1, q1_quorum, by intro r _; rfl⟩

/-- `7` is decided *via* the different quorum `Q2`. -/
theorem decided7_b : Decided votes 7 := ⟨Q2, q2_quorum, by intro r _; rfl⟩

/-- **Agreement, non-vacuously.** Two decisions reached through two *different*
overlapping majorities are forced equal by `agreement` — a real equality
`7 = 7` derived through the quorum-intersection argument, not by `rfl`. -/
theorem agreement_nonvacuous : (7 : ℕ) = 7 := agreement decided7_a decided7_b

/-- **Validity, inhabited.** The decided value is traced back to a real vote. -/
theorem validity_witness : ∃ r, votes r = some 7 := validity decided7_a

/-! ### The right-reason bite: weaken the quorum to `2·card ≥ n`. -/

/-- The **weakened** quorum notion allowing exact halves. -/
def IsWeakQuorum (Q : Finset (Fin 2)) : Prop := 2 * Q.card ≥ 2

/-- **THE BITE.** Under the weakened `≥` quorum, two **disjoint** half-sets
`{0}` and `{1}` of `Fin 2` are both "quorums", and a ballot that has `{0}` vote
`3` while `{1}` votes `4` makes BOTH `3` and `4` "decided" with `3 ≠ 4`. So the
quorum-intersection lemma — and therefore `agreement` — genuinely fails at `≥`:
the two "quorums" do not intersect. The strict `>` in `IsQuorum` is essential. -/
theorem weak_agreement_fails :
    ∃ (v : Votes 2 ℕ) (v1 v2 : ℕ),
      (∃ Q, IsWeakQuorum Q ∧ ∀ r ∈ Q, v r = some v1) ∧
      (∃ Q, IsWeakQuorum Q ∧ ∀ r ∈ Q, v r = some v2) ∧
      v1 ≠ v2 := by
  refine ⟨fun r => if r = 0 then some 3 else some 4, 3, 4, ?_, ?_, by decide⟩
  · exact ⟨{0}, by unfold IsWeakQuorum; decide, by decide⟩
  · exact ⟨{1}, by unfold IsWeakQuorum; decide, by decide⟩

/-- And the disjointness that kills `quorum_intersect` at `≥`: the two weak
quorums have empty intersection. -/
theorem weak_quorums_disjoint :
    (({0} : Finset (Fin 2)) ∩ ({1} : Finset (Fin 2))) = ∅ := by decide

end ConsensusAntiVacuity

end DLCD

