import DLCD.Consensus
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-! # DLC-D — single-decree BYZANTINE agreement SAFETY (the `3f+1` fault model)

`DLCD.Consensus` earned single-decree safety under the **crash** fault model:
`IsQuorum Q := 2 * Q.card > n` (strict majority), `quorum_intersect` (any two
majorities share a member), and `agreement` (at most one value decided). A
crashed replica is *silent* — it never votes wrongly, so a strict-majority
self-intersecting quorum system suffices.

This module **composes alongside** that crash layer (it does NOT touch
`Consensus.lean`) with the strictly stronger **Byzantine** fault model: up to
`f` replicas may be *arbitrary / adversarial* — they may equivocate, sending
one vote to one quorum and a conflicting vote to another. Under equivocation a
mere majority overlap is worthless: the single common replica of two majorities
may be exactly the Byzantine one, which votes both ways. The classical fix
(Pease–Shostak–Lamport; Dwork–Lynch–Stockmeyer) is the population bound
`n ≥ 3f+1` with `≥ 2f+1`-of-`3f+1` quorums, so that any two quorums share
`≥ f+1` replicas — of which at least one is **honest**. That honest common
member is the Byzantine analogue of `quorum_intersect`, and it carries agreement.

## The model — Byzantine quorums, a fault set, honest-certified decisions

- **Byzantine quorum.** `IsByzQuorum Q := 3 * Q.card > 2 * n`, i.e. `card > 2n/3`
  (`≥ 2f+1` when `n = 3f+1`). The `> 2/3` threshold is the load-bearing choice
  (see `crash_majority_byz_agreement_fails`): it forces `|Q1 ∩ Q2| ≥ f+1 > f`.
- **Fault set.** `B : Finset (Fin n)` with `B.card ≤ f` — the (possibly unknown)
  Byzantine replicas; the *honest* replicas are `Bᶜ`. The population bound
  `n ≥ 3*f+1` is an explicit hypothesis.
- **Decision.** `ByzDecided B votes v := ∃ Q, IsByzQuorum Q ∧ ∀ r ∈ Q, r ∉ B →
  votes r = some v`. A value is certified iff some Byzantine quorum's **honest**
  members all voted it. This is the faithful Byzantine reading: Byzantine
  members (`r ∈ B`) are *unconstrained* — they may equivocate — so a certificate
  can only rest on the honest votes it contains. (Contrast the crash `Decided`,
  which constrains *every* quorum member, because a crashed node is silent, not
  adversarial.) `votes : Fin n → Option V` is the honest ballot; `honest_consistent`
  says honest replicas cast at most one value.

## The safety metatheorems (fully proved, no `sorry`)

1. **`byz_quorum_honest_intersect`** — THE BFT SAFETY CORE. Two Byzantine
   quorums share an **honest** replica: `∃ r, r ∈ Q1 ∧ r ∈ Q2 ∧ r ∉ B`.
   Pigeonhole: `|Q1 ∩ Q2| = |Q1| + |Q2| - |Q1 ∪ Q2| ≥ |Q1| + |Q2| - n`, and from
   `3|Qᵢ| > 2n` plus `n ≥ 3f+1` one gets `3|Q1 ∩ Q2| ≥ n + 2 ≥ 3f+3`, so
   `|Q1 ∩ Q2| ≥ f+1 > f ≥ |B|`; hence `(Q1 ∩ Q2) \ B` is nonempty. The `∉ B`
   is the whole Byzantine point — a common member that could be Byzantine buys
   nothing.
2. **`byz_agreement`** — at most one value is certified, under ≤ f Byzantine
   faults + `n ≥ 3f+1` + honest consistency. The honest common member voted
   both `v1` and `v2`; being honest (`∉ B`), its vote is constrained by BOTH
   certificates and single-valued, so `v1 = v2`. Byzantine members may
   equivocate; the honest intersection member cannot.
3. **`byz_validity`** — a certified value is backed by a real **honest** vote
   (`byz_quorum_honest_intersect Q Q` exhibits an honest member of the deciding
   quorum). A Byzantine-only quorum can never certify a value.

## The right-reason bite

`crash_majority_byz_agreement_fails`: replace the `3f+1`-Byzantine quorum with a
mere **crash majority** (`IsQuorum`, `2·card > n`) under Byzantine faults. At
`n = 3, f = 1, B = {1}`, the two majorities `{0,1}` and `{1,2}` intersect ONLY
in `{1} = B` — the Byzantine node. Their honest cores are the disjoint `{0}`
and `{2}`, which vote `3` and `4`; so both `3` and `4` are "certified" with
`3 ≠ 4`. `byz_agreement` fails. `crash_quorums_are_not_byz` confirms these size-2
majorities are NOT Byzantine quorums (`3·2 = 6 ≯ 6 = 2·3`): the `> 2n/3` bound is
load-bearing — crash-majority is insufficient once faults can equivocate.

## Anti-vacuity witness

`ByzWitness`: `n = 4, f = 1` (so `3f+1 = 4`), fault set `B = {3}` (`card 1 ≤ f`),
two genuinely distinct 3-node Byzantine quorums `{0,1,2}` and `{1,2,3}` (each
`3·3 = 9 > 8 = 2n`) sharing the **honest** core `{1,2}`; honest replicas all vote
`7` while the Byzantine node 3 equivocates (`votes 3 = some 99 ≠ 7`); both
quorums certify `7`; `byz_agreement` yields uniqueness *through* the honest
intersection. Real Byzantine quorums, a real `card ≤ f` fault set, a real
equivocating node, a real honest-certified decision — nothing vacuous.

## Honest scope — what is FENCED

This is single-decree Byzantine **SAFETY** (agreement + validity), the tractable
core, proved in full. Deferred:
- **Byzantine LIVENESS** — view-change / leader-election / partial-synchrony
  progress (that a decision is *eventually* reached) is a separate PROGRESS
  property; nothing here asserts progress. SOTA foundational path: Bythos
  (CCS'24, compositional mechanised BFT safety+liveness in Coq) and TetraBFT
  (PODC'24).
- **Multi-decree Byzantine lift** — folding this atom over a replicated log
  (the Byzantine twin of `MultiDecree.log_agreement`) is future work; it reuses
  this `byz_agreement` per slot exactly as `MultiDecree` reuses crash `agreement`.
- The crash layer `Consensus.lean` is UNCHANGED; the two fault models compose
  side by side.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Castro–Liskov, *Practical Byzantine Fault Tolerance*, OSDI'99 — `n ≥ 3f+1`,
  `2f+1`-of-`3f+1` quorums for SMR under Byzantine faults:
  https://www.usenix.org/conference/osdi-99/practical-byzantine-fault-tolerance ,
  https://pmg.csail.mit.edu/papers/osdi99.pdf
- Dwork–Lynch–Stockmeyer, *Consensus in the Presence of Partial Synchrony*,
  J.ACM 35(2) 1988 — `t`-resilient consensus iff `N > 3t` (the `3f+1` bound),
  the FLP-circumventing partial-synchrony model:
  https://dl.acm.org/doi/10.1145/42282.42283 ,
  https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf
- Malkhi–Reiter, *Byzantine Quorum Systems*, 1998 — quorum systems whose any
  two members intersect in enough replicas to include an honest one:
  https://www.cs.cmu.edu/~reiter/papers/1998/DC.pdf
- Zhao–Pîrlea–Grimm–Sergey et al., *Compositional Verification of Composite
  Byzantine Protocols* (Bythos), CCS'24 — foundational compositional mechanised
  BFT safety+liveness in Coq (the SOTA liveness path fenced above):
  https://dl.acm.org/doi/10.1145/3658644.3690355 , https://pirlea.net/papers/bythos-ccs24.pdf
- Yu–Losa–Wang, *TetraBFT: Reducing Latency of Unauthenticated, Responsive BFT
  Consensus*, PODC'24: https://dl.acm.org/doi/10.1145/3662158.3662783 ,
  https://arxiv.org/abs/2405.02615
-/

namespace DLCD

/-! ## 1. Byzantine quorums, the fault model, and the honest-intersection lemma. -/

section ByzantineConsensus

-- Population size `n`; Byzantine-fault budget `f`; replicas are `Fin n`; values `V`.
variable {n f : ℕ} {V : Type*}

/-- A **Byzantine quorum** is a `> 2/3` supermajority of the `n` replicas:
`3 * Q.card > 2 * n`, i.e. `card > 2n/3` (`≥ 2f+1` of `3f+1`). The `> 2/3`
threshold is the load-bearing choice (see `crash_majority_byz_agreement_fails`):
it forces any two quorums to overlap in `≥ f+1` replicas, one of them honest. -/
def IsByzQuorum (Q : Finset (Fin n)) : Prop := 3 * Q.card > 2 * n

/-- **THE KEY LEMMA — Byzantine quorum intersection has an HONEST common member.**
Under the population bound `n ≥ 3f+1` and a fault set `B` with `|B| ≤ f`, any two
Byzantine quorums `Q1`, `Q2` share a replica that is **not** Byzantine.

Pigeonhole on cardinalities: with `u = |Q1 ∪ Q2| ≤ n`, `i = |Q1 ∩ Q2|`,
inclusion–exclusion gives `u + i = |Q1| + |Q2|`; from `3|Q1| > 2n`, `3|Q2| > 2n`
and `3u ≤ 3n` we get `3i = 3|Q1| + 3|Q2| - 3u ≥ 4n + 2 - 3n = n + 2 ≥ 3f + 3`,
so `i ≥ f+1`. Then `|(Q1 ∩ Q2) \ B| ≥ i - |B| ≥ (f+1) - f = 1 > 0`, so the
intersection contains an honest replica. This — the `∉ B`, not the bare overlap —
is the BFT safety core: a common member that might be Byzantine carries nothing. -/
theorem byz_quorum_honest_intersect {B Q1 Q2 : Finset (Fin n)}
    (hn : n ≥ 3 * f + 1) (hB : B.card ≤ f)
    (h1 : IsByzQuorum Q1) (h2 : IsByzQuorum Q2) :
    ∃ r, r ∈ Q1 ∧ r ∈ Q2 ∧ r ∉ B := by
  unfold IsByzQuorum at h1 h2
  -- The union fits inside the whole population of size `n`.
  have hunion : (Q1 ∪ Q2).card ≤ n := by
    have := Finset.card_le_card (Finset.subset_univ (Q1 ∪ Q2))
    simpa [Finset.card_univ, Fintype.card_fin] using this
  -- Inclusion–exclusion for `card`.
  have hkey : (Q1 ∪ Q2).card + (Q1 ∩ Q2).card = Q1.card + Q2.card :=
    Finset.card_union_add_card_inter Q1 Q2
  -- The intersection is at least `f+1` replicas (the pigeonhole count).
  have hinter : (Q1 ∩ Q2).card ≥ f + 1 := by omega
  -- Removing the ≤ f Byzantine replicas still leaves ≥ 1: an honest common member.
  have hsdiff := Finset.le_card_sdiff B (Q1 ∩ Q2)
  have hpos : 0 < ((Q1 ∩ Q2) \ B).card := by omega
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_sdiff, Finset.mem_inter] at hr
  exact ⟨r, hr.1.1, hr.1.2, hr.2⟩

/-! ## 2. Votes and the Byzantine decision predicate. -/

/-- A value is **Byzantine-decided** (certified) iff some Byzantine quorum's
**honest** members all voted for it. Byzantine members (`r ∈ B`) are
unconstrained — they may equivocate — so a certificate rests only on the honest
votes it contains. Contrast `Consensus.Decided`, which constrains *every* member
(a crashed node is silent, not adversarial). -/
def ByzDecided (B : Finset (Fin n)) (votes : Fin n → Option V) (v : V) : Prop :=
  ∃ Q : Finset (Fin n), IsByzQuorum Q ∧ ∀ r ∈ Q, r ∉ B → votes r = some v

/-! ## 3. BYZANTINE AGREEMENT and VALIDITY — the safety core. -/

/-- **BYZANTINE AGREEMENT — the safety metatheorem.** Under ≤ f Byzantine faults
(`|B| ≤ f`), the population bound `n ≥ 3f+1`, and honest consistency (honest
replicas cast at most one value), at most one value is certified.
`byz_quorum_honest_intersect` gives an HONEST replica `r ∈ Q1 ∩ Q2`; being honest
(`r ∉ B`), its vote is constrained by *both* certificates — `votes r = some v1`
and `votes r = some v2` — and single-valued, so `v1 = v2`. The `∉ B` is
load-bearing: without it the common member could be Byzantine, equivocating, and
neither certificate would constrain it. -/
theorem byz_agreement {B : Finset (Fin n)} {votes : Fin n → Option V} {v1 v2 : V}
    (hn : n ≥ 3 * f + 1) (hB : B.card ≤ f)
    (honest_consistent :
      ∀ r, r ∉ B → ∀ w1 w2 : V, votes r = some w1 → votes r = some w2 → w1 = w2)
    (h1 : ByzDecided B votes v1) (h2 : ByzDecided B votes v2) : v1 = v2 := by
  obtain ⟨Q1, hq1, hv1⟩ := h1
  obtain ⟨Q2, hq2, hv2⟩ := h2
  obtain ⟨r, hr1, hr2, hrB⟩ := byz_quorum_honest_intersect (f := f) hn hB hq1 hq2
  have e1 : votes r = some v1 := hv1 r hr1 hrB
  have e2 : votes r = some v2 := hv2 r hr2 hrB
  exact honest_consistent r hrB v1 v2 e1 e2

/-- **BYZANTINE VALIDITY.** A certified value is backed by a real **honest** vote:
`byz_quorum_honest_intersect Q Q` exhibits an honest member of the deciding
quorum, whose vote is `some v`. A Byzantine-only quorum can never certify a value
— the honest core of every Byzantine quorum is nonempty. -/
theorem byz_validity {B : Finset (Fin n)} {votes : Fin n → Option V} {v : V}
    (hn : n ≥ 3 * f + 1) (hB : B.card ≤ f)
    (h : ByzDecided B votes v) : ∃ r, r ∉ B ∧ votes r = some v := by
  obtain ⟨Q, hq, hv⟩ := h
  obtain ⟨r, hr1, _, hrB⟩ := byz_quorum_honest_intersect (f := f) hn hB hq hq
  exact ⟨r, hrB, hv r hr1 hrB⟩

end ByzantineConsensus

/-! ## 4. The right-reason bite — a CRASH-MAJORITY quorum FAILS under Byzantine
faults. We reuse `Consensus.IsQuorum` (`2 * Q.card > n`, the actual crash-fault
quorum) to make the contrast exact: it is enough for crashes, insufficient for
Byzantine equivocation. -/

namespace ByzBite

/-- These size-2 crash majorities of `Fin 3` are NOT Byzantine quorums
(`3·2 = 6 ≯ 6 = 2·3`): the `> 2n/3` bound genuinely excludes them. -/
theorem crash_quorums_are_not_byz :
    ¬ IsByzQuorum ({0, 1} : Finset (Fin 3)) := by
  unfold IsByzQuorum; decide

/-- The two crash majorities of the bite intersect ONLY in `{1}` — which is the
Byzantine node `B`. Their honest cores `{0}` and `{2}` are disjoint, so no honest
replica ties the two decisions together. -/
theorem crash_bite_intersection_is_byzantine :
    (({0, 1} : Finset (Fin 3)) ∩ ({1, 2} : Finset (Fin 3))) = {1} := by decide

/-- **THE BITE.** Weaken the quorum from `IsByzQuorum` to a mere crash majority
(`IsQuorum`, `2·card > n`) under Byzantine faults. At `n = 3`, `f = 1`,
`B = {1}` (the equivocating Byzantine node), the two crash majorities `{0,1}`
and `{1,2}` have honest cores `{0}` and `{2}`; the split ballot (`0 ↦ 3`,
`2 ↦ 4`) makes BOTH `3` and `4` "certified" (each quorum's honest members
unanimously vote its value) with `3 ≠ 4`. Byzantine agreement FAILS: the two
quorums' only common member is Byzantine, so nothing forces the values equal.
Under a real `IsByzQuorum` the honest cores would overlap
(`byz_quorum_honest_intersect`) and agreement would hold — the `> 2n/3` bound is
load-bearing. -/
theorem crash_majority_byz_agreement_fails :
    ∃ (B : Finset (Fin 3)) (votes : Fin 3 → Option ℕ) (v1 v2 : ℕ),
      B.card ≤ 1 ∧
      (∃ Q : Finset (Fin 3), IsQuorum Q ∧ ∀ r ∈ Q, r ∉ B → votes r = some v1) ∧
      (∃ Q : Finset (Fin 3), IsQuorum Q ∧ ∀ r ∈ Q, r ∉ B → votes r = some v2) ∧
      v1 ≠ v2 := by
  refine ⟨{1}, fun r => if r = 2 then some 4 else some 3, 3, 4,
          by decide, ?_, ?_, by decide⟩
  · exact ⟨{0, 1}, by unfold IsQuorum; decide, by decide⟩
  · exact ⟨{1, 2}, by unfold IsQuorum; decide, by decide⟩

end ByzBite

/-! ## 5. Anti-vacuity — a concrete `n=4, f=1` Byzantine decision and agreement. -/

namespace ByzWitness

/-- Four replicas — the minimal Byzantine population for `f = 1` (`3f+1 = 4`). -/
abbrev N : ℕ := 4
/-- One tolerated Byzantine fault. -/
abbrev F : ℕ := 1

/-- The fault set: replica 3 is Byzantine. `|B| = 1 ≤ f`. -/
def B : Finset (Fin N) := {3}

/-- The fault set respects the budget. -/
theorem B_card : B.card ≤ F := by decide

/-- The population bound `n ≥ 3f+1` holds (`4 ≥ 4`). -/
theorem n_bound : N ≥ 3 * F + 1 := by decide

/-- The ballot: honest replicas vote `7`; the Byzantine node 3 **equivocates**,
voting `99`. `ByzDecided` ignores node 3's vote, so its equivocation is harmless. -/
def votes : Fin N → Option ℕ := fun r => if r = 3 then some 99 else some 7

/-- The Byzantine node genuinely equivocates (`votes 3 = some 99 ≠ 7`) — the
witness is not a degenerate all-honest configuration. -/
theorem byz_node_equivocates : votes 3 = some 99 ∧ (99 : ℕ) ≠ 7 := by decide

/-- First Byzantine quorum `{0,1,2}` (`3·3 = 9 > 8 = 2·4`). -/
def Q1 : Finset (Fin N) := {0, 1, 2}
/-- Second Byzantine quorum `{1,2,3}` — genuinely distinct from `Q1`. -/
def Q2 : Finset (Fin N) := {1, 2, 3}

/-- `{0,1,2}` is a Byzantine quorum. -/
theorem q1_byz : IsByzQuorum Q1 := by unfold IsByzQuorum Q1; decide
/-- `{1,2,3}` is a Byzantine quorum. -/
theorem q2_byz : IsByzQuorum Q2 := by unfold IsByzQuorum Q2; decide
/-- The two Byzantine quorums are genuinely different sets. -/
theorem quorums_distinct : Q1 ≠ Q2 := by decide

/-- The honest core of the intersection is exactly `{1,2}` — two HONEST replicas
(both `∉ B`), the members that force agreement. -/
theorem honest_core : (Q1 ∩ Q2) \ B = {1, 2} := by decide

/-- `byz_quorum_honest_intersect` inhabited on the concrete pair: the two
Byzantine quorums share an honest replica. -/
theorem honest_intersection : ∃ r, r ∈ Q1 ∧ r ∈ Q2 ∧ r ∉ B :=
  byz_quorum_honest_intersect (f := F) n_bound B_card q1_byz q2_byz

/-- `7` is certified via `Q1`: every honest member of `{0,1,2}` voted `7`. -/
theorem decided7_via_q1 : ByzDecided B votes 7 := ⟨Q1, q1_byz, by decide⟩

/-- `7` is certified via the different quorum `Q2 = {1,2,3}`: its honest members
`{1,2}` voted `7`; the Byzantine member 3 (`∈ B`) is ignored. -/
theorem decided7_via_q2 : ByzDecided B votes 7 := ⟨Q2, q2_byz, by decide⟩

/-- Honest consistency: `votes` is a function, so each honest replica casts at
most one value. -/
theorem honest_consistent :
    ∀ r, r ∉ B → ∀ w1 w2 : ℕ, votes r = some w1 → votes r = some w2 → w1 = w2 := by
  intro r _ w1 w2 h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- **Byzantine agreement, non-vacuously.** Two certificates through two
*different* Byzantine quorums are forced equal by `byz_agreement` — a real
equality `7 = 7` derived *through* the honest-intersection lemma (not `rfl`),
despite the Byzantine node 3 equivocating. -/
theorem byz_agreement_nonvacuous : (7 : ℕ) = 7 :=
  byz_agreement (f := F) n_bound B_card honest_consistent decided7_via_q1 decided7_via_q2

/-- **Byzantine validity, inhabited.** The certified value is traced back to a
real HONEST vote — a Byzantine-only quorum could not have produced it. -/
theorem validity_witness : ∃ r, r ∉ B ∧ votes r = some 7 :=
  byz_validity (f := F) n_bound B_card decided7_via_q1

end ByzWitness

end DLCD
