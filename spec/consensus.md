# DLC-D Consensus — single-decree and multi-decree safety + liveness (Phase R0 — spec mirror)

**Status:** Descriptive mirror of `lean/DLCD/Consensus.lean`,
`lean/DLCD/MultiDecree.lean`, `lean/DLCD/Termination.lean`, and
`lean/DLCD/MultiDecreeLiveness.lean`. As with `spec/rsm-semantics.md`, the Lean
is the source of truth and this document trails it; every definition and theorem
name matches the Lean exactly.

**Model, not runtime.** These are guarantees about the Lean consensus model, not
about a running consensus service. Leader election is **not** modelled (quorums
are given, not elected); liveness assumes an explicit, FLP-necessary fairness
hypothesis (§3). All theorems below are proved with no `sorry`.

This document earns the `CommittedLog` oracle that `spec/rsm-semantics.md` took
as given: it shows the committed log is a **function of the votes**, not a free
assumption. It is organized as single-decree safety (§1–§2), the oracle bridge
(§2.3), multi-decree safety / log matching (§2.4), and liveness (§3).

---

## 0. Prior art (canonical references; URLs recorded)

- Lamport, *The Part-Time Parliament* / *Paxos Made Simple* — single-decree
  Paxos and quorum intersection.
- mwhittaker, *Single-Decree Paxos* — the phase-1/phase-2 quorum decision and
  the intersection argument:
  <https://mwhittaker.github.io/blog/single_decree_paxos/>
- Howard–Malkhi–Spiegelman, *Flexible Paxos: Quorum intersection revisited*
  (arXiv:1608.06696): <https://arxiv.org/abs/1608.06696>,
  <https://fpaxos.github.io/>
- Chand–Liu–Stoller, *Formal Verification of Multi-Paxos for Distributed
  Consensus*, FM 2016 — per-slot safety ("for each slot, only a single command
  may be decided"): <https://arxiv.org/pdf/1606.01387>,
  <https://www3.cs.stonybrook.edu/~stoller/papers/fm2016.pdf>
- García-Pérez–Gotsman–Meshman–Sergey, *Paxos Consensus, Deconstructed and
  Abstracted*, ESOP 2018 — Multi-Paxos safety by *reusing* single-decree Paxos:
  <https://ilyasergey.net/assets/pdf/papers/paxos-deconstructed-esop18.pdf>
- Ongaro–Ousterhout, *Raft* — Log Matching / State-Machine Safety over a
  replicated log of slots: <https://raft.github.io/raft.pdf>
- van Renesse–Altinbuken, *Paxos Made Moderately Complex* — per-slot liveness
  ("if one or more commands have been proposed for a slot, some command is
  eventually decided for that slot"):
  <https://www.cs.cornell.edu/home/rvr/Paxos/paxos.pdf>
- decentralizedthoughts, *From Single-Shot Agreement to State Machine
  Replication* — SMR as an array of single-shot instances, one per slot:
  <https://decentralizedthoughts.github.io/2022-11-19-from-single-shot-to-smr/>
- Fischer–Lynch–Paterson (FLP, 1985) — async + one crash ⇒ no deterministic
  consensus, so a fairness assumption is *mandatory* (the necessity witnessed by
  the liveness bites in §3).

---

## 1. Single-decree consensus (`DLCD.Consensus`)

A single decree (one log slot) is modelled over a finite replica set `Fin n`,
values `V`. All definitions are in `section Consensus` with
`variable {n : ℕ} {V : Type*}`.

### 1.1 Quorums and the intersection lemma

```
def IsQuorum (Q : Finset (Fin n)) : Prop := 2 * Q.card > n     -- STRICT majority

theorem quorum_intersect {Q1 Q2 : Finset (Fin n)}
    (h1 : IsQuorum Q1) (h2 : IsQuorum Q2) : (Q1 ∩ Q2).Nonempty
```

**Design notes**

- A quorum is a **strict** majority. Strict `>` is the load-bearing choice: it
  makes majorities a *self-intersecting* quorum system — any two overlap.
- `quorum_intersect` is **THE KEY LEMMA**; every safety guarantee below flows
  from it. The proof is `card` pigeonhole:
  `card(Q1∪Q2) ≤ n < card(Q1)+card(Q2)` and
  `card(Q1∪Q2)+card(Q1∩Q2) = card(Q1)+card(Q2)` (inclusion–exclusion), so
  `card(Q1∩Q2) > 0`.
- **Right-reason bite.** Weakening to `2·card ≥ n` (allowing exact-half
  "quorums") breaks everything: `weak_agreement_fails` exhibits two **disjoint**
  half-sets of `Fin 2`, each a weak "quorum", deciding *different* values, so
  `quorum_intersect` and hence `agreement` genuinely fail at `≥`
  (`weak_quorums_disjoint` records the empty intersection). The strict `>` is
  essential.

### 1.2 Votes, decision, and the safety core

```
abbrev Votes (n : ℕ) (V : Type*) := Fin n → Option V     -- each replica casts ≤ one value

def Decided (votes : Fin n → Option V) (v : V) : Prop :=
  ∃ Q : Finset (Fin n), IsQuorum Q ∧ ∀ r ∈ Q, votes r = some v

theorem agreement {votes} {v1 v2 : V}
    (h1 : Decided votes v1) (h2 : Decided votes v2) : v1 = v2

theorem validity {votes} {v : V} (h : Decided votes v) : ∃ r, votes r = some v

theorem decided_proposed {votes} {Proposed : V → Prop}
    (hvp : ∀ r v, votes r = some v → Proposed v) {v}
    (h : Decided votes v) : Proposed v
```

**Design notes**

- `Votes` is a *function* returning one value per replica — single decree.
- `Decided votes v` says a whole quorum unanimously voted `v`.
- **`agreement` is the safety metatheorem**: at most one value is decided. A
  replica in `Q1 ∩ Q2` (from `quorum_intersect`) voted `some v1` and `some v2`;
  a function returns one value, so `v1 = v2`.
- `validity` traces a decided value back to a real vote (via
  `quorum_intersect Q Q`); `decided_proposed` sharpens it: if replicas only vote
  proposed values, a decided value was proposed — the analogue of
  capability-safety's "only authorized commands are decided."

### 2.3 Discharging the log oracle (the bridge)

`spec/rsm-semantics.md` took `CommittedLog` as an oracle. Here each slot `i`
carries its own ballot `slotVotes i`; a log is legitimate iff each slot is that
slot's `Decided` value. Then the committed log is *determined* by the votes:

```
theorem committed_prefix_agree (slotVotes : ℕ → Votes n Command)
    (logA logB : CommittedLog) (hlen : logA.length = logB.length)
    (hA : ∀ i c, logA[i]? = some c → Decided (slotVotes i) c)
    (hB : ∀ i c, logB[i]? = some c → Decided (slotVotes i) c) :
    logA = logB

theorem replicas_converge_via_consensus (slotVotes : ℕ → Votes n Command)
    {init logA logB r1 r2} (hlen : logA.length = logB.length)
    (hA : …) (hB : …)
    (h1 : AppliedPrefix init logA r1) (h2 : AppliedPrefix init logB r2)
    (happ : r1.applied = r2.applied) :
    r1.store = r2.store
```

**Design notes**

- `committed_prefix_agree` is the **bridge lemma**: two legitimate logs of equal
  length agree slot-by-slot (per-slot `agreement`), hence are equal
  (`List.ext_getElem?`). The committed log is a function of the votes, not a
  free oracle.
- `replicas_converge_via_consensus` (guarantee **G4**) chains the bridge into
  the Phase-1.0 seed: two replicas running *independent* consensus instances
  (`logA`, `logB`) still converge, because agreement forces `logA = logB`. The
  shared-log assumption of `spec/rsm-semantics.md` is now **earned** per slot.

### 1.3 Honest scope of the single-decree increment

This increment is **SAFETY only** (agreement + validity + quorum intersection),
the tractable core, proved in full. **Termination / liveness** — that a decision
*is eventually reached* — is §3; nothing in `Consensus.lean` asserts progress.

---

## 2.4 Multi-decree safety / log matching (`DLCD.MultiDecree`)

The single-decree atom is lifted to a full replicated log: one independent
single-decree ballot per slot. Per Chand–Liu–Stoller and García-Pérez et al.,
this is *composition* — single-decree Paxos is **reused verbatim**; quorum
intersection is not reproved.

```
abbrev SlotBallots (n : ℕ) := ℕ → Votes n Command   -- one independent ballot per slot

def SlotDecided (sb : SlotBallots n) (i : ℕ) (c : Command) : Prop := Decided (sb i) c

theorem slot_agreement (sb) (i) {c₁ c₂} (h₁ : SlotDecided sb i c₁)
    (h₂ : SlotDecided sb i c₂) : c₁ = c₂ := agreement h₁ h₂

theorem slot_validity (sb) (i) {c} (h : SlotDecided sb i c) : ∃ r, sb i r = some c

def LogConsistent (sb : SlotBallots n) (log : CommittedLog) : Prop :=
  ∀ i c, log[i]? = some c → SlotDecided sb i c

theorem log_agreement {sb log₁ log₂}
    (h₁ : LogConsistent sb log₁) (h₂ : LogConsistent sb log₂) :
    ∀ (i) (c₁ c₂), log₁[i]? = some c₁ → log₂[i]? = some c₂ → c₁ = c₂

theorem log_agreement_eq {sb log₁ log₂} (hlen : log₁.length = log₂.length)
    (h₁ : LogConsistent sb log₁) (h₂ : LogConsistent sb log₂) : log₁ = log₂

theorem replicas_converge_multidecree {sb init log₁ log₂ r1 r2}
    (hlen : …) (h₁ : …) (h₂ : …) (hp1 : …) (hp2 : …)
    (happ : r1.applied = r2.applied) : r1.store = r2.store
```

**Design notes**

- Slots are bare naturals — no order structure between decrees is needed for
  safety (Chand–Liu–Stoller). `sb i` is exactly a single-decree ballot.
- **`slot_agreement`** is *literally* `Consensus.agreement` instantiated at
  `votes := sb i` — the multi-decree safety atom, inheriting `quorum_intersect`.
- **`log_agreement`** is Raft's **Log Matching / State-Machine Safety**: two
  logs consistent with the same slot-ballots agree at every index (pointwise
  `slot_agreement`).
- **`log_agreement_eq`** (guarantee **G4**) folds that to *equal logs* at equal
  length — the committed log is a function of the ballots.
  `replicas_converge_multidecree` chains to equal stores via the Phase-1.0 seed.
- **Right-reason bite.** `weak_slot_breaks_log_agreement`: at a single slot over
  `Fin 2`, a *weak* per-slot quorum (`2·card ≥ n`) lets two disjoint singletons
  `{0}`, `{1}` decide different commands `cA ≠ cB`; then `[cA]` and `[cB]` are
  each weak-consistent yet disagree at slot 0 — `log_agreement` is refuted.
  Strict-majority-per-slot is load-bearing.
- **Leader election is deferred.** Paxos *safety* holds regardless of leader:
  agreement per slot follows from quorum intersection alone, never from who
  proposed. A dueling-proposer scenario can stall *progress* but can never
  decide two commands at one slot, so no leader model is assumed here.

---

## 3. Liveness — the log grows under fairness (FLP-necessity)

Safety is silent about progress. The liveness increment supplies the matching
progress property under an explicit, FLP-necessary fairness assumption.

### 3.1 The fairness hypotheses and single-decree progress (`DLCD.Termination`)

```
def WeakFair (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V) : Prop :=
  ∀ k r, r ∈ Q → sched k r = none → ∃ k', k' > k ∧ sched k' r = some v

def MonotoneVotes (sched : ℕ → Votes n V) : Prop :=
  ∀ k r x, sched k r = some x → sched (k + 1) r = some x

theorem weakfair_terminates (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V)
    (hwf : WeakFair sched Q v) (hmono : MonotoneVotes sched) (hq : IsQuorum Q)
    (hhonest : ∀ k r, r ∈ Q → sched k r ≠ none → sched k r = some v) :
    ∃ k, Decided (sched k) v
```

**Design notes**

- **`WeakFair`**: an enabled quorum replica that has not yet voted *eventually*
  (at some strictly later step) casts vote `v`. This is the standard weak-
  fairness / non-starvation scheduling assumption.
- **`MonotoneVotes`** (non-retraction): once a replica votes a value it keeps it
  forever — the single-decree "votes are not retracted" invariant.
- **`weakfair_terminates`** (guarantee **G3**, single-decree progress): under
  weak fairness, monotone votes, a majority quorum, and honesty (quorum
  replicas only ever vote `v`), a value is eventually `Decided`. The proof is a
  well-founded rank-decrease argument (`weakfair_reaches_zero`), where the rank
  counts un-voted quorum replicas.
- **FLP-necessity, right-reason bite.** `WeakFairBite`: a starved schedule
  (`starve`: replica 0 perpetually enabled, never voting) never decides
  (`starve_never_decides`) and is provably *not* `WeakFair`
  (`starve_not_weakfair`), so `bite_needs_weakfair` shows the fairness
  hypothesis is load-bearing — exactly FLP made concrete. The bridge theorem
  `command_eventually_written_weakfair` re-founds the earlier liveness metatheorem
  on `WeakFair`, guarded by `budget.fairDelivery` (the `FailureBudget` contract).

### 3.2 Multi-decree liveness (`DLCD.MultiDecreeLiveness`)

The per-ballot termination theorem is lifted across slots: each slot gets its
own time-evolving ballot, and every slot is eventually decided, so the log grows
without bound. Termination is **not reproved** — `weakfair_terminates` is applied
verbatim per slot.

```
abbrev SlotSchedule (n : ℕ) := ℕ → ℕ → Votes n Command    -- slot i, time t ↦ ballot

theorem log_grows_unbounded (ss : SlotSchedule n) (Q : Finset (Fin n))
    (props : ℕ → Command)
    (hlive : ∀ i, WeakFair (ss i) Q (props i) ∧ MonotoneVotes (ss i) ∧
      (∀ k r, r ∈ Q → (ss i) k r ≠ none → (ss i) k r = some (props i)))
    (hq : IsQuorum Q) :
    ∀ L, ∃ (sb : SlotBallots n) (log : CommittedLog),
      log.length = L ∧ LogConsistent sb log ∧ ∀ i, i < L → SlotDecided sb i (props i)
```

**Design notes**

- **`log_grows_unbounded`** (guarantee **G3**, multi-decree liveness): for *any*
  target length `L`, there is a snapshot `sb` (each slot sampled at its own
  decision time `t i`, extracted by choice from the per-slot `∃ t`) and a
  length-`L` `LogConsistent` log — every one of its `L` slots is `Decided`. The
  snapshot is a *genuinely reached* configuration, not an oracle. A companion
  `log_decided_by_bounded_time` gives the honest "eventually, all of a finite
  prefix has decided" via `Finset.sup` of the finitely-many decision times.
- **Right-reason bite.** `starved_slot_stalls_growth`: starve one slot `i₀` (the
  Command-lift of the `WeakFairBite.starve`) and it never decides, so no
  `LogConsistent` log carries an entry at `i₀`; in prefix-ordered application
  (`deliver` applies slot `i₀+1` only after `i₀`) growth *stalls at `i₀`*. Per-
  slot weak-fairness is necessary for growth — FLP made concrete, per slot.

### 3.3 Honest scope of liveness

- Liveness is under **per-slot weak-fairness + majority quorum**; weak fairness
  is the standard FLP-necessary scheduling assumption, its necessity witnessed
  by the bites. Without it a slot starves forever and the log cannot grow.
- **Leader election is still deferred** — liveness is per-slot and assumes each
  slot's honest replicas eventually vote its proposal; who proposes (leader) and
  dueling-proposer termination are orthogonal and not modelled.
- The fairness schedule is **modelled, not tied to a running scheduler** (the
  live-scheduling open fence). `weakfair_terminates` / `log_grows_unbounded` use
  `Classical.choice` for fair-schedule extraction.
- Safety (§2) and liveness (§3) are complementary: neither implies the other.
