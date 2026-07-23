# DLC-D Distributed Guarantees — the G1–G4 manifest (Phase R0 — spec mirror)

**Status:** Descriptive mirror of the machine-checked ledger
`lean/DLCD/Summary.lean` and its per-theorem status records in
`lean/theorem-status.json` (`DLCD_*` keys). This document is the **doc-level
twin** of that ledger: for each guarantee it names the theorem exactly as the
ledger re-exports it, gives a one-line English statement, cites the module, and
records the honest OPEN fences. Keep the two consistent — `Summary.lean` carries
a name-drift tripwire (`abbrev … := @DLCD.<name>`) that fails to compile if a
headline theorem is renamed or deleted; this file must be edited in lockstep.

**Model, not runtime.** Every guarantee below is about the **Lean model** of the
replicated delegation register, *not* about `dlc-verifier`'s Rust at run time
(the runtime is the separately-approved R1–R6 program). Each `DLCD_*` theorem is
a top-level, fully-proved (`status = "proven"`, no `sorry`) statement whose
axioms are snapshotted within `[propext, Classical.choice, Quot.sound]`
(`lean/expected-axioms/dlcd-*.txt`). `status = "proven"` means proved **as
stated about the DLC-D model**; the fences below record what the model does and
does not cover.

The operational substrate the guarantees are stated over is `spec/rsm-
semantics.md`; the consensus that earns the committed log is `spec/consensus.md`.

---

## The four guarantee classes at a glance

| Class | Theorem (ledger name) | Module |
|---|---|---|
| **G1** authority | `capability_safety` | `DLCD/CapSafety.lean` |
| **G1** authority (linear) | `capability_safety_linear` | `DLCD/CapSafetyLinear.lean` |
| **G1** confidentiality (semantic) | `log_noninterference` | `DLCD/LabelFlow.lean` |
| **G1** confidentiality (typed) | `distributed_noninterference` | `DLCD/DistributedNI.lean` |
| **G1** confidentiality (fence-closer) | `wellTypedLog_implies_htyped` | `DLCD/TypedLog.lean` |
| **G2** linearizability | `single_linearization` | `DLCD/Linearizable.lean` |
| **G3** liveness (single-decree) | `weakfair_terminates` | `DLCD/Termination.lean` |
| **G3** liveness (multi-decree) | `log_grows_unbounded` | `DLCD/MultiDecreeLiveness.lean` |
| **G4** convergence (consensus) | `replicas_converge_via_consensus` | `DLCD/Consensus.lean` |
| **G4** convergence (CALM) | `Calm.coordination_free_convergence` | `DLCD/Calm.lean` |
| **G4** multi-decree safety | `log_agreement_eq` | `DLCD/MultiDecree.lean` |
| **Seal** joint satisfiability | `SliceWitness.dlc_d_slice_witness` | `DLCD/Witness.lean` |

All are re-exported under namespace `DLCD.Ledger` in `Summary.lean`.

---

## G1 — authority + confidentiality

### `capability_safety` — authority enforced by construction

```
theorem capability_safety (log : CommittedLog) (hwf : WellFormedLog log) :
    ∀ c ∈ log, ∃ issuer, Authorized c issuer
```

- **English.** Every command in a well-formed committed log carries a genuine
  `Deriv (issuer says writeCap)` credential — authority is enforced by
  construction, not audited after the fact.
- **How.** `Authorized c issuer` requires `c.cap = some (Prop'.says issuer
  capProp)` *and* a `Nonempty (Deriv Γ capTerm (Prop'.says issuer capProp))`
  witness. `WellFormedLog` is an inductive provenance predicate (empty, or an
  `Authorized` `commit` onto a well-formed log); the theorem *extracts*
  authorization by induction over that provenance. The `commit` function
  (`spec/rsm-semantics.md` §3) is the only ingress and demands the proof.
  `committed_write_says_cap` specializes this to writes.
- **Fences.** Model, not runtime. `saysI`-on-`CDeriv`: see the linear layer.

### `capability_safety_linear` — the same, over the linear CARVe credential

```
theorem capability_safety_linear (log : CommittedLog) (hwf : WellFormedLogL log) :
    ∀ c ∈ log, ∃ issuer, AuthorizedL c issuer
```

- **English.** The linear twin of `capability_safety`: every command in a
  well-formed log carries a `CDerivS` (linear, resource-correct) signed
  `issuer says capProp` credential.
- **How.** `AuthorizedL` uses a `CDerivS` witness — a *sealed* judgment layered
  over the DILL-sound CARVe judgment `CDeriv`. `CDerivS.embed` lifts any `CDeriv`
  derivation; `CDerivS.saysI` adds the linear signed-affirmation introduction
  that `CDeriv` deliberately cannot host (adding `saysI` directly to `CDeriv`
  would make its modality-keeping `saysE` β-branch reachable and untypable,
  breaking subject reduction). The seal never feeds back into `CDeriv`, so no
  `CDeriv` metatheorem is perturbed. `CDerivS.saysI` passes the context through
  **unchanged**, so a linear (`Mult.one`) subject stays linear.
- **Fences.** Model, not runtime. This *partly addresses* the `saysI`-on-`CDeriv`
  fence — the linear signed credential now runs on a judgment built over the
  migrated CARVe judgment — but a *functorial* `Deriv → CDerivS` embedding
  (making the additive and linear layers one) is **honestly deferred**; the
  credential *shapes* correspond one-for-one, the embedding does not yet exist.

### `log_noninterference` — semantic confidentiality

```
theorem log_noninterference (ℓ : Label) (log : List LCommand) (s0 : LStore) :
    view ℓ (applyPrefixL log s0)
      = view ℓ (applyPrefixL (log.filter (fun lc => flowsTo lc.label ℓ)) s0)
```

- **English.** A labelled log's low-observable projection (`view ℓ`) is
  independent of its high inputs — applying the whole log and applying only its
  `⊑ ℓ` subsequence induce the *same* low view.
- **How.** A Goguen–Meseguer purge argument: high commands move only high cells,
  and the low subsequence is oblivious to that (`applyL_high_lowAgree`,
  `applyPrefixL_lowAgree`). The corollary `view_depends_only_on_low` states that
  two logs agreeing on their `⊑ ℓ` subsequence induce equal low views.
- **Fences.** Model, not runtime.

### `distributed_noninterference` — typed confidentiality across replicas

```
theorem distributed_noninterference (ℓLow : Label) (χ : Prop') {ℓhigh : Label}
    (hhigh : Label.le ℓhigh ℓLow = false) :
    ∀ (k : Nat) {g₁ g₂ : GlobalConfig}, g₁.log = g₂.log →
      LowEquivG ℓLow (Prop'.at χ ℓhigh) g₁ g₂ →
      LowEquivG ℓLow (Prop'.at χ ℓhigh) (worldSteps k g₁) (worldSteps k g₂)
```

- **English.** Two globally-configured runs that are low-equivalent at a high
  type stay low-equivalent after any number `k` of world steps — a high store
  difference stays invisible to a low observer across replicas and time.
- **How.** Induction on `k` over `worldStep_preserves_high`, reusing DLC's
  fundamental-lemma non-interference (`DLC.t3_two_run_general`).
- **Fences.** Model, not runtime. The confidentiality strength **inherits
  `T3_noninterference`'s propositional-core fragment scope** (it consumes
  `DLC.t3_two_run_general`, whose fragment is the propositional computational
  core, non-interference modulo declassification); extending from `PropDeriv` to
  the full `Deriv` judgment with linear context splitting is that layer's open
  item.

### `wellTypedLog_implies_htyped` — closing the typed-log fence

```
theorem wellTypedLog_implies_htyped {φ : Prop'} {log : CommittedLog}
    (hwt : WellTypedLog φ log) :
    ∀ (n : Nat) (c : Command), log[n]? = some c →
      Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true
```

- **English.** A well-typed committed log discharges the host-typing premise
  that `distributed_noninterference` consumes — so the typed guarantee actually
  *fires on real logs*, not just under a raw assumption.
- **How.** `WellTypedLog` is an admission-gate invariant; each entry is a closed
  low-preserving core endomorphism `φ ⊸ φ`. `worldStep_preserves_low_typed`
  removes the raw `htyped` assumption by feeding this through.
- **Fences.** Model, not runtime; the admission gate is a modelled
  well-typedness check, not a running validator.

---

## G2 — linearizability

### `single_linearization` — one sequential order respected by all

```
theorem single_linearization {init : Term} {log : CommittedLog} {r1 r2 : Replica}
    (h1 : AppliedPrefix init log r1) (h2 : AppliedPrefix init log r2) :
    ∃ σ : Nat → Term, r1.store = σ r1.applied ∧ r2.store = σ r2.applied
```

- **English.** All replicas' observed stores are samples of ONE sequential
  trajectory `seqTrajectory init log` at their own applied index — a single
  linearization order respected by all (Herlihy–Wing linearizability specialized
  to the deterministic register).
- **How.** The trajectory `σ := seqTrajectory init log` is exactly
  `applyPrefix init (log.take k)`; both replicas' stores are that function
  sampled at their index (`linearizable` unpacks the existential;
  `linearizable_via_consensus` discharges the log oracle so even independent
  consensus instances share one order).
- **Fences.** Model, not runtime. **Store-type change**: the committed store is a
  fixed `Term`; generalizing the result to a richer store type is future work.

---

## G3 — liveness

### `weakfair_terminates` — single-decree progress

```
theorem weakfair_terminates (sched : ℕ → Votes n V) (Q : Finset (Fin n)) (v : V)
    (hwf : WeakFair sched Q v) (hmono : MonotoneVotes sched) (hq : IsQuorum Q)
    (hhonest : ∀ k r, r ∈ Q → sched k r ≠ none → sched k r = some v) :
    ∃ k, Decided (sched k) v
```

- **English.** Under weak fairness (plus non-retraction, a majority quorum, and
  honesty) a single decree is eventually decided.
- **How.** Well-founded rank-decrease on the count of un-voted quorum replicas
  (`weakfair_reaches_zero`). See `spec/consensus.md` §3.1.
- **Fences.** Model, not runtime. **Live-scheduling**: the weak-fairness /
  delivery schedule is modelled, not tied to a running scheduler.
  **Leader election**: quorums are given, not elected. Uses `Classical.choice`.

### `log_grows_unbounded` — multi-decree liveness

```
theorem log_grows_unbounded (ss : SlotSchedule n) (Q : Finset (Fin n))
    (props : ℕ → Command) (hlive : …) (hq : IsQuorum Q) :
    ∀ L, ∃ (sb : SlotBallots n) (log : CommittedLog),
      log.length = L ∧ LogConsistent sb log ∧ ∀ i, i < L → SlotDecided sb i (props i)
```

- **English.** Under a fair per-slot schedule the multi-decree committed log
  grows without bound: for any target length `L` there is a *reached* snapshot
  and a length-`L` `LogConsistent` log.
- **How.** Lifts `weakfair_terminates` across slots (applied verbatim per slot),
  then materializes the log. See `spec/consensus.md` §3.2.
- **Fences.** Model, not runtime. **Live-scheduling**: the fair slot schedule is
  modelled, not tied to a running scheduler. Uses `Classical.choice`.

---

## G4 — convergence + multi-decree safety

### `replicas_converge_via_consensus` — coordination-based convergence

```
theorem replicas_converge_via_consensus (slotVotes : ℕ → Votes n Command)
    {init logA logB r1 r2} (hlen : logA.length = logB.length) (hA : …) (hB : …)
    (h1 : AppliedPrefix init logA r1) (h2 : AppliedPrefix init logB r2)
    (happ : r1.applied = r2.applied) :
    r1.store = r2.store
```

- **English.** Replicas that deliver a quorum-`Decided` value reach EQUAL stores,
  even from independent consensus instances — agreement forces the logs equal,
  the deterministic fold finishes.
- **How.** `committed_prefix_agree` (per-slot `agreement`) ⇒ `logA = logB` ⇒
  Phase-1.0 seed `replicas_converge_on_prefix`. See `spec/consensus.md` §2.3.
- **Fences.** Model, not runtime. **Leader election**: quorums are given, not
  elected. Uses `Classical.choice`.

### `Calm.coordination_free_convergence` — the CALM route

```
theorem coordination_free_convergence {ds₁ ds₂ : List L} (s₀ : L)
    (hset : ∀ x, x ∈ ds₁ ↔ x ∈ ds₂)
    {r₁ r₂ : L} (h₁ : r₁ = merge ds₁ s₀) (h₂ : r₂ = merge ds₂ s₀) :
    r₁ = r₂
```

- **English.** Monotone / commutative (join-with-delta) updates converge with
  **no coordination** — two replicas that absorbed the same *set* of deltas
  reach the same state, robust to reordering *and* duplication (Hellerstein–
  Alvaro CALM: monotone ⇒ coordination-free).
- **How.** `merge` is a `SemilatticeSup` join-fold; `merge_mem_invariant` makes
  the result depend only on the delta set. The right-reason bite
  (`overwrite_merge_diverges`) shows a non-monotone last-writer-wins update
  *diverges* — the CALM boundary is real.
- **Fences.** Model, not runtime.

### `log_agreement_eq` — multi-decree safety / agreement

```
theorem log_agreement_eq {sb : SlotBallots n} {log₁ log₂ : CommittedLog}
    (hlen : log₁.length = log₂.length)
    (h₁ : LogConsistent sb log₁) (h₂ : LogConsistent sb log₂) : log₁ = log₂
```

- **English.** Two logs agreeing on the per-slot ballots are equal — Raft Log
  Matching (see `spec/consensus.md` §2.4).
- **How.** `List.ext_getElem?` + pointwise `log_agreement` (⇐ `slot_agreement`
  ⇐ `agreement` ⇐ `quorum_intersect`).
- **Fences.** Model, not runtime. Uses `Classical.choice`.

---

## The seal — `SliceWitness.dlc_d_slice_witness`

```
def dlc_d_slice_witness : SliceWitnessBundle where
  capability_authorized := g1_capability_safe
  wellFormed            := committedLog_wellFormed
  decided               := wcmd_decided
  converged             := replicas_converge
  linearizable          := linearizable_run
  live                  := ⟨write_live.1, both_eventually_apply.1, both_eventually_apply.2⟩
  state_changed         := state_changed
```

- **English.** One inhabited `SliceWitnessBundle` on a single real 2-replica
  execution that is *simultaneously* capability-authorized, consensus-committed,
  converging, linearizable, and live — THE demonstration that G1–G4 are **jointly
  satisfiable**, not vacuously true. The `def`-shaped seal is itself the proof:
  an inhabited bundle *is* a proof of joint satisfiability.
- **Non-vacuity.** The write payload `λ_. ⟨x, x⟩` genuinely changes the store
  (`state_changed : r1.store ≠ init`), the budget contract holds
  (`budget.withinContract = true`), and the negative contrast
  (`unauthWrite_not_authorized`) shows the capability gate is real — an
  unguarded write (`cap = none`) can never enter a well-formed log.
- **Fences (inherited, joint):** model not runtime; store-type change;
  live-scheduling; `saysI`-on-`CDeriv` (now *partly* addressed by `CDerivS`, see
  G1 linear); leader election; surface syntax (examples are built in abstract
  syntax, not the concrete surface language).

---

## The honest OPEN fences (consolidated)

Every guarantee above carries one or more of these; none is overclaimed away:

1. **Model, not runtime** — guarantees about the Lean model, not `dlc-verifier`
   at run time. The runtime is the separately-approved R1–R6 program. *(all)*
2. **Store-type change** — the committed store is a fixed `Term`. *(G2, seal)*
3. **Live-scheduling** — `FailureBudget.fairDelivery` / the fair slot schedule
   is a modelled assumption, not tied to a running scheduler (FLP makes some
   fairness assumption mandatory). *(G3, seal)*
4. **`saysI`-on-`CDeriv`** — the migrated CARVe judgment did not natively carry
   the signed `says` credential; `CDerivS` (G1 linear) now hosts it as a sealed
   layer, but a functorial `Deriv → CDerivS` embedding is deferred. *(G1, seal)*
5. **Leader election** — quorums are given, not elected. *(G3, G4, seal)*
6. **Surface syntax** — examples are in abstract syntax, not the concrete
   surface language. *(seal)*
7. **Confidentiality fragment** — `distributed_noninterference` inherits the
   propositional-core fragment scope of the non-interference lemma it consumes
   (`DLC.t3_two_run_general`), non-interference modulo declassification. *(G1)*

---

## Prior art (canonical references; URLs recorded)

- Hawblitzel et al., *IronFleet* (machine-checked RSM safety + liveness manifest):
  <https://www.microsoft.com/en-us/research/publication/ironfleet-proving-safety-liveness-practical-distributed-systems/>
- Herlihy–Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects*, TOPLAS 12(3), 1990 (G2): <https://dl.acm.org/doi/10.1145/78969.78972>
- Ongaro–Ousterhout, *Raft* — Log Matching / State-Machine Safety (G4):
  <https://raft.github.io/raft.pdf>
- Hellerstein–Alvaro, *Keeping CALM: When Distributed Consistency Is Easy* —
  monotone ⇒ coordination-free (G4 CALM): <https://arxiv.org/abs/1901.01930>
- Goguen–Meseguer, *Security Policies and Security Models* — non-interference /
  purge (G1 semantic confidentiality).
- Fischer–Lynch–Paterson (FLP, 1985) — the fairness necessity behind the G3
  live-scheduling fence.
- Chand–Liu–Stoller, *Formal Verification of Multi-Paxos*, FM 2016 (G4 safety):
  <https://www3.cs.stonybrook.edu/~stoller/papers/fm2016.pdf>
