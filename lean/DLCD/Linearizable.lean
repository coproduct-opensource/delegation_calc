import DLCD.Consensus

/-! # DLC-D Phase 1.2b — CONCURRENCY-SAFETY: linearizability of the replicated register

This module completes the fourth and final guarantee of the DLC-D vertical
slice — **concurrency-safety**, in its precise form for a replicated object:
**linearizability**. Phase 1.0 gave the deterministic per-replica fold
(`applyPrefix`), 1.1 earned the shared totally-ordered log via single-decree
consensus (`agreement` / `committed_prefix_agree`), and 1.2c gave liveness.
Here we prove that the replicated delegation register is a **linearizable
object**: its observable behavior is indistinguishable from a single
sequential execution in the committed-log order.

## The SMR-linearizability argument (why the committed log IS the linearization)

Linearizability (Herlihy–Wing 1990) asks for a single **total order** on
operations, consistent with real-time precedence, such that the object's
observed responses match a **sequential** run of the object's specification in
that order. State-machine replication realizes this almost by construction:

- **The linearization order = the committed log.** `CommittedLog := List Command`
  is a *List* — its positions are linearly ordered by index, and consensus
  (`agreement`) decides each slot exactly once. So there is ONE total order,
  shared by all correct replicas, and it is genuinely total (`linearization_total`,
  `position_functional`).
- **The sequential specification = `applyPrefix init`.** The register's
  sequential semantics is the deterministic fold of `applyCommand` in log order:
  `seqSpec init log := applyPrefix init log` is the state after the whole
  sequential history; `seqTrajectory init log k := seqSpec init (log.take k)` is
  the state after the first `k` committed operations — the object's specification
  automaton run locally.
- **Every observation lies on that one sequential trajectory.** A correct
  replica's `store` at `applied = k` is *exactly* `seqTrajectory init log k`
  (`store_is_seq_prefix` — this is essentially the Phase-1.0 `AppliedPrefix`
  invariant, repackaged as "the store is the sequential-spec run of a PREFIX of
  the committed total order"). No observation can contradict the sequential
  spec in log order.
- **All replicas share the one linearization.** By `agreement` /
  `committed_prefix_agree`, independent consensus instances produce the *same*
  committed log, so every replica linearizes against the SAME order
  (`linearizable_via_consensus`).

This is exactly the SMR route to linearizability: *processes agree on a
sequential order of the concurrent invocations, then each simulates the
sequential specification automaton locally* (Herlihy–Wing; the SMR framing in
arXiv:2407.01720 and Jepsen's linearizability model).

## The headline theorems

- `store_is_seq_prefix` — a correct replica's store is the sequential-spec run
  of a committed-log prefix (packaging `AppliedPrefix`).
- `single_linearization` (**THE METATHEOREM**) — for any two replicas (or one
  replica across time) following the protocol over the same committed log, there
  is a SINGLE sequential run `σ = seqTrajectory init log` such that each
  replica's observed store equals `σ` at its own applied-index. One
  linearization order, respected by all.
- `linearizable_via_consensus` — the same, but the shared log is *earned*: two
  replicas that ran independent single-decree consensus still linearize against
  ONE order, because `agreement` forces their logs equal.
- `observations_compatible` — real-time monotonicity: a *later* observation
  (larger `applied`) is a sequential *continuation* of an earlier one along the
  very same run. This is the real-time-order-respecting content, for the
  register's read/observe operations.
- `linearization_total` / `position_functional` — the linearization order
  exists and is a genuine total order (List positions, decided once per slot).

## Honest scope — what is PROVED vs. FENCED

**PROVED (the SMR-linearizability core for this register):** every reachable
correct-replica store equals `seqSpec` of a committed-log prefix; the committed
log is the single total order all replicas share (via `agreement`); later
observations continue earlier ones along that one run. For a replicated register
whose only observable is its store, *this is the linearizability content* — the
store-history is a sequential run of the spec in the committed order.

**FENCED (deliberately NOT formalized here):** the full Herlihy–Wing
*history* model — explicit invocation/response events with real-time
*intervals*, a `<_rt` partial order over overlapping operations, and the
existence-of-a-linearization theorem quantified over arbitrary concurrent
histories with pending operations. We model the *committed* order (the SMR
linearization point is "the slot is applied") and the store-trajectory it
induces, not client-side invocation/response timestamps. We also do NOT model
returns/read-responses as first-class operations (the register here is
write-then-observe-store); interval-linearizability relaxations for conditional
waits / bidirectional flows (argued to be the *right* SMR criterion in
arXiv:2407.01720) are explicitly out of scope. `observations_compatible`
supplies the real-time-monotonicity fragment that a full history model would
generalize.

## The right-reason bite

A replica whose store does NOT follow the committed order — one that claims to
have `applied` a slot but whose store was fabricated / left un-updated
(out-of-order or forged) — is NOT on the sequential trajectory:
`LinearizableBite.bad_off_trajectory` shows its store `≠ seqTrajectory` at its applied
index, and `LinearizableBite.bad_not_applied_prefix` shows it therefore *cannot* satisfy
`AppliedPrefix`. So the `AppliedPrefix`/in-order-application hypothesis is
load-bearing: drop it and a divergent store is not `seqSpec`-consistent, i.e.
the object is no longer linearizable. Linearizability is a property of protocol
runs, not of arbitrary stores.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Hauck–Heß, *Linearizability and State-Machine Replication: Is it a match?*
  (arXiv:2407.01720) — the SMR-linearization framing (agree a serial order, each
  replica simulates the sequential specification locally) and the argument that
  interval-linearizability is the right SMR criterion:
  https://arxiv.org/pdf/2407.01720 , https://arxiv.org/html/2407.01720v1
- Herlihy–Wing, *Linearizability: A Correctness Condition for Concurrent
  Objects* (TOPLAS 1990) — the definition: a total order consistent with
  real-time precedence matching a sequential specification run.
- Jepsen, *Linearizability* (the object-as-state-machine / total serial order
  model): https://jepsen.io/consistency/models/linearizable
- decentralizedthoughts, *Consensus for SMR* (the committed log is the total
  order; prefix completeness):
  https://decentralizedthoughts.github.io/2019-10-15-consensus-for-state-machine-replication/
- *A Unified Model of Non-transactional Consistency Levels* (arXiv:2409.01576)
  — linearizability as the strongest level, a serial total order:
  https://arxiv.org/pdf/2409.01576
-/

namespace DLCD

open DLC

/-! ## 1. The sequential specification and its trajectory. -/

/-- **The register's sequential specification.** The sequential semantics of the
delegation register is the deterministic fold of `applyCommand` over the whole
committed history in log order — the state after running the entire sequential
history from `init`. This IS the specification automaton an SMR replica
simulates locally. -/
def seqSpec (init : Term) (log : CommittedLog) : Term := applyPrefix init log

/-- The **sequential trajectory**: the object's state after the first `k`
committed operations, i.e. the sequential spec run on the length-`k` prefix of
the committed total order. This is the single sequence of states the whole
system is a view onto. -/
def seqTrajectory (init : Term) (log : CommittedLog) (k : Nat) : Term :=
  seqSpec init (log.take k)

/-- `seqSpec` is definitionally the Phase-1.0 fold — the specification and the
implementation share one transition function. -/
theorem seqSpec_eq_applyPrefix (init : Term) (log : CommittedLog) :
    seqSpec init log = applyPrefix init log := rfl

/-! ## 2. Linearization = the committed log: every store is a sequential prefix. -/

/-- **Every correct-replica observation lies on the sequential trajectory.** A
replica satisfying the in-order-application invariant `AppliedPrefix` has, at
`applied = k`, a store equal to the sequential-spec run of the length-`k`
committed prefix. This packages `AppliedPrefix` as the linearizability content:
the store is the sequential-specification run of a PREFIX of the committed total
order — no observation contradicts the spec in log order. -/
theorem store_is_seq_prefix {init : Term} {log : CommittedLog} {r : Replica}
    (h : AppliedPrefix init log r) :
    r.store = seqSpec init (log.take r.applied) := h

/-- Restated against the named trajectory: the store is the trajectory sampled
at the replica's applied-index. -/
theorem observation_on_trajectory {init : Term} {log : CommittedLog} {r : Replica}
    (h : AppliedPrefix init log r) :
    r.store = seqTrajectory init log r.applied := h

/-! ## 3. The committed log is a genuine TOTAL ORDER (the linearization order). -/

/-- **Positions are functional.** Each slot of the committed total order holds
exactly one command: `log[i]?` is a function, so the linearization order assigns
a unique operation to each position. (Consensus `agreement` is what makes this
hold across independent replicas; here it is the intrinsic List fact.) -/
theorem position_functional (log : CommittedLog) (i : Nat) {c c' : Command}
    (h : log[i]? = some c) (h' : log[i]? = some c') : c = c' := by
  rw [h] at h'; exact Option.some.inj h'

/-- **The linearization order is total.** The committed-log positions are the
natural numbers, linearly ordered: any two slots are comparable. Together with
`position_functional` this is exactly "a single total order on operations
exists" — the order Herlihy–Wing require, here supplied for free by the List. -/
theorem linearization_total (i j : Nat) : i < j ∨ i = j ∨ j < i :=
  Nat.lt_trichotomy i j

/-- The order is irreflexive and transitive (a strict total order): inherited
from `Nat.lt`. Bundled for the record. -/
theorem linearization_strict_order :
    (∀ i : Nat, ¬ i < i) ∧ (∀ i j k : Nat, i < j → j < k → i < k) :=
  ⟨fun i => Nat.lt_irrefl i, fun _ _ _ h1 h2 => Nat.lt_trans h1 h2⟩

/-- **The linearization, bundled.** The committed log presents one linearization:
a position map (the total order) and the single sequential trajectory every
correct replica's store is a sample of. -/
structure Linearization (init : Term) (log : CommittedLog) where
  /-- The total order: slot `i` of the committed order holds `log[i]`. -/
  positionOf : Nat → Option Command := fun i => log[i]?
  /-- The single sequential run of the spec in the committed order. -/
  trajectory : Nat → Term := seqTrajectory init log

/-- Canonical linearization of a committed log. -/
def theLinearization (init : Term) (log : CommittedLog) : Linearization init log := {}

/-- The canonical linearization is *faithful*: every correct replica's store lies
on its trajectory at the replica's applied-index. -/
theorem theLinearization_faithful {init : Term} {log : CommittedLog} {r : Replica}
    (h : AppliedPrefix init log r) :
    r.store = (theLinearization init log).trajectory r.applied := h

/-! ## 4. Real-time monotonicity: a later observation continues an earlier one. -/

/-- Split a `take j` at an earlier point `i ≤ j`: the length-`j` prefix is the
length-`i` prefix followed by the intervening slots. -/
theorem take_prefix_append (log : CommittedLog) {i j : Nat} (hij : i ≤ j) :
    log.take j = log.take i ++ (log.drop i).take (j - i) := by
  have hj : j = i + (j - i) := by omega
  conv_lhs => rw [hj]
  rw [List.take_add]

/-- **The sequential run composes along prefixes.** Running the spec to the
length-`j` prefix equals running it to the length-`i` prefix and then continuing
with the intervening committed slots (`i ≤ j`). This is the associativity of the
single sequential execution. -/
theorem seqSpec_take_continuation (init : Term) (log : CommittedLog) {i j : Nat}
    (hij : i ≤ j) :
    seqSpec init (log.take j)
      = applyPrefix (seqSpec init (log.take i)) ((log.drop i).take (j - i)) := by
  unfold seqSpec applyPrefix
  rw [take_prefix_append log hij, List.foldl_append]

/-- **REAL-TIME MONOTONICITY (observations are compatible).** For two replicas
following the protocol over the same committed log, if `r1` observed no later
than `r2` (`r1.applied ≤ r2.applied`), then `r2`'s store is a *sequential
continuation* of `r1`'s store along the one committed run — `r2` applied exactly
the intervening committed slots on top of `r1`'s state. So the later observation
never contradicts the earlier one; both are points on the single linearization,
in real-time order. This is the real-time-precedence fragment of Herlihy–Wing
for the register's observe operation. -/
theorem observations_compatible {init : Term} {log : CommittedLog} {r1 r2 : Replica}
    (hij : r1.applied ≤ r2.applied)
    (h1 : AppliedPrefix init log r1) (h2 : AppliedPrefix init log r2) :
    r2.store
      = applyPrefix r1.store ((log.drop r1.applied).take (r2.applied - r1.applied)) := by
  have e1 := store_is_seq_prefix h1
  have e2 := store_is_seq_prefix h2
  rw [e2, seqSpec_take_continuation init log hij, ← e1]

/-! ## 5. THE METATHEOREM — linearizability of the replicated register. -/

/-- **LINEARIZABILITY — the metatheorem (single committed log).** For any two
replicas (or a single replica at two times) that follow the protocol over the
*same* committed log, there is a SINGLE sequential run `σ = seqTrajectory init
log` — the sequential specification executed in the committed-log total order —
such that each replica's observed store equals `σ` at its own applied-index.
That is: there exists ONE linearization order (the committed log) that every
observation respects. No observation contradicts the sequential spec in log
order, so the register is a linearizable object. -/
theorem single_linearization {init : Term} {log : CommittedLog} {r1 r2 : Replica}
    (h1 : AppliedPrefix init log r1) (h2 : AppliedPrefix init log r2) :
    ∃ σ : Nat → Term, r1.store = σ r1.applied ∧ r2.store = σ r2.applied :=
  ⟨seqTrajectory init log, h1, h2⟩

/-- The metatheorem, unpacked without the existential: both stores are literally
the same trajectory function sampled at their respective indices — making the
"one linearization order" fully explicit. -/
theorem linearizable {init : Term} {log : CommittedLog} {r1 r2 : Replica}
    (h1 : AppliedPrefix init log r1) (h2 : AppliedPrefix init log r2) :
    r1.store = seqTrajectory init log r1.applied
      ∧ r2.store = seqTrajectory init log r2.applied :=
  ⟨h1, h2⟩

/-- **LINEARIZABILITY WITH THE ORACLE DISCHARGED.** Even two replicas that ran
*independent* single-decree consensus instances (producing `logA`, `logB`)
linearize against ONE order: `agreement` (via `committed_prefix_agree`) forces
`logA = logB`, so there is a single committed log `log` and a single sequential
run `σ` that BOTH replicas' observed stores respect. This is the full
SMR-linearizability statement — the shared linearization order is *earned* by
consensus, not assumed. -/
theorem linearizable_via_consensus {n : ℕ} (slotVotes : ℕ → Votes n Command)
    {init : Term} {logA logB : CommittedLog} {r1 r2 : Replica}
    (hlen : logA.length = logB.length)
    (hA : ∀ i c, logA[i]? = some c → Decided (slotVotes i) c)
    (hB : ∀ i c, logB[i]? = some c → Decided (slotVotes i) c)
    (h1 : AppliedPrefix init logA r1)
    (h2 : AppliedPrefix init logB r2) :
    ∃ (log : CommittedLog) (σ : Nat → Term),
      log = logA ∧ log = logB
        ∧ r1.store = σ r1.applied ∧ r2.store = σ r2.applied := by
  have hlog : logA = logB := committed_prefix_agree slotVotes logA logB hlen hA hB
  subst hlog
  exact ⟨logA, seqTrajectory init logA, rfl, rfl, h1, h2⟩

/-! ## 6. The right-reason BITE — the in-order hypothesis is load-bearing.

A replica that claims to have applied a committed slot but whose store was left
un-updated (or fabricated / applied out of order) is NOT on the sequential
trajectory, and hence CANNOT satisfy `AppliedPrefix`. Drop the in-order
hypothesis and a divergent store is no longer `seqSpec`-consistent — the object
stops being linearizable. Linearizability is a property of protocol-respecting
runs. -/

namespace LinearizableBite

open DLCD.RsmAntiVacuity (dup)

/-- The 2-command committed log used for the bite and the anti-vacuity witness. -/
def init : Term := Term.var 0

/-- The committed total order: two `dup` slots (positions 0 and 1). -/
def log2 : CommittedLog := [dup, dup]

/-- A **fabricated / out-of-order** replica: it claims `applied = 1` (one slot
consumed) but its store is still the untouched `init` — it never actually
applied the committed command in order. -/
def badReplica : Replica := ⟨0, init, 1⟩

/-- The fabricated store is OFF the sequential trajectory: at `applied = 1` the
linearization demands `seqTrajectory init log2 1 = ⟨var 0, var 0⟩`, but the store
is the untouched `var 0`. The store contradicts the sequential spec in log
order. -/
theorem bad_off_trajectory :
    badReplica.store ≠ seqTrajectory init log2 badReplica.applied := by
  show Term.var 0 ≠ Term.pair (Term.var 0) (Term.var 0)
  intro h; exact Term.noConfusion h

/-- Therefore the fabricated replica CANNOT satisfy `AppliedPrefix`: the in-order
application hypothesis is load-bearing. Without it (an arbitrary store) the
linearizability guarantee `store_is_seq_prefix` would be false. -/
theorem bad_not_applied_prefix : ¬ AppliedPrefix init log2 badReplica := by
  intro h
  exact bad_off_trajectory (store_is_seq_prefix h)

end LinearizableBite

/-! ## 7. Anti-vacuity — a concrete 2-command log, its linearization exhibited.

A committed log of two genuinely state-changing `dup` slots. A replica delivers
both in order; its store IS the sequential fold `seqSpec init log2`, and the
single linearization (one `σ` both the mid-run and the completed replica respect)
is exhibited. The three trajectory states `S0, S1, S2` are pairwise distinct, so
nothing is discharged over a no-op. -/

namespace AntiVacuityLin

open DLCD.RsmAntiVacuity (dup)

def init : Term := Term.var 0
def log2 : CommittedLog := [dup, dup]

/-- The sequential trajectory, computed. `S0 = var 0`, `S1 = ⟨var 0, var 0⟩`,
`S2 = ⟨S1, S1⟩` — each step genuinely changes the store. -/
def S0 : Term := Term.var 0
def S1 : Term := Term.pair (Term.var 0) (Term.var 0)
def S2 : Term := Term.pair S1 S1

theorem traj0 : seqTrajectory init log2 0 = S0 := rfl
theorem traj1 : seqTrajectory init log2 1 = S1 := rfl
theorem traj2 : seqTrajectory init log2 2 = S2 := rfl

/-- The three trajectory points are pairwise distinct: the run is non-trivial. -/
theorem states_distinct : S0 ≠ S1 ∧ S1 ≠ S2 ∧ S0 ≠ S2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact Term.noConfusion h
  · intro h; injection h with h1 _; exact Term.noConfusion h1
  · intro h; exact Term.noConfusion h

/-- A replica progression delivering both committed slots in order. -/
def r0 : Replica := ⟨0, init, 0⟩
def r1 : Replica := deliver log2 r0
def r2 : Replica := deliver log2 r1

/-- The base replica satisfies the invariant trivially (`take 0 = []`). -/
theorem base_inv : AppliedPrefix init log2 r0 := by
  unfold AppliedPrefix applyPrefix; rfl

/-- After one delivery the invariant is maintained (Phase-1.0 lemma). -/
theorem inv1 : AppliedPrefix init log2 r1 := deliver_maintains_prefix base_inv

/-- After both deliveries the invariant is maintained. -/
theorem inv2 : AppliedPrefix init log2 r2 := deliver_maintains_prefix inv1

/-- The fully-delivered replica's store IS the sequential fold of the whole
committed log — `seqSpec init log2` — i.e. it sits at the end of the single
sequential run. Non-vacuous: `S2` is the twice-changed store, not `init`. -/
theorem r2_store_is_seqspec : r2.store = seqSpec init log2 := by
  have h := store_is_seq_prefix inv2
  -- `log2.take r2.applied` is definitionally `log2` (r2.applied ≡ 2, |log2| = 2);
  -- Lean 4.31's simp no longer evaluates the concrete `List.take`, so reduce
  -- the fold argument by definitional `rfl`.
  exact h.trans (by rfl)

theorem r2_store_is_S2 : r2.store = S2 := r2_store_is_seqspec

/-- **The single linearization, exhibited.** The mid-run replica `r1` (at
`applied = 1`) and the completed replica `r2` (at `applied = 2`) both respect ONE
sequential run `σ = seqTrajectory init log2`: `r1.store = σ 1` and
`r2.store = σ 2`. The committed log `[dup, dup]` is the linearization order and
both observations are points on its sequential trajectory. -/
theorem linearization_exhibited :
    ∃ σ : Nat → Term, r1.store = σ r1.applied ∧ r2.store = σ r2.applied :=
  single_linearization inv1 inv2

/-- The exhibited linearization is non-vacuous: the two observed stores are the
*distinct* states `S1` and `S2` (the store genuinely advanced along the run). -/
theorem linearization_nonvacuous :
    r1.store = S1 ∧ r2.store = S2 ∧ S1 ≠ S2 := by
  refine ⟨?_, r2_store_is_S2, (states_distinct.2.1)⟩
  have h := store_is_seq_prefix inv1
  -- `seqSpec init (log2.take r1.applied)` reduces definitionally to `S1`
  -- (r1.applied ≡ 1); reduce by `rfl` since 4.31 simp no longer evaluates it.
  exact h.trans (by rfl)

/-- Real-time monotonicity on the concrete run: `r2`'s store is `r1`'s store with
the one intervening committed slot applied — the later observation continues the
earlier along the single run. -/
theorem concrete_compatible :
    r2.store = applyPrefix r1.store ((log2.drop r1.applied).take (r2.applied - r1.applied)) :=
  observations_compatible (by decide) inv1 inv2

end AntiVacuityLin

end DLCD
