import DLC.Reduce

/-! # DLC-D Phase 1.0 — the RSM operational substrate

This module opens the **DLC-D Phase 1** vertical slice: a *replicated*
delegation register whose per-replica command engine is DLC's own
deterministic reduction (`DLC.step`). Phase 1.0 lays the **operational
skeleton** — the failure-model contract, the command/replica/log/config
data, the delivery step, and the **convergence seed** — and defers real
consensus to a later increment.

## The state-machine-replication (SMR) model we mirror
State-machine replication (Lamport 1978) turns a deterministic sequential
service into a fault-tolerant one by:

1. **Total-order broadcast / a replicated log.** Consensus agrees on an
   ever-growing, *linearly ordered* command log; each slot is decided
   *once* (single-decree per slot). This is the "atomic broadcast" building
   block. Here the log is `CommittedLog := List Command`.
2. **Deterministic application.** Every correct replica, starting from the
   *same* initial state and applying the *same committed prefix in the same
   order*, reaches the *same* state. This is the SMR convergence guarantee,
   and it rests entirely on the transition function being a *function*.
3. **A failure model.** The guarantees hold relative to a declared
   crash-fault bound `f` and a fair-delivery assumption. We make that model
   an explicit, consumable *contract* (`FailureBudget`) rather than prose.

Prior art (web-searched 2026-07-22):
- Consensus for SMR — decentralizedthoughts (single-decree per slot; the
  "Prefix Completeness" property that makes correct replicas share
  identical log prefixes):
  https://decentralizedthoughts.github.io/2019-10-15-consensus-for-state-machine-replication/
- SMR concepts & advances (three SMR properties: same start state; same op
  on same state ⇒ same result; same order):
  https://www.emergentmind.com/topics/state-machine-replication-smr
- Lamport 1978 total-ordering ⇒ replicated state machine (survey framing):
  https://www.sciencedirect.com/science/article/pii/S0167404823001104
- Linearizability & SMR: https://arxiv.org/pdf/2407.01720

## What is abstract vs. proved in Phase 1.0
- **ABSTRACT / oracle:** the `CommittedLog` itself. Real single-decree
  consensus (agreement on each slot) is a *later* increment — exactly as
  `ThreadFair`/`drand` fair-delivery was an *external* assumption in the
  earlier Iris write-once-cell → replicated-register lift. Phase 1.0 takes
  the committed, totally-ordered log as given.
- **PROVED:** that per-replica application is a deterministic fold of
  `applyCommand` over the committed prefix, hence two replicas that have
  applied the *same* prefix from the *same* initial store hold **equal**
  stores (`replicas_converge_on_prefix`), and that `deliver` *preserves*
  the prefix invariant (`deliver_maintains_prefix`) — so the invariant the
  seed rests on is the one `worldStep` actually establishes, not a vacuous
  hypothesis.

## Toward capability/IFC-typed writes
Each `Command` carries an (abstract) `cap` slot — the guarding capability /
IFC label a *later* increment will require a `CDeriv`/`says` witness for.
The store is a `DLC.Term`, and `DLC.CDeriv Γ store φ` already types any such
term, so a written value CAN carry a full CARVe/DILL derivation with no
structural change here; Phase 1.0 keeps the guard opaque and the store
untyped-at-the-operational-layer.

## The convergence seed
`replicas_converge_on_prefix` is the distributed analogue of the Iris
`Joinable`/per-config-determinism convergence: the seed the full
convergence metatheorem (later increments, over the *live* log with
consensus discharged) builds on.
-/

namespace DLCD

open DLC

/-! ## 1. The failure model as an enforced contract.

`FailureBudget` mirrors the `DLC.DpBudget` graded-comonad template
(`zero`/`saturatingAdd`/`le`): a declared crash-fault tolerance `f` and a
`fairDelivery` assumption, plus a *consumable* grade `consumed` counting
crash faults charged so far. `withinContract` is the enforced predicate —
the slice's guarantees are stated relative to it. -/

/-- The failure-model contract the slice's guarantees are relative to. -/
structure FailureBudget where
  /-- Maximum tolerated crash faults (the `f` of an `f`-resilient protocol). -/
  maxFaults : Nat
  /-- The fair-delivery assumption: every message sent to a correct replica
  is eventually delivered. An *external* assumption in Phase 1.0. -/
  fairDelivery : Bool
  /-- Consumable grade: crash faults charged against the contract so far.
  Mirrors `DpBudget`'s consumed grade. -/
  consumed : Nat
  deriving Repr, DecidableEq

namespace FailureBudget

/-- The zero grade: an `f`-resilient, fair-delivery contract with no faults
charged yet. -/
def zero (f : Nat) : FailureBudget := ⟨f, true, 0⟩

/-- Charge additional consumed faults (monotone, like DP sequential
composition on the grade). -/
def saturatingAdd (b : FailureBudget) (extra : Nat) : FailureBudget :=
  { b with consumed := b.consumed + extra }

/-- Within-contract iff the charged faults have not exceeded the tolerated
bound. This is the enforced predicate the guarantees are relative to. -/
def le (b : FailureBudget) : Bool := decide (b.consumed ≤ b.maxFaults)

/-- The declared contract holds: fair delivery is assumed and the crash-fault
budget is not overspent. -/
def withinContract (b : FailureBudget) : Bool := b.fairDelivery && b.le

end FailureBudget

/-! ## 2. Commands, replicas, the committed log, and the global config. -/

/-- A replicated operation: a `DLC.Term` payload to apply to the store, plus
an (abstract, Phase-1.0-opaque) guarding-capability / IFC-label slot that a
later increment will require a `CDeriv`/`says` witness for. -/
structure Command where
  /-- The operation, as a `DLC.Term` applied to the replica's store. -/
  payload : Term
  /-- The guarding capability / IFC label this write must eventually prove.
  Abstract in Phase 1.0 (`none` = unguarded skeleton write). -/
  cap : Option Prop' := none

/-- Local register state of a single replica: its identity, its store (a
`DLC.Term` register value), and how far it has consumed the committed log. -/
structure Replica where
  /-- Replica identity. -/
  id : Nat
  /-- The local register value. -/
  store : Term
  /-- Number of committed-log slots this replica has applied. -/
  applied : Nat

/-- The totally-ordered committed sequence — the consensus output. ABSTRACT
in Phase 1.0: real single-decree consensus that fills each slot is a later
increment; here the committed log is taken as given (an oracle). -/
abbrev CommittedLog := List Command

/-- A global configuration: the replicas, the committed log, and the failure
contract the guarantees are relative to. -/
structure GlobalConfig where
  /-- The replica set. -/
  replicas : List Replica
  /-- The committed, totally-ordered command log (oracle in Phase 1.0). -/
  log : CommittedLog
  /-- The declared failure-model contract. -/
  budget : FailureBudget

/-! ## 3. Deterministic command application. -/

/-- Fuel bound for normalizing a command application. Fixed and global, so
`applyCommand` is a total, deterministic function of `(Command, Term)`. -/
def applyFuel : Nat := 1024

/-- Apply a command to a store: run DLC reduction on `payload store` to a
normal form (bounded by `applyFuel`). Deterministic — `reduceWithFuel` is a
function and `DLC.step` is deterministic (`ReduceMeta.step_deterministic`),
so this is the deterministic transition function SMR convergence needs. -/
def applyCommand (c : Command) (s : Term) : Term :=
  (reduceWithFuel (Term.app c.payload s) applyFuel).1

/-- The deterministic fold of a *committed prefix* onto an initial store.
This is the whole of the replica's state as a function of what it applied. -/
def applyPrefix (init : Term) (cmds : CommittedLog) : Term :=
  cmds.foldl (fun s c => applyCommand c s) init

/-- Deliver the next committed slot to a replica: advance `applied` and apply
`log[applied]`. If the replica is caught up to the committed log, it is a
no-op (nothing more is committed yet). -/
def deliver (log : CommittedLog) (r : Replica) : Replica :=
  match log[r.applied]? with
  | some c => { r with store := applyCommand c r.store, applied := r.applied + 1 }
  | none => r

/-- One world step: every replica delivers its next committed slot. (Which
replicas step, and message loss/reordering, live under the `FailureBudget`
contract; the fair-delivery assumption guarantees each correct replica
*eventually* advances.) -/
def worldStep (g : GlobalConfig) : GlobalConfig :=
  { g with replicas := g.replicas.map (deliver g.log) }

/-! ## 4. The convergence invariant and the convergence seed. -/

/-- The prefix invariant: replica `r`'s store is exactly the deterministic
fold of the committed prefix it has applied, from the shared initial store
`init`. This is what "correct replica" means operationally in Phase 1.0. -/
def AppliedPrefix (init : Term) (log : CommittedLog) (r : Replica) : Prop :=
  r.store = applyPrefix init (log.take r.applied)

/-- Folding one more command onto a prefix. If slot `n` of the log is `c`,
the fold of the first `n+1` slots is `applyCommand c` of the fold of the
first `n`. -/
theorem applyPrefix_succ (init : Term) (log : CommittedLog) (n : Nat)
    (c : Command) (h : log[n]? = some c) :
    applyPrefix init (log.take (n + 1)) = applyCommand c (applyPrefix init (log.take n)) := by
  have htake : log.take (n + 1) = log.take n ++ [c] := by
    rw [List.take_add_one, h]
    rfl
  unfold applyPrefix
  rw [htake, List.foldl_append]
  rfl

/-- `deliver` preserves the prefix invariant: a replica whose store is the
fold of its applied prefix still has that property after delivering the next
committed slot. Hence the seed's hypothesis is exactly what `worldStep`
maintains — the invariant is not vacuous. -/
theorem deliver_maintains_prefix {init : Term} {log : CommittedLog} {r : Replica}
    (h : AppliedPrefix init log r) :
    AppliedPrefix init log (deliver log r) := by
  unfold AppliedPrefix deliver
  cases hget : log[r.applied]? with
  | none => simpa [hget] using h
  | some c =>
      unfold AppliedPrefix at h
      rw [applyPrefix_succ init log r.applied c hget, ← h]

/-- **THE CONVERGENCE SEED.** Two replicas that have applied the *same
committed prefix* (same length, same log, same initial store) hold **equal**
stores. Because per-replica application is a deterministic *fold* of
`applyCommand` over the committed prefix, the store is a *function* of the
applied prefix alone — the distributed analogue of the Iris
`Joinable`/per-config-determinism convergence. The full convergence
metatheorem (over the live log, with consensus discharged) builds on this. -/
theorem replicas_converge_on_prefix {init : Term} {log : CommittedLog}
    {r1 r2 : Replica}
    (h1 : AppliedPrefix init log r1)
    (h2 : AppliedPrefix init log r2)
    (hlen : r1.applied = r2.applied) :
    r1.store = r2.store := by
  unfold AppliedPrefix at h1 h2
  rw [h1, h2, hlen]

/-! ## 5. Anti-vacuity — a concrete, state-*changing* 2-replica convergence.

The command's payload is `λx. ⟨x, x⟩` (duplicate the register value into an
additive pair). Applied to the initial store `var 0`, it reduces to
`⟨var 0, var 0⟩` — the store genuinely CHANGES (distinct head constructor),
so the seed is not discharged over a no-op. -/

namespace RsmAntiVacuity

/-- The dup command: `λ_:atom0. ⟨x, x⟩`. -/
def dup : Command := { payload := Term.lam (Prop'.atom 0) (Term.pair (Term.var 0) (Term.var 0)) }

/-- The shared initial store. -/
def init : Term := Term.var 0

/-- The one-slot committed log. -/
def log : CommittedLog := [dup]

/-- Applying `dup` really changes the store: `var 0 ↦ ⟨var 0, var 0⟩`. -/
example : applyCommand dup init = Term.pair (Term.var 0) (Term.var 0) := rfl

/-- Two replicas, both having delivered the single committed slot. -/
def r1 : Replica := deliver log ⟨0, init, 0⟩
def r2 : Replica := deliver log ⟨1, init, 0⟩

/-- The initial (pre-delivery) replicas satisfy the prefix invariant trivially
(`take 0 = []`, `applyPrefix init [] = init`). -/
theorem base_invariant (rid : Nat) :
    AppliedPrefix init log ⟨rid, init, 0⟩ := by
  unfold AppliedPrefix applyPrefix
  rfl

/-- Both replicas have applied the same prefix, so the seed forces equal
stores — and that common store is the *changed* `⟨var 0, var 0⟩`, not the
initial `var 0`. -/
theorem converge : r1.store = r2.store := by
  have h1 : AppliedPrefix init log r1 := deliver_maintains_prefix (base_invariant 0)
  have h2 : AppliedPrefix init log r2 := deliver_maintains_prefix (base_invariant 1)
  have hlen : r1.applied = r2.applied := rfl
  exact replicas_converge_on_prefix h1 h2 hlen

/-- Non-vacuity witness: the converged store is the transformed value, and it
is genuinely distinct from the initial store. -/
theorem converged_store_changed :
    r1.store = Term.pair (Term.var 0) (Term.var 0) ∧ r1.store ≠ init := by
  refine ⟨rfl, ?_⟩
  intro h
  exact Term.noConfusion h

end RsmAntiVacuity

end DLCD
