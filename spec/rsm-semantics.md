# DLC-D Replicated-State-Machine Semantics (Phase R0 — spec mirror)

**Status:** Descriptive mirror of the Lean model `lean/DLCD/*.lean`, written to
apply the repo's *spec-first* discipline retroactively to the distributed
layer. Unlike `spec/syntax.md` and `spec/typing-rules.md` (which the Lean and
Rust encodings *follow*), this document **trails** the Lean: `lean/DLCD/Rsm.lean`
is the source of truth and this file mirrors it. Every definition and theorem
name below matches that module exactly (a wrong name here defeats the purpose).

**Model, not runtime.** Everything here is a guarantee about the **Lean model**
of a replicated delegation register — *not* a proof about `dlc-verifier`'s Rust
at run time. The running distributed runtime is the separately-approved R1–R6
program; the RSM semantics is the abstract object those guarantees are stated
over. Fairness and the failure budget are **explicit modelled assumptions**
(§1), not properties of a live scheduler.

This is the doc-level companion to `spec/consensus.md` (which earns the
committed-log oracle) and `spec/distributed-guarantees.md` (the G1–G4 manifest).

---

## 0. What state-machine replication we mirror

State-machine replication (SMR; Lamport 1978, Schneider 1990) turns a
deterministic sequential service into a fault-tolerant one by three ingredients,
each of which has a direct counterpart in `DLCD.Rsm`:

1. **A replicated, totally-ordered log.** Consensus agrees on an ever-growing,
   linearly-ordered command log; each slot is decided once. Here the log is
   `CommittedLog := List Command`. In Phase 1.0 it is taken as an **oracle**;
   `spec/consensus.md` earns it per slot.
2. **Deterministic application.** Every correct replica, starting from the same
   initial store and applying the same committed prefix in the same order,
   reaches the same state. This rests entirely on the transition function being
   a *function* — realized here by `applyCommand` (`DLC.step` is deterministic).
3. **A failure model.** The guarantees hold relative to a declared crash-fault
   bound `f` and a fair-delivery assumption, made an explicit consumable
   contract (`FailureBudget`, §1) rather than left as prose.

Everything in `Rsm.lean` lives in namespace `DLCD` and `open DLC`.

### Prior art (canonical references; URLs recorded)

- Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*
  (1978) — total order ⇒ replicated state machine.
- Schneider, *Implementing Fault-Tolerant Services Using the State Machine
  Approach: A Tutorial*, ACM Computing Surveys 22(4), 1990:
  <https://www.cs.cornell.edu/fbs/publications/SMSurvey.pdf>
- Hawblitzel et al., *IronFleet: Proving Safety and Liveness of Practical
  Distributed Systems* — the template of a machine-checked RSM with both safety
  and liveness guarantees:
  <https://www.microsoft.com/en-us/research/publication/ironfleet-proving-safety-liveness-practical-distributed-systems/>
- Ongaro–Ousterhout, *In Search of an Understandable Consensus Algorithm
  (Raft)* — a replicated log of per-slot decrees driving a state machine:
  <https://raft.github.io/raft.pdf>
- decentralizedthoughts, *Consensus for State Machine Replication* — single
  decree per slot; prefix completeness ⇒ correct replicas share identical
  prefixes:
  <https://decentralizedthoughts.github.io/2019-10-15-consensus-for-state-machine-replication/>

---

## 1. The failure model as an enforced contract — `FailureBudget`

The guarantees are stated relative to a declared crash-fault tolerance and a
fair-delivery assumption. Rather than leave this as prose, the model makes it a
*consumable* contract, mirroring DLC's `DpBudget` graded-comonad template
(`zero` / `saturatingAdd` / `le`).

```
structure FailureBudget where
  maxFaults    : Nat      -- the `f` of an `f`-resilient protocol
  fairDelivery : Bool     -- every message to a correct replica is eventually delivered
  consumed     : Nat      -- crash faults charged against the contract so far
  deriving Repr, DecidableEq
```

Operations (namespace `FailureBudget`):

```
def zero (f : Nat) : FailureBudget := ⟨f, true, 0⟩          -- f-resilient, fair, nothing charged
def saturatingAdd (b : FailureBudget) (extra : Nat)         -- charge `extra` crash faults (monotone)
    : FailureBudget := { b with consumed := b.consumed + extra }
def le (b : FailureBudget) : Bool := decide (b.consumed ≤ b.maxFaults)
def withinContract (b : FailureBudget) : Bool := b.fairDelivery && b.le
```

**Design notes**

- `withinContract` is **the enforced predicate** the whole slice's guarantees
  are relative to: fair delivery is assumed *and* the crash-fault budget is not
  overspent. It is a `Bool` (decidable), and the seal (`spec/distributed-
  guarantees.md`) discharges it concretely (`budget.withinContract = true`).
- `fairDelivery` is an **external assumption** in the model — the FLP-necessary
  scheduling hypothesis that liveness (`spec/consensus.md` §3) consumes. Tying
  it to a running scheduler is an open fence (the "live-scheduling" fence).
- `consumed` is a consumable grade; `saturatingAdd` is monotone, matching DP
  sequential composition on the grade.

---

## 2. Commands, replicas, the committed log, the global config

```
structure Command where
  payload : Term              -- the operation, a DLC.Term applied to the store
  cap     : Option Prop' := none   -- guarding capability / IFC label (opaque in 1.0)

structure Replica where
  id      : Nat               -- replica identity
  store   : Term              -- the local register value (a DLC.Term)
  applied : Nat               -- number of committed-log slots applied so far

abbrev CommittedLog := List Command   -- the totally-ordered consensus output

structure GlobalConfig where
  replicas : List Replica
  log      : CommittedLog     -- oracle in Phase 1.0; earned per slot in consensus.md
  budget   : FailureBudget    -- the failure contract the guarantees are relative to
```

**Design notes**

- The store is a `DLC.Term`, so a written value can carry a full DLC / CARVe
  derivation with no structural change; Phase 1.0 keeps the store
  *untyped-at-the-operational-layer* and the `cap` guard *opaque* (`none` = an
  unguarded skeleton write). The capability/IFC layers (`spec/distributed-
  guarantees.md` G1) supply the witness a real write must carry in its `cap`
  slot: `some (Prop'.says issuer capProp)`.
- `CommittedLog` is **ABSTRACT** in Phase 1.0 (an oracle). Real single-decree
  consensus that fills each slot is `spec/consensus.md`; convergence there is
  proved *relative* to the oracle and then the oracle is discharged per slot.
- **Store-type change** is an open fence: the committed store is a fixed `Term`;
  a richer store type is future work.

---

## 3. Deterministic command application

The transition function SMR convergence rests on is `applyCommand`: it runs DLC
reduction on `payload store` to a normal form under a fixed global fuel bound,
so it is a *total, deterministic function of `(Command, Term)`*.

```
def applyFuel : Nat := 1024

def applyCommand (c : Command) (s : Term) : Term :=
  (reduceWithFuel (Term.app c.payload s) applyFuel).1

def applyPrefix (init : Term) (cmds : CommittedLog) : Term :=
  cmds.foldl (fun s c => applyCommand c s) init
```

**Design notes**

- Determinism is inherited from `DLC.step` (`ReduceMeta.step_deterministic`)
  and the fact that `reduceWithFuel` is a function and `applyFuel` is fixed and
  global. This is the whole basis of convergence: the store is a *function* of
  the applied prefix alone.
- `applyPrefix` is the deterministic left-fold of a committed prefix onto an
  initial store — the entirety of a replica's state as a function of what it
  applied.

### Delivery and the world step

```
def deliver (log : CommittedLog) (r : Replica) : Replica :=
  match log[r.applied]? with
  | some c => { r with store := applyCommand c r.store, applied := r.applied + 1 }
  | none   => r                            -- caught up: no-op

def worldStep (g : GlobalConfig) : GlobalConfig :=
  { g with replicas := g.replicas.map (deliver g.log) }
```

**Design notes**

- `deliver` advances one replica by one committed slot (`applied` bumped,
  `log[applied]` applied). If the replica is caught up to the committed log it
  is a no-op — nothing more is committed yet.
- `worldStep` advances every replica by one slot. *Which* replicas step, and
  message loss/reordering, live under the `FailureBudget` contract: the
  `fairDelivery` assumption guarantees each correct replica *eventually*
  advances. `worldStep` does not change the log (`worldStep_log : (worldStep
  g).log = g.log`), which is what lets the confidentiality guarantees
  (`spec/distributed-guarantees.md` G1) iterate over `worldSteps k`.

### Capability-gated ingress — `commit`

The *only* way a command enters the committed log is `commit`, which demands a
proof that the issuer holds the guarding capability (defined in
`lean/DLCD/CapSafety.lean`; its authorization discipline is `spec/distributed-
guarantees.md` G1):

```
def commit (g : GlobalConfig) (c : Command) (issuer : Principal)
    (_auth : Authorized c issuer) : GlobalConfig :=
  { g with log := g.log ++ [c] }
```

`commit` appends exactly the one command whose `Authorized c issuer` proof it
required, and nothing else can slip in (`mem_commit_authorized`). This is the
enforce-by-construction gate that makes `capability_safety` an extraction over
log provenance rather than an audited invariant.

---

## 4. The convergence invariant and the convergence seed

The operational meaning of "correct replica" is the **prefix invariant**: its
store is exactly the deterministic fold of the committed prefix it has applied.

```
def AppliedPrefix (init : Term) (log : CommittedLog) (r : Replica) : Prop :=
  r.store = applyPrefix init (log.take r.applied)
```

Two supporting facts and the seed:

```
theorem applyPrefix_succ (init) (log) (n) (c) (h : log[n]? = some c) :
    applyPrefix init (log.take (n + 1)) = applyCommand c (applyPrefix init (log.take n))

theorem deliver_maintains_prefix {init log r} (h : AppliedPrefix init log r) :
    AppliedPrefix init log (deliver log r)

theorem replicas_converge_on_prefix {init log r1 r2}
    (h1 : AppliedPrefix init log r1) (h2 : AppliedPrefix init log r2)
    (hlen : r1.applied = r2.applied) :
    r1.store = r2.store
```

**Design notes**

- `deliver_maintains_prefix` is what makes the invariant **non-vacuous**: the
  hypothesis the seed rests on is exactly the one `worldStep` maintains, not a
  hypothesis no reachable configuration satisfies.
- `replicas_converge_on_prefix` is **THE CONVERGENCE SEED**: two replicas that
  have applied the same committed prefix (same length, same log, same initial
  store) hold **equal** stores, because per-replica application is a
  deterministic fold — the store is a function of the applied prefix alone.
  This is the distributed analogue of the Iris `Joinable` / per-config
  determinism convergence. Every downstream convergence theorem
  (`replicas_converge_via_consensus`, `replicas_converge_multidecree`,
  `single_linearization`) chains into this seed once its own log oracle is
  discharged.

### Non-vacuity (a state-*changing* 2-replica convergence)

`Rsm.lean`'s `RsmAntiVacuity` namespace exhibits a *concrete* run so the seed is
not discharged over a no-op: the command `dup := λ_:atom0. ⟨x, x⟩` applied to the
initial store `var 0` reduces to `⟨var 0, var 0⟩` (a genuinely distinct head
constructor). Both replicas deliver the one committed slot, `converge` forces
their stores equal, and `converged_store_changed` certifies the common store is
the *transformed* `⟨var 0, var 0⟩`, not the initial `var 0`. The seed fires on a
run where the state really changes.

---

## 5. Honest fences (this document)

- **Model, not runtime** — as stated in the header; the runtime is R1–R6.
- **Committed-log oracle (Phase 1.0)** — `CommittedLog` is assumed here; it is
  earned per slot in `spec/consensus.md`.
- **Store-type change** — the store is a fixed `Term`; a richer store type is
  future work.
- **Live-scheduling** — `FailureBudget.fairDelivery` is a modelled assumption,
  not tied to a running scheduler.
- **Opaque capability guard** — the `Command.cap` slot is opaque at the
  operational layer here; the proof-carrying discipline lives in the G1 layers.
