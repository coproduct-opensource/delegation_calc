# R6.1 — the runnable node: trusted shell over the verified transition core

*Design memo. 2026-07-24. Branch `dlc-d/phase0-carve`, HEAD `cae8667`. Realizes
roadmap §2 R6.1 (`spec/dlc-d-roadmap.md`). Companion to `spec/r6-failure-modes-as-types-design.md`
(R6.0), which specifies the developer surface; this memo specifies the thing the
surface will deploy onto.*

---

## 0. What this increment delivers, and the standard it must meet

A **running replicated node**: `cargo run -p dlc-d-node` starts a cluster, replicates a
command log through the consensus predicates, and the replicas converge on the same store.

The standard is not "it runs". It is:

> **Every state transition of the running node is a call into a function that the R2
> correspondence already proved refines the Lean model.** The shell schedules; it never
> computes state.

If the shell recomputed even one store update itself, the transported guarantees
(`rust_world_step_correct`, `rust_capability_safety`, `rust_consensus_agreement`,
`rust_worldStep_preserves_high`) would stop applying to the deployed binary and the whole
R2 bridge would be decorative. So the design is organized around making that property
*checkable*, not merely intended.

---

## 1. The verified assets this node deploys

| Node action | Function called | Transported theorem covering it |
|---|---|---|
| append a decided command | `dlc_core::rsm::commit` | `DLCD.Transport.rust_capability_safety` |
| advance the local replica | `dlc_core::rsm::world_step` (→ `deliver` → `apply_command` → `reduce_with_fuel`) | `rust_world_step_correct`, `rust_deliver_correct` |
| store as a function of the log | `dlc_core::rsm::apply_prefix` | `rust_apply_prefix_correct`, `rust_replicas_converge`, `rust_single_linearization` |
| decide a slot | `dlc_d_rsm::consensus::decided` / `is_quorum` | `TransportConsensus.rust_consensus_agreement` |
| the failure contract | `dlc_core::rsm::FailureBudget::within_contract` | `DLCD.budgeted_guarantee_voids_over_budget` (model side) |

Everything else in the crate — the event loop, the message plumbing, the leader's ballot
bookkeeping, timers — is **shell**, and is in the TCB (§5).

## 2. State representation: the node's view IS a `GlobalConfig`

The obvious shape for a node is "my `Replica` + my copy of the log". That shape would force
the shell to write `replica.store` and `replica.applied` itself — precisely the thing §0
forbids.

**Ruling:** a node's local view is a `dlc_core::rsm::GlobalConfig` whose `replicas` vector
holds *exactly one* element (itself). Then:

- committing is `view = rsm::commit(&view, cmd)` — verbatim, verified;
- advancing is `view = rsm::world_step(&view)` — verbatim, verified (on a singleton replica
  vector, `world_step` *is* `deliver` for this replica, by its own definition);
- the shell owns **no** store field, **no** applied counter, **no** log vector of its own.

The cost is a one-element `Vec` per node. The benefit is that the deployed transition
surface is exactly the corresponded surface, with no adapter code in between.

### 2.1 Local views vs. the model's global configuration

The Lean model's `worldStep` steps *every* replica at once; a real cluster steps nodes
independently. These agree, and the reason is structural rather than incidental:
`DLCD.worldStep g = { g with replicas := g.replicas.map (deliver g.log) }`, and `deliver`
reads only `(log, own replica)`. So a node's local advance is its own component of the
model's map, and assembling the nodes' singleton views into one `GlobalConfig` after all of
them have stepped over the same log yields exactly `worldStep` of the assembled prior
configuration.

This is asserted as a **test over the real node states** (`ensemble_refines_world_step`),
not as prose: the test assembles the per-node views and compares against
`rsm::world_step` of the assembled predecessor. It is the seam between "each node is
correct" and "the cluster is the model", and it is where a scheduling bug would show up.

Fence, stated plainly: the assembly argument holds because every node applies the **same**
committed log. That the logs *are* the same is what the consensus layer must provide, and
at this increment it is provided by a fixed leader broadcasting after a quorum decision
(§3), not by a verified leader-election protocol (§6).

## 3. Consensus: single-decree per slot, fixed leader

Minimal, and deliberately matched to what is already verified:

```
client → leader:   submit(cmd)
leader → all:      Propose { slot, cmd }
follower → leader: Vote { slot, from, cmd }
leader:            ballot[from] = Some(cmd);  decided(&ballot, &cmd) ?
leader → all:      Commit { slot, cmd }
every node:        view = commit(view, cmd);  drain: view = world_step(view)
```

The decision gate is `dlc_d_rsm::consensus::decided`, whose ballot shape
(`Vec<Option<Command>>` indexed by replica) is exactly what `rust_consensus_agreement`
quantifies over — so the deployed decision is the one the transported agreement theorem
talks about. Crash-only, not Byzantine: followers vote for what the leader proposes.
(`DLCD_byz_agreement` exists in the model but the runtime path here is the crash-fault one,
matching `Consensus.lean`.)

Slot discipline: a node accepts `Commit { slot }` only when `slot == log.len()`, so the log
is append-only and gap-free by construction — the shape `WellFormedLog` provenance and
`rust_capability_safety` assume.

## 4. Transport: in-process channels now, sockets after Tamarin — and why

`CLAUDE.md` is explicit: *"Tamarin model first. Then ProVerif cross-check. Then wire format.
Then code. Wire-format changes that don't have a corresponding Tamarin-model change are
banned."* The consensus message set (`Propose`/`Vote`/`Commit`) is a **new protocol**, and
`models/tamarin/dlc.spthy` models the delegation protocol, not a replication protocol.
Extending the models to the distributed protocol is an open plan item (R4).

**Ruling:** R6.1a ships the node over an **in-process `tokio::sync::mpsc` transport** and
introduces **no new wire encoding whatsoever**. Nodes are independent async tasks with
independent state; only the bytes-on-a-socket layer is deferred. R6.1b = Tamarin model +
ProVerif cross-check of the replication protocol, *then* a socket transport whose payload
encoding reuses `dlc_protocol::wire::{encode, decode, encode_prop, decode_prop}` verbatim
rather than inventing a second term encoding.

This is a real limitation and is not dressed up: **the node is a real event-driven
distributed program with a trusted, loss-free, in-process transport.** What it demonstrates
about scheduling, quorum, crash tolerance and convergence is genuine; what it does not yet
demonstrate is behaviour over an adversarial network.

The transport boundary is a single enum-in / enum-out interface so that R6.1b swaps the
carrier without touching node logic.

## 5. TCB — enumerated honestly

Trusted (unverified) in the running system:

1. `rustc` / LLVM / the host — accepted program-wide (not an end-to-end verification).
2. **`tokio` and the event loop** — scheduling, task spawn, channel delivery.
3. **The transport** — in-process channels; delivery is assumed reliable. This is where the
   model's `fair_delivery: true` assumption is *provided* rather than proved.
4. **The shell's protocol logic** — leader selection (static), ballot bookkeeping, slot
   matching, the drain loop. Verified content is what these *call*, not the calls themselves.
   R3 (RefinedRust) is the eventual route to refining the shell; roadmap §3 keeps it after
   the demo, and this increment takes the shell-in-TCB option knowingly.
5. **Clock/timeouts** — none are load-bearing at R6.1a (no failure detector, no election).
6. **`cap` is carried, not checked** — the capability is a `Prop`-layer obligation
   (`rust_capability_safety` is conditioned on `Authorized` of the decoded command). The node
   transports the `cap` slot; it does not verify a credential. R6.2's surface is what
   discharges it at compile time.

Not trusted (verified, via R2): the transition core — `commit`, `world_step`, `deliver`,
`apply_command`, `apply_prefix`, the reducer, `is_quorum`, `decided` — under the R2
partial-correctness condition (guarantees hold when the bounded reducer returns `ok`).

## 6. Scenarios the demo must exercise, including the failing one

Anti-vacuity and right-reason discipline apply to a runtime demo as much as to a theorem:

- **Convergence (positive).** 3 nodes, a 3-command workload; all replicas end on the same
  store, and that store is the *changed* one — `apply_prefix(init, log)`, not `init`. A demo
  that converged on the initial store would prove nothing.
- **Crash tolerance (the budget is real).** `FailureBudget { max_faults: 1 }`, one follower
  crashed: 2 of 3 still form a quorum, the cluster still commits and the survivors still
  converge. `consumed = 1 ≤ max_faults = 1` — within contract.
- **The bite (must fail, for the right reason).** Crash 2 of 3: `decided` returns false, no
  `Commit` is broadcast, and the cluster **stalls with its safety intact** — stores never
  diverge, they just stop advancing. Liveness is lost exactly when the budget is exceeded
  (`consumed = 2 > max_faults = 1`), which is the runtime shadow of
  `budgeted_guarantee_voids_over_budget`. The failure mode must be *stall*, not *divergence*;
  a test asserting divergence-freedom under over-budget crash is what makes the bite
  meaningful.
- **Leader crash is out of scope** and disclosed: there is no election (roadmap §5 backlog),
  so a crashed leader stalls the cluster regardless of budget.

## 7. Checkable definition of done

1. `cargo build`/`cargo test -p dlc-d-node` green; `cargo run -p dlc-d-node` prints a
   converged, changed store for every node.
2. The four scenarios of §6 exist as tests, including the over-budget stall.
3. `ensemble_refines_world_step` passes over real node states (§2.1).
4. **Purity check**: no assignment to a `store` / `applied` / `log` field anywhere in
   `crates/dlc-d-node`; the only writes to node state are whole-view replacements produced
   by `rsm::commit` / `rsm::world_step`. Enforced by a test that greps the crate source, so
   a future edit that inlines a state update fails CI rather than silently voiding §0.
5. No new wire encoding (§4). No change to `dlc-core` / `dlc-d-rsm` ⇒ the Aeneas drift gate
   and the 77 axiom snapshots are untouched.
6. Existing gates: `check-axioms`, `check-claims`, `check-drift` all still green.

## 8. What this increment explicitly does not claim

- Not a claim that the *cluster* is verified: the shell, transport and leader are trusted (§5).
- Not a network-facing node: in-process transport only (§4).
- Not a capability-enforcing node: `cap` is carried, discharge is R6.2's job (§5.6).
- Not IFC-enforcing at runtime: labels are type-layer artifacts; a faithful runtime decode is
  provably impossible (roadmap §1 R2 honest scope), and R6.0's surface is the honest route.
- The R2 partial-correctness condition rides along: the transported guarantees hold when the
  bounded reducer returns `ok`.
