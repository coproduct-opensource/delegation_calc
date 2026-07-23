import DLCD.Rsm
import DLCD.CapSafety
import DLCD.Consensus
import DLCD.MultiDecree
import DLCD.MultiDecreeLiveness
import DLCD.Liveness
import DLCD.Termination
import DLCD.Linearizable
import DLCD.Witness
import DLCD.LabelFlow
import DLCD.Calm
import DLCD.DistributedNI
import DLCD.TypedLog
import DLCD.CapSafetyLinear
import DLCD.ByzantineConsensus

/-!
# DLC-D guarantee ledger — the machine-checked status manifest

This module imports EVERY `DLCD.*` module at once. **That it compiles is the
proof of namespace hygiene**: before Phase 2.i, several modules put their
anti-vacuity examples in the shared generic namespaces `DLCD.Bite`,
`DLCD.Witness`, `DLCD.AntiVacuity`, so co-importing any two of them failed with
`environment already contains 'DLCD.Witness.hi'`. Each module's example
namespace is now module-unique (`LabelFlowBite`, `DistNIWitness`,
`RsmAntiVacuity`, …), so the whole DLC-D surface co-imports cleanly and this
ledger can re-export every headline guarantee in one place.

The re-export block at the bottom is a **name-drift tripwire**: each guarantee
is aliased with `abbrev … := @DLCD.<name>`. If any headline theorem is renamed
or deleted, this file fails to compile — the ledger cannot silently fall out of
sync with the theorems it advertises.

## The guarantees (each name is a top-level, machine-checked `DLCD.*` theorem)

### G1 — authority + confidentiality
- **`capability_safety`** (`DLCD/CapSafety.lean`): every command in a
  `WellFormedLog` carries a genuine `Deriv (issuer says writeCap)` credential —
  authority is enforced by construction, not audited after the fact.
- **`log_noninterference`** (`DLCD/LabelFlow.lean`): the SEMANTIC confidentiality
  guarantee — a labelled log's low-observable projection is independent of its
  high inputs.
- **`distributed_noninterference`** (`DLCD/DistributedNI.lean`): the TYPED
  confidentiality guarantee across replicas, reusing DLC's fundamental-lemma
  non-interference (`DLC.t3_two_run_general`).
- **`wellTypedLog_implies_htyped`** (`DLCD/TypedLog.lean`): closes the typed-log
  fence — a well-typed committed log discharges the host-typing premise that
  `distributed_noninterference` consumes, so the typed guarantee actually fires
  on real logs.

### G2 — linearizability
- **`single_linearization`** (`DLCD/Linearizable.lean`): all replicas' observed
  stores are samples of ONE sequential trajectory `seqTrajectory init log` at
  their own applied index — a single linearization order respected by all.

### G3 — liveness
- **`weakfair_terminates`** (`DLCD/Termination.lean`): under weak fairness a
  single decree is eventually decided (single-decree progress).
- **`log_grows_unbounded`** (`DLCD/MultiDecreeLiveness.lean`): under a fair slot
  schedule the multi-decree committed log grows without bound.

### G4 — convergence + multi-decree safety
- **`replicas_converge_via_consensus`** (`DLCD/Consensus.lean`): replicas that
  deliver a quorum-`Decided` value reach EQUAL stores (coordination-based
  convergence).
- **`Calm.coordination_free_convergence`** (`DLCD/Calm.lean`): the CALM route —
  monotone/commutative updates converge with NO coordination.
- **`log_agreement_eq`** (`DLCD/MultiDecree.lean`): two logs agreeing on the
  per-slot ballots are equal (multi-decree safety / agreement).

### The seal
- **`SliceWitness.dlc_d_slice_witness`** (`DLCD/Witness.lean`, a `def`): one
  inhabited `SliceWitnessBundle` on a single real 2-replica execution that is
  simultaneously capability-authorized, consensus-committed, converging,
  linearizable, and live — THE demonstration that G1–G4 are jointly satisfiable,
  not vacuously true.

## Honest OPEN fences (documented, not proved here)
- **Live-log / `FailureBudget` scheduling closure**: the delivery-schedule
  fairness feeding liveness is modelled, not tied to a running scheduler.
- **Store-type change**: the committed store is a fixed `Term`; a richer store
  type is future work.
- **`saysI`-on-`CDeriv`**: the CARVe-migrated `CDeriv` judgment does not yet
  carry the signed `says` credential the capability layer uses.
- **Leader election**: quorums are given, not elected.
- **Model, not runtime**: these are guarantees about the Lean model, not a
  proof about `dlc-verifier`'s Rust at run time.
- **Surface syntax**: examples are built in abstract syntax, not the concrete
  surface language.

## Prior art (web-searched 2026-07-22)
- Mathlib naming conventions — namespace-per-type discipline and snake_case
  theorem names for composable proof libraries:
  https://leanprover-community.github.io/contribute/naming.html
- Lean 4 standard-library naming guide (fully-qualified names / namespace
  hierarchy): https://github.com/leanprover/lean4/blob/master/doc/std/naming.md
- Hawblitzel et al., *IronFleet: Proving Safety and Liveness of Practical
  Distributed Systems* — module organization + a status manifest of
  machine-checked safety AND liveness guarantees for a real RSM:
  https://www.microsoft.com/en-us/research/publication/ironfleet-proving-safety-liveness-practical-distributed-systems/
-/

namespace DLCD.Ledger

-- G1: authority + confidentiality
abbrev capability_safety            := @DLCD.capability_safety
-- G1 (R1-inc4a): capability-safety recovered from the command's TYPE by
-- commit-I inversion (typing-native twin of `capability_safety`).
abbrev capability_safety_by_inversion := @DLCD.capability_safety_by_inversion
abbrev capability_safety_linear     := @DLCD.capability_safety_linear
abbrev log_noninterference          := @DLCD.log_noninterference
abbrev distributed_noninterference  := @DLCD.distributed_noninterference
abbrev wellTypedLog_implies_htyped  := @DLCD.wellTypedLog_implies_htyped
-- G2: linearizability
abbrev single_linearization         := @DLCD.single_linearization
-- G3: liveness
abbrev weakfair_terminates          := @DLCD.weakfair_terminates
abbrev log_grows_unbounded          := @DLCD.log_grows_unbounded
-- G4: convergence + multi-decree safety
abbrev replicas_converge_via_consensus := @DLCD.replicas_converge_via_consensus
abbrev coordination_free_convergence   := @DLCD.Calm.coordination_free_convergence
abbrev log_agreement_eq             := @DLCD.log_agreement_eq
-- Byzantine fault-model extension (single-decree safety under ≤f Byzantine)
abbrev byz_agreement                := @DLCD.byz_agreement
-- The seal (a `def`, so re-exported as an `abbrev`)
abbrev dlc_d_slice_witness          := @DLCD.SliceWitness.dlc_d_slice_witness

end DLCD.Ledger
