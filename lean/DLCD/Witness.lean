import DLCD.CapSafety
import DLCD.Linearizable
import DLCD.Liveness

/-! # DLC-D Phase 1.3 — THE DLC-D VERTICAL-SLICE WITNESS

This module is the **sealing witness** of the DLC-D vertical slice: it exhibits a
SINGLE concrete 2-replica execution and proves that ALL FOUR distributed
guarantees hold on it, **non-vacuously**. It is the distributed analogue of the
Iris `spinProg_witnessed` seal — the one increment whose entire job is to
demonstrate that the four universal metatheorems are *jointly satisfiable on a
real instance*, not empty conditionals.

## Why a witness at all — the anti-vacuity / IronFleet discipline

A universal theorem `∀ x, H x → G x` is worthless if `H` is unsatisfiable: it
guarantees nothing because it applies to nothing. The remedy is a
**demonstration** — a concrete `a` with a proof of `H a` (and hence `G a`),
showing the hypotheses are jointly inhabited on a real run. This is the
discipline behind end-to-end verified distributed systems such as **IronFleet**
(Hawblitzel et al., CACM 2017), which verifies *both* safety and liveness of a
real Paxos-based replicated-state-machine implementation and a sharded key-value
store — the guarantees are meaningful precisely because they are discharged on
an actual system, not a vacuous spec. Here we compose DLC-D's four separately
proved guarantees — capability-safety (`CapSafety`), consensus/convergence
(`Consensus`/`Rsm`), linearizability (`Linearizable`), and liveness
(`Liveness`) — onto ONE fixed run and show each is inhabited on real objects.

## The ONE concrete run (everything is a real, kernel-checkable object)

- **Two replicas** `r1Seed = ⟨0, var 0, 0⟩`, `r2Seed = ⟨1, var 0, 0⟩`, sharing
  the initial store `init = var 0`.
- **A capability-authorized, state-CHANGING write** `wcmd`: guarded by the real
  `says`-credential `issuer says writeCap` (`writeCommand issuer writeCap
  writeVal`), whose payload `writeVal = λ_. ⟨x, x⟩` genuinely transforms the
  store (`applyCommand wcmd (var 0) = ⟨var 0, var 0⟩`). The `issuer`, `writeCap`,
  signature, and the signed credential `saysWitness` are reused *verbatim* from
  `CapSafety.CapSafetyAntiVacuity` — a genuine `Deriv … (issuer says writeCap)`.
- **A `FailureBudget` with `fairDelivery = true`** (`FailureBudget.zero 1`).
- **A correct quorum** `Qall = univ : Finset (Fin 2)` — the whole 2-replica set,
  a strict majority (`2·2 > 2`).

## The five sealed facts (each on the objects above, nothing opaque)

1. **Capability-safety** (`g1_capability_safe`): `wcmd` is `Authorized issuer`
   carrying the REAL `Deriv (issuer says writeCap)` credential; committing it
   through the enforce-by-construction `commit` gate yields a `WellFormedLog`,
   and `committed_write_says_cap` recovers the signed credential from the log —
   the committed write provably came from a capability-holder.
2. **Consensus / convergence** (`wcmd_decided`, `replicas_converge`): `wcmd` is
   `Decided` by the concrete quorum `Qall`; feeding that decision through
   `replicas_converge_via_consensus`, both replicas — delivering the one
   committed slot — reach EQUAL stores (the converged value `⟨var 0, var 0⟩`).
3. **Concurrency-safety / linearizability** (`linearizable_run`, `on_trajectory`):
   the converged store lies on the single sequential run
   `σ = seqTrajectory init clog`; both replicas' observed stores are `σ` sampled
   at their own applied-index — one linearization order, respected by all.
4. **Liveness** (`write_live`, `both_eventually_apply`): under the
   `fairDelivery = true` contract, `wcmd` is eventually `Decided` and eventually
   applied by BOTH replicas (`command_eventually_written` /
   `command_eventually_applied`).
5. **State genuinely CHANGES** (`state_changed`): the converged/written value
   `⟨var 0, var 0⟩` ≠ the initial store `var 0`, so nothing is vacuous.

`dlc_d_slice_witness : SliceWitnessBundle` bundles all five into one inhabited
record — THE seal that DLC-D's four guarantees are jointly satisfiable on a real
capability-authorized, consensus-committed, converging, linearizable, live
2-replica execution. A negative contrast (`unauthWrite_not_authorized`) confirms
the gate is real: an unguarded write can never enter the well-formed log.

`#print axioms dlc_d_slice_witness = [propext, Classical.choice, Quot.sound]`
(the Mathlib-`Finset` base) — no `sorryAx`, no `native_decide`.

## Prior art (web-searched 2026-07-22; URLs recorded)
- Hawblitzel–Howell–Kapritsos–Lorch–Parno–Roberts–Setty–Zill, *IronFleet:
  Proving Safety and Liveness of Practical Distributed Systems* (CACM 60(7),
  2017) — end-to-end machine-checked safety AND liveness of a real Paxos RSM and
  a sharded KV store; the guarantees are demonstrated on an actual system:
  https://www.andrew.cmu.edu/user/bparno/papers/ironfleet-cacm.pdf ,
  https://cacm.acm.org/research/ironfleet/ ,
  https://www.microsoft.com/en-us/research/publication/ironfleet-proving-safety-liveness-practical-distributed-systems/
- microsoft/Ironclad (the IronFleet artifact):
  https://github.com/microsoft/Ironclad/blob/main/ironfleet/README.md
- Yao et al., *Shipwright: Proving liveness of distributed systems with
  Byzantine participants* (arXiv:2507.14080) — recent end-to-end liveness
  verification: https://arxiv.org/pdf/2507.14080
- The non-vacuous-witness / demonstration discipline: a universal theorem is
  empty unless its hypotheses are jointly satisfiable on a real instance — the
  same anti-vacuity ledger used across this program (`CapSafety.CapSafetyAntiVacuity`,
  `Consensus.ConsensusAntiVacuity`, `Rsm.RsmAntiVacuity`, `Liveness.LivenessAntiVacuity`).
-/

namespace DLCD

open DLC

namespace SliceWitness

/-! ## 0. The reused REAL capability credential.

`issuer`, `writeCap`, `sig`, and the signed says-credential `saysWitness` are
taken verbatim from `CapSafety.CapSafetyAntiVacuity`. `saysWitness` is a genuine
`Deriv … (issuer says writeCap)` built by the signature-carrying `Deriv.saysI` —
the PCA signed capability the commit gate demands. -/

open DLCD.CapSafetyAntiVacuity (issuer writeCap sig saysWitness)

/-! ## 1. The ONE concrete run: two replicas, one authorized state-changing write. -/

/-- The state-CHANGING write payload `λ_. ⟨x, x⟩` (duplicate the register value).
Identical to `Rsm`'s `dup` payload, so it genuinely transforms the store. -/
def writeVal : Term := Term.lam (Prop'.atom 0) (Term.pair (Term.var 0) (Term.var 0))

/-- The shared initial store. -/
def init : Term := Term.var 0

/-- **THE authorized, state-changing write command.** Guarded by `issuer says
writeCap` (capability-authorized) AND carrying the dup payload (state-changing).
Because `Authorized` depends only on the `cap` slot, this single command is both
provably authorized and provably state-changing — the object that lets all four
guarantees meet on one run. -/
def wcmd : Command := writeCommand issuer writeCap writeVal

/-- The two replica seeds, both starting at the shared initial store, `applied = 0`. -/
def r1Seed : Replica := ⟨0, init, 0⟩
def r2Seed : Replica := ⟨1, init, 0⟩

/-- The FIXED initial global config: two replicas, empty (well-formed) log, and a
`FailureBudget` with `fairDelivery = true` (`FailureBudget.zero 1`). -/
def g0 : GlobalConfig := { replicas := [r1Seed, r2Seed], log := [], budget := FailureBudget.zero 1 }

/-- `wcmd` is `Authorized` by `issuer` — witnessed by the REAL signed credential
`saysWitness`. This is the term one MUST hold to call `commit`. -/
theorem wcmd_authorized : Authorized wcmd issuer :=
  ⟨_, _, _, rfl, ⟨saysWitness⟩⟩

/-! ## 2. GUARANTEE 1 — capability-safety: the committed write carries a real credential. -/

/-- Commit the authorized write through the enforce-by-construction gate. This
call type-checks ONLY because `wcmd_authorized` is supplied. -/
def gCommitted : GlobalConfig := commit g0 wcmd issuer wcmd_authorized

/-- The committed log is well-formed by construction of `commit`. -/
theorem committedLog_wellFormed : WellFormedLog gCommitted.log :=
  commit_wellFormed wcmd_authorized WellFormedLog.nil

/-- The authorized write really is in the committed log. -/
theorem wcmd_committed : wcmd ∈ gCommitted.log := by
  simp [gCommitted, commit, g0]

/-- **CAPABILITY-SAFETY on the run.** The committed write carries a REAL `Deriv`
credential of `issuer says writeCap` — recovered from the well-formed log by the
`committed_write_says_cap` metatheorem. The committed write provably came from a
capability-holder. -/
theorem g1_capability_safe :
    ∃ (Γ : Ctx) (t : Term), Nonempty (Deriv Γ t (Prop'.says issuer writeCap)) :=
  committed_write_says_cap committedLog_wellFormed (value := writeVal) wcmd_committed

/-! ## 3. GUARANTEE 2 — consensus decides the write; both replicas converge. -/

/-- The single-decree ballot over the 2 replicas: both vote for the write command. -/
def votesW : Votes 2 Command := fun _ => some wcmd

/-- The correct quorum: the whole 2-replica set (a strict majority: `2·2 > 2`). -/
def Qall : Finset (Fin 2) := Finset.univ

theorem Qall_quorum : IsQuorum Qall := by unfold IsQuorum Qall; decide

/-- **CONSENSUS.** The write is `Decided` by the concrete quorum `Qall` — a real
quorum unanimously voting the real command. -/
theorem wcmd_decided : Decided votesW wcmd :=
  ⟨Qall, Qall_quorum, by intro r _; rfl⟩

/-- The committed log both replicas apply: the single slot holding the decided write. -/
def clog : CommittedLog := [wcmd]

/-- Both replicas after delivering the one committed slot. -/
def r1 : Replica := deliver clog r1Seed
def r2 : Replica := deliver clog r2Seed

/-- The seeds satisfy the prefix invariant trivially (`take 0 = []`). -/
theorem r1Seed_inv : AppliedPrefix init clog r1Seed := by
  unfold AppliedPrefix applyPrefix; rfl
theorem r2Seed_inv : AppliedPrefix init clog r2Seed := by
  unfold AppliedPrefix applyPrefix; rfl

/-- After delivery both replicas maintain the prefix invariant (Phase-1.0 lemma). -/
theorem r1_inv : AppliedPrefix init clog r1 := deliver_maintains_prefix r1Seed_inv
theorem r2_inv : AppliedPrefix init clog r2 := deliver_maintains_prefix r2Seed_inv

/-- The per-slot ballot family: every slot's value is decided by `votesW`. -/
def slotVotes : ℕ → Votes 2 Command := fun _ => votesW

/-- Every committed slot of `clog` is `Decided` by its ballot — the single slot
`0` holds `wcmd`, decided by `wcmd_decided`; there is no other slot. -/
theorem clog_slots_decided : ∀ i c, clog[i]? = some c → Decided (slotVotes i) c := by
  intro i c h
  cases i with
  | zero =>
      simp only [clog, List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact wcmd_decided
  | succ j =>
      simp [clog] at h

/-- **CONVERGENCE (via consensus).** Both replicas — running the consensus-decided
committed log — reach EQUAL stores. The equality is driven by `agreement` (both
logs forced equal) composed with the deterministic-fold convergence seed. -/
theorem replicas_converge : r1.store = r2.store :=
  replicas_converge_via_consensus slotVotes rfl clog_slots_decided clog_slots_decided
    r1_inv r2_inv rfl

/-- The converged store is the *transformed* value `⟨var 0, var 0⟩` — the `dup`
write applied to `init`. -/
theorem converged_store : r1.store = Term.pair (Term.var 0) (Term.var 0) := rfl

/-- **STATE GENUINELY CHANGES.** The converged/written value is distinct from the
initial store — nothing is vacuous. -/
theorem state_changed : r1.store ≠ init := by
  rw [converged_store]
  intro h; exact Term.noConfusion h

/-! ## 4. GUARANTEE 3 — concurrency-safety: the converged store is linearizable. -/

/-- **LINEARIZABILITY.** There is a SINGLE sequential run `σ = seqTrajectory init
clog` such that each replica's observed store equals `σ` at its own applied-index
— one linearization order (the committed log), respected by both replicas. -/
theorem linearizable_run :
    ∃ σ : Nat → Term, r1.store = σ r1.applied ∧ r2.store = σ r2.applied :=
  single_linearization r1_inv r2_inv

/-- The linearization made explicit: both stores are literally
`seqTrajectory init clog` sampled at their indices. -/
theorem on_trajectory :
    r1.store = seqTrajectory init clog r1.applied
      ∧ r2.store = seqTrajectory init clog r2.applied :=
  linearizable r1_inv r2_inv

/-! ## 5. GUARANTEE 4 — liveness: the write is eventually decided and applied by both. -/

/-- The FailureBudget with `fairDelivery = true` and the crash-fault grade unspent. -/
def budget : FailureBudget := FailureBudget.zero 1

/-- The contract holds: fair delivery assumed, fault budget not overspent. -/
theorem budget_contract : budget.withinContract = true := by decide

/-- The liveness run: at every step the correct quorum votes the write. -/
def run : ℕ → Votes 2 Command := fun _ => votesW

/-- Honesty: every vote of the run is `some wcmd`. -/
theorem run_honest : ∀ k r, r ∈ Qall → (run k) r ≠ none → (run k) r = some wcmd := by
  intro k r _ _; rfl

/-- The rank (unvoted-correct count) is `0` at every step — the whole quorum has
already voted. -/
theorem run_rank_zero (k : ℕ) : rank Qall (run k) = 0 := by
  show rank Qall votesW = 0
  decide

/-- Fairness is (vacuously) satisfied: the rank is never positive to decrease,
because every correct replica has voted. This is the operational meaning of
`fairDelivery = true`, guarded by it. -/
theorem run_fair : budget.fairDelivery = true →
    ∀ k, 0 < rank Qall (run k) → rank Qall (run (k + 1)) < rank Qall (run k) := by
  intro _ k hk
  rw [run_rank_zero] at hk
  omega

/-- **LIVENESS (the full metatheorem on the run).** Under the `fairDelivery =
true` contract, `wcmd` is BOTH (1) eventually `Decided` and (2) eventually
applied by the replica — its slot-0 write reflected in the store. -/
theorem write_live :
    (∃ k, Decided (run k) wcmd) ∧
    (∃ m, ((deliver clog)^[m] r1Seed).applied = 0 + 1 ∧
          ((deliver clog)^[m] r1Seed).store = applyCommand wcmd (applyPrefix init (clog.take 0)) ∧
          AppliedPrefix init clog ((deliver clog)^[m] r1Seed)) :=
  command_eventually_written budget budget_contract run Qall wcmd Qall_quorum
    run_honest run_fair (i := 0) (log := clog) (by decide) rfl rfl r1Seed_inv

/-- **BOTH replicas eventually apply the write.** Delivery-liveness for each
replica: after bounded deliveries each has advanced past the committed slot. -/
theorem both_eventually_apply :
    (∃ m, 0 < ((deliver clog)^[m] r1Seed).applied) ∧
    (∃ m, 0 < ((deliver clog)^[m] r2Seed).applied) :=
  ⟨command_eventually_applied clog r1Seed 0 (by decide),
   command_eventually_applied clog r2Seed 0 (by decide)⟩

/-! ## 6. THE SEAL — all five facts bundled on the one concrete run. -/

/-- **THE DLC-D VERTICAL-SLICE WITNESS.** An inhabited record of the five sealed
facts on the ONE concrete 2-replica execution: capability-authorized (real
credential), consensus-decided, converged, linearizable, live (both replicas),
and state-changing. Its inhabitant `dlc_d_slice_witness` is the seal that DLC-D's
four guarantees are jointly satisfiable on a real run. -/
structure SliceWitnessBundle where
  /-- 1. Capability-safety: the committed write carries a real `says`-credential. -/
  capability_authorized :
    ∃ (Γ : Ctx) (t : Term), Nonempty (Deriv Γ t (Prop'.says issuer writeCap))
  /-- The committed log is well-formed (built only by authorized commits). -/
  wellFormed : WellFormedLog gCommitted.log
  /-- 2a. Consensus: the write is decided by the concrete quorum. -/
  decided : Decided votesW wcmd
  /-- 2b. Convergence: both replicas reach equal stores. -/
  converged : r1.store = r2.store
  /-- 3. Linearizability: both observations lie on one sequential run. -/
  linearizable : ∃ σ : Nat → Term, r1.store = σ r1.applied ∧ r2.store = σ r2.applied
  /-- 4. Liveness: the write is eventually decided and applied by both replicas. -/
  live :
    (∃ k, Decided (run k) wcmd) ∧
    (∃ m, 0 < ((deliver clog)^[m] r1Seed).applied) ∧
    (∃ m, 0 < ((deliver clog)^[m] r2Seed).applied)
  /-- 5. Non-vacuity: the converged/written value differs from the initial store. -/
  state_changed : r1.store ≠ init

/-- **THE SEAL, inhabited.** All five DLC-D guarantees, discharged on the single
concrete capability-authorized, consensus-committed, converging, linearizable,
live 2-replica execution. This is the non-vacuous witness. -/
def dlc_d_slice_witness : SliceWitnessBundle where
  capability_authorized := g1_capability_safe
  wellFormed := committedLog_wellFormed
  decided := wcmd_decided
  converged := replicas_converge
  linearizable := linearizable_run
  live := ⟨write_live.1, both_eventually_apply.1, both_eventually_apply.2⟩
  state_changed := state_changed

/-! ## 7. Negative contrast — the gate is real. -/

/-- An unguarded write (`cap = none`) with the same state-changing payload. -/
def unauthWrite : Command := { payload := writeVal, cap := none }

/-- **NEGATIVE CONTRAST.** The unguarded write is NOT authorizable — there is no
`says`-guard to prove — so it can never enter the well-formed committed log. The
enforce-by-construction gate is real, not decorative. -/
theorem unauthWrite_not_authorized : ¬ Authorized unauthWrite issuer :=
  not_authorized_of_cap_none rfl

end SliceWitness

end DLCD
