import DLCD.Correspondence   -- the R2.3 partial-correctness squares + decode `⟦·⟧`
import DLCD.Linearizable     -- G2: seqSpec / single_linearization (over applyPrefix)
import DLCD.CapSafety        -- G1-cap: Authorized / WellFormedLog / capability_safety
import DLCD.DistributedNI    -- G1-NI: LowEquivG / worldStep_preserves_high

/-! # DLC-D Phase R2.4a — the TRANSPORT CAPSTONE: pulling the hand guarantees back
to the deployed Rust runtime through the R2.3 correspondence squares.

R2.3 (`DLCD.Correspondence`) proved the **partial-correctness transport squares**:
the Aeneas-generated `dlc_core.rsm` engine, decoded by `⟦·⟧` (`decGC`/`decTermC`/…),
matches the hand `DLCD.Rsm` model **whenever the generated op returns `ok`**:

* `world_step_square  : world_step g = ok g' → (closedness) → ⟦g'⟧ = worldStep ⟦g⟧`
* `apply_prefix_square: apply_prefix init cmds = ok res → (closedness) → ⟦res⟧ = applyPrefix ⟦init⟧ ⟦cmds⟧`
* `deliver_square     : deliver log r = ok r' → (closedness) → ⟦r'⟧ = deliver ⟦log⟧ ⟦r⟧`
* `commit_square      : ⟦commit g c⟧.log = ⟦g⟧.log ++ [⟦c⟧]`

This module **spends** those squares. For each cleanly-transportable hand guarantee
`P (worldStep …)` / `P (applyPrefix …)` / `P (commit …)`, it produces a `rust_*`
corollary **conditioned on the Rust op returning `ok`** (partial correctness — no-fail
is NOT a theorem; an adversarial ≥2³¹-node payload genuinely overflows the U32
binder-depth counter, see `spec/r2-inc3c-fuelloop-analysis.md`), proved by rewriting
the DECODED Rust result through the square so it inherits `P`. Nothing here weakens a
hand guarantee; every corollary routes through a real square and lands a real decoded
conclusion. No `sorry`, no `axiom`, no `native_decide`; every `rust_*` footprint is
exactly `[propext, Classical.choice, Quot.sound]`.

## What transports cleanly (and what does not)
| Guarantee | `rust_*` corollary | route |
|-----------|--------------------|-------|
| headline transport | `rust_world_step_correct` | `world_step_square` |
| G4 convergence / CALM | `rust_replicas_converge` | `apply_prefix_square` + `replicas_converge_on_prefix` |
| G2 linearizability | `rust_store_is_seqSpec`, `rust_single_linearization` | `apply_prefix_square` + `single_linearization` |
| G3 delivery (operational core) | `rust_deliver_correct` | `deliver_square` |
| G1 capability-safety | `rust_capability_safety` | `commit_square` + `capability_safety` |
| G1 NI (high case) | `rust_worldStep_preserves_high` | `world_step_square` (×2) + `worldStep_preserves_high` |

**Deferred (with reason, NOT forced):**
* **Consensus agreement** (`is_quorum_square`/`decided_square`, hand `agreement`/
  `committed_prefix_agree`). These squares live in `DLCD.CorrespondenceConsensus`,
  which owns the SECOND generated tree (`dlc_d_rsm`). That tree cannot be imported
  into the same Lean module as `dlc_core` (both emit `instDiscriminantTermIsize`,
  which collides at import — see `DLCD.Correspondence`'s header). So a `rust_agreement`
  corollary must live in a module rooted on the `dlc_d_rsm` tree (next to
  `CorrespondenceConsensus`), NOT here. The hand `agreement`/`committed_prefix_agree`
  are pure statements over `Decided`/`Votes` and the two consensus squares already
  bridge `consensus.is_quorum`/`consensus.decided` ↔ them, so the corollary is a
  one-liner once it is in a tree-compatible module. Left out of `Transport.lean`
  purely to keep this module single-generated-tree-clean.
* **G3 liveness reachability** (`command_eventually_applied`, `fair_quorum_decides`,
  `command_eventually_committed`). These are multi-step reachability facts over the
  `FailureBudget` / fair-delivery ORACLE and the abstract `Votes`/`SlotSchedule`
  scheduler — NOT over a single executable `world_step`/`apply_command`. The square
  bridges ONE operational step; iterated fair-scheduling liveness has no executable
  counterpart in the RSM (the scheduler is Phase-1.0-oracular). The transportable
  operational core — that one delivery step advances the decoded replica exactly as
  the model — IS captured by `rust_deliver_correct`. The fair-run wrapper is not a
  property of the code and is honestly out of transport scope.
* **G4 CALM lattice metatheorem** (`Calm.coordination_free_convergence`). Stated over
  an ABSTRACT join-semilattice `L`, not over the RSM `worldStep`/`applyPrefix`; it has
  no generated-side operation to route a square through. The RSM-level convergence it
  motivates IS `replicas_converge_on_prefix`, which `rust_replicas_converge` transports.

## ★★★ THE NI / LABEL-DECODE CRUX — analysis verdict (R2.4a deliverable ★)

The question: `DistributedNI`/`LabelFlow` noninterference is a 2-run hyperproperty that
DISTINGUISHES IFC labels, while the decode `decLab : ifc.Label → DLC.Label` is a CONSTANT
(`fun _ => Label.bottom`) — label-blind. Does NI transport, and if so how honestly?

**(a) Are labels in the executable RSM state? — YES (as inert term payload), but the
NI-relevant labels are NOT.**
The executable `GlobalConfig` is `{ replicas : Vec Replica, log : Vec Command, budget }`
with `Replica.store : syntax.Term`. `syntax.Term` DOES carry labels — `LiftLabel (ifc.Label) _`,
`Declassify (ifc.Label) _ _`, `Command _ _ (ifc.Label)` — and `ifc.Label = alloc.vec.Vec U32`.
So labels are physically present in the runtime store. **BUT**: (1) `reduce.step`/`shift`/`subst`
are LABEL-BLIND — they carry those `Vec U32` fields through UNCHANGED, never branching on a
label value (this is exactly why `decLab` being constant is sound for the reducer
correspondence — `Correspondence` §2d). (2) Crucially, the label the NI *observability gate*
keys on is the STORE-TYPE label `ℓhigh` in `Prop'.at χ ℓhigh`, together with the observer
clearance `ℓLow` — these are TYPING-LAYER / Prop artifacts from the `PropDeriv` judgment.
They are **entirely absent** from the executable `GlobalConfig`: the RSM carries no store types
and no typing derivation. So the quantity distributed-NI distinguishes lives wholly in the
type layer, not in the executable state.

**(b) Can `decLabel` be made FAITHFUL (Vec U32 → CapabilityLattice injectively)? — NO, and it
would not help.**
`DLC.Label = nucleus_ifc_kernel.CapabilityLattice` is a 13-field record over the 3-element enum
`CapabilityLevel` → exactly 3¹³ = 1 594 323 elements, **finite**. `ifc.Label = Vec U32` is
countably **infinite**. No injection `Vec U32 ↪ CapabilityLattice` exists (infinite → finite).
A globally faithful decode is *impossible*. Moreover — even a faithful decode of the
TERM-carried labels would NOT transport `worldStep_preserves_high`, because that theorem's gate
uses the store-TYPE label `ℓhigh`, which is not a term field and not in the executable state at
all. Faithfulness of the term-label decode is *irrelevant* to NI transport.

**(c) The HONEST NI transport + recommendation.**
NI transports as a **preservation** corollary — `rust_worldStep_preserves_high` below — and it
does so CLEANLY and non-vacuously: the hand `LRel`/`LowEquivG` relation is defined by recursion
on the store TYPE `φ` and checks only TYPE-level labels; it never inspects a term-carried label,
so the decode collapsing `Vec U32 → ⊥` is orthogonal to it. Via `world_step_square` applied to
each of two runs, `⟦gᵢ'⟧ = worldStep ⟦gᵢ⟧`, so the decoded stepped configs inherit
`worldStep_preserves_high`: *a `ℓLow`-observer cannot distinguish the two decoded runs after an
`ok` world step, given they were low-equivalent at a HIGH store type over a shared log.* This is
genuine (the `DistNIWitness` high-differs-yet-low-equal witness survives decode — the decoded
stores can genuinely differ and the gate still hides them).

**The exact residual (honest fence).** The transported statement is about the DECODED (typed-
model) configs, with the store type `Prop'.at χ ℓhigh` and observer `ℓLow` supplied as EXTERNAL
parameters. It is NOT the claim "the Rust runtime's own label annotations enforce confidentiality":
the runtime carries no store types and no typing derivation, so there is no executable object to
attach `ℓhigh` to. The `low` case (`worldStep_preserves_low`) additionally needs a typed-log
invariant (`PropDeriv [] payload (φ ⊸ φ)`) which is likewise a typing-layer hypothesis the RSM
does not witness; it transports on the SAME external-typing footing (not specialized below to keep
the module lean, but identical in shape to the high case). Term-carried labels are inert under
both the reducer (carried unchanged) and the decode (collapsed to `⊥`), and — being the *values*
NI's relation never reads — their collapse costs the transport nothing.

**Recommendation: HONEST-CAVEAT, not make-faithful.** A faithful term-label decode is both
impossible (infinite→finite) and useless (the gate reads type labels, not term labels). The
honest transport is `rust_worldStep_preserves_high` with the explicit fence that store-types and
the observer are external typing parameters and term-labels are inert. **Confidence: HIGH** — the
finiteness obstruction is decisive, and the type-vs-term-label separation is manifest in the
definitions (`LRel` recurses on `Prop'`, the store is a `Term`).

## Prior art (from `Correspondence.lean`/`DistributedNI.lean` headers; WebSearch budget
exhausted this cycle):
- Aeneas (Ho–Protzenko–Fromherz, ICFP 2022): extracted-fn ↔ spec refinement.
  https://arxiv.org/abs/2206.07185
- Grove (Sharma et al., SOSP 2023): impl refines an abstract state-machine spec (the
  decode / invoke-abstract / re-encode square). https://iris-project.org/pdfs/2023-sosp-grove.pdf
- seL4 IFC (Murray et al.): machine-checked NI over a deterministic state machine — the
  closest verified RSM-NI prior art; `worldStep` is that machine, `LowEquivG` the observation.
- FLAQR (Mondal–Algehed–Arden, CSF 2022): confidentiality under consensus/replication.
  https://arxiv.org/abs/2205.04384
-/

namespace DLCD.Transport

open Aeneas Aeneas.Std Result
open dlc_core
open DLCD.Correspondence

/-! ## 1. ★ THE HEADLINE TRANSPORT — `rust_world_step_correct`.

`world_step_square`, repackaged as the headline partial-correctness transport with the
`ok`-premise leading: one synchronous world step of the deployed Rust engine, when it
returns `ok g'`, decodes to exactly the hand `DLCD.worldStep` of the decoded input. This
is the equation every G1–G4 pull-back rides on. -/
theorem rust_world_step_correct (g g' : rsm.GlobalConfig)
    (hok : rsm.world_step g = ok g')
    (hstores : ∀ rep ∈ g.replicas.val, ClosedTm rep.store)
    (hlog : ∀ c ∈ g.log.val, ClosedTm c.payload) :
    decGC decTermC decPropC g' = DLCD.worldStep (decGC decTermC decPropC g) :=
  world_step_square g g' hstores hlog hok

/-- The per-step operational leaf `apply_prefix_square`, repackaged with the `ok`-premise
leading: folding a committed command prefix onto an initial store, when the Rust fold
returns `ok res`, decodes to the hand `DLCD.applyPrefix`. Both G2 and G4 spend this. -/
theorem rust_apply_prefix_correct (init res : syntax.Term) (cmds : Slice rsm.Command)
    (hok : rsm.apply_prefix init cmds = ok res)
    (hinit : ClosedTm init) (hcmds : ∀ c ∈ cmds.val, ClosedTm c.payload) :
    decTermC res = DLCD.applyPrefix (decTermC init) (cmds.val.map (decCmd decTermC decPropC)) :=
  apply_prefix_square init res cmds hinit hcmds hok

/-! ## 2. Shared bridge: an `ok` Rust prefix-fold IS a hand `AppliedPrefix`.

The decoded result of `rsm.apply_prefix init cmds = ok res`, packaged as a `Replica`
whose store is `⟦res⟧` and whose `applied` count is the whole decoded log length,
satisfies the hand invariant `AppliedPrefix ⟦init⟧ ⟦cmds⟧` — because `log.take log.length =
log`, so the invariant's `applyPrefix … (log.take applied)` is exactly what
`apply_prefix_square` gives. Both the convergence and the linearization transports spend
this bridge, feeding the decoded replica into a hand metatheorem. -/
private theorem appliedPrefix_of_run (init res : syntax.Term) (cmds : Slice rsm.Command)
    (hinit : ClosedTm init) (hcmds : ∀ c ∈ cmds.val, ClosedTm c.payload)
    (hok : rsm.apply_prefix init cmds = ok res) :
    DLCD.AppliedPrefix (decTermC init) (cmds.val.map (decCmd decTermC decPropC))
      ⟨0, decTermC res, (cmds.val.map (decCmd decTermC decPropC)).length⟩ := by
  show decTermC res = DLCD.applyPrefix (decTermC init)
    ((cmds.val.map (decCmd decTermC decPropC)).take
      (cmds.val.map (decCmd decTermC decPropC)).length)
  rw [List.take_length]
  exact apply_prefix_square init res cmds hinit hcmds hok

/-! ## 3. ★ G4 — CONVERGENCE / CALM (the flagship).

Two Rust replicas that each folded the SAME committed prefix onto the same initial store
(both Rust runs returning `ok`) decode to EQUAL stores. Routes through `apply_prefix_square`
(via the bridge) into the hand convergence metatheorem `replicas_converge_on_prefix`: the
decoded store is a deterministic FUNCTION of the applied prefix, so coordination-free
replicas converge. Non-vacuous — the `dup` witness (`Correspondence.applyPreservesWS_witness`)
exhibits a genuinely state-CHANGING converged store, so this is not discharged over a no-op. -/
theorem rust_replicas_converge (init res₁ res₂ : syntax.Term) (cmds : Slice rsm.Command)
    (hinit : ClosedTm init) (hcmds : ∀ c ∈ cmds.val, ClosedTm c.payload)
    (hok₁ : rsm.apply_prefix init cmds = ok res₁)
    (hok₂ : rsm.apply_prefix init cmds = ok res₂) :
    decTermC res₁ = decTermC res₂ :=
  DLCD.replicas_converge_on_prefix
    (appliedPrefix_of_run init res₁ cmds hinit hcmds hok₁)
    (appliedPrefix_of_run init res₂ cmds hinit hcmds hok₂) rfl

/-! ## 4. ★ G2 — LINEARIZABILITY.

Every `ok` Rust prefix-fold's decoded store lies on the SEQUENTIAL SPECIFICATION trajectory:
it equals `seqSpec ⟦init⟧ ⟦cmds⟧` — the sequential-spec run of the committed prefix in log
order. No decoded observation contradicts the sequential spec. Routes through
`apply_prefix_square` + `seqSpec_eq_applyPrefix`. -/
theorem rust_store_is_seqSpec (init res : syntax.Term) (cmds : Slice rsm.Command)
    (hok : rsm.apply_prefix init cmds = ok res)
    (hinit : ClosedTm init) (hcmds : ∀ c ∈ cmds.val, ClosedTm c.payload) :
    decTermC res = DLCD.seqSpec (decTermC init) (cmds.val.map (decCmd decTermC decPropC)) := by
  rw [DLCD.seqSpec_eq_applyPrefix]
  exact apply_prefix_square init res cmds hinit hcmds hok

/-- **The single linearization order, transported.** Two Rust replicas folding the same
committed prefix (both returning `ok`) both respect ONE sequential run `σ`: their decoded
stores are the same trajectory function sampled at their applied-index. Routes through the
bridge into the hand metatheorem `single_linearization`. This is the SMR-linearizability
content: there exists a single committed total order every decoded observation is a point on. -/
theorem rust_single_linearization (init res₁ res₂ : syntax.Term) (cmds : Slice rsm.Command)
    (hinit : ClosedTm init) (hcmds : ∀ c ∈ cmds.val, ClosedTm c.payload)
    (hok₁ : rsm.apply_prefix init cmds = ok res₁)
    (hok₂ : rsm.apply_prefix init cmds = ok res₂) :
    ∃ σ : Nat → DLC.Term,
      decTermC res₁ = σ (cmds.val.map (decCmd decTermC decPropC)).length
      ∧ decTermC res₂ = σ (cmds.val.map (decCmd decTermC decPropC)).length :=
  DLCD.single_linearization
    (appliedPrefix_of_run init res₁ cmds hinit hcmds hok₁)
    (appliedPrefix_of_run init res₂ cmds hinit hcmds hok₂)

/-! ## 5. G3 — DELIVERY (the transportable operational core).

One delivery step of the deployed Rust engine, when it returns `ok r'`, decodes to exactly
the hand `DLCD.deliver` of the decoded log and replica. This is the operational core the
fair-scheduling liveness wrappers (`command_eventually_applied`, …) are built ON; those
wrappers quantify over the Phase-1.0 fair-delivery ORACLE and have no executable counterpart
(see the module header's deferral note). `deliver_square`, repackaged with `ok` leading. -/
theorem rust_deliver_correct (log : alloc.vec.Vec rsm.Command) (r r' : rsm.Replica)
    (hok : rsm.deliver log r = ok r')
    (hr : ClosedTm r.store) (hlog : ∀ c ∈ log.val, ClosedTm c.payload) :
    decRep decTermC r' = DLCD.deliver (decLog decTermC decPropC log) (decRep decTermC r) :=
  deliver_square log r r' hr hlog hok

/-! ## 6. ★ G1 — CAPABILITY-SAFETY.

Committing a command to the deployed Rust engine's log, when it returns `ok g'`, keeps the
decoded log CAPABILITY-SAFE: every command in the decoded new log was authorized (some
principal `says` its guarding capability, with a real derivation). Routes through
`commit_square` (the decoded new log is `⟦g⟧.log ++ [⟦c⟧]`), the provenance constructor
`WellFormedLog.commit`, and the hand metatheorem `capability_safety`. Conditioned on the
decoded prior log being well-formed and the decoded new command authorized — the hand
guarantee's own hypotheses, unweakened. -/
theorem rust_capability_safety (g g' : rsm.GlobalConfig) (c : rsm.Command)
    (issuer : DLC.Principal)
    (hok : rsm.commit g c = ok g')
    (hlen : g.log.val.length < Std.Usize.max)
    (hwf : DLCD.WellFormedLog (decLog decTermC decPropC g.log))
    (hauth : DLCD.Authorized (decCmd decTermC decPropC c) issuer) :
    ∀ cmd ∈ (decGC decTermC decPropC g').log, ∃ iss, DLCD.Authorized cmd iss := by
  -- `commit_square`: `⟦commit g c⟧.log = ⟦g⟧.log ++ [⟦c⟧]`; specialize at the `ok g'`.
  have hlog' : (decGC decTermC decPropC g').log
      = decLog decTermC decPropC g.log ++ [decCmd decTermC decPropC c] := by
    have h : (ok ((decGC decTermC decPropC g').log) : Result (List DLCD.Command))
        = ok (decLog decTermC decPropC g.log ++ [decCmd decTermC decPropC c]) := by
      have h0 := commit_square decTermC decPropC g c hlen
      rw [hok] at h0
      exact h0
    exact Result.ok.inj h
  -- The decoded new log is a `WellFormedLog.commit` node; extract authorization from it.
  have hwf' : DLCD.WellFormedLog (decGC decTermC decPropC g').log := by
    rw [hlog']; exact DLCD.WellFormedLog.commit hwf hauth
  exact DLCD.capability_safety _ hwf'

/-! ## 7. ★★★ G1 — DISTRIBUTED NONINTERFERENCE (high case) — THE CRUX, transported.

See the module header's ★★★ analysis for the full verdict. The NI *preservation* property
transports cleanly: because the hand relation `LowEquivG`/`LRel` recurses on the store TYPE
and keys its observability gate on the type-level label `ℓhigh` (never on a term-carried
label), the label-blind decode is orthogonal to it. Applying `world_step_square` to EACH of
two runs rewrites `⟦gᵢ'⟧ = worldStep ⟦gᵢ⟧`, so the decoded stepped configs inherit
`worldStep_preserves_high`: a `ℓLow`-observer cannot distinguish the two decoded runs after an
`ok` world step, given they were `LowEquivG` at a HIGH store type over a shared decoded log.

HONEST FENCE (restated at the theorem): the store type `Prop'.at χ ℓhigh` and observer `ℓLow`
are EXTERNAL typing parameters — the executable RSM carries no store types. This is NI of the
DECODED typed model with the Rust step proven to match, NOT a claim that the runtime's own
label bytes enforce IFC. Non-vacuous: `DistNIWitness` exhibits genuinely-differing high stores
that stay low-equivalent, and decode preserves that (the decoded stores can differ; the gate
still hides them). -/
theorem rust_worldStep_preserves_high (ℓLow : DLC.Label) (χ : DLC.Prop') {ℓhigh : DLC.Label}
    (hhigh : DLC.Label.le ℓhigh ℓLow = false)
    (g₁ g₂ g₁' g₂' : rsm.GlobalConfig)
    (hs₁ : ∀ rep ∈ g₁.replicas.val, ClosedTm rep.store)
    (hl₁ : ∀ c ∈ g₁.log.val, ClosedTm c.payload)
    (hs₂ : ∀ rep ∈ g₂.replicas.val, ClosedTm rep.store)
    (hl₂ : ∀ c ∈ g₂.log.val, ClosedTm c.payload)
    (hlogeq : (decGC decTermC decPropC g₁).log = (decGC decTermC decPropC g₂).log)
    (hrel : DLCD.LowEquivG ℓLow (DLC.Prop'.at χ ℓhigh)
      (decGC decTermC decPropC g₁) (decGC decTermC decPropC g₂))
    (hok₁ : rsm.world_step g₁ = ok g₁') (hok₂ : rsm.world_step g₂ = ok g₂') :
    DLCD.LowEquivG ℓLow (DLC.Prop'.at χ ℓhigh)
      (decGC decTermC decPropC g₁') (decGC decTermC decPropC g₂') := by
  rw [world_step_square g₁ g₁' hs₁ hl₁ hok₁, world_step_square g₂ g₂' hs₂ hl₂ hok₂]
  exact DLCD.worldStep_preserves_high ℓLow χ hhigh hlogeq hrel

end DLCD.Transport
