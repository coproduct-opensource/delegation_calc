import DLCD.Transport   -- the R2.4a single-step transport corollaries + the R2.3 squares

/-! # DLC-D Phase R5 / IFC-1 — FULL-EXECUTION NONINTERFERENCE, transported.

`DLCD.Transport.rust_worldStep_preserves_high` (R2.4a) transported the model's
distributed-NI *preservation* one `world_step` at a time: two `ok` Rust world
steps that start `LowEquivG`-related stay `LowEquivG`-related after ONE step. This
module (spec/r5-ifc-replan.md §5, target IFC-1) generalizes that to a WHOLE RUN:
two multi-step Rust executions that each stay `ok` for `k` steps and start
`LowEquivG`-related remain `LowEquivG`-related after `k` steps — i.e. it transports
the model's already-proven `DLCD.distributed_noninterference` (and its low-case
sibling) to the deployed Aeneas runtime core.

## What is new (the §5 staging)
* **IFC-1.a — `world_step_preserves_closed`.** The one routine prerequisite: an `ok`
  Rust `world_step` preserves decoded closedness of every replica store and of the
  log. This is the side-condition that lets the transport square be re-applied at
  the NEXT step. Proved through the model: `world_step_square` decodes `g'` to
  `DLCD.worldStep ⟦g⟧`, and `DLCD.deliver`/`DLCD.applyCommand` provably preserve
  `DLC.Closed` (bounded reduction preserves closedness — `DLC.step_preserves_closed`
  iterated; the log is unchanged by `worldStep`).
* **IFC-1.b — `rust_worldSteps_correct`.** A `k`-step Rust run that stays `ok`
  decodes to `k` iterations of the model `DLCD.worldSteps`. Induction on the run,
  composing `world_step_square` + IFC-1.a at each step.
* **IFC-1.c — `rust_distributed_noninterference` (the headline).** Two `k`-step `ok`
  Rust runs, low-equivalent at a HIGH store type over a shared decoded log, stay
  low-equivalent after the whole run. Rewrite both runs by IFC-1.b, then apply the
  MODEL's `DLCD.distributed_noninterference`.
* **IFC-1.d — `rust_distributed_noninterference_low`.** The low case on the same
  external-typing footing: a `k`-step run of a shared typed-core-endomorphism log
  preserves `LowEquivG` at the (fixed) store type. Iterates
  `DLCD.worldStep_preserves_low` (via the new model capstone `worldSteps_preserves_low`)
  and transports it by IFC-1.b.

## Honest fence (unchanged from R2.4a, restated)
`χ`, `ℓhigh`, `ℓLow`, and the low case's per-command `PropDeriv [] payload (φ ⊸ φ)`
typing obligation remain **EXTERNAL typing parameters** — the executable RSM carries
no store types and no typing derivation (Transport.lean §7 ★★★; the decode
impossibility). IFC-1 makes the *preservation* total-in-time; it does NOT make the
runtime self-witness the classification. That is the R6/IFC-2 hook. Everything here
is CONDITIONED on the Rust ops returning `ok` (partial correctness, consistent with
R2), routes through the real `world_step_square`, and lands the model's real proven
NI — no weakening of `DLCD.distributed_noninterference`, no new axiom/`sorry`.

`#print axioms` footprint of every theorem: `[propext, Classical.choice, Quot.sound]`.
-/

namespace DLCD.Transport

open Aeneas Aeneas.Std Result
open dlc_core
open DLCD.Correspondence

/-! ## 0. Model-level closedness preservation (pure `DLCD.Rsm` facts).

These are statements about the HAND model (`DLC.Closed`, `DLCD.deliver`,
`DLCD.applyCommand`, `DLCD.worldStep`); they touch no generated code and edit no
model file (they live here, in the transport module). They discharge the
"reduction preserves closedness" fact the memo §5 flags as the sole real obligation. -/

/-- Bounded reduction preserves closedness: iterating `DLC.step` from a CLOSED seed
stays closed (`DLC.step_preserves_closed` per step). -/
theorem reduceWithFuel_preserves_closed :
    ∀ (n : Nat) (M : DLC.Term), DLC.Closed M → DLC.Closed (DLC.reduceWithFuel M n).1 := by
  intro n
  induction n with
  | zero => intro M hcl; simpa only [DLC.reduceWithFuel] using hcl
  | succ m ih =>
      intro M hcl
      simp only [DLC.reduceWithFuel]
      cases hstep : DLC.step M with
      | none => simpa using hcl
      | some M' =>
          have hcl' := DLC.step_preserves_closed hstep hcl
          simpa using ih M' hcl'

/-- `app` of two closed terms is closed. -/
theorem closed_app {a b : DLC.Term} (ha : DLC.Closed a) (hb : DLC.Closed b) :
    DLC.Closed (DLC.Term.app a b) := by
  intro i hi
  simp only [DLC.usesVar, Bool.or_eq_false_iff]
  exact ⟨ha i hi, hb i hi⟩

/-- `DLCD.applyCommand` (bounded reduction of `payload ▸ store`) preserves closedness. -/
theorem applyCommand_preserves_closed (c : DLCD.Command) {s : DLC.Term}
    (hpay : DLC.Closed c.payload) (hs : DLC.Closed s) :
    DLC.Closed (DLCD.applyCommand c s) := by
  unfold DLCD.applyCommand
  exact reduceWithFuel_preserves_closed _ _ (closed_app hpay hs)

/-- `DLCD.deliver` preserves store closedness: the no-op branch keeps the store, the
delivery branch applies a closed-payload command to a closed store. -/
theorem deliver_preserves_closed_store {L : DLCD.CommittedLog} {r : DLCD.Replica}
    (hr : DLC.Closed r.store) (hL : ∀ c ∈ L, DLC.Closed c.payload) :
    DLC.Closed (DLCD.deliver L r).store := by
  unfold DLCD.deliver
  cases hget : L[r.applied]? with
  | none => simpa using hr
  | some c =>
      show DLC.Closed (DLCD.applyCommand c r.store)
      exact applyCommand_preserves_closed c (hL c (List.mem_of_getElem? hget)) hr

/-- `DLCD.worldStep` preserves store closedness across the whole replica list. -/
theorem worldStep_stores_closed {g : DLCD.GlobalConfig}
    (hlogcl : ∀ c ∈ g.log, DLC.Closed c.payload)
    (hc : ∀ r ∈ g.replicas, DLC.Closed r.store) :
    ∀ r ∈ (DLCD.worldStep g).replicas, DLC.Closed r.store := by
  intro r hr
  simp only [DLCD.worldStep] at hr
  rw [List.mem_map] at hr
  obtain ⟨r', hr'mem, rfl⟩ := hr
  exact deliver_preserves_closed_store (hc r' hr'mem) hlogcl

/-! ## 1. Bridging decoded closedness to the runtime `ClosedTm`. -/

/-- A `map`-transport of a `∀ ∈`-predicate: if `xs.map f = zs` and every element of
`zs` satisfies `P`, then `P (f x)` for every `x ∈ xs`. -/
theorem forall_of_map_eq {α β : Type _} {f : α → β} {P : β → Prop}
    {xs : List α} {zs : List β}
    (h : xs.map f = zs) (hz : ∀ z ∈ zs, P z) : ∀ x ∈ xs, P (f x) := by
  intro x hx
  apply hz
  rw [← h]
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

/-- Runtime store-closedness (`ClosedTm`) of `g`'s replicas ⇒ decoded closedness of
the decoded replicas' stores. -/
theorem decoded_stores_closed {g : rsm.GlobalConfig}
    (hs : ∀ rep ∈ g.replicas.val, ClosedTm rep.store) :
    ∀ r ∈ (decGC decTermC decPropC g).replicas, DLC.Closed r.store := by
  intro r hr
  simp only [decGC] at hr
  rw [List.mem_map] at hr
  obtain ⟨r'', hmem, rfl⟩ := hr
  exact hs r'' hmem

/-- Runtime payload-closedness of `g`'s log ⇒ decoded closedness of the decoded log's
payloads. -/
theorem decoded_log_closed {g : rsm.GlobalConfig}
    (hl : ∀ c ∈ g.log.val, ClosedTm c.payload) :
    ∀ c ∈ (decGC decTermC decPropC g).log, DLC.Closed c.payload := by
  intro c hc
  simp only [decGC, decLog] at hc
  rw [List.mem_map] at hc
  obtain ⟨c'', hmem, rfl⟩ := hc
  exact hl c'' hmem

/-! ## 2. ★ IFC-1.a — an `ok` Rust `world_step` preserves closedness.

The iteration's side-condition: the decoded stores of the stepped config stay
closed (so the next `world_step_square` applies), and the log — unchanged by
`worldStep` — stays closed too. Proved by decoding `g'` through `world_step_square`
into `DLCD.worldStep ⟦g⟧` and spending the model's `deliver`/`applyCommand`
closedness preservation. -/
theorem world_step_preserves_closed (g g' : rsm.GlobalConfig)
    (hok : rsm.world_step g = ok g')
    (hs : ∀ rep ∈ g.replicas.val, ClosedTm rep.store)
    (hl : ∀ c ∈ g.log.val, ClosedTm c.payload) :
    (∀ rep ∈ g'.replicas.val, ClosedTm rep.store)
      ∧ (∀ c ∈ g'.log.val, ClosedTm c.payload) := by
  have hsq : decGC decTermC decPropC g' = DLCD.worldStep (decGC decTermC decPropC g) :=
    world_step_square g g' hs hl hok
  -- The decoded stepped replicas are `DLCD.deliver ⟦log⟧` over the decoded replicas.
  have hreps : g'.replicas.val.map (decRep decTermC)
      = (decGC decTermC decPropC g).replicas.map
          (DLCD.deliver (decGC decTermC decPropC g).log) := by
    calc g'.replicas.val.map (decRep decTermC)
        = (decGC decTermC decPropC g').replicas := rfl
      _ = (DLCD.worldStep (decGC decTermC decPropC g)).replicas := by rw [hsq]
      _ = (decGC decTermC decPropC g).replicas.map
            (DLCD.deliver (decGC decTermC decPropC g).log) := rfl
  -- The decoded log is unchanged (`worldStep` only advances `applied`).
  have hlogmap : g'.log.val.map (decCmd decTermC decPropC)
      = (decGC decTermC decPropC g).log := by
    calc g'.log.val.map (decCmd decTermC decPropC)
        = (decGC decTermC decPropC g').log := rfl
      _ = (DLCD.worldStep (decGC decTermC decPropC g)).log := by rw [hsq]
      _ = (decGC decTermC decPropC g).log := rfl
  refine ⟨?_, ?_⟩
  · -- store closedness of the stepped config
    have hz : ∀ z ∈ (decGC decTermC decPropC g).replicas.map
          (DLCD.deliver (decGC decTermC decPropC g).log), DLC.Closed z.store := by
      intro z hzmem
      rw [List.mem_map] at hzmem
      obtain ⟨r, hrmem, rfl⟩ := hzmem
      exact deliver_preserves_closed_store
        (decoded_stores_closed hs r hrmem) (decoded_log_closed hl)
    intro rep hrep
    exact forall_of_map_eq hreps hz rep hrep
  · -- log closedness of the stepped config
    intro c hc
    exact forall_of_map_eq hlogmap (decoded_log_closed hl) c hc

/-! ## 3. IFC-1.b — a multi-step `ok` Rust run decodes to iterated `worldSteps`. -/

/-- `RustRunOk k g gk`: `k` successive `ok` Rust `world_step`s carry `g` to `gk`. -/
inductive RustRunOk : Nat → rsm.GlobalConfig → rsm.GlobalConfig → Prop where
  | zero (g : rsm.GlobalConfig) : RustRunOk 0 g g
  | step {n : Nat} {g g' gk : rsm.GlobalConfig} :
      rsm.world_step g = ok g' → RustRunOk n g' gk → RustRunOk (n + 1) g gk

/-- **IFC-1.b.** A `k`-step Rust run that stays `ok` decodes to `k` model
`worldSteps`. Induction on the run; each step composes `world_step_square`
(value-correctness) with `world_step_preserves_closed` (the side-condition that
keeps the next square applicable). -/
theorem rust_worldSteps_correct :
    ∀ (k : Nat) (g gk : rsm.GlobalConfig), RustRunOk k g gk →
      (∀ rep ∈ g.replicas.val, ClosedTm rep.store) →
      (∀ c ∈ g.log.val, ClosedTm c.payload) →
      decGC decTermC decPropC gk = DLCD.worldSteps k (decGC decTermC decPropC g) := by
  intro k g gk hrun
  induction hrun with
  | zero g => intro _ _; rfl
  | @step n g g' gk hstep _ ih =>
      intro hs hl
      obtain ⟨hs', hl'⟩ := world_step_preserves_closed g g' hstep hs hl
      have hgk := ih hs' hl'
      have hsq : decGC decTermC decPropC g' = DLCD.worldStep (decGC decTermC decPropC g) :=
        world_step_square g g' hs hl hstep
      have hstepeq : DLCD.worldSteps (n + 1) (decGC decTermC decPropC g)
          = DLCD.worldSteps n (DLCD.worldStep (decGC decTermC decPropC g)) := rfl
      rw [hstepeq, hgk, hsq]

/-! ## 4. ★ IFC-1.c — FULL-EXECUTION HIGH-CASE NI at the runtime (the headline). -/

/-- **IFC-1.c — `rust_distributed_noninterference`.** Two `k`-step Rust executions
that each stay `ok`, start `LowEquivG`-related at a HIGH store type `Prop'.at χ ℓhigh`
(`ℓhigh ⋠ ℓLow`) over a shared decoded log, remain `LowEquivG`-related after the whole
run. Rewrites both runs by IFC-1.b, then discharges the model's already-proven
`DLCD.distributed_noninterference`. `χ`/`ℓhigh`/`ℓLow` are EXTERNAL typing parameters
(the R6/IFC-2 hook); the runtime carries no store types. Partial correctness
(conditioned on both runs returning `ok`); the real `LowEquivG` conclusion is
inherited from the model, not restated as `x = x`. -/
theorem rust_distributed_noninterference
    (ℓLow : DLC.Label) (χ : DLC.Prop') {ℓhigh : DLC.Label}
    (hhigh : DLC.Label.le ℓhigh ℓLow = false)
    (k : Nat) (g₁ g₂ g₁ₖ g₂ₖ : rsm.GlobalConfig)
    (hrun₁ : RustRunOk k g₁ g₁ₖ) (hrun₂ : RustRunOk k g₂ g₂ₖ)
    (hs₁ : ∀ rep ∈ g₁.replicas.val, ClosedTm rep.store)
    (hl₁ : ∀ c ∈ g₁.log.val, ClosedTm c.payload)
    (hs₂ : ∀ rep ∈ g₂.replicas.val, ClosedTm rep.store)
    (hl₂ : ∀ c ∈ g₂.log.val, ClosedTm c.payload)
    (hlogeq : (decGC decTermC decPropC g₁).log = (decGC decTermC decPropC g₂).log)
    (hrel : DLCD.LowEquivG ℓLow (DLC.Prop'.at χ ℓhigh)
      (decGC decTermC decPropC g₁) (decGC decTermC decPropC g₂)) :
    DLCD.LowEquivG ℓLow (DLC.Prop'.at χ ℓhigh)
      (decGC decTermC decPropC g₁ₖ) (decGC decTermC decPropC g₂ₖ) := by
  rw [rust_worldSteps_correct k g₁ g₁ₖ hrun₁ hs₁ hl₁,
      rust_worldSteps_correct k g₂ g₂ₖ hrun₂ hs₂ hl₂]
  exact DLCD.distributed_noninterference ℓLow χ hhigh k hlogeq hrel

/-! ## 5. IFC-1.d — FULL-EXECUTION LOW-CASE NI at the runtime.

The low case's per-command `PropDeriv [] payload (φ ⊸ φ)` core-endomorphism obligation
and the store type `φ` are the SAME external typing parameters IFC-2/R6's `#[write]`
obligation will discharge from the source. The model has only a single-step low
preservation (`DLCD.worldStep_preserves_low`); we first iterate it into a full-run
model capstone, then transport that by IFC-1.b. -/

/-- Model capstone (low case): a `k`-step run of a shared typed-core-endomorphism log,
on closed low-equivalent configs, preserves `LowEquivG` at the fixed store type `φ`.
Iterates `DLCD.worldStep_preserves_low`, threading closedness via
`worldStep_stores_closed` and the invariant log (`DLCD.worldStep_log`). -/
theorem worldSteps_preserves_low (ℓLow : DLC.Label) (φ : DLC.Prop') :
    ∀ (k : Nat) {g₁ g₂ : DLCD.GlobalConfig}, g₁.log = g₂.log →
      (∀ (n : Nat) (c : DLCD.Command), g₁.log[n]? = some c →
        Nonempty (DLC.PropDeriv [] c.payload (DLC.Prop'.imp φ φ)) ∧ DLC.CoreTerm c.payload = true) →
      (∀ c ∈ g₁.log, DLC.Closed c.payload) →
      (∀ r ∈ g₁.replicas, DLC.Closed r.store) → (∀ r ∈ g₂.replicas, DLC.Closed r.store) →
      DLCD.LowEquivG ℓLow φ g₁ g₂ →
      DLCD.LowEquivG ℓLow φ (DLCD.worldSteps k g₁) (DLCD.worldSteps k g₂) := by
  intro k
  induction k with
  | zero => intro g₁ g₂ _ _ _ _ _ hrel; exact hrel
  | succ n ih =>
      intro g₁ g₂ hlog htyped hlogcl hc₁ hc₂ hrel
      have hstep := DLCD.worldStep_preserves_low ℓLow φ hlog htyped hc₁ hc₂ hrel
      show DLCD.LowEquivG ℓLow φ
        (DLCD.worldSteps n (DLCD.worldStep g₁)) (DLCD.worldSteps n (DLCD.worldStep g₂))
      refine ih (g₁ := DLCD.worldStep g₁) (g₂ := DLCD.worldStep g₂) ?_ ?_ ?_ ?_ ?_ hstep
      · rw [DLCD.worldStep_log, DLCD.worldStep_log, hlog]
      · rw [DLCD.worldStep_log]; exact htyped
      · rw [DLCD.worldStep_log]; exact hlogcl
      · exact worldStep_stores_closed hlogcl hc₁
      · exact worldStep_stores_closed (by rw [← hlog]; exact hlogcl) hc₂

/-- **IFC-1.d — `rust_distributed_noninterference_low`.** Two `k`-step `ok` Rust runs
of a shared typed-core-endomorphism committed log, closed and `LowEquivG`-related at
store type `φ`, remain `LowEquivG`-related after the whole run. The typed-log
obligation and store type `φ` are EXTERNAL (the R6/IFC-2 hook), on the same footing as
the high case; closedness is decoded from the runtime `ClosedTm` hypotheses. Rewrites
both runs by IFC-1.b, then discharges the model capstone `worldSteps_preserves_low`. -/
theorem rust_distributed_noninterference_low
    (ℓLow : DLC.Label) (φ : DLC.Prop')
    (k : Nat) (g₁ g₂ g₁ₖ g₂ₖ : rsm.GlobalConfig)
    (hrun₁ : RustRunOk k g₁ g₁ₖ) (hrun₂ : RustRunOk k g₂ g₂ₖ)
    (hs₁ : ∀ rep ∈ g₁.replicas.val, ClosedTm rep.store)
    (hl₁ : ∀ c ∈ g₁.log.val, ClosedTm c.payload)
    (hs₂ : ∀ rep ∈ g₂.replicas.val, ClosedTm rep.store)
    (hl₂ : ∀ c ∈ g₂.log.val, ClosedTm c.payload)
    (hlog : (decGC decTermC decPropC g₁).log = (decGC decTermC decPropC g₂).log)
    (htyped : ∀ (n : Nat) (c : DLCD.Command),
        (decGC decTermC decPropC g₁).log[n]? = some c →
        Nonempty (DLC.PropDeriv [] c.payload (DLC.Prop'.imp φ φ)) ∧ DLC.CoreTerm c.payload = true)
    (hrel : DLCD.LowEquivG ℓLow φ
      (decGC decTermC decPropC g₁) (decGC decTermC decPropC g₂)) :
    DLCD.LowEquivG ℓLow φ
      (decGC decTermC decPropC g₁ₖ) (decGC decTermC decPropC g₂ₖ) := by
  rw [rust_worldSteps_correct k g₁ g₁ₖ hrun₁ hs₁ hl₁,
      rust_worldSteps_correct k g₂ g₂ₖ hrun₂ hs₂ hl₂]
  exact worldSteps_preserves_low ℓLow φ k hlog htyped
    (decoded_log_closed hl₁) (decoded_stores_closed hs₁) (decoded_stores_closed hs₂) hrel

end DLCD.Transport
