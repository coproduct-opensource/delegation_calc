import DLCD.Rsm
import DLC.NonInterferenceFundamental
import DLC.NonInterferenceLR
import DLC.NonInterferenceEnv
import DLC.Progress
import DLC.IFCLabel

/-! # DLC-D Phase 2.d — DISTRIBUTED NONINTERFERENCE (`LRelᴳ` over `GlobalConfig` pairs)

This module supplies the **type-system half** of DLC-D's distributed
confidentiality guarantee, complementary to `DLCD.LabelFlow` (Phase 2.b), which
supplied the *semantic / store-projection* half (`view`, `log_noninterference`).
Here we lift DLC's SEQUENTIAL two-run logical relation `DLC.LRel` — and its
fundamental lemma `DLC.fundamental` / corollary `DLC.t3_two_run_general` — from
single closed terms to **pairs of replicated global configurations**, and prove
that the world's transition function (`worldStep` / `deliver`) **preserves**
global low-equivalence: a low observer cannot distinguish two replicated
executions that started low-equivalent.

## The statement, in one line
`LowEquivG ℓLow φ g₁ g₂` relates two `GlobalConfig`s when their replica lists
have the same shape (pairwise-equal ids and `applied` indices) and pairwise
`LRel ℓLow φ`-related stores. `worldStep_preserves_high` /
`worldStep_preserves_low` show `worldStep` maps `LowEquivG` to `LowEquivG`; the
capstone `distributed_noninterference` iterates this over a full run.

## Prior art (web-searched 2026-07-22; URLs recorded)
- **FLAQR** — Mondal–Algehed–Arden, *Applying consensus and replication securely
  with FLAQR* (CSF 2022): a core calculus for distributed apps with quorum
  replication whose noninterference theorems characterize confidentiality /
  integrity / availability in the presence of consensus, replication, and
  failures. THE closest prior art; this module is the LR / type-system shadow of
  FLAQR's replicated-store confidentiality, over DLC's own calculus.
  https://arxiv.org/abs/2205.04384 , https://arxiv.org/pdf/2205.04384
- **Sabelfeld–Myers**, *Language-Based Information-Flow Security* (IEEE JSAC
  2003): the canonical survey of the logical-relations / two-run method for
  noninterference we lift here. https://www.cse.chalmers.se/~andrei/jsac.pdf
- **seL4 IFC** — Murray et al., machine-checked information-flow enforcement over
  a deterministic state machine — the closest *verified* RSM-NI prior art; our
  `worldStep` is the deterministic state machine, `view`/`LRelᴳ` the observation.
  https://sel4.systems/Research/pdfs/sel4-from-general-purpose-to-proof-information-flow-enforcement.pdf
- **Frumin–Krebbers–Birkedal**, *Mechanized Logical Relations for
  Termination-Insensitive Noninterference* (POPL 2021): logical-relations NI
  over higher-order state via Iris — the mechanization idiom we follow (a PER of
  related runs, closed under reduction). https://dl.acm.org/doi/10.1145/3434291
- **Goguen–Meseguer noninterference** (1982): the purge/observation framing that
  Phase 2.b's semantic half instantiates; this half is its type-carried dual.
  https://en.wikipedia.org/wiki/Non-interference_(security)

## Honest fences (what this IS and IS NOT)
- **This LIFTS DLC's proven sequential NI; it re-proves nothing.** The load is
  carried by `DLC.LRel` (the two-run relation), `DLC.fundamental` /
  `DLC.lrel_self` / `DLC.t3_two_run_general` over the `PropDeriv` computational
  core, and `DLC.lrel_expand` (anti-reduction). The plan's gating of Phase 2.d
  behind a `CDeriv`-swap was over-conservative: `PropDeriv`'s two-run relation
  already carries everything the store-level lift needs. No `CDeriv` swap here.
- **The high-command case is the essence and is proved in FULL.** At a HIGH store
  type `.at χ ℓhigh` with `ℓhigh ⋠ ℓLow`, `DLC.LRel` is `True` by the *observability
  gate* (`DLC.NonInterferenceLR`, the `.at` clause's `if_neg` branch). So
  `LowEquivG` at a high store type is preserved by `worldStep` for ANY commands
  on any matching-shape configs — high-typed store contents are
  low-indistinguishable by construction. `worldStep_preserves_high` is exactly
  this, and it genuinely fires the gate (`worldStep_preserves_high` reduces the
  store obligation through the `if_neg`, not over an empty replica list — see the
  differing-high `DistNIWitness`).
- **The low-command case is proved via `fundamental`-composition** at the
  per-command load-bearing step (`applyCommand_preserves_LRel`) and lifted to
  `worldStep` (`worldStep_preserves_low`). It requires the delivered command's
  payload to be a *core* `PropDeriv` endomorphism of the store type
  (`PropDeriv [] p (φ ⊸ φ)`, `CoreTerm p`) and the stores closed — the honest
  hypotheses under which `applyCommand` (which is `DLC.reduceWithFuel` of
  `payload ▸ store`) provably respects `LRel`. `applyCommand` being *exactly*
  bounded reduction of a well-typed payload is what makes `lrel_self` (reflexivity
  from `fundamental`) + the arrow clause + forward reduction-closure close it.
- **What `applyCommand` actually is** (`DLCD.Rsm`): `applyCommand c s =
  (reduceWithFuel (Term.app c.payload s) applyFuel).1` — deterministic bounded
  β-normalization of `payload` applied to the store. So a command IS a function
  applied to the register; the low case is genuine `LRel`-arrow composition, not
  a bespoke transition.
- **Residual / deferred.** (1) The low case assumes a *typed log invariant*
  (every committed command's payload is a `φ ⊸ φ` core term) rather than deriving
  it from consensus — consensus is `DLCD.Rsm`'s Phase-1.0 oracle, so command
  well-typing is likewise assumed here, not proved. (2) Store-type *change* across
  a command (a command mapping type φ to a distinct ψ) is not modeled; `LowEquivG`
  is at a fixed store type — the natural setting for "a command preserves the
  store's classification." (3) The full `worldStep`-closure over the *live* log
  with fault scheduling (the `FailureBudget` contract) is Phase-1.0-oracular; we
  close a single `worldStep` and iterate it purely.

## What is proved (the deliverables)
1. `LowEquivG` — global low-equivalence over `GlobalConfig` pairs.
2. `worldStep_preserves_high` — FULL: a `worldStep` on matching-shape configs at a
   HIGH store type preserves `LowEquivG`, firing the observability gate.
3. `applyCommand_preserves_LRel` + `worldStep_preserves_low` — a `worldStep`
   delivering the SAME low (typed-core-endomorphism) command to closed,
   low-equivalent configs preserves `LowEquivG`, via `lrel_self` + arrow + forward
   reduction-closure of `LRel`.
4. `distributed_noninterference` — the capstone: iterating `worldStep` from a
   `LowEquivG` start at a high store type keeps configs `LowEquivG`, so a low
   observer cannot distinguish the two executions.
5. `DistNIBite.badDeliver_breaks_lowEquiv` — a `badApply` that DECLASSIFIES WITHOUT
   AUTHORITY (strips a high store's label down to `⊥`) provably FALSIFIES
   `LowEquivG`-preservation: two high-low-equal configs become low-distinguishable.
   The gate / typed-endomorphism discipline is load-bearing.
6. `DistNIWitness.*` — a concrete 2-replica two-run whose HIGH store inputs GENUINELY
   DIFFER yet stay `LowEquivG` (and `worldStep`-preserved), plus
   `DistNIWitness.via_fundamental` reusing `DLC.t3_two_run_general` directly.
-/

namespace DLCD

open DLC

/-! ## 0. Forward reduction-closure of `LRel`.

`DLC.NonInterferenceLR` proves ANTI-reduction (head expansion, `lrel_expand`).
The low case needs the MIRROR: `LRel` is closed under FORWARD reduction, because
`applyCommand` hands us the relation on the *un-reduced* `payload ▸ store` and the
store is the *reduct*. Forward closure follows from determinism
(`steps_semiconfluent`) exactly as anti-reduction follows from congruence; it is
proved here (not in the sequential file) since it is this phase's need. -/

/-- A single forward step from a value-shaped path: if `M` steps to `M'` and also
reduces to a value `V`, then `M'` reduces to that same `V` (determinism). -/
theorem steps_forward_value {M M' V : Term} (hstep : step M = some M')
    (hV : Value V) (hMV : Steps M V) : Steps M' V := by
  rcases steps_semiconfluent (Steps.single hstep) hMV with h | h
  · exact h
  · rw [value_steps_eq hV h]; exact .refl _

/-- Forward closure of `Joinable` on the left. -/
theorem joinable_forward_left {M M' N : Term} (hstep : step M = some M')
    (h : Joinable M N) : Joinable M' N := by
  obtain ⟨V, hMV, hNV⟩ := h
  rcases steps_semiconfluent (Steps.single hstep) hMV with hf | hf
  · exact ⟨V, hf, hNV⟩
  · exact ⟨M', .refl M', hNV.trans hf⟩

/-- **Forward reduction-closure of `LRel` on the LEFT.** The mirror of
`lrel_expand_left`: if `M` steps to `M'`, then `M'` inherits `M`'s relation.
Induction on the proposition; the value-style cases push the reduct forward via
determinism, the projective `and` and the arrows lift through `fst`/`snd`/`app`
congruence. -/
theorem lrel_step_left (ℓLow : Label) :
    ∀ (φ : Prop') {M M' N : Term}, step M = some M' →
      LRel ℓLow φ M N → LRel ℓLow φ M' N := by
  intro φ
  induction φ with
  | top => intro M M' N _ _; trivial
  | bot => intro M M' N _ _; trivial
  | atom n => intro M M' N h hr; exact joinable_forward_left h hr
  | speaksFor p q => intro M M' N h hr; exact joinable_forward_left h hr
  | «at» φ ℓ ih =>
      intro M M' N h hr
      simp only [LRel] at hr ⊢
      split at hr <;> rename_i hle
      · rw [if_pos hle]
        obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
        exact ⟨m₁, m₂, steps_forward_value h (by simp [Value]) hM, hN, hp⟩
      · rw [if_neg hle]; trivial
  | «says» p φ ih =>
      intro M M' N h hr
      obtain ⟨m₁, σ₁, m₂, σ₂, hM, hN, hp⟩ := hr
      exact ⟨m₁, σ₁, m₂, σ₂, steps_forward_value h (by simp [Value]) hM, hN, hp⟩
  | within τ φ ih =>
      intro M M' N h hr
      obtain ⟨m₁, m₂, hM, hN, hp⟩ := hr
      exact ⟨m₁, m₂, steps_forward_value h (by simp [Value]) hM, hN, hp⟩
  | boxed O φ ih => intro M M' N _ _; trivial
  | and φ ψ ihφ ihψ =>
      intro M M' N h hr
      exact ⟨ihφ (step_fst_congr h) hr.1, ihψ (step_snd_congr h) hr.2⟩
  | or φ ψ ihφ ihψ =>
      intro M M' N h hr
      rcases hr with ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩ | ⟨χ₁, χ₂, a₁, a₂, hM, hN, hp⟩
      · exact .inl ⟨χ₁, χ₂, a₁, a₂, steps_forward_value h (by simp [Value]) hM, hN, hp⟩
      · exact .inr ⟨χ₁, χ₂, a₁, a₂, steps_forward_value h (by simp [Value]) hM, hN, hp⟩
  | tensor φ ψ ihφ ihψ =>
      intro M M' N h hr
      obtain ⟨a₁, b₁, a₂, b₂, hM, hN, hp, hq⟩ := hr
      exact ⟨a₁, b₁, a₂, b₂, steps_forward_value h (by simp [Value]) hM, hN, hp, hq⟩
  | imp φ ψ ihφ ihψ =>
      intro M M' N h hr X Y hX hY hXY
      exact ihψ (step_app_congr h) (hr X Y hX hY hXY)
  | lolli φ ψ ihφ ihψ =>
      intro M M' N h hr X Y hX hY hXY
      exact ihψ (step_app_congr h) (hr X Y hX hY hXY)
  | replicated φ ih =>
      -- intro-form def (§5.2): forward-step the left `command`-reduction path.
      intro M M' N h hr
      obtain ⟨M₁, c₁, ℓ₁, M₂, c₂, ℓ₂, hM, hN, hp⟩ := hr
      exact ⟨M₁, c₁, ℓ₁, M₂, c₂, ℓ₂, steps_forward_value h (by simp [Value]) hM, hN, hp⟩

/-- Forward closure on the RIGHT, by symmetry. -/
theorem lrel_step_right (ℓLow : Label) (φ : Prop') {M N N' : Term}
    (h : step N = some N') (hr : LRel ℓLow φ M N) : LRel ℓLow φ M N' :=
  lrel_symm ℓLow φ (lrel_step_left ℓLow φ h (lrel_symm ℓLow φ hr))

/-- Multi-step forward closure on the left. -/
theorem lrel_steps_left (ℓLow : Label) (φ : Prop') {M M' N : Term}
    (hM : Steps M M') (hr : LRel ℓLow φ M N) : LRel ℓLow φ M' N := by
  induction hM with
  | refl _ => exact hr
  | head h _ ih => exact ih (lrel_step_left ℓLow φ h hr)

/-- Multi-step forward closure on the right. -/
theorem lrel_steps_right (ℓLow : Label) (φ : Prop') {M N N' : Term}
    (hN : Steps N N') (hr : LRel ℓLow φ M N) : LRel ℓLow φ M N' := by
  induction hN with
  | refl _ => exact hr
  | head h _ ih => exact ih (lrel_step_right ℓLow φ h hr)

/-- Forward reduction-closure on both sides — the low case's workhorse. -/
theorem lrel_reduce (ℓLow : Label) (φ : Prop') {M M' N N' : Term}
    (hM : Steps M M') (hN : Steps N N') (hr : LRel ℓLow φ M N) :
    LRel ℓLow φ M' N' :=
  lrel_steps_right ℓLow φ hN (lrel_steps_left ℓLow φ hM hr)

/-! ## 1. `applyCommand` is bounded reduction — the `Steps` witness. -/

/-- `reduceWithFuel` produces a `Steps`-reduct of its input: the whole point of
`applyCommand` being a fold of `step`. -/
theorem reduceWithFuel_steps (t : Term) (fuel : Nat) :
    Steps t (reduceWithFuel t fuel).1 := by
  induction fuel generalizing t with
  | zero => exact .refl _
  | succ n ih =>
      cases hstep : step t with
      | none => simp only [reduceWithFuel, hstep]; exact .refl _
      | some t' =>
          have hfst : (reduceWithFuel t (n + 1)).1 = (reduceWithFuel t' n).1 := by
            simp only [reduceWithFuel, hstep]
          rw [hfst]
          exact .head hstep (ih t')

/-- **`applyCommand` genuinely reduces `payload ▸ store`.** `Steps` from the
un-reduced application to the delivered store — the bridge that lets the forward
closure of `LRel` connect `lrel_self`'s arrow output to the concrete new store. -/
theorem applyCommand_steps (c : Command) (s : Term) :
    Steps (Term.app c.payload s) (applyCommand c s) :=
  reduceWithFuel_steps _ _

/-! ## 2. Global low-equivalence. -/

/-- Per-replica relatedness: same identity, same log position, and stores related
by DLC's two-run relation `LRel` at store type `φ` and observer clearance `ℓLow`. -/
def ReplicaRel (ℓLow : Label) (φ : Prop') (r₁ r₂ : Replica) : Prop :=
  r₁.id = r₂.id ∧ r₁.applied = r₂.applied ∧ LRel ℓLow φ r₁.store r₂.store

/-- **Global low-equivalence** over `GlobalConfig` pairs: the replica lists are
pairwise `ReplicaRel`-related (`List.Forall₂`), i.e. same shape and low-related
stores. This is `LRelᴳ` — the type-system lift of `LRel` to whole configs. Two
configs are `LowEquivG` exactly when a `ℓLow`-observer, reading every replica's
store through `LRel`, cannot tell them apart. -/
def LowEquivG (ℓLow : Label) (φ : Prop') (g₁ g₂ : GlobalConfig) : Prop :=
  List.Forall₂ (ReplicaRel ℓLow φ) g₁.replicas g₂.replicas

/-! ## 3. `deliver` shape lemmas. -/

/-- `deliver` never changes a replica's identity. -/
theorem deliver_id (L : CommittedLog) (r : Replica) : (deliver L r).id = r.id := by
  unfold deliver; split <;> rfl

/-- `deliver` advances two same-position replicas in lockstep. -/
theorem deliver_applied_eq (L : CommittedLog) {r₁ r₂ : Replica}
    (happ : r₁.applied = r₂.applied) :
    (deliver L r₁).applied = (deliver L r₂).applied := by
  unfold deliver
  rw [happ]
  cases L[r₂.applied]? with
  | none => exact happ
  | some c => rfl

/-! ## 4. THE HIGH-COMMAND CASE — the observability gate (proved in FULL).

At a HIGH store type `.at χ ℓhigh` with `ℓhigh ⋠ ℓLow`, `LRel` is `True` by the
gate, so *any* two matching-shape configs are `LowEquivG` and `worldStep`
preserves it — high store contents are low-indistinguishable by construction. -/

/-- **The observability gate.** At a store type classified HIGH for the observer
(`ℓhigh ⋠ ℓLow`), any two stores are `LRel`-related — this is the `if_neg` branch
of `DLC.LRel`'s `.at` clause. THE mechanism of distributed NI. -/
theorem lrel_at_high (ℓLow : Label) (χ : Prop') {ℓhigh : Label}
    (hhigh : Label.le ℓhigh ℓLow = false) (M N : Term) :
    LRel ℓLow (Prop'.at χ ℓhigh) M N := by
  simp only [LRel]
  rw [if_neg (by simp [hhigh])]
  trivial

/-- Per-replica high preservation: `deliver` keeps two same-shape replicas
same-shape, and the store obligation dissolves through the gate. -/
theorem deliver_preserves_high (ℓLow : Label) (χ : Prop') {ℓhigh : Label}
    (hhigh : Label.le ℓhigh ℓLow = false) (L : CommittedLog) {r₁ r₂ : Replica}
    (hid : r₁.id = r₂.id) (happ : r₁.applied = r₂.applied) :
    ReplicaRel ℓLow (Prop'.at χ ℓhigh) (deliver L r₁) (deliver L r₂) := by
  refine ⟨?_, deliver_applied_eq L happ, lrel_at_high ℓLow χ hhigh _ _⟩
  rw [deliver_id, deliver_id, hid]

/-- Lifting the per-replica gate over the whole replica list. -/
theorem forall2_deliver_high (ℓLow : Label) (χ : Prop') {ℓhigh : Label}
    (hhigh : Label.le ℓhigh ℓLow = false) (L : CommittedLog) :
    ∀ {rs₁ rs₂ : List Replica},
      List.Forall₂ (ReplicaRel ℓLow (Prop'.at χ ℓhigh)) rs₁ rs₂ →
      List.Forall₂ (ReplicaRel ℓLow (Prop'.at χ ℓhigh))
        (rs₁.map (deliver L)) (rs₂.map (deliver L)) := by
  intro rs₁ rs₂ h
  induction h with
  | nil => exact .nil
  | cons hhead _ ih =>
      exact .cons (deliver_preserves_high ℓLow χ hhigh L hhead.1 hhead.2.1) ih

/-- **HIGH-COMMAND PRESERVATION (FULL).** A `worldStep` on two configs sharing a
committed log, related at a HIGH store type, stays related — regardless of what
commands are delivered. This is distributed NI's core: a high-typed store cannot
leak into a low observer's view, so the world may evolve it arbitrarily. -/
theorem worldStep_preserves_high (ℓLow : Label) (χ : Prop') {ℓhigh : Label}
    (hhigh : Label.le ℓhigh ℓLow = false) {g₁ g₂ : GlobalConfig}
    (hlog : g₁.log = g₂.log)
    (hrel : LowEquivG ℓLow (Prop'.at χ ℓhigh) g₁ g₂) :
    LowEquivG ℓLow (Prop'.at χ ℓhigh) (worldStep g₁) (worldStep g₂) := by
  unfold LowEquivG
  simp only [worldStep]
  rw [hlog]
  exact forall2_deliver_high ℓLow χ hhigh g₂.log hrel

/-! ## 5. THE LOW-COMMAND CASE — `fundamental`-composition.

Delivering the SAME command, whose payload is a *core* `PropDeriv` endomorphism
of the store type, to two closed low-equivalent configs preserves `LowEquivG`:
`lrel_self` (reflexivity from `fundamental`) gives the arrow relation on the
payload, the arrow clause maps the related stores, and forward reduction-closure
lands on the delivered stores. -/

/-- **THE LOAD-BEARING LOW STEP.** If a command's payload is a closed core
`PropDeriv` endomorphism `φ ⊸ φ`, then applying it to two closed `LRel`-related
stores yields `LRel`-related stores. Proof: `lrel_self` from DLC's `fundamental`
gives `LRel (φ ⊸ φ) p p`; the arrow clause applied to the related stores gives
`LRel φ (p ▸ s₁) (p ▸ s₂)`; `applyCommand` reduces `p ▸ sᵢ` to the delivered
store, and `lrel_reduce` (forward closure) carries the relation to the reducts. -/
theorem applyCommand_preserves_LRel (ℓLow : Label) (φ : Prop') (c : Command)
    (dp : PropDeriv [] c.payload (Prop'.imp φ φ)) (hcore : CoreTerm c.payload = true)
    {s₁ s₂ : Term} (hs₁ : Closed s₁) (hs₂ : Closed s₂)
    (hrel : LRel ℓLow φ s₁ s₂) :
    LRel ℓLow φ (applyCommand c s₁) (applyCommand c s₂) := by
  have harr : LRel ℓLow (Prop'.imp φ φ) c.payload c.payload := lrel_self ℓLow dp hcore
  simp only [LRel] at harr
  have hstep := harr s₁ s₂ hs₁ hs₂ hrel
  exact lrel_reduce ℓLow φ (applyCommand_steps c s₁) (applyCommand_steps c s₂) hstep

/-- Per-replica low preservation: `deliver` of a typed-core-endomorphism log to
two closed, same-shape, low-related replicas preserves relatedness. -/
theorem deliver_preserves_low (ℓLow : Label) (φ : Prop') {L : CommittedLog}
    (htyped : ∀ (n : Nat) (c : Command), L[n]? = some c →
      Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true)
    {r₁ r₂ : Replica}
    (hc₁ : Closed r₁.store) (hc₂ : Closed r₂.store)
    (hrel : ReplicaRel ℓLow φ r₁ r₂) :
    ReplicaRel ℓLow φ (deliver L r₁) (deliver L r₂) := by
  obtain ⟨hid, happ, hstore⟩ := hrel
  refine ⟨by rw [deliver_id, deliver_id, hid], deliver_applied_eq L happ, ?_⟩
  unfold deliver
  rw [happ]
  cases hget : L[r₂.applied]? with
  | none => simpa using hstore
  | some c =>
      simp only
      obtain ⟨⟨hdp⟩, hhcore⟩ := htyped r₂.applied c hget
      exact applyCommand_preserves_LRel ℓLow φ c hdp hhcore hc₁ hc₂ hstore

/-- Lifting per-replica low preservation over the whole replica list. -/
theorem forall2_deliver_low (ℓLow : Label) (φ : Prop') {L : CommittedLog}
    (htyped : ∀ (n : Nat) (c : Command), L[n]? = some c →
      Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true) :
    ∀ {rs₁ rs₂ : List Replica},
      List.Forall₂ (ReplicaRel ℓLow φ) rs₁ rs₂ →
      (∀ r ∈ rs₁, Closed r.store) → (∀ r ∈ rs₂, Closed r.store) →
      List.Forall₂ (ReplicaRel ℓLow φ) (rs₁.map (deliver L)) (rs₂.map (deliver L)) := by
  intro rs₁ rs₂ h
  induction h with
  | nil => intro _ _; exact .nil
  | @cons a b l₁ l₂ hhead _ ih =>
      intro hc₁ hc₂
      refine .cons (deliver_preserves_low ℓLow φ htyped
        (hc₁ a List.mem_cons_self) (hc₂ b List.mem_cons_self) hhead) ?_
      exact ih (fun r hr => hc₁ r (List.mem_cons_of_mem _ hr))
        (fun r hr => hc₂ r (List.mem_cons_of_mem _ hr))

/-- **LOW-COMMAND PRESERVATION.** A `worldStep` delivering a shared, typed-core-
endomorphism committed log to two closed, low-equivalent configs preserves
`LowEquivG`, by `fundamental`-composition at each replica. -/
theorem worldStep_preserves_low (ℓLow : Label) (φ : Prop') {g₁ g₂ : GlobalConfig}
    (hlog : g₁.log = g₂.log)
    (htyped : ∀ (n : Nat) (c : Command), g₁.log[n]? = some c →
      Nonempty (PropDeriv [] c.payload (Prop'.imp φ φ)) ∧ CoreTerm c.payload = true)
    (hc₁ : ∀ r ∈ g₁.replicas, Closed r.store)
    (hc₂ : ∀ r ∈ g₂.replicas, Closed r.store)
    (hrel : LowEquivG ℓLow φ g₁ g₂) :
    LowEquivG ℓLow φ (worldStep g₁) (worldStep g₂) := by
  unfold LowEquivG
  simp only [worldStep]
  rw [hlog]
  exact forall2_deliver_low ℓLow φ (by rw [← hlog]; exact htyped) hrel hc₁ hc₂

/-! ## 6. THE CAPSTONE — distributed noninterference over a full run. -/

/-- Iterate `worldStep` `k` times. -/
def worldSteps (k : Nat) (g : GlobalConfig) : GlobalConfig :=
  match k with
  | 0 => g
  | n + 1 => worldSteps n (worldStep g)

/-- `worldStep` preserves the log (delivery only advances `applied`). -/
theorem worldStep_log (g : GlobalConfig) : (worldStep g).log = g.log := rfl

/-- **DISTRIBUTED NONINTERFERENCE (type-system half).** Two replicated executions
that start `LowEquivG` at a HIGH store type, over a shared committed log, remain
`LowEquivG` after ANY number of `worldStep`s — so a `ℓLow`-observer can never
distinguish them, no matter how the world schedules delivery. This is the
distributed analogue of `DLC.t3_two_run_general`, carried by the calculus's own
`LRel` up to whole global configurations. -/
theorem distributed_noninterference (ℓLow : Label) (χ : Prop') {ℓhigh : Label}
    (hhigh : Label.le ℓhigh ℓLow = false) :
    ∀ (k : Nat) {g₁ g₂ : GlobalConfig}, g₁.log = g₂.log →
      LowEquivG ℓLow (Prop'.at χ ℓhigh) g₁ g₂ →
      LowEquivG ℓLow (Prop'.at χ ℓhigh) (worldSteps k g₁) (worldSteps k g₂) := by
  intro k
  induction k with
  | zero => intro g₁ g₂ _ hrel; exact hrel
  | succ n ih =>
      intro g₁ g₂ hlog hrel
      exact ih (by rw [worldStep_log, worldStep_log, hlog])
        (worldStep_preserves_high ℓLow χ hhigh hlog hrel)

/-! ## 7. THE RIGHT-REASON BITE — declassify-without-authority breaks preservation.

`badApply` strips a HIGH store's label down to `⊥` — a downgrade with no authority
(the type-level twin of Phase 2.b's `badApplyL` write-down). It is NOT a well-typed
`φ ⊸ φ` core endomorphism (it *changes the classification*), so it is outside the
low-preservation hypothesis; and it demonstrably breaks `LowEquivG`: two configs
that are low-equivalent at a HIGH type (their differing high stores hidden by the
gate) become low-DISTINGUISHABLE at the resulting low type. The gate / typed-
endomorphism discipline is load-bearing, not decorative. -/

namespace DistNIBite

/-- A genuinely HIGH label to the `⊥`-observer (reused shape from `LabelFlow`). -/
def hi : Label := { Label.bottom with read_files := .Always }

/-- `hi` does not flow to `⊥`. -/
theorem hi_not_low : Label.le hi Label.bottom = false := by decide

/-- `⊥` flows to `⊥`. -/
theorem bot_low : Label.le Label.bottom Label.bottom = true := by decide

/-- The high store type (hidden by the gate to a `⊥`-observer). -/
def φhi : Prop' := Prop'.at (Prop'.atom 0) hi

/-- The low store type the leak lands on (observable to `⊥`). -/
def φlo : Prop' := Prop'.at (Prop'.atom 0) Label.bottom

/-- `var`s are normal forms: any reduction path from a `var` is stationary. -/
theorem steps_var {i : Nat} {W : Term} (h : Steps (Term.var i) W) : W = Term.var i := by
  cases h with
  | refl => rfl
  | head hstep _ => cases hstep

/-- Two distinct `var`s share no common reduct. -/
theorem var01_not_joinable : ¬ Joinable (Term.var 0) (Term.var 1) := by
  rintro ⟨W, h0, h1⟩
  have e0 : W = Term.var 0 := steps_var h0
  have e1 : W = Term.var 1 := steps_var h1
  rw [e0] at e1
  injection e1 with hn
  exact absurd hn (by decide)

/-- **The leak — a metalevel declassify-without-authority.** Strips a
`liftLabel _ inner` down to `liftLabel ⊥ inner`, exposing the high payload at the
lowest label. This is the `badApplyL` write-down at the type level: it is not
realizable as a well-typed `φhi ⊸ φhi` core endomorphism. -/
def badApply : Term → Term
  | Term.liftLabel _ inner => Term.liftLabel Label.bottom inner
  | t => t

/-- **THE TERM-LEVEL BITE.** After the leak, the two (originally gate-hidden,
differing) high stores are NOT `LRel`-related at the LOW type: they reduce to
`liftLabel ⊥ (var 0)` and `liftLabel ⊥ (var 1)`, whose payloads `var 0`, `var 1`
are not `Joinable`. So the gate that made them equal is gone. -/
theorem leak_breaks_lrel :
    ¬ LRel Label.bottom φlo (badApply (Term.liftLabel hi (Term.var 0)))
        (badApply (Term.liftLabel hi (Term.var 1))) := by
  intro h
  simp only [badApply, φlo, LRel] at h
  rw [if_pos bot_low] at h
  obtain ⟨m₁, m₂, hM, hN, hp⟩ := h
  have e1 : Term.liftLabel Label.bottom m₁ = Term.liftLabel Label.bottom (Term.var 0) :=
    value_steps_eq (by simp [Value]) hM
  have e2 : Term.liftLabel Label.bottom m₂ = Term.liftLabel Label.bottom (Term.var 1) :=
    value_steps_eq (by simp [Value]) hN
  simp only [Term.liftLabel.injEq, true_and] at e1 e2
  rw [e1, e2] at hp
  exact var01_not_joinable hp

/-- Two single-replica configs whose high stores GENUINELY DIFFER. -/
def g₁ : GlobalConfig :=
  { replicas := [⟨0, Term.liftLabel hi (Term.var 0), 0⟩], log := [], budget := FailureBudget.zero 1 }

def g₂ : GlobalConfig :=
  { replicas := [⟨0, Term.liftLabel hi (Term.var 1), 0⟩], log := [], budget := FailureBudget.zero 1 }

/-- Before the leak the two configs ARE low-equivalent at the high type — the gate
hides the differing stores. -/
theorem before_lowEquiv : LowEquivG Label.bottom φhi g₁ g₂ := by
  refine List.Forall₂.cons ?_ List.Forall₂.nil
  exact ⟨rfl, rfl, lrel_at_high Label.bottom (Prop'.atom 0) hi_not_low _ _⟩

/-- The leaky delivery applied to a config: relabel every replica's store to `⊥`. -/
def leakConfig (g : GlobalConfig) : GlobalConfig :=
  { g with replicas := g.replicas.map (fun r => { r with store := badApply r.store }) }

/-- **THE BITE.** After the leaky (authority-free declassify) delivery, the two
configs are NO LONGER low-equivalent at the low type: the high difference the gate
hid is now exposed to the `⊥`-observer. `LowEquivG`-preservation FAILS — so the
gate / typed-endomorphism discipline that makes `worldStep_preserves_*` hold is
load-bearing. -/
theorem badDeliver_breaks_lowEquiv :
    ¬ LowEquivG Label.bottom φlo (leakConfig g₁) (leakConfig g₂) := by
  intro h
  simp only [LowEquivG, leakConfig, g₁, g₂, List.map_cons, List.map_nil] at h
  cases h with
  | cons hhead _ => exact leak_breaks_lrel hhead.2.2

end DistNIBite

/-! ## 8. ANTI-VACUITY WITNESS — differing HIGH inputs, maintained low-equivalence.

A concrete 2-replica two-run whose HIGH store contents GENUINELY DIFFER, yet the
configs are `LowEquivG` and `worldStep` PRESERVES it. Non-vacuous: the high slot
really varies (`≠`), the low observer provably cannot tell (`LowEquivG` holds and
is preserved). `via_fundamental` additionally reuses `DLC.t3_two_run_general`
directly to exhibit the store-level `LRel` a differing high hypothesis induces. -/

namespace DistNIWitness

/-- A genuinely HIGH label to the `⊥`-observer. -/
def hi : Label := { Label.bottom with read_files := .Always }

theorem hi_not_low : Label.le hi Label.bottom = false := by decide

/-- The high store type. -/
def φhi : Prop' := Prop'.at (Prop'.atom 0) hi

/-- Two closed, genuinely-different high store payloads (distinct type
annotations ⇒ distinct terms). -/
def a₁ : Term := Term.lam (Prop'.atom 0) (Term.var 0)
def a₂ : Term := Term.lam (Prop'.atom 1) (Term.var 0)

/-- Run 1: two replicas each holding the high store `liftLabel hi a₁`. -/
def g₁ : GlobalConfig :=
  { replicas := [⟨0, Term.liftLabel hi a₁, 0⟩, ⟨1, Term.liftLabel hi a₁, 0⟩],
    log := [RsmAntiVacuity.dup], budget := FailureBudget.zero 1 }

/-- Run 2: the same shape, but the high stores hold the DIFFERENT `liftLabel hi a₂`. -/
def g₂ : GlobalConfig :=
  { replicas := [⟨0, Term.liftLabel hi a₂, 0⟩, ⟨1, Term.liftLabel hi a₂, 0⟩],
    log := [RsmAntiVacuity.dup], budget := FailureBudget.zero 1 }

/-- `a₁` and `a₂` are distinct terms (their store-payload annotations differ). -/
theorem a_differ : a₁ ≠ a₂ := by
  intro h; unfold a₁ a₂ at h
  injection h with hφ _
  injection hφ with hn
  exact absurd hn (by decide)

/-- **HIGH GENUINELY DIFFERS.** The replica-0 stores of the two runs are distinct
terms — the high input really varies. -/
theorem high_differs : g₁.replicas[0].store ≠ g₂.replicas[0].store := by
  show Term.liftLabel hi a₁ ≠ Term.liftLabel hi a₂
  intro h; injection h with _ hinner; exact a_differ hinner

/-- The two runs share a committed log (same protocol). -/
theorem same_log : g₁.log = g₂.log := rfl

/-- **LOW OBSERVER CANNOT TELL.** Despite the differing high stores, the two runs
are `LowEquivG` at the high store type — every store obligation dissolves through
the observability gate. -/
theorem lowEquiv : LowEquivG Label.bottom φhi g₁ g₂ := by
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · exact ⟨rfl, rfl, lrel_at_high Label.bottom (Prop'.atom 0) hi_not_low _ _⟩
  · exact ⟨rfl, rfl, lrel_at_high Label.bottom (Prop'.atom 0) hi_not_low _ _⟩

/-- **PRESERVED ACROSS THE WORLD STEP.** `worldStep` (which here delivers the
`dup` command, advancing both runs' `applied 0 → 1` and rewriting the stores)
keeps the two runs `LowEquivG` — distributed NI in action on a genuinely-active
world step with differing high inputs. -/
theorem lowEquiv_preserved :
    LowEquivG Label.bottom φhi (worldStep g₁) (worldStep g₂) :=
  worldStep_preserves_high Label.bottom (Prop'.atom 0) hi_not_low same_log lowEquiv

/-- ...and across an arbitrary number of world steps (the capstone, instantiated). -/
theorem lowEquiv_preserved_forever (k : Nat) :
    LowEquivG Label.bottom φhi (worldSteps k g₁) (worldSteps k g₂) :=
  distributed_noninterference Label.bottom (Prop'.atom 0) hi_not_low k same_log lowEquiv

/-! ### Reusing `DLC.t3_two_run_general` directly.

The store-level `LRel` a differing HIGH hypothesis induces on an observable-typed
core computation — the sequential seed the whole config-level lift rests on. Here
`Mwit` is a closed observable-`⊥`-typed core term in a context whose head
hypothesis is HIGH; `t3_two_run_general` relates its two instantiations under
arbitrary differing closed high inputs `N₁ ≠ N₂`. -/

/-- A closed, `⊥`-observable core computation living under a HIGH hypothesis. -/
def Mwit : Term := Term.liftLabel Label.bottom (Term.lam (Prop'.atom 0) (Term.var 0))

/-- Its observable (low) result type. -/
def φwit : Prop' := Prop'.at (Prop'.imp (Prop'.atom 0) (Prop'.atom 0)) Label.bottom

/-- `Mwit` is well-typed under a HIGH head hypothesis. -/
def dWit : PropDeriv [Prop'.at (Prop'.atom 0) hi] Mwit φwit :=
  .liftLabel _ _ _ _ (.impI _ _ _ _ (.varA _ 0 _ rfl))

/-- Two genuinely different closed HIGH inputs. -/
def N₁ : Term := Term.lam (Prop'.atom 0) (Term.var 0)
def N₂ : Term := Term.lam (Prop'.atom 1) (Term.var 0)

theorem N₁_closed : Closed N₁ := by
  unfold Closed N₁
  exact closedAbove_lam_iff.mpr (closedAbove_var_iff.mpr (by omega))

theorem N₂_closed : Closed N₂ := by
  unfold Closed N₂
  exact closedAbove_lam_iff.mpr (closedAbove_var_iff.mpr (by omega))

theorem N_differ : N₁ ≠ N₂ := by
  intro h; unfold N₁ N₂ at h
  injection h with hφ _
  injection hφ with hn
  exact absurd hn (by decide)

/-- **REUSING `t3_two_run_general`.** An observable-typed core computation cannot
distinguish two differing closed instantiations of its HIGH hypothesis: the two
store values it produces are `LRel`-related at the low type though the high inputs
`N₁ ≠ N₂` differ. This IS the sequential seed the config-level `LowEquivG` lifts. -/
theorem via_fundamental :
    LRel Label.bottom φwit (msubst Mwit [N₁]) (msubst Mwit [N₂]) :=
  t3_two_run_general Label.bottom dWit (by decide) hi_not_low
    N₁_closed N₂_closed EnvRel.nil

end DistNIWitness

end DLCD
