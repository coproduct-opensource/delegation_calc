# R5 — IFC-refinement re-plan (post-impossibility)

*Investigation + design memo. 2026-07-23. Branch `dlc-d/phase0-carve`.
Author-facing decision memo — nothing here is committed to a real branch; no
model/guarantee file was edited.*

Supersedes the original R5 line ("refine `distributed_noninterference` into a
1-run SMT setting via self-composition assuming a faithful runtime-label
decode"). R2 proved that plan's load-bearing premise **impossible**; this memo
re-plans around what is genuinely achievable and recommends a target.

---

## 1. What is proven now, and what the impossibility rules out (honest baseline)

### 1.1 Proven (the runtime IFC we actually have)

`lean/DLCD/Transport.lean :: rust_worldStep_preserves_high` — a **single-step
NI-preservation corollary** at the runtime surface:

> Given two Aeneas-core `world_step`s that both return `ok`, that share a decoded
> log, and that are `LowEquivG ℓLow (Prop'.at χ ℓhigh)`-related on input (with
> `ℓhigh ⋠ ℓLow`), the decoded outputs stay `LowEquivG`-related.

It routes `world_step_square` (×2, once per run) into the hand metatheorem
`DLCD.worldStep_preserves_high`. Footprint `[propext, Classical.choice,
Quot.sound]`, non-vacuous (the `DistNIWitness` differing-high witness survives
decode).

Underneath it, the **model side is stronger and complete**:
- `DLCD.distributed_noninterference` — full-run preservation: `LowEquivG` at a
  high store type is preserved by *any number* of `worldStep`s (induction on `k`).
- `DLCD.worldStep_preserves_low` — the low case (delivering a shared
  `PropDeriv [] p (φ ⊸ φ)` core-endomorphism command preserves `LowEquivG`),
  via `fundamental`/`lrel_self` composition.
- `DLCD.LabelFlow.log_noninterference` — the semantic/store-projection half:
  the low view is a function of only the low-committed subsequence (Goguen–
  Meseguer purge). Plus right-reason bites (`badDeliver_breaks_lowEquiv`,
  `badApplyL_breaks_noninterference`) and non-vacuity witnesses on both halves.

So the **model** enjoys full distributed NI; the **runtime** currently inherits
only the **single-step high-case preservation** corollary.

### 1.2 What the impossibility rules out (do not re-attempt)

The original R5 assumed a faithful `decLabel : ifc.Label → DLC.Label`. Two
independent obstructions kill it (Transport.lean header ★★★, verified this
session — build on it):

1. **Cardinality.** `DLC.Label = nucleus's CapabilityLattice` is a 13-field
   record over a 3-element enum → **finite (3¹³)**. Runtime `ifc.Label = Vec U32`
   is countably **infinite**. No injection infinite ↪ finite exists. A globally
   faithful decode is *impossible*.
2. **Layer mismatch (the deeper one).** Even a faithful *term-label* decode would
   not help, because the label distributed-NI keys on is the **store-TYPE** label
   `ℓhigh` in `Prop'.at χ ℓhigh`, a `PropDeriv`/typing-layer artifact. The
   executable `GlobalConfig` carries **no store types and no typing derivation**
   (`Replica.store : Term`; `Command.cap : Option Prop'` is opaque and unused in
   Phase 1.0; `reduce/shift/subst` are label-blind, carrying `Vec U32` fields
   through unchanged). The quantity NI distinguishes lives wholly in a layer the
   RSM does not carry.

**Consequence for framing.** "The runtime's own label *bytes* enforce IFC" is
not achievable by decode, and never will be — not because the proof is hard but
because the executable state has no object to attach the classification to. Any
stronger runtime IFC must *supply* the classification as an external/typed
parameter, not *recover* it from `Vec U32`. This is the hinge the whole re-plan
turns on.

---

## 2. Candidate targets

Legend — feasibility is my estimate of effort-to-green given the current tree;
"buys" is the marketing-honest delta over §1.1.

### IFC-1 — Full-execution NI-preservation transport (cheapest real strengthening)

**What.** Generalize `rust_worldStep_preserves_high` from one step to the whole
run: transport `DLCD.distributed_noninterference` (already proven in the model)
to the Aeneas core, i.e. two multi-step Rust executions that stay `ok` and start
`LowEquivG` remain `LowEquivG` after `k` steps. Also lift the low case
(`worldStep_preserves_low`) to the runtime on the same external-typing footing.

**Feasibility: HIGH.** Pure Lean over the existing squares; no new substrate. The
proof is a straight induction on `k` (or on a fuel/step list) that at each step
composes `world_step_square` (×2) exactly as the existing single-step corollary
does — the same shape as the model's `distributed_noninterference` induction. The
one real obligation is *threading the `ok`/closedness hypotheses through the
iteration*: each `world_step` must return `ok` and preserve `ClosedTm` on stores
and log so the next square applies. Closedness-preservation of `world_step`
under `ok` is the lemma to add (a `deliver`/`applyCommand` closedness-preservation
— `applyCommand` is bounded reduction, and reduction preserves closedness, a fact
already latent in the `DLC.Reduce` metatheory). The log is invariant under
`worldStep` (`worldStep_log : (worldStep g).log = g.log = rfl`), so `hlogeq`
survives the iteration for free.

**Cost:** ~1 short module (est. 60–120 lines). Sub-increments in §5.

**Buys:** upgrades the runtime IFC claim from "one step preserves" to "the whole
deployed execution preserves" — the honest, headline-worthy runtime NI statement.
Closes the gap between what the model proves (full run) and what transports (one
step). This is the difference between "a step is safe" and "the running node is
safe," which is the claim a reader actually wants.

**Relation to R6:** IFC-1 is a *precondition* for R6's IFC obligation to mean
anything at the metal: R6 says "flow respects labels for the deployed binary,"
and that binary runs many steps. IFC-1 is the run-level lemma that R6's per-service
`flow = χ ⊑ ℓ` obligation discharges into.

**Fence it does NOT remove:** `χ`, `ℓhigh`, `ℓLow` remain **external typing
parameters**. IFC-1 makes the *preservation* total-in-time; it does not make the
runtime *self-witness* the classification. That is IFC-2's job.

### IFC-2 — Typed-label runtime surface (the R6 unification) ★ the real unlock

**What.** Make labels first-class in the program the developer writes. R6's
`#[dlc_d::service(flow = χ ⊑ ℓ_low)]` (roadmap §2) puts the store's classification
`χ`/`ℓ` **into the service type**. At compile time the macro emits a `PropDeriv`
(store-type) obligation that the store field is typed `Prop'.at χ ℓ` and each
`#[write]`/command payload is a `PropDeriv [] p (φ ⊸ φ)` core endomorphism (or an
authorized declassify). Those are *exactly* the external parameters and
hypotheses that `rust_worldStep_preserves_high` / `worldStep_preserves_low` /
(IFC-1) `distributed_noninterference` already consume.

**Does making labels first-class in R6 RECOVER faithful runtime IFC?** — **Yes,
and it is the *only* thing that can, because it sidesteps the decode entirely.**
The decode-impossibility says "you cannot *read* the classification back out of
`Vec U32` executable bytes." IFC-2 doesn't read it back — it **carries it forward
from the source**: the developer wrote `flow = χ ⊑ ℓ`, the macro compiles that
into (a) a discharged obligation on the source program and (b) a runtime whose
correspondence to the model is the R2 square. The classification `ℓhigh` now has
a real object to attach to — **the type the developer wrote**, checked at build
time, not `Vec U32` at run time. NI becomes a statement about *runtime-typed
programs* (programs that compiled under the `service` obligation), and its
enforcement is: "this program compiled ⟹ its store field carries `Prop'.at χ ℓ`
⟹ (IFC-1) its deployed multi-step execution preserves `LowEquivG` at that type ⟹ a
`ℓ`-observer cannot distinguish it from any low-equivalent run." The `Vec U32`
bytes never enter the argument — they are inert payload the reducer carries
through, orthogonal to the type-layer gate (Transport.lean §7).

**This is the answer.** "Invest in IFC" and "build the failure-modes-as-types
surface (R6)" are **the same move.** The impossibility is not a wall around IFC;
it is a *proof that IFC must be a compile-time-typed property, not a runtime-byte
property* — which is precisely the R6 thesis ("make the failure envelope a type,
make compilation the proof"). IFC-2 = the `flow` axis of R6, and it is what makes
stronger runtime IFC **both achievable and ergonomic**: achievable because it
supplies the parameter the decode cannot; ergonomic because the developer states
`flow = χ ⊑ ℓ` in one line and `cargo build` green is the proof.

**Feasibility: MEDIUM (design HIGH, mechanization is R6-scoped).** The Lean-side
lemmas IFC-2 *consumes* already exist (high case) or are IFC-1 (full run) + the existing
low case. The new work is the **surface→obligation compiler**: the macro/checker
that (a) elaborates `flow = χ ⊑ ℓ` into a concrete `DLC.Prop'` + `Label`, (b)
emits the `PropDeriv` store-type obligation and the per-write endomorphism/authorized-
declassify obligation, (c) routes a failure to a `rustc`-shaped diagnostic. This
is exactly R6.0/R6.2 scope. The proof-theoretic content is *done*; the ergonomics
and the macro are the work.

**Cost:** design memo + macro prototype + obligation-routing (R6.0/R6.2 — a phase,
not a lemma). But the *IFC-specific* increment on top of R6's existing plan is
small: R6 already lists `flow = χ ⊑ ℓ_low` as one of its three compile-time
rejections. IFC-2 is "make that rejection route through the NI theorems (IFC-1) rather
than a bespoke check."

**Buys:** the honest, defensible **"first" claim**: a runtime whose IFC/NI is
enforced by construction at compile time and certified to the deployed binary via
the R2 correspondence — with the label as a source-level type, not a runtime
artifact. It converts the impossibility from an apology into the design principle.

**Relation to R6:** IFC-2 *is* R6's `flow` axis. Recommending IFC-2 = recommending that
R5's remaining IFC investment be spent *inside* R6.0/R6.2, not as a separate phase.

### IFC-3 — Self-composition / product construction

**What.** Prove the 2-run hyperproperty `distributed_noninterference` by
self-composing `worldStep` into a product machine and proving a 1-run safety
property, then (per the original plan) push it to a 1-run SMT setting.

**Feasibility: N/A for the runtime; LOW value.** Two problems. (1) The runtime
**carries no labels**, so any product machine you build is over the *decoded
model*, not the executable — self-composition is **purely model-side**. It buys
nothing at the runtime surface the decode-impossibility didn't already block.
(2) The model already *has* the 2-run relation proved directly (`LRel`/`LowEquivG`
+ `fundamental`); self-composition is a *reformulation*, not a strengthening — it
would trade a working logical-relations proof for a product-program proof of the
same fact. The only genuine payoff of self-composition is **automation** (a 1-run
safety property is SMT/model-checkable), but SMT-automation of a Lean-proven
theorem is negative-value here (we already have the machine-checked proof, and
the SMT setting cannot see the `Vec U32`↔type layer gap any better than Lean can).

**Verdict: drop.** The original R5's self-composition step was in service of the
faithful-decode plan, which is dead. Keep the *idea* only as a possible future
tactic for automating R6's per-service obligation discharge if the `PropDeriv`
obligations ever need push-button checking — but that is an R6 ergonomics tactic,
not an R5 IFC target. Note in §6 as a deferred automation option, not a target.

### IFC-4 — Iris/RefinedRust relational logic (SeLoC/ReLoC-style) over the shell

**What.** Prove NI relationally over the **async Rust shell** (R3's RefinedRust
substrate — the event loop, interior mutability, transport) using an Iris
relational logic (SeLoC / ReLoC carry hyperproperties natively).

**Feasibility: LOW now, HIGH strategic value later.** The pure transition core is
already NI-verified (model + IFC-1 transport); R3 exists specifically for what Aeneas
cannot touch — the concurrent shell (roadmap §3). A relational Iris proof would
cover the part IFC-1/IFC-2 *don't*: that the async scheduling/transport shell doesn't
leak (timing/scheduling channels, message metadata). BUT: (1) RefinedRust is
installed but the shell refinement itself is R3-spike-only (not built); a
relational-logic NI on top of an unbuilt functional refinement is two layers of
unbuilt work. (2) SeLoC/ReLoC target termination-*insensitive* NI over a
heap-manipulating language; adapting to RefinedRust's ownership model + DLC's
label lattice is a research-grade effort. (3) The shell's leaks are largely
*timing/availability* channels, which DLC's confidentiality lattice does not
currently model.

**Cost:** large, research-grade; blocked on R3 shell refinement existing.

**Buys:** the *complete* story (shell included). This is the eventual ceiling, but
it is R3+R6-downstream, not an R5-now move.

**Relation to R6:** complements IFC-2 — IFC-2 covers the typed transition core's flows;
IFC-4 would eventually cover the shell R2 can't reach. Sequence IFC-4 *after* R3 shell
refinement and R6.1 node exist.

### IFC-5 — Declassification / one-shot IFC

**What.** Give runtime IFC *content* to the `declassify` construct + the 13-axis
portcullis lattice: an authorized downgrade `ℓ → ℓ'` witnessed by a
`DeclassifyPolicy`/`DeclassifyProof`, connecting to nucleus's one-shot-
declassification work.

**Feasibility: MEDIUM; genuine but narrow content.** Findings from the tree:
- `Term.declassify : Label → Term → Term → Term` exists (`Syntax.lean`), typed by
  `Deriv.declassify` (`Judgment.lean` — `Γ ⊢ declassify_ℓ'(M,π) : Prop'.at φ ℓ'`),
  and its reduction is **frozen** (`Reduce.lean` §166: "the frozen eliminations
  (verify, attenuate, declassify) are checked by the verifier layers rather
  than" the reducer). So declassify is enforcement-at-the-type/verifier-layer by
  design — exactly the IFC-2 shape. Its DLC↔nucleus `DeclassifyProof` bridge lives in
  `DLC.IFCLabel`.
- The NI theorems' right-reason bites (`DistNIBite.badApply`,
  `LabelFlowBite.badApplyL`) already prove that *unauthorized* declassify (a
  label-strip with no policy) **breaks** `LowEquivG`/`log_noninterference`. So the
  calculus already distinguishes authorized from unauthorized downgrade; the open
  content is proving that the *authorized* `declassify` (with a valid policy
  witness) preserves a **weakened**, declassification-aware NI (the standard
  "delimited/relaxed noninterference" statement: low view is a function of the low
  log *plus the sanctioned declassifications*).
- The **live one-shot gap** (memory: `hc6-declassification-linearity-gap`,
  `nucleus-one-shot-declassification-design`) is that nucleus's declass token is
  time-bounded and replayable while Lean proves it one-shot. That is a *nucleus*
  soundness gap, not a DLC-D R5 target — but IFC-5's DLC-side declassify story is the
  place a fix would land conceptually.

**Cost:** MEDIUM — a delimited-NI theorem (`declassify` preserves NI-modulo-
sanctioned-flows) is a real but self-contained Lean increment; the nucleus
one-shot fix is separate and out of R5 scope.

**Buys:** IFC *with* a controlled escape hatch — necessary for any real service
(pure NI forbids all downgrade, which no ledger/KV app can live with). Makes the
`flow` axis *usable*, not just enforceable.

**Relation to R6:** IFC-5 is the *second* half of R6's `flow` axis: IFC-2 enforces
`χ ⊑ ℓ`; IFC-5 supplies the sanctioned-downgrade rule a real service needs. R6's
demo (a KV ledger) will almost certainly need one declassify (e.g. publish a
balance-changed event), so IFC-5 becomes concretely necessary at R6.3.

---

## 3. ★ Recommendation

**Recommended target: IFC-1 now → IFC-2 as the frame (with IFC-5 pulled in at R6.3).
Drop IFC-3. Defer IFC-4 behind R3.**

Concretely, an ordered combination:

1. **IFC-1 immediately** — the cheapest real strengthening, pure Lean over existing
   squares, upgrades the runtime claim from single-step to full-execution
   preservation. Do this regardless of the R6 decision; it stands alone and it is
   the run-level lemma everything else cites.
2. **Re-frame R5's remaining IFC investment as IFC-2 = R6's `flow` axis.** Do *not*
   run R5 as a separate phase. The impossibility is a *proof that IFC must be a
   compile-time-typed property* — which is the R6 thesis. Spend the "invest more
   in IFC" energy on R6.0's `flow = χ ⊑ ℓ` obligation, routing it through the IFC-1
   NI theorems.
3. **Pull IFC-5 (delimited/authorized declassify NI) in at R6.3** when the demo needs
   a sanctioned downgrade — not before.
4. **Drop IFC-3** (model-side only; reformulation not strengthening). Keep
   self-composition only as a possible future obligation-automation tactic.
5. **Defer IFC-4** until R3's shell refinement and an R6.1 node exist; it is the
   eventual ceiling (shell-inclusive NI), not an R5-now move.

**Confidence: HIGH** on the framing (IFC-2 = R6's `flow` axis is the unlock;
IFC-1 is the free win; IFC-3 is dead); **MEDIUM-HIGH** on IFC-1's mechanization landing in
one short module (the one risk is the closedness-preservation-under-`ok`-iteration
lemma, which is routine but unwritten).

**Is IFC-2 the unification of "invest in IFC" and "build failure-modes-as-types"?
— YES, decisively.** They are the same move. The decode-impossibility does not
block IFC; it *dictates its form*: the label must be a source-level type checked
at compile time, which is exactly what R6's `#[dlc_d::service(flow = …)]` provides.

**The single decisive consideration:** the executable runtime state carries **no
object to attach a classification to** (no store types; `Vec U32` is inert
payload). Therefore stronger runtime IFC *cannot* be recovered from the runtime —
it can only be **supplied from the source as a type** and **carried to the metal
by the R2 correspondence**. That is IFC-2, and IFC-2 is R6. Everything else (IFC-1) is
plumbing that makes the supplied guarantee total-in-time; everything ruled out
(IFC-3, faithful decode) tried to recover from the runtime what is not there.

---

## 4. Why not "just accept preservation"?

The roadmap's parked question was "stronger runtime IFC vs. accept preservation +
typed-label surface (R6)." This memo's answer: **those are not alternatives.** The
typed-label surface (IFC-2/R6) *is* the stronger runtime IFC — it is what makes
preservation a statement about *the program the developer wrote and compiled*,
rather than an external-parameter lemma about a decoded model. Accepting
preservation *and* building the R6 surface is the strongest honest position; IFC-1
makes the preservation full-run so the surface's guarantee reaches the whole
deployed execution.

---

## 5. Staging sketch for the recommended target (IFC-1, with the IFC-2 hooks)

Each sub-increment states a checkable Lean statement. IFC-1 lives in a new module
(proposed `lean/DLCD/TransportNI.lean`) importing `DLCD.Transport`; it edits **no**
hand-guarantee or model file.

**IFC-1.a — closedness is preserved by an `ok` world step.** The iteration's
side-condition lemma.
```lean
theorem world_step_preserves_closed (g g' : rsm.GlobalConfig)
    (hok : rsm.world_step g = ok g')
    (hs : ∀ rep ∈ g.replicas.val, ClosedTm rep.store)
    (hl : ∀ c ∈ g.log.val, ClosedTm c.payload) :
    (∀ rep ∈ g'.replicas.val, ClosedTm rep.store)
      ∧ (∀ c ∈ g'.log.val, ClosedTm c.payload)
```
(Core fact: `apply_command` is bounded reduction and reduction preserves
`ClosedTm`; the log is unchanged by `world_step`.)

**IFC-1.b — a multi-step Rust run stays decode-square-aligned.** Iterated
`world_step` returning `ok` at each step decodes to iterated model `worldSteps`.
```lean
theorem rust_worldSteps_correct : ∀ (k : Nat) (g gk : rsm.GlobalConfig),
    RustRunOk g gk k →           -- k successful world_steps from g to gk
    (closedness on g) →
    decGC decTermC decPropC gk = DLCD.worldSteps k (decGC decTermC decPropC g)
```
(Induction on `k`, composing `rust_world_step_correct` + IFC-1.a at each step.)

**IFC-1.c — full-execution high-case NI preservation at the runtime (the headline).**
```lean
theorem rust_distributed_noninterference
    (ℓLow : DLC.Label) (χ : DLC.Prop') {ℓhigh : DLC.Label}
    (hhigh : DLC.Label.le ℓhigh ℓLow = false)
    (k : Nat) (g₁ g₂ g₁ₖ g₂ₖ : rsm.GlobalConfig)
    (hrun₁ : RustRunOk g₁ g₁ₖ k) (hrun₂ : RustRunOk g₂ g₂ₖ k)
    (closedness on g₁, g₂)
    (hlogeq : (decGC … g₁).log = (decGC … g₂).log)
    (hrel : DLCD.LowEquivG ℓLow (DLC.Prop'.at χ ℓhigh)
              (decGC … g₁) (decGC … g₂)) :
    DLCD.LowEquivG ℓLow (DLC.Prop'.at χ ℓhigh)
      (decGC … g₁ₖ) (decGC … g₂ₖ)
```
(Rewrite both runs by IFC-1.b, then apply the *model's* already-proven
`DLCD.distributed_noninterference`.)

**IFC-1.d — full-execution low-case at the runtime.** Same shape, transporting
`worldStep_preserves_low` under the typed-log hypothesis (the per-command
`PropDeriv [] p (φ ⊸ φ)` core-endomorphism obligation). This is the statement
whose hypothesis IFC-2/R6's `#[write]` obligation will *discharge from the source*.

**IFC-2 hook (R6.0, not R5 Lean).** Design the `flow = χ ⊑ ℓ` → `(DLC.Prop', Label)`
elaboration and the obligation `PropDeriv [] store_field (Prop'.at χ ℓ)` +
per-write `PropDeriv [] payload (φ ⊸ φ)`, routed to a `rustc`-shaped diagnostic.
The theorem these obligations feed is IFC-1.c/IFC-1.d. **Checkable acceptance test:** a
well-typed service compiles and its node satisfies IFC-1.c; each of the three
violation variants (un-typed store field / non-endomorphism write / label-leaking
flow) fails a *named* obligation with a source-located error.

**IFC-5 hook (R6.3).** Add `Deriv.declassify`'s delimited-NI lemma: an authorized
`declassify_ℓ'(M, π)` with valid policy `π` preserves NI-modulo-sanctioned-flows
(low view = function of low log + sanctioned downgrades). The bite theorems
(`DistNIBite`, `LabelFlowBite`) already fix the *un*authorized case as the
negative witness.

---

## 6. Deferred automation note (salvage from IFC-3)

Self-composition/product-construction has **no** runtime-IFC value (model-side
only; the runtime carries no labels). Retain it *only* as a candidate tactic for
**push-button discharge of R6's per-service `PropDeriv` obligations** if manual
proof terms become an ergonomics bottleneck at R6.2 — i.e. encode the endomorphism
obligation as a 1-run safety property an SMT backend can check. This is an R6
ergonomics option, not an R5 IFC target.

---

## 7. Fresh-2026 web searches a later pass should run

*(WebSearch budget was exhausted this session — 200/200 — so these are deferred.
Run before mechanizing IFC-2 and before scoping IFC-4.)*

1. `delimited release noninterference Lean 4 2025 2026` — prior art for the IFC-5
   authorized-declassify statement in a proof assistant.
2. `information flow control type system Rust macro compile-time 2025 2026` —
   IFC-2 surface prior art (how others compile a source-level flow annotation to a
   discharged obligation; error ergonomics).
3. `RefinedRust relational separation logic noninterference 2025 2026` — is there
   a SeLoC/ReLoC-style relational layer *on RefinedRust* yet (IFC-4 feasibility)?
4. `SeLoC ReLoC noninterference mechanization Iris 2024 2025 2026` — current state
   of Iris relational NI logics (IFC-4 substrate maturity).
5. `state machine replication information flow noninterference verified 2025 2026`
   — updates to the seL4-IFC / FLAQR line for the full-run transport framing (IFC-1).
6. `label as type dependent classification runtime enforcement 2025 2026` — is the
   "supply the label from the source type" pattern (IFC-2's core) named/standard
   anywhere, to cite or contrast.
7. `self-composition hyperproperty SMT product program 2025 2026` — only to
   confirm the §6 automation option's current tooling before investing.

---

## 8. Verified references (from in-tree headers; not re-searched this session)

- Aeneas — Ho–Protzenko–Fromherz, ICFP 2022. https://arxiv.org/abs/2206.07185
- Grove — Sharma et al., SOSP 2023.
  https://iris-project.org/pdfs/2023-sosp-grove.pdf
- seL4 IFC — Murray et al. (machine-checked NI over a deterministic state machine;
  the closest verified RSM-NI prior art).
  https://sel4.systems/Research/pdfs/sel4-from-general-purpose-to-proof-information-flow-enforcement.pdf
- FLAQR — Mondal–Algehed–Arden, CSF 2022 (confidentiality under consensus/
  replication). https://arxiv.org/abs/2205.04384 ; journal version
  https://journals.sagepub.com/doi/abs/10.3233/JCS-230048
- Frumin–Krebbers–Birkedal, *Mechanized Logical Relations for TINI*, POPL 2021
  (the Iris relational-NI idiom IFC-4 would build on).
  https://dl.acm.org/doi/10.1145/3434291
- Sabelfeld–Myers, *Language-Based Information-Flow Security*, IEEE JSAC 2003.
  https://www.cse.chalmers.se/~andrei/jsac.pdf
- FLAM/FLAC — Arden et al. https://arxiv.org/pdf/1412.3136
- Decentralized Label Model — Myers–Liskov, TOSEM 2000.
  https://dl.acm.org/doi/10.1145/363516.363526
