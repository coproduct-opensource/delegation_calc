# DLC-D Phase R2 — Increment R2.2: decode `⟦·⟧` + the cheap structural squares (design)

Status: **DESIGN ONLY.** No `.rs`/`.lean` edits, no lakefile/script edits, no
snapshot changes, no commit. This document specifies R2.2 of the DLC-D
verified-runtime program per the parent design `spec/r2-dlc-d-rsm-design.md`
(§3 option 2c, §4, §6 R2.2/R2.3, §7).

Branch `dlc-d/phase0-carve`, HEAD `f32a93b`.

**One-line scope.** R2.2 adds the one-directional decode `⟦·⟧` (generated →
hand) and the *cheap* structural refinement squares
(`deliver`, `world_step`, `apply_prefix`, `is_quorum`, `decided`, `commit`),
**assuming** the reducer/`apply_command` correspondence as an *explicit stated
`Prop`-valued hypothesis* (`AppCommandRefines`) — never an `axiom`, never a
`sorry`. R2.2 does **not** prove that hypothesis (that is R2.3, the deferred
crux). The honest R2.2 claim is: *the operational structural squares hold
**conditional on** the reducer correspondence; the whole operational transport
is thereby reduced to exactly one stated lemma.*

> **BLOCKING FINDING — SUPERSEDED by Arch-1 (see §R2.2a UPDATE below).** In the
> *pre-Arch-1* tree, `dlc_core.reduce.reduce_with_fuel` was translated as an
> **`axiom`** in the *standalone DlcDRsm* tree (`dlc-d-rsm` had `reduce` as a
> dependency crate, so Charon exposed only optimized MIR → opaque stub). The
> "anti-vacuity witness cannot compute" fork below was a direct consequence.
> Arch-1 (commit `4bf9ff1`) relocated the RSM transition core + reducer into
> `dlc-core` as ONE primary Aeneas tree, so `reduce_with_fuel`, `apply_command`,
> `world_step`, `deliver` are now **real `def`s in the DlcCore tree** and
> `apply_command` computes. OPEN QUESTION 1 is therefore **resolved for the
> correspondence target** (which is now DlcCore, not DlcDRsm). A *different*
> blocker now gates actually evaluating the witness — see §R2.2a UPDATE.

---

## §R2.2a UPDATE (2026-07-23, post-Arch-1, HEAD `4bf9ff1`)

This increment (R2.2a) is the "make the DlcCore Aeneas tree compile by filling
its external-function holes, with a soundness-conscious per-external ruling"
step that precedes writing the decode `⟦·⟧` and the squares (still R2.2b). Four
things change relative to the body of this document, which was written pre-Arch-1
against the standalone DlcDRsm tree:

1. **Correspondence target is the DlcCore tree, not DlcDRsm.** The decode and
   squares now relate the **`lean/DLC/Aeneas/DlcCore`** tree (real defs:
   `reduce.reduce_with_fuel`, `reduce.step`, `rsm.apply_command`,
   `rsm.apply_prefix`, `rsm.deliver`, `rsm.world_step`, `rsm.commit`) to the
   hand model. The DlcDRsm tree is now only the consensus layer
   (`consensus.is_quorum`, `consensus.decided`) over `dlc_core.rsm.Command`.

2. **Decode `⟦·⟧` directions (unchanged shape, retargeted names).**
   - `⟦·⟧_Tm : DlcCore.syntax.Term → DLC.Term` (hand model in `lean/DLC/Syntax.lean`).
   - `⟦·⟧_Pr : DlcCore.syntax.Prop → DLC.Prop'` likewise.
   - `⟦·⟧_rsm : DlcCore.rsm.{Command,Replica,GlobalConfig,FailureBudget} → DLCD.*`
     (the RSM state decodes into the DLCD hand model). Container decodes
     (`Vec`, `Option`) compose as before (§2.2).

3. **`AppCommandRefines` (restated, now a computing target).** The single
   deferred obligation is unchanged in spirit but is now stated against the
   real `rsm.apply_command`:
   `∀ (c : DlcCore.rsm.Command) (s : DlcCore.syntax.Term),`
   `  (rsm.apply_command c s).map ⟦·⟧_Tm = ok (DLCD.applyCommand ⟦c⟧ ⟦s⟧)`.
   Because `apply_command` is now a real `def` that unfolds to
   `reduce_with_fuel (App c.payload s) APPLY_FUEL`, this is a statement about a
   *computing* function, not an opaque axiom. It remains an explicit
   `Prop`-valued **hypothesis** (never an `axiom`, never `sorry`); R2.2b proves
   the cheap squares conditional on it, R2.3 discharges it.

4. **Anti-vacuity witness is now CLOSABLE (in principle).** `apply_command`
   computes, so `⟦rsm.apply_command dup init⟧` reduces to a concrete hand-model
   term and the satisfiability witness for `AppCommandRefines` at a closed input
   can be closed by `decide`/`native_decide`/`rfl` once the tree elaborates.
   The pre-Arch-1 "stuck on an opaque axiom" obstruction is gone.

**NEW blocker discovered in R2.2a (must clear before the witness can be
evaluated).** Filling the external holes is *necessary but not sufficient* to
compile the DlcCore tree. The committed, drift-clean generated
`lean/DLC/Aeneas/DlcCore/Funs.lean` does **not** elaborate under Lean 4.31:
Aeneas (`ad905f5`) emits the **recursive `Debug`/`Hash` trait instances**
(`syntax.Term.Insts.CoreFmtDebug`, `syntax.Prop.…`, `principal.Principal.…`,
`obligation.Obligation.…`; `principal.Principal.Insts.CoreHashHash`) with a
**forward reference** — the `…Insts.CoreFmtDebug.fmt` function body mentions the
`…Insts.CoreFmtDebug` *instance* that is defined ~200 lines later, with **no
`mutual` block** — so Lean reports `Unknown constant …Insts.CoreFmtDebug`
(63 sites). Two more sites are **namespace/field shadowing**: struct fields
named `obligation` / `principal` shadow the same-named modules, so
`obligation.Seal` / `obligation.Discharged` / `principal.…` resolve as
(nonexistent) field projections (`Types.lean:232`, `Funs.lean:3124`, +2). Total
**73 elaboration errors, none in `FunsExternal.lean` and none related to the
external holes.** These are pre-existing generated-code defects that were latent
because the `DLCAeneas` lib had only ever been *drift-gated, never compiled*.

Clearing them (a **pre-req to R2.2b**, out of R2.2a's "fill the holes" scope) is
a source-level fix + regenerate: either (a) drop `#[derive(Debug, Hash)]` from
the recursive `dlc-core` types (Debug/Hash are formatting-only, off every
correspondence compute path — see the ruling table) so Aeneas stops emitting the
recursive instances, and rename the `Discharged.obligation` field (and any
`principal`-named field) to un-shadow the module; or (b) an Aeneas emission fix
that wraps recursive `Debug`/`Hash` instances in `mutual` / self-references the
`fmt` function. Both require regenerating the tree (and re-running the drift
gate). This is escalated, not silently worked around.

> The DlcDRsm tree, by contrast, emits **no** `Debug`/`Hash` instances (only the
> consensus functions + the `Command` `PartialEq`), so with its filled
> `FunsExternal.lean` (structural `BEq`-derived `Command::eq`, on the `decided`
> compute path) the **`DLCDRsmAeneas` lib COMPILES** and
> `dlc_core.rsm.Command.Insts.CoreCmpPartialEqCommand.eq` has a clean axiom
> footprint `[propext, Classical.choice, Quot.sound]`.

---

## §0. Prior art (web-searched 2026-07-23; URLs recorded)

The R2.2 pattern — *prove a hand-written Lean model equals the Aeneas-generated
Lean function via a per-function decode square, stating the not-yet-proven
reducer step as an explicit hypothesis rather than an axiom* — sits in the
Aeneas "refine the extracted function against a spec" tradition, with the
distributed-systems refinement-square framing from Perennial/Grove/IronFleet.

- **Aeneas: Rust verification by functional translation** (Ho–Protzenko–Fromherz,
  ICFP 2022) — the method: Charon→LLBC→Aeneas emits each Rust function as a Lean
  `Result α` (`ok`/`fail`/`div`) function; you *write a spec and prove the
  extracted function matches it*. R2.2's squares are exactly this "prove the
  extracted function matches the (hand) spec" step, one-directional (decode).
  - https://arxiv.org/abs/2206.07185
  - https://dl.acm.org/doi/abs/10.1145/3547647
  - https://lean-lang.org/use-cases/aeneas/  (the `Result α` = ok/fail/div framing the `.map decode = ok …` square folds no-fail into)
  - https://www.sonho.fr/assets/documents/aeneas.html
- **From Rust Source Code to Mathematical Proof** (RuntimeVerification) and the
  **Rust-to-Lean pipeline experience report** — "write a formal spec of what the
  extracted function should do and prove the extracted function matches it";
  arithmetic wrapped in monads exposing overflow/panic as explicit failure
  (the `U32` `WellScoped` fence in §3, §4.4).
  - https://runtimeverification.com/blog/from-rust-source-code-to-mathematical-proof
  - https://arxiv.org/pdf/2605.30106
  - https://github.com/e6qu/rust-lean-aeneas  (list/fold refinement over Aeneas output, tutorial-level)
- **Grove: a Separation-Logic Library for Verifying Distributed Systems**
  (Sharma et al., SOSP 2023; Perennial/Iris) — the "verified implementation
  refines an abstract state-machine spec" bar for replicated systems; the
  refinement *square* (decode the impl state, invoke the abstract guarantee,
  re-encode). Also the sober ~12× proof:code anchor for §7's honest cost.
  - https://iris-project.org/pdfs/2023-sosp-grove.pdf
  - https://arxiv.org/pdf/2309.03046
  - https://github.com/mit-pdos/grove
- **Trillium / Igloo** (intensional refinement; linking compositional refinement
  and separation logic for distributed systems) — the general shape of a
  refinement relation between an operational impl and an abstract model that
  the structural squares instantiate for `world_step`.
  - https://arxiv.org/pdf/2109.07863
  - https://arxiv.org/pdf/2010.04749
- **Stating an unproven lemma as an explicit hypothesis without vacuity.** The
  kernel does *not* check hypotheses are satisfiable (`False → anything`), so a
  conditional theorem `AppCommandRefines → square` can be vacuously true; the
  discipline is to exhibit a closed **satisfiability witness** for the
  hypothesis (this program's per-theorem "satisfiable + refutable witness"
  anti-vacuity pattern). Confirmed as a live formalization-defect class in the
  benchmarking literature (vacuous/unsatisfiable hypotheses making statements
  trivially provable).
  - https://arxiv.org/pdf/2606.29493  (vacuous-hypothesis / formalization-defect class)
  - https://leanprover.github.io/theorem_proving_in_lean/propositions_and_proofs.html  (implication vs asserting the antecedent)

Takeaway carried into the design: the value is the *machine-checked square*
plus a *closed satisfiability witness that the hypothesis is inhabitable on a
state-changing input* — the latter is what makes `AppCommandRefines → square`
non-vacuous rather than free.

### §0.1 In-tree reconnaissance (decisive)

Verified against the working tree at `f32a93b`:

1. **No `dlc_core.syntax.Term ↔ DLC.Term` decode exists in-tree.** Outside the
   generated trees, only `lean/DLC/Syntax.lean` and `lean/DLC/Subst.lean`
   mention `dlc_core` — both in *prose comments* describing the future
   `function_correspondence_subst`, neither an actual decode/lemma. So the
   Term/Prop-payload decode is genuinely unbuilt; per ruling 2 it must be
   treated **abstractly** in R2.2 (§2.3).
2. **`lean_lib «Correspondence»` is already taken** (root `DLC.Correspondence`
   = the T2 crypto correspondence). The new lib must therefore be named
   distinctly — `«DLCDCorrespondence»` per ruling 1 — no collision.
3. **The generated `Term`/`Prop` live under the `dlc_d_rsm` namespace.** The
   `dlc_d_rsm.llbc` *inlines* `dlc-core`, so the payload type the decode must
   consume is `dlc_d_rsm.dlc_core.syntax.Term` (the inlined copy), **not** the
   standalone-tree `dlc_core.syntax.Term` from `DLC.Aeneas.DlcCore`. These are
   two *distinct* Lean inductives. The decode's source type is the inlined one.
4. **`reduce_with_fuel` is an `axiom` in the DlcDRsm tree.** In the standalone
   `DLC.Aeneas.DlcCore` tree, `reduce.reduce_with_fuel` is a **full `def`**
   (`Funs.lean:5318`, with `reduce_with_fuel_loop` / `.body`). In the DlcDRsm
   tree it is an **`axiom`** in `FunsExternal_Template.lean:76`, and the
   re-export `DLCD/Aeneas/DlcDRsm.lean` imports that template. So the committed
   tree's `transition.apply_command` bottoms out on an *opaque axiom with no
   reduction rule*. This is the blocking finding → OPEN QUESTION 1, §5, §7.

---

## §1. Lib layout + exact lakefile / lean.yml edits

### 1.1 New file and lib (ruling 1, confirmed)

- **New file** `lean/DLCD/Correspondence.lean`, module `DLCD.Correspondence`,
  importing **both** the hand model and the generated tree:
  ```lean
  import DLCD.Rsm                 -- the SPEC side (hand model)
  import DLCD.Aeneas.DlcDRsm      -- the CODE side (generated, inlined dlc_core)
  ```
  The decode `⟦·⟧` lives in this same file for R2.2 (split into
  `lean/DLCD/Aeneas/Decode.lean` later at R2.4, as the parent doc allows).

- **New `lean_lib` in `lean/lakefile.lean`** (append after the `DLCD` lib,
  before or after `«Correspondence»`; name must differ from the existing
  `«Correspondence»`):
  ```lean
  -- DLC-D Phase R2.2: the decode ⟦·⟧ and the conditional structural refinement
  -- squares relating the Aeneas-generated dlc-d-rsm functions to DLCD.Rsm,
  -- assuming the reducer correspondence (AppCommandRefines) as a stated
  -- hypothesis (R2.3 discharges it). Imports DLCD (hand model) + the generated
  -- DLCD.Aeneas.DlcDRsm tree, so building this lib COMPILES that tree in the
  -- main build (previously drift-gated only).
  lean_lib «DLCDCorrespondence» where
    roots := #[`DLCD.Correspondence]
  ```
  **srcDir/root incantation — confirmed matches the `DLCD` lib pattern.** The
  package root is `lean/`; default `srcDir = "."`. Module `DLCD.Correspondence`
  resolves to `lean/DLCD/Correspondence.lean` under the default srcDir — exactly
  as the `«DLCD»` lib's `DLCD.Rsm → lean/DLCD/Rsm.lean`. **No custom `srcDir`
  is needed** (unlike `«DLCDRsmAeneas»`, whose `srcDir := "DLCD/Aeneas"` exists
  only to relocate the generated tree's `DlcDRsm.*`-rooted modules; this
  hand-written file uses its full `DLCD.`-prefixed module name and needs no
  relocation).

### 1.2 CI wiring (`.github/workflows/lean.yml`)

- **Add `DLCDCorrespondence` to the `LIBS` list** in the "lake build
  per-theorem libraries" step (so it is compiled + `sorry`-gated + audited by
  `check-axioms.sh` alongside the rest):
  ```
  LIBS="Decidability CtxWellFormed Correspondence NonInterference \
        ObligationSoundness ProtocolCorrespondence Progress Witness \
        CoproductAlgebra GradedBridge GradedDistributiveLaw GradedBridgeGeneric \
        CarveProto DerivClosed CarveCtx CarveJudgment DLCD DLCDCorrespondence"
  ```
- **Leave `DLCDRsmAeneas` in `EXCLUDED`** (unchanged). It does not need its own
  `LIBS` entry: building `DLCDCorrespondence` (which imports
  `DLCD.Aeneas.DlcDRsm`) **transitively compiles the generated tree** as a
  dependency. The `EXCLUDED` list only asserts "not *directly* wired into the
  per-lib loop"; the CI gate (every declared lib is in `LIBS ∪ EXCLUDED`) stays
  satisfied.

**Confirmed consequence (ruling 1).** Adding `DLCDCorrespondence` to `LIBS`
means the main build now *compiles the DlcDRsm generated tree*, which today is
only drift-gated (`DLCDRsmAeneas` is `EXCLUDED` and built by nobody in the
per-lib loop). This **closes a latent gap** — a generated tree that compiles
under `check-drift` in isolation but was never type-checked inside the main
Lean image. Two caveats, both benign for CI but load-bearing for §5/§6:
- The tree carries **`axiom` declarations** (the `core.fmt.*` external stubs,
  the `Clone`/`PartialEq` externals, and — critically — `reduce_with_fuel`).
  Compiling them is fine and does **not** trip `check-axioms.sh`, which audits
  only the *tracked theorems* listed in `lean/expected-axioms/`, not every
  axiom in the dependency graph.
- But **any** square theorem or witness whose `#print axioms` is taken will
  surface those axioms in its footprint (deliver → apply_command →
  `reduce_with_fuel`). This is why §6 recommends **not** pinning any R2.2 axiom
  snapshot until OPEN QUESTION 1 is resolved.

---

## §2. The decode `⟦·⟧` — signatures (per type) and the Term-payload seam

Direction: **one-directional, generated → hand** (option 2c). Decode only; no
encode, no round-trip laws.

### 2.1 The abstract payload seam (ruling 2 — the precise seam)

Per §0.1(1) there is **no** `dlc_core.syntax.Term → DLC.Term` decode in-tree,
and building one is the deferred `dlc-core` correspondence (R2.3+). So R2.2
treats the Term/Prop decode **abstractly**: the container decodes are
*parametric* over two seam functions, carried alongside `AppCommandRefines`.

```lean
variable (decTm : dlc_d_rsm.dlc_core.syntax.Term → DLC.Term)   -- ABSTRACT seam
variable (decPr : dlc_d_rsm.dlc_core.syntax.Prop → DLC.Prop')  -- ABSTRACT seam
```

Rationale: the structural squares (`deliver`, `world_step`, `apply_prefix`,
`commit`) **never inspect `Term` structure** — they only *carry* payloads
opaquely through `List`/`Vec` plumbing and hand each payload to the
`apply_command` square. Hence they hold for *any* `decTm`/`decPr`, provided the
`apply_command` hypothesis is stated over the *same* `decTm`/`decPr`. This is
the "carry it in the hypothesis" seam ruling 2 asks for, made precise: the seam
is two free functions the whole R2.2 development is parametric over, pinned to
concrete structural decodes only in the witness (§5) and in R2.3.

### 2.2 The concrete container decodes (all defined in R2.2)

These are total, computable, and structural; they consume the seam functions.
(`Std.U32.val : Nat` and `alloc.vec.Vec.toList`/`.val` are the Aeneas-API
accessors; exact names verified at implementation time against `Aeneas.Std`.)

```lean
/-- FailureBudget: u32 → Nat, structural. CONCRETE (no seam). -/
def decBudget (b : dlc_d_rsm.budget.FailureBudget) : DLCD.FailureBudget :=
  { maxFaults := b.max_faults.val, fairDelivery := b.fair_delivery,
    consumed  := b.consumed.val }

/-- Command: payload via the abstract decTm; cap via decPr (Option-mapped). -/
def decCmd (c : dlc_d_rsm.state.Command) : DLCD.Command :=
  { payload := decTm c.payload, cap := c.cap.map decPr }

/-- Replica: id/applied u32→Nat; store via decTm. -/
def decRep (r : dlc_d_rsm.state.Replica) : DLCD.Replica :=
  { id := r.id.val, store := decTm r.store, applied := r.applied.val }

/-- CommittedLog: Vec Command → List Command, pointwise decCmd. -/
def decLog (log : alloc.vec.Vec dlc_d_rsm.state.Command) : DLCD.CommittedLog :=
  (log.toList).map (decCmd decTm decPr)

/-- GlobalConfig: replicas + log + budget. -/
def decGC (g : dlc_d_rsm.state.GlobalConfig) : DLCD.GlobalConfig :=
  { replicas := (g.replicas.toList).map (decRep decTm decPr),
    log      := decLog decTm decPr g.log,
    budget   := decBudget g.budget }
```

(Each `dec*` that touches a payload takes `decTm`/`decPr` as leading
parameters; elided above for readability but explicit in the file.)

### 2.3 Seam ruling (explicit)

**`decTm` / `decPr` are abstract in R2.2.** They are exactly the deferred
`dlc-core` Term/Prop correspondence. R2.2 proves nothing about them; it is
parametric over them. The one place a *concrete* `decTm₀` is exhibited is the
anti-vacuity witness (§5), and there only on the small closed fragment the
`dup` example uses (`Var`, `Lam`, `Pair`, `Prop.Atom`). The full structural
`decTm`/`decPr` over all ~25 `Term` / ~15 `Prop` constructors, and the proof
that it commutes with the reducer, is R2.3.

---

## §3. `AppCommandRefines` — the single deferred obligation (the headline output)

This is the one lemma the entire operational transport is reduced to. It is a
**`def ... : Prop`** (ruling 3) — **not** an `axiom`, **not** a `sorry`. The
structural square theorems take it as a hypothesis `(hcmd : AppCommandRefines
decTm decPr)`.

### 3.1 Supporting predicate — the `U32` fence (honest, decidable)

```lean
/-- Well-scopedness / no-U32-overflow fence: the reduction of `App payload s`
    under `APPLY_FUEL` never triggers a `U32` shift/subst overflow, hence
    `reduce_with_fuel` never returns `.fail`. Decidable structural predicate on
    the generated Term. (Trivially true for the small closed store-transformers
    the RSM uses; see the anti-vacuity payload.) -/
def WellScopedTm (t : dlc_d_rsm.dlc_core.syntax.Term) : Prop := …
```

`WellScopedTm` is the sound content of the `U32`-vs-`Nat` gap (parent §3.1(i)).
It is folded into the square via the `.map … = ok …` form below, which *also*
asserts no-fail (if `apply_command` returns `.fail`, the LHS is `.fail ≠ ok`).

### 3.2 THE STATEMENT

```lean
/-- **THE ONE REMAINING OBLIGATION.** The generated per-command engine
    `transition.apply_command` refines the hand-written `DLCD.applyCommand`
    under the (abstract) payload decode, on well-scoped inputs — and never
    fails/diverges (folded into the `= .ok` equation via `Result.map`).

    R2.2 ASSUMES this (as a hypothesis on every structural square). R2.3
    (the deferred `dlc-core` reducer correspondence) DISCHARGES it. It is
    NOT an axiom and NOT a sorry: it is a named `Prop` a later increment
    inhabits. -/
def AppCommandRefines
    (decTm : dlc_d_rsm.dlc_core.syntax.Term → DLC.Term)
    (decPr : dlc_d_rsm.dlc_core.syntax.Prop → DLC.Prop') : Prop :=
  ∀ (c : dlc_d_rsm.state.Command) (s : dlc_d_rsm.dlc_core.syntax.Term),
    WellScopedTm s → WellScopedTm c.payload →
    (dlc_d_rsm.transition.apply_command c s).map decTm
      = Result.ok (DLCD.applyCommand (decCmd decTm decPr c) (decTm s))
```

Notes on the exact form:
- **`Result.map decTm (…) = ok (…)`** is the clean one-directional square: it
  simultaneously asserts (i) no-`fail`/no-`div` (`= ok`) and (ii) decode-
  agreement, using *only* the decode direction. No encode, no `.run`/partial
  projection.
- The RHS `DLCD.applyCommand (decCmd … c) (decTm s)` is the hand model from
  `Rsm.lean:161` (`(reduceWithFuel (Term.app c.payload s) applyFuel).1`).
- Quantified over **all** well-scoped `(c, s)`. It is the universally-closed
  form R2.3 will prove by the reducer induction; the *witness* (§5) proves one
  instance to defeat vacuity.
- Statable and type-correct **today** (both sides exist). Only its *proof*
  (R2.3) and its *witness computation* (§5) interact with OPEN QUESTION 1.

---

## §4. The structural squares — exact conditional statements + proof sketches

All are `theorem`s parametric over `decTm`/`decPr`. The three that route
through `apply_command` take `(hcmd : AppCommandRefines decTm decPr)`; the
three that do not (`is_quorum`, `decided`, `commit`) take no `hcmd`.

Shared plumbing lemmas (small; some may already exist in `Aeneas.Std`, verify):
- `L_vecget`  : `Slice.get s i` / `Vec.index` relate to `List.get?`/`getElem?`
  of the decoded list at `i.val` (index-decode bridge).
- `L_veclen`  : `Vec.len v = v.toList.length`; `Slice.len` similarly.
- `L_clone`   : the generated `Clone::clone` on `Replica`/`Command`/`Term` is
  `pure`-identity in `Result` (`clone x = ok x` after decode) — **CAVEAT**:
  `Term`/`Prop` `Clone` are *external axioms* in the tree (like
  `reduce_with_fuel`); `L_clone` for payloads is therefore itself a seam fact
  (see OPEN QUESTION 1; for R2.2 it is carried, not proved, or the concrete
  witness instantiates it).
- `L_u32succ` : `(r.applied + 1#u32).val = r.applied.val + 1` under no-overflow.

### 4.1 `deliver_square` (uses `hcmd`)

```lean
theorem deliver_square
    (hcmd : AppCommandRefines decTm decPr)
    (log : alloc.vec.Vec dlc_d_rsm.state.Command)
    (r : dlc_d_rsm.state.Replica)
    (hr : WellScopedTm r.store) (hlog : ∀ c ∈ log.toList, WellScopedTm c.payload) :
    (dlc_d_rsm.transition.deliver log r).map (decRep decTm decPr)
      = Result.ok (DLCD.deliver (decLog decTm decPr log) (decRep decTm decPr r))
```
**Sketch.** Unfold `transition.deliver`; case on
`Slice.get (log.deref) (r.applied.cast)`:
- `none` ⇒ LHS `= (clone r).map decRep = ok (decRep r)` (via `L_clone` on the
  container; store payload carried), and `log[r.applied]? = none` (via
  `L_vecget` + `L_veclen`), so `DLCD.deliver … = decRep r`. Close by `rfl`.
- `some c` ⇒ LHS reduces to `(apply_command c r.store).map decTm` lifted into
  the new `Replica`; apply **`hcmd`** at `(c, r.store)` to rewrite it to
  `DLCD.applyCommand (decCmd c) (decTm r.store)`; `L_u32succ` gives
  `applied+1`; `L_vecget` gives `log[r.applied]? = some (decCmd c)`, matching
  `DLCD.deliver`'s `some` branch (`Rsm.lean:174`). Close.

### 4.2 `world_step_square` (uses `hcmd`)

```lean
theorem world_step_square
    (hcmd : AppCommandRefines decTm decPr)
    (g : dlc_d_rsm.state.GlobalConfig) (hg : WellScopedGC g) :
    (dlc_d_rsm.transition.world_step g).map (decGC decTm decPr)
      = Result.ok (DLCD.worldStep (decGC decTm decPr g))
```
**Sketch.** `DLCD.worldStep g = { g with replicas := g.replicas.map (deliver
g.log) }` (`Rsm.lean:181`). The generated `world_step` builds `stepped` by an
**accumulator `push` loop** (`world_step_loop`, `Funs.lean:588`), pushing
`deliver(v1, v[i])` for `i = 0 … len-1`. Since `push` *appends* in index order,
the accumulator equals `List.map (transition.deliver g.log) g.replicas.toList`
(no reversal). Prove the loop spec by induction generalizing the accumulator:
```lean
world_step_loop_spec :
  (world_step_loop {0,n} v v1 acc0).map (·.toList.map decRep)
    = ok (acc0.toList.map decRep ++ (v.toList.drop k).map (deliver …))   -- generalized
```
then instantiate `acc0 = Vec.new` (empty). Rewrite each `transition.deliver`
image via **`deliver_square`** (4.1); `map`/`decLog`/`decGC` commute pointwise.
**Risk:** the accumulator-generalization lemma is the one non-one-liner here
(§7). Order is confirmed preserved (push, not push-front), so no `List.reverse`
appears — this is the main thing that could have made it *not* cheap, and it is
fine.

### 4.3 `apply_prefix_square` (uses `hcmd`)

```lean
theorem apply_prefix_square
    (hcmd : AppCommandRefines decTm decPr)
    (init : dlc_d_rsm.dlc_core.syntax.Term)
    (cmds : Slice dlc_d_rsm.state.Command)
    (hinit : WellScopedTm init)
    (hcmds : ∀ c ∈ cmds.toList, WellScopedTm c.payload) :
    (dlc_d_rsm.transition.apply_prefix init cmds).map decTm
      = Result.ok (DLCD.applyPrefix (decTm init) ((cmds.toList).map (decCmd decTm decPr)))
```
**Sketch.** `DLCD.applyPrefix init cmds = cmds.foldl (fun s c => applyCommand c
s) init` (`Rsm.lean:166`). The generated `apply_prefix_loop` (`Funs.lean:526`)
is an accumulator fold applying `apply_command cmds[i] acc`. Prove the loop spec
by induction generalizing `acc`, rewriting each `apply_command` step via
**`hcmd`**; matches `List.foldl applyCommand`. (Structurally identical to
`world_step` but folding a `Term` accumulator instead of building a `Vec`.)

### 4.4 `is_quorum_square` (NO `hcmd`; bool ↔ Prop)

```lean
theorem is_quorum_square (card n : Std.U32) (hno : 2 * card.val < 2^32) :
    dlc_d_rsm.consensus.is_quorum card n
      = Result.ok (decide (2 * card.val > n.val))
```
**Sketch.** `consensus.is_quorum = do let i ← 2#u32*card; ok (i > n)`
(`Funs.lean:188`). Under `hno`, the `U32` multiply does not overflow
(`(2*card).val = 2*card.val`), so it reduces to `ok (2*card.val > n.val)`.
Relates to the *operationalized* `DLCD.IsQuorum` (`2·card > n`); the
`Finset`-cardinality `Prop` form stays Lean-only (parent §1.2). `hno` is the
honest `U32` fence for the multiply.

### 4.5 `decided_square` (NO `hcmd`)

```lean
theorem decided_square (votes : Slice (Option dlc_d_rsm.state.Command))
    (v : dlc_d_rsm.state.Command) (hno : 2 * (count …) < 2^32) :
    dlc_d_rsm.consensus.decided votes v
      = Result.ok (decide (2 * (votes.toList.countP (· = some v)) > votes.toList.length))
```
**Sketch.** The `decided_loop` (`Funs.lean:218`) counts indices whose vote
equals `v`, then calls `is_quorum count len`. Prove the count loop equals
`List.countP` by accumulator induction; then `is_quorum_square`.
**Seam caveat:** the per-element test uses the generated `Command` `PartialEq`,
which for the `Term` payload calls `Term`'s `PartialEq` — an **external axiom**
in the tree (same class as `reduce_with_fuel`). So `decided_square` as an
equality with a decidable `countP` needs `Command` equality to be decode-
faithful, itself a seam fact (carry it, or restrict to the concrete witness).
Note in the doc as a *second, smaller* instance of OPEN QUESTION 1.

### 4.6 `commit_square` (NO `hcmd`; pure append)

```lean
theorem commit_square (g : dlc_d_rsm.state.GlobalConfig) (c : dlc_d_rsm.state.Command) :
    (dlc_d_rsm.transition.commit g c).map (fun g' => (decGC decTm decPr g').log)
      = Result.ok (decLog decTm decPr g.log ++ [decCmd decTm decPr c])
```
**Sketch.** `transition.commit` clones `g.log`, `push`es `c`
(`Funs.lean:637`). `push` appends, so the decoded log is `decLog g.log ++
[decCmd c]`. There is **no** `DLCD.commit` in `Rsm.lean` (commit lives in
`CapSafety.lean` and its guarantee is typing-level, parent §4 fence), so the
square is stated against the *append operation* directly — the operational
core only. `L_clone` on the container `Vec` is used; payloads carried.

---

## §5. The anti-vacuity witness — exact statement + proof strategy

**Purpose (ruling 4).** A conditional theorem `AppCommandRefines → square` is
vacuous if `AppCommandRefines` is uninhabitable. The witness proves
`AppCommandRefines` is **satisfiable on the concrete state-changing input** —
the `dup`-payload example (`Rsm.lean:245`, mirrored in the crate's
`lib.rs` test `dup()`), where the store genuinely changes `var 0 ↦ ⟨var 0, var
0⟩` (distinct head constructor, not a no-op).

### 5.1 The two components

**(A) Hand-side non-triviality (closable TODAY, axioms clean).** Already proved
in `Rsm.lean`:
```lean
-- DLCD.RsmAntiVacuity.converged_store_changed :
--   r1.store = Term.pair (Term.var 0) (Term.var 0) ∧ r1.store ≠ init
```
R2.2 re-exports / cites this to establish the *conclusion* side is non-trivial:
`DLCD.applyCommand dup init = ⟨var0,var0⟩ ≠ init` by `rfl` + `Term.noConfusion`.
Axiom footprint: clean (`propext`-class only). This part needs no generated
tree.

**(B) Hypothesis satisfiability on the concrete input — the target of ruling
4.** Exhibit a concrete structural decode `decTm₀`/`decPr₀` (on the small `dup`
fragment: `Var`, `Lam`, `Pair`, `Prop.Atom`) and prove the *instance* of
`AppCommandRefines` at the generated `dup`/`init`:
```lean
/-- The concrete-input satisfiability witness: for the anti-vacuity dup command
    and initial store, the generated apply_command decodes to the hand
    applyCommand, and the result is the CHANGED store ⟨var0,var0⟩ ≠ init. -/
theorem appCommandRefines_witness :
    (dlc_d_rsm.transition.apply_command dupGen initGen).map decTm₀
        = Result.ok (Term.pair (Term.var 0) (Term.var 0))
      ∧ (Term.pair (Term.var 0) (Term.var 0)) ≠ initHand
```
where `dupGen : dlc_d_rsm.state.Command` and `initGen :
dlc_d_rsm.dlc_core.syntax.Term` are the generated-side `dup`/`var 0`, `decTm₀`
the concrete fragment decode, `initHand = Term.var 0`.

**Proof strategy for (B):** unfold `transition.apply_command`; evaluate
`reduce_with_fuel` on `App (Lam _ (Pair (Var 0)(Var 0))) (Var 0)` — one β-step
to `Pair (Var 0)(Var 0)`, then no redex, loop exits early (well under 1024
fuel); `.map decTm₀` gives `Pair (var 0)(var 0)`; second conjunct by
`Term.noConfusion`. Evaluation is via **Aeneas simp/`progress` normal-form
lemmas for `reduce_with_fuel_loop`**, *not* `rfl` (the `loop` combinator is
well-founded recursion and does not `rfl`-reduce) and *not* `native_decide`
(banned). Expected axiom footprint: `[propext, Classical.choice, Quot.sound]`.

### 5.2 THE BLOCKER (OPEN QUESTION 1 — this is why the pass matters)

Component **(B) cannot be closed against the committed generated tree**, because
`dlc_d_rsm.dlc_core.reduce.reduce_with_fuel` is an **`axiom`** (§0.1(4)) with no
reduction rule. `transition.apply_command dupGen initGen` is therefore *stuck*:
it neither `rfl`-, `simp`-, nor `decide`-reduces, and any proof of the instance
would either be impossible or would have to *assume* a value for the axiom —
defeating the point. Concretely:
- The witness's `#print axioms` would include
  `dlc_d_rsm.dlc_core.reduce.reduce_with_fuel`, which is **not** in the allowed
  set `[propext, Classical.choice, Quot.sound]` — violating ruling 4 outright.
- Component **(A)** is unaffected (pure hand model) and can land now.

**Resolution options (present, do not silently decide — see OPEN QUESTION 1):**
1. **Regenerate the DlcDRsm tree so `reduce_with_fuel` is a full `def`** (as it
   already is in the standalone `DLC.Aeneas.DlcCore` tree). This is almost
   certainly an Aeneas invocation/config difference (dependency-crate functions
   with loops emitted opaque). If `scripts/aeneas-translate.sh` can be made to
   fully translate the inlined `dlc_core` reducer for the `dlc-d-rsm` target,
   `apply_command` computes and the witness closes exactly as §5.1(B). *This is
   an R2.1-artifact fix, arguably a prerequisite of R2.2, not R2.2 proper.*
2. **Fill the external hole** by authoring `lean/DLCD/Aeneas/DlcDRsm/FunsExternal.lean`
   (rename from the template) that *defines* `reduce_with_fuel` — but the honest
   definition is the reduce loop, which already exists in the DlcCore tree over
   a *different* `Term` inductive (`dlc_core.syntax.Term` ≠
   `dlc_d_rsm.dlc_core.syntax.Term`), so this needs a Term-copy bridge just to
   reuse it. Messier; and a hand-authored `FunsExternal.lean` changes the
   drift-gate surface.
3. **Defer component (B) to R2.3** and land R2.2 with only component (A) + the
   *statement* of `appCommandRefines_witness` as the R2.3 target. This keeps
   R2.2 honest (squares + hypothesis + hand-side non-triviality) but means R2.2
   does **not** fully discharge ruling 4's "closed satisfiability witness."

**Recommendation:** Option 1 (regenerate to a real `reduce_with_fuel` def),
since it is the same computational content already trusted in the DlcCore tree,
unblocks the witness cleanly, and removes an unintended axiom from the compiled
image the moment §1.2 pulls the tree into the main build. But this is a
generation/gate change outside the rulings' "additive Lean only" R2.2 envelope,
so it needs the author's ruling.

---

## §6. Governance delta

Exactly what R2.2 changes, and what it must not:

- **52 existing expected-axioms snapshots: BYTE-UNCHANGED.** R2.2 edits **no**
  `lean/DLCD/*.lean` guarantee file (only *adds* `lean/DLCD/Correspondence.lean`)
  and no `lean/DLC/*` file. *Nit to reconcile:* the ruling says 52; the working
  tree's `lean/expected-axioms/` currently lists **53** files — confirm which is
  the tracked count before touching anything (do not add/remove any).
- **New conditional squares: NOT added to `theorem-status.json` / README /
  any public claim.** They are "in progress" (they take a hypothesis), so
  `scripts/check-claims.sh` stays green (adding nothing to claims cannot exceed
  ledger status). Do **not** advertise them.
- **`check-tautologies.sh`: stays green.** `AppCommandRefines` is a real
  `∀`-quantified equality `Prop`, not `True`/`x = x`; the squares are real
  equalities. No placeholder bodies.
- **`sorry` gate: stays green.** No `sorry` anywhere; `AppCommandRefines` is a
  `def`, the squares are real proofs, the hypothesis is a *parameter*.
- **Anti-vacuity witness axiom pinning (ruling 5 decision):**
  - Component **(A)** (hand-side non-triviality) *may* be pinned with a new
    `lean/expected-axioms/<name>.txt` = `[propext, Classical.choice,
    Quot.sound]` — clean, generated-tree-independent. **Recommend pin it** so
    its footprint is gated (and add `<name>` to `check-axioms.sh`'s tracked
    set + `LIBS` already covers `DLCDCorrespondence`).
  - Component **(B)** (`appCommandRefines_witness`): **do NOT pin until OPEN
    QUESTION 1 is resolved.** While `reduce_with_fuel` is an axiom, (B) cannot
    close with a clean footprint, and pinning its snapshot would *bake the
    `reduce_with_fuel` axiom (and the fmt/clone externals) into the accepted
    axiom set* — precisely the vacuity/soundness smell to avoid. Pin (B) only
    once the tree gives `reduce_with_fuel` a real `def` and the footprint is
    verified `= [propext, Classical.choice, Quot.sound]` (and specifically
    **free of `Lean.ofReduceBool`** — i.e. no `native_decide`).
- **No `theorem-status.json` entry** for the witness either until (B) closes;
  R2.2's public posture is the honest claim of §7.

---

## §7. Honest cost, risks, and what could force this to NOT be cheap

| Piece | Size | Risk |
|---|---|---|
| decode `⟦·⟧` container decodes (§2.2) + abstract seam | ~60 LOC | **Low.** Structural; `decTm`/`decPr` abstract. |
| `AppCommandRefines` + `WellScopedTm` (§3) | ~25 LOC | **Low.** A statement, not a proof. |
| plumbing lemmas `L_vecget`/`L_veclen`/`L_clone`/`L_u32succ` | ~60 LOC | **Low–med.** Some may exist in `Aeneas.Std`; `L_clone` on payloads is a seam caveat (OQ1). |
| `deliver`/`apply_prefix`/`world_step` squares (§4.1–4.3) | ~150 LOC | **Med.** The accumulator-generalization lemmas (loop-vs-`map`/`foldl`) are the only non-one-liners. Order is push-append = no reversal (verified), so they stay cheap. |
| `is_quorum`/`decided`/`commit` squares (§4.4–4.6) | ~70 LOC | **Low–med.** `decided` has the `Command`-`PartialEq`-external seam caveat. |
| anti-vacuity witness (A) (§5.1) | ~15 LOC | **Low** — already essentially in `Rsm.lean`. |
| anti-vacuity witness (B) (§5.1/5.2) | ~30 LOC | **BLOCKED** — see OQ1. |

**Dominant risk — OPEN QUESTION 1 (`reduce_with_fuel` is an axiom).** This is
the thing that could force R2.2 to not deliver its headline (the closed
satisfiability witness). Precise blast radius:
- The **structural squares are UNAFFECTED**: they route `apply_command` to
  `hcmd` and never force it to compute, so they are statable and provable
  *conditionally* even with `reduce_with_fuel` opaque. R2.2's *conditional*
  content is fully deliverable today.
- The **anti-vacuity witness (B) IS blocked**: it must *compute* through
  `apply_command`, which is stuck on the axiom. Without resolving OQ1, ruling
  4's "closed, sorry-free, `native_decide`-free, clean-axiom satisfiability
  witness" cannot be met. This is not a cost overrun; it is a *precondition*
  that R2.1's generated artifact does not currently satisfy.

**Other risks (lower):**
- **`world_step_loop` shape.** The concern flagged in the task (does the
  indexed `push`-accumulator loop cleanly commute with `⟦·⟧`?) is **resolved
  favorably**: `push` appends in index order, so the loop builds `List.map`
  with no `reverse`. It needs a generalized-accumulator induction lemma but no
  reordering algebra. If it had been a push-*front* / reversed accumulator, the
  square would have needed a `List.reverse` reconciliation — it does not.
- **Two `Term` copies.** The decode source is the *inlined*
  `dlc_d_rsm.dlc_core.syntax.Term`, distinct from the DlcCore-tree
  `dlc_core.syntax.Term`. Keep every square/decode over the inlined type;
  reusing DlcCore-tree lemmas would need a Term-copy bridge (relevant to OQ1
  option 2).
- **Term/Prop-payload decode is abstract (seam).** Fine for the structural
  squares (they carry payloads opaquely) and for R2.3 to fill; the only place
  it must be concrete is witness (B) on the `dup` fragment.
- **`U32`/`Nat` fences** (`WellScopedTm`, `is_quorum`'s `2*card`, `applied+1`)
  are honest stated hypotheses, benign for RSM inputs — not hand-waved.
- **`decided`/`Command`-`PartialEq` external** is a second, smaller instance of
  the same axiom-stub seam as `reduce_with_fuel` (OQ1); note it, do not pin
  `decided_square`'s axioms until resolved.

**Honest R2.2 claim (ruling 6).** Do **not** claim "the Rust core satisfies
G1–G4" anywhere. The claim R2.2 earns is: *the operational structural squares
(`deliver`, `world_step`, `apply_prefix`, `is_quorum`, `decided`, `commit`)
hold **conditional on** the single stated reducer correspondence
`AppCommandRefines`; the whole operational transport is thereby reduced to
exactly that one lemma* — with the caveat (OQ1) that the closed satisfiability
witness for `AppCommandRefines` awaits a `reduce_with_fuel` `def` in the
generated tree.

---

## OPEN QUESTIONS (author ruling needed — not decided here)

1. **[BLOCKING] `reduce_with_fuel` is an `axiom` in the DlcDRsm tree.** The
   committed `lean/DLCD/Aeneas/DlcDRsm/FunsExternal_Template.lean` declares
   `reduce_with_fuel` as an external `axiom` (whereas the standalone
   `DLC.Aeneas.DlcCore` tree has it as a full `def`). Consequently
   `transition.apply_command` does not compute, and the anti-vacuity witness
   component (B) — ruling 4's headline deliverable — **cannot be closed with a
   clean axiom footprint** against the current tree. Resolution options in §5.2
   (recommend option 1: regenerate the tree so the inlined `dlc_core` reducer is
   a real `def`). *This wasn't in the rulings and changes what R2.2 can
   deliver; needs an explicit call.* (Note: the structural squares are
   unaffected and fully deliverable conditionally.)
2. **Second, smaller instance of the same seam:** `Term`/`Prop` `Clone` and
   `Command`/`Term` `PartialEq` are also external axioms in the tree (used by
   `deliver`/`world_step`/`commit` `L_clone` and by `decided`). Same resolution
   as OQ1 if option 1 (regenerate) is taken; otherwise these are carried facts.
3. **Snapshot count.** Ruling 5 says "52 expected-axioms snapshots"; the tree
   currently lists **53** files under `lean/expected-axioms/`. Confirm the
   tracked count so "byte-unchanged" is unambiguous before R2.2 touches
   anything.
4. **Witness (A) pinning.** Recommend pinning the hand-side non-triviality
   witness's axioms (clean `[propext, Classical.choice, Quot.sound]`) now, and
   pinning (B) only post-OQ1. Confirm.
