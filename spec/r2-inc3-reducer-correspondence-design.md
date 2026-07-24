# R2.3 — the reducer/subst correspondence: discharging `AppCommandRefines` and `ApplyPreservesWS`

**Status:** DESIGN ONLY (no source touched). Branch `dlc-d/phase0-carve`, HEAD `3ea4c32`.
**Scope:** instantiate the two parametric obligations the landed structural squares
(`lean/DLCD/Correspondence.lean`) assume, for a *concrete full* payload decode
`decTm : dlc_core.syntax.Term → DLC.Term` / `decPr : dlc_core.syntax.Prop → DLC.Prop'`,
by proving the Aeneas-generated `reduce`/`subst` core refines the hand `DLC.step`/`subst`
model under a well-scoped/closed fence and never `.fail`s.

This is the long-deferred dlc-core reducer correspondence (the leaf the whole R2
operational transport rests on). Known high-cost. This document decomposes it into four
sub-increments, states the exact lemmas, and surfaces the rulings I need before implementation.

---

## §0. Web-searched prior art (2026-07-23; URLs recorded)

- **Aeneas** (Ho–Protzenko, POPL/ICFP; *Rust verification by functional translation*): each
  Rust fn → a `Result α` (`ok`/`fail`/`div`) pure Lean fn; you prove the extracted fn matches
  a spec. This is exactly the `decTm <$> aeneas_fn … = ok (hand_fn …)` shape our squares use.
  - https://dl.acm.org/doi/10.1145/3547647 , https://aeneasverif.github.io/ , https://lean-lang.org/use-cases/aeneas/
- **Aeneas loop reasoning via combinators** (the `loop`/`ControlFlow` `cont`/`done` combinator,
  reasoned by a decreasing measure + accumulator generalization; `loop.eq_1` unfolding; the
  `step`/`step*`/`progress` tactics, `scalar_tac`/`bv_tac` for machine integers, `grind`/`agrind`):
  the jxl-rs case study is the current reference for the loop-combinator idiom that our
  `reduce_with_fuel_loop` correspondence needs.
  - https://jonathan.protzenko.fr/2026/05/05/jxl-rs.html , https://github.com/AeneasVerif/aeneas
- **Lean partial_fixpoint / equational lemmas / functional induction** (`fun_induction`,
  extrinsic well-founded unfolding, the `partial_fixpoint` monadic fixpoint whose equational
  lemmas we must use because `reduce.step`/`subst.*` are emitted `partial_fixpoint`, NOT
  structural — they do not `rfl`-reduce):
  - https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/
  - https://www.joachim-breitner.de/blog/816-Extrinsic_termination_proofs_for_well-founded_recursion_in_Lean
  - https://github.com/leanprover/lean4/issues/3983
- **de Bruijn shift/subst faithfulness** (Autosubst / Autosubst 2 with a Lean backend; the
  "notoriously tedious substitution composition lemma is fully proved, tractable" result; a
  2025 modular Lean 4 confluence/SN framework that fully proves the subst lemmas):
  - https://www.ps.uni-saarland.de/autosubst/ , https://www.ps.uni-saarland.de/Publications/documents/StarkEtAl_2018_Autosubst-2_.pdf
  - https://dl.acm.org/doi/pdf/10.1145/2676724.2693163 (de Bruijn substitution algebra, CPP'15)
  - https://arxiv.org/abs/2512.09280 (Lean 4 λ-calculus w/ products+sums; shift/subst lemmas fully proved)
- **Grove** (SOSP'23): verified distributed impl refines an abstract state-machine spec; the
  refinement *square* discipline; the **12× proof:code** ratio anchor for this class of work
  (our cost table §5 calibrates against it, but note our subst/step are *mirror-generated*, so
  we expect materially better than 12×).
  - https://iris-project.org/pdfs/2023-sosp-grove.pdf , https://arxiv.org/pdf/2309.03046
- **A Refinement Methodology for Distributed Programs in Rust** (Bila–Pereira–Müller, OOPSLA'25;
  ghost-code model embedded in the program) — adjacent SOTA for Rust→model refinement, contrast
  to the Aeneas functional-translation route we take.
  - https://pm.inf.ethz.ch/publications/BilaPereiraMueller25.pdf
- Vacuity/satisfiability-witness discipline (carried from R2.2b): https://arxiv.org/pdf/2606.29493

**Prior-art takeaway.** The refinement-square shape and the loop-combinator idiom are exactly
the established Aeneas patterns (and already demonstrated in-tree: `world_step_loop_spec` /
`apply_prefix_loop_spec` in `Correspondence.lean` reconcile the *same* `loop`/`ControlFlow`
combinator against a hand fold by accumulator induction — the `reduce_with_fuel` reconciliation
is the third instance of a proven idiom, not a new technique). The genuinely novel labor is the
`U32`/`I64`↔`Nat` faithful-arithmetic content of subst/shift under a closedness fence.

---

## §1. The concrete full decode + the well-scopedness fence

### 1.1 Full decode (all constructors)

The generated and hand ASTs are **mirror-for-mirror** (both are translations of
`crates/dlc-core/src/syntax.rs`): identical constructor sets, identical arity, identical binder
structure. The decode is therefore a total structural homomorphism, `U32.val → Nat` at the
scalar leaves. It is defined by three mutually-supporting maps (none recursive through the other's
recursion, so plain structural recursion suffices):

```
decPrin : principal.Principal → DLC.Principal        -- Atom (bytes.map …) / And / Or / Acting, structural
decLab  : ifc.Label → DLC.Label                       -- already handled by decGC's `decBudget`-style leaf; Label = nucleus CapabilityLattice, decode is identity-of-representation
decOb   : obligation.Obligation → DLC.Obligation      -- structural, scalar leaves .val→Nat
decSig  : syntax.Signature → DLC.Signature            -- { alg, bytes } structural
decPr   : syntax.Prop → DLC.Prop'                      -- Top/Bot/Atom(.val)/Imp/And/Or/Says(decPrin)/SpeaksFor/At(·,decLab)/Boxed(decOb,·)/Within/Tensor/Lolli/Replicated(·,decLab)
decTm   : syntax.Term → DLC.Term                       -- all 26 ctors; Var(.val→Nat), Lam(decPr,·), … Command(·,·,decLab), RunCmd(·,·)
```

The witness fragment `decTm₀`/`decPr₀` (§5 of `Correspondence.lean`) is the restriction of
`decTm`/`decPr` to `{Var, Lam, App, Pair, Prop.Atom}`; R2.3 replaces the `_ => .var 0` /
`_ => .top` default arms with the real structural cases. **The full decode must be shown to agree
with `decTm₀` on the fragment** (a `decide`/`rfl` compatibility lemma) so the existing anti-vacuity
witness `appCommandRefines_witness` and `applyPreservesWS_witness` continue to typecheck against
the concrete instance — or, cleaner, re-state those witnesses against the full `decTm`.

**One faithfulness side-lemma the decode must satisfy** (needed by the `delegate`-β step case):
`decPrin (principal.Principal.Acting p q) = DLC.Principal.acting (decPrin p) (decPrin q)` — holds
by `rfl` if the generated `delegate` arm builds `Principal.Acting` directly (confirmed: the
Aeneas `reduce.step` delegate arm constructs the `Acting` node, it does not call a helper).

### 1.2 The fence: flat `WellScopedTm` is NOT enough — this is the load-bearing finding

The landed `WellScopedTm` (`Correspondence.lean` §3) is a *flat* predicate: every `Var i` has
`i.val < 2^31`. It is decidable and honest, and it is what the squares already carry. But it is
**almost certainly insufficient for R2.3**, for two independent reasons:

1. **The `I32` depth-cast in `subst_at`.** The generated `subst.subst_at` Var/`eq` arm does
   `let i1 ← hcast .I32 depth; subst.shift value i1 0`. `hcast .I32` **fails** unless
   `depth < 2^31`. `depth` is the accumulated binder depth, which grows `+1` (lam/saysBind/
   letSays/case) or `+2` (letTensor) per binder and is **not bounded by any Var-index bound** —
   `λλ…λ(var 0)` has huge depth but every index is `0`. So no-fail needs a **binder-depth / AST-height
   bound** that flat `WellScopedTm` does not provide.
2. **`WellScopedTm` is not preserved by `shift`** (breaks `ApplyPreservesWS`). `subst`'s eq-arm
   emits `shift value depth 0`, which raises `value`'s free indices by `depth`. Flat well-scopedness
   bounds `i < 2^31` and `depth < 2^31`, but the *sum* `i + depth` can reach `~2^32 > 2^31`, so the
   reduct can contain a `Var` index `≥ 2^31` — **outside** `WellScopedTm`. The predicate that IS
   preserved by shift/subst/reduce is genuine **closedness** (`ClosedAbove t k`: every free index
   `< k`), which is the standard de Bruijn invariant.

**Recommended fence (subject to §6 ruling #1).** Adopt, as the concrete instance of the fence, a
*conjunction*:

```
WellScopedTm' t  :=  DLC.ClosedAbove (decTm t) 0        -- t decodes to a CLOSED hand term (no free vars)
                     ∧  heightB t < 2^31                 -- decidable AST-height bound (rules out the I32/U32 overflow)
```

- `ClosedAbove … 0` (closed) is inductively preserved by `shift`/`subst`/`step` — the standard
  metatheory, and **already partly in-tree**: `DLC.DerivClosed` provides `ClosedAbove`,
  `closedAbove_mono`, `closedAbove_shift`, `deriv_closedAbove` (`lean/DLC/DerivClosed.lean`). This
  is the reusable metatheory that makes the preservation direction cheap.
- `heightB t < 2^31` is decidable and gives `depth ≤ 2·height < 2^32` and (with closedness bounding
  live indices by the current depth) `i + delta < 2^32`, so every `hcast`/`+` in shift/subst
  succeeds — the no-fail content.
- On the RSM's actual inputs (closed ground store `var 0`, small closed λ payloads) both conjuncts
  are trivially true, so the existing anti-vacuity witnesses survive.

**Cost of this choice:** the four *landed* squares are stated over the abstract `WellScopedTm`;
instantiating the parametric obligations at `WellScopedTm'` does not require editing the squares
(they are universally quantified over the predicate via the `AppCommandRefines`/`ApplyPreservesWS`
`def`s, which *fix* `WellScopedTm`). **This is the friction point** — see §6 ruling #1: either
(a) redefine `WellScopedTm := WellScopedTm'` (touches the landed `def`s and their witnesses, must
re-verify the squares — but the squares only *consume* `WellScopedTm` hypotheses, so strengthening
the predicate they assume is monotone and should not break them), or (b) keep flat `WellScopedTm`
and prove R2.3 needs only it by a separate global argument that RSM inputs never overflow (weaker,
riskier, arguably dishonest about the height bound). I recommend (a).

---

## §2. Sub-increment decomposition

The dependency spine is `subst/shift` ⟶ `step` ⟶ `reduce_with_fuel` ⟶ `apply_command`, plus a
preservation companion running alongside. Four sub-increments:

### R2.3a — subst/shift correspondence (the crux)

**Lemma statements** (schematic; `Result.map` folds in no-fail):

```
shift_corr :
  ∀ (t : syntax.Term) (delta : Std.I32) (cutoff : Std.U32),
    Fence t → 0 ≤ delta.val → (bounds so no cast/add overflows) →
    decTm <$> subst.shift t delta cutoff
      = Result.ok (DLC.shift (decTm t) delta.toNat cutoff.val)

substAt_corr :
  ∀ (body value : syntax.Term) (depth : Std.U32),
    Fence body → Fence value → (depth < 2^31) →
    decTm <$> subst.subst_at body value depth
      = Result.ok (DLC.substAt (decTm body) (decTm value) depth.val)

subst_corr :                          -- corollary at depth 0
  Fence body → Fence value →
    decTm <$> subst.subst body value = Result.ok (DLC.subst (decTm body) (decTm value))
```

**Proof strategy.** `fun_induction subst.shift` / `fun_induction subst.subst_at` (the Aeneas
`partial_fixpoint` functional-induction principle), one case per constructor. All 20-odd
recursive arms are *homomorphic* — child recurses, `clone` sub-results are identity by the
already-proven `termClone_id`/`propClone_id`/… family (§2c of `Correspondence.lean`), `bind_tc_ok`
collapses the monad, IH closes. The three interesting arms:
- `shift`/`Var`: `if i < cutoff` matches hand `if i < cutoff` (both decode `.val`); else the
  `I64` path: `scalar_tac`/`bv_tac` proves `hcast .I64 i`, `+ delta`, `¬(shifted < 0)`,
  `hcast .U32 shifted` all succeed under the fence and `shifted.val = i.val + delta.toNat`,
  matching hand `var (i + delta)`. The `shifted < 0` dead branch is discharged by `0 ≤ delta`.
- `subst_at`/`Var`: `OrdU32.cmp i depth` trichotomy ↦ hand `if i = depth / i > depth / else`:
  `lt`→`ok body` = `var i`; `eq`→`hcast .I32 depth; shift value …` reduces to hand
  `shift value depth 0` **via `shift_corr`** (so R2.3a is internally sequenced: `substAt` depends
  on `shift`); `gt`→`i - 1#u32` (`scalar_tac`: `i > depth ≥ 0 ⇒ i ≥ 1`, no underflow) = `var (i-1)`.
- binder arms (`lam`,`saysBind`,`letSays`,`case` `+1`; `letTensor` `+2`): the `cutoff + k#u32`
  must not overflow — discharged from `heightB`/depth bound by `scalar_tac`; then IH at the bumped
  cutoff, whose `.val` equals hand `cutoff + k`.

**Idioms:** `fun_induction`, `simp only [<generated eq lemmas>]`, `scalar_tac`/`bv_tac` (for every
`U32`/`I32`/`I64` obligation), the `termClone_id` family, `bind_tc_ok`/`bind_ok`, `Result.map_ok`.

**Risk/cost:** HIGH. This is the single riskiest sub-increment (tied with R2.3c). ~20 homomorphic
arms are mechanical but voluminous; the Var/eq arithmetic and the shift/subst interleaving carry
the real proof obligations. Est. 250-450 lines.

### R2.3b — single-step correspondence

**Lemma statement:**

```
step_corr :
  ∀ (t : syntax.Term), Fence t →
    (Option.map decTm) <$> reduce.step t = Result.ok (DLC.step (decTm t))
```

(`reduce.step : Result (Option Term)`; hand `DLC.step : Term → Option Term`; the outer `Result`
is the no-fail claim, the inner `Option` is value-vs-redex.)

**Proof strategy.** `fun_induction reduce.step` (or structural `cases` on `t` then on the head).
Value arms (`Var`,`Lam`,`sign`,`pair`,`inl`,`inr`,`tensorIntro`,`now`,`withinIntro`,`verify`,
`attenuate`,`boxed`,`liftLabel`,`declassify`,`command`) → both `none`, `rfl`/`simp`. The 11
elimination arms (`app`,`fst`,`snd`,`case`,`letTensor`,`saysBind`,`letSays`,`sfExtract`,`delegate`,
`discharge`,`runCmd`): each splits on its scrutinee's head. **Redex sub-cases invoke R2.3a**
(`subst_corr` / for `letTensor`, `subst (subst body (shift a 1 0)) b` via `shift_corr`+`subst_corr`).
**Congruence (ξ) sub-cases invoke the IH** (`step_corr` on the scrutinee). Two arm-specific notes:
- The generated `App`/`Delegate` arms enumerate *every* head constructor of the scrutinee (via
  `Box…as_ref`) — ~26 near-identical ξ sub-arms that each do `step f; clone x; App f2 x`. These
  collapse uniformly: non-`Lam` heads all route to `step f` (the IH), and `clone x = ok x` by
  `termClone_id`. A single `<;>` combinator or a helper lemma tames the fan-out.
- `saysBind`/`letSays`/`delegate` redex arms carry a principal-equality guard (`if p = p'`) and the
  `Acting` construction — needs the `decPrin`-commutes-with-`Acting` side-lemma (§1.1) and that
  `DecidableEq` on decoded principals agrees with the generated `PartialEq` (a `decide`-level
  compatibility fact).

**Idioms:** `fun_induction reduce.step`, IH threading, `subst_corr`, `termClone_id`, `Option.map`,
`scalar_tac` only incidentally (step itself is arithmetic-free except through subst).

**Risk/cost:** MEDIUM-HIGH. Voluminous (the App/Delegate head fan-out) but each case is shallow
once R2.3a is in hand. Est. 300-500 lines, dominated by the enumerated head arms.

### R2.3c — fuel-loop correspondence

**Lemma statement:**

```
reduce_with_fuel_corr :
  ∀ (t : syntax.Term) (fuel : Std.U32), Fence t →
    (fun p => decTm p.1) <$> reduce.reduce_with_fuel t fuel
      = Result.ok (DLC.reduceWithFuel (decTm t) fuel.val).1     -- FIRST component only
```

**Crucial simplification:** `rsm.apply_command` binds `let (t2, _) ← reduce_with_fuel …` (discards
the step-count) and hand `applyCommand` takes `.1`. **The second component (step count) never
enters the correspondence** — Aeneas returns the range-index-at-stop / `fuel`, hand returns the
number of steps taken; these differ, but both are discarded. So R2.3c only reconciles the FINAL
TERM. This kills the thorniest part of a naive fuel reconciliation.

**Proof strategy.** This is the *third* in-tree instance of the `loop`/`ControlFlow` accumulator
idiom already proven twice in `Correspondence.lean` (`world_step_loop_spec`,
`apply_prefix_loop_spec`). Generalize over remaining fuel and prove a loop-invariant by induction on
`rem : Nat`:

```
reduce_loop_spec :
  ∀ (rem : Nat) (k : Std.U32) (cur : syntax.Term),
    Fence cur → k.val + rem = fuel.val →
    (fun p => decTm p.1) <$> reduce.reduce_with_fuel_loop {start:=k, «end»:=fuel} fuel cur
      = Result.ok (DLC.reduceWithFuel (decTm cur) rem).1
```

- `rem = 0` (`k = fuel`): `IteratorRange.next` returns `none` → `done (cur, fuel)`; hand
  `reduceWithFuel _ 0 = (cur, 0)`. Both `.1 = decTm cur`. (Uses the `next_done` idiom, cf.
  `next_done_usize`.)
- `rem = m+1`: `next` yields `some k` (range non-empty), then `reduce.step cur`:
  - `step cur = none` (normal form) via **R2.3b** → `done (cur, k)`; hand `reduceWithFuel` also sees
    `step (decTm cur) = none` → `(cur, 0)`, `.1 = decTm cur`. ✔
  - `step cur = some next` via **R2.3b** → `cont (iter1, next)`, loop recurses; hand steps to
    `decTm next` and recurses with fuel `m`. **Fence preservation of `next`** (from the R2.3d
    companion / R2.3a preservation) feeds the IH. ✔

**Idioms:** the in-tree `loop_cont`/`loop_fin`/`next_succ`/`next_done` lemmas (already present,
`U32` variants trivially added next to the `Usize` ones), induction on remaining fuel, `step_corr`,
the fence-preservation lemma from R2.3d, `scalar_tac` for the range advance.

**Risk/cost:** MEDIUM. The idiom is proven twice already; the novelty is only that the loop body
calls `step` (routed through R2.3b) and the accumulator is a bare term. The `reduce_with_fuel`
wrapper prepends a `clone` (`termClone_id`). Est. 120-200 lines.

### R2.3d — assemble `AppCommandRefines` + `ApplyPreservesWS`

**`AppCommandRefines`:** `rsm.apply_command c s` clones `c.payload` and `s` (both `termClone_id`),
builds `App payload s`, runs `reduce_with_fuel … APPLY_FUEL`. Hand `applyCommand` =
`(reduceWithFuel (app payload s) applyFuel).1`, and `APPLY_FUEL = 1024#u32` matches
`applyFuel = 1024` (both confirmed). So:

```
decTm <$> rsm.apply_command c s
  = decTm <$> (reduce_with_fuel (App (clone c.payload) (clone s)) 1024).fst-ish
  = (R2.3c) reduceWithFuel (decTm (App c.payload s)) 1024 |>.1
  = reduceWithFuel (app (decTm c.payload) (decTm s)) 1024 |>.1
  = DLCD.applyCommand (decCmd decTm decPr c) (decTm s)          ✔
```

Needs `App` decode to commute (`rfl`) and `decCmd`'s `.payload = decTm c.payload` (`rfl`). Closes
`AppCommandRefines decTm decPr` under the `WellScopedTm'` fence. **Small.**

**`ApplyPreservesWS`:** the reduct of a fenced store under a fenced command is fenced. This is the
**preservation companion** and rides alongside R2.3a/b/c:

```
shift_preserves_closed  : ClosedAbove t k → ClosedAbove (DLC.shift t d c) (k+d)     -- EXISTS: DerivClosed.closedAbove_shift
substAt_preserves_closed: ClosedAbove body (k+1) → ClosedAbove value k → ClosedAbove (DLC.substAt body value depth) k   -- NEW companion to R2.3a
step_preserves_closed   : ClosedAbove (decTm t) 0 → step (decTm t) = some t' → ClosedAbove t' 0   -- NEW companion to R2.3b
reduceWithFuel_preserves_closed : … by fuel induction, companion to R2.3c
```

Plus a `heightB`-preservation (height does not increase under β/subst — or, more cheaply, re-derive
the height bound of the reduct from closedness + a coarse size bound; ruling #2). Then
`ApplyPreservesWS` follows: the reduct stays closed (hence `ClosedAbove … 0`) and height-bounded,
so `WellScopedTm'` holds. **Reuses `closedAbove_shift`; the subst/step preservation lemmas are the
standard de Bruijn results and are the genuine new labor here.**

**Risk/cost:** LOW-MEDIUM for the assembly; the preservation companion is MEDIUM (standard but
must be proved, ~150-250 lines) — and its DIFFICULTY DEPENDS ENTIRELY on ruling #1 (if the fence
stays flat `WellScopedTm`, preservation is likely FALSE; if it becomes closedness, it is standard).

---

## §3. The `U32`/`I32`/`I64` ↔ `Nat` treatment (the honest soundness content)

The hand model is pure `Nat`; the generated model is machine-integer. Faithfulness has three
arithmetic sites, each discharged by `scalar_tac`/`bv_tac` under the fence:

1. **`shift`/`Var` (the only genuinely subtle one).** Generated: `i:U32 → hcast .I64 → + (delta:I32 as I64) → check ≥ 0 → hcast .U32`. Hand: `i + delta` in `Nat`.
   - `hcast .I64 i` always succeeds (`U32.max = 2^32-1 < I64.max`); `i.val` unchanged.
   - `delta ≥ 0` (established: shift's *only* caller is `subst_at`'s eq-arm with `delta = I32(depth)`,
     `depth ≥ 0`) ⇒ `shifted = i + delta ≥ 0`, the `< 0` branch is **dead** (matches hand having no
     such branch — the hand `shift` is monotone-up only).
   - `hcast .U32 shifted` succeeds iff `shifted.val < 2^32`. Fence gives `i.val < 2^31` (or, under
     closedness, `i.val ≤ depth`) and `delta = depth < 2^31`, so `shifted.val < 2^32`. ✔ And then
     `(hcast .U32 shifted).val = i.val + delta.toNat`, the decode of the hand result.
2. **`subst_at`/`Var` `eq` cast `hcast .I32 depth`.** Succeeds iff `depth < 2^31` — the
   binder-depth bound, supplied by `heightB t < 2^31` (⇒ `depth ≤ 2·height < 2^31`). This is
   precisely why flat `WellScopedTm` is insufficient (§1.2 finding).
3. **binder-bump `cutoff/depth + k#u32` (`k ∈ {1,2}`) and `subst_at`/`Var` `gt` `i - 1#u32`.**
   The `+k` cannot overflow given `depth < 2^31` (`scalar_tac`); the `-1` cannot underflow because
   the `gt` guard gives `i > depth ≥ 0 ⇒ i ≥ 1` (`scalar_tac`). Both `.val`-equal the hand `Nat`
   `+k` / `-1`.

**Decode of scalars:** `U32.val → Nat` at every `Var i`, obligation/label/atom index. `decLab` is
representation-identity on `ifc.Label` (nucleus's `CapabilityLattice`). The honest soundness
statement: *the machine-integer reducer computes the same de Bruijn term as the `Nat` model,
provided indices and binder depth stay below `2^31` — a bound the fence makes explicit and
decidable, and which every RSM input satisfies with astronomical headroom.*

---

## §4. The no-`.fail` argument + how `ApplyPreservesWS` is proved

**No-fail.** Every `.fail` in the generated core arises from exactly the arithmetic sites in §3
(a `hcast`/`+`/`-` overflow) — `clone`s are total (`termClone_id` = always `ok`), the range
iterator is total, `OrdU32.cmp` is total. Since the fence discharges every arithmetic obligation
(§3.1-3.3), no site fails. This is folded into the `= Result.ok …` form of every R2.3a/b/c lemma:
proving the map-equation *is* proving no-fail (a `.fail`/`.div` LHS could never equal `.ok`,
cf. the existing `map_ok_inv`). So no separate no-fail theorem is needed — it is a corollary of
each correspondence lemma's `ok`-shape.

Note `partial_fixpoint` also admits `.div` (non-termination) as a value; the loop is bounded by
`fuel` iterations so the *loop* is div-free, and `step`/`subst` are structurally decreasing on the
term so their `partial_fixpoint` unfoldings terminate on every concrete term — `.div` never arises
on closed inputs. The `= ok` shape rules out `.div` exactly as it rules out `.fail`.

**`ApplyPreservesWS`** (see R2.3d). Proved by the preservation companion running alongside
R2.3a/b/c: `closedAbove_shift` (in-tree) + new `substAt_preserves_closed` + `step_preserves_closed`
+ `reduceWithFuel_preserves_closed`, giving closedness of the reduct; plus height-bound
preservation. **This is a companion induction to R2.3b/c, not a separate arc.** Its viability is
entirely gated on ruling #1 (closedness fence vs flat fence).

---

## §5. Honest cost table + riskiest step

| Sub-inc | What | Est. lines | Risk | Reused in-tree |
|--------|------|-----------|------|----------------|
| R2.3a | subst/shift correspondence (`shift_corr`, `substAt_corr`, `subst_corr`) | 250-450 | **HIGH** | `termClone_id` family; `bind_tc_ok` |
| R2.3b | single-step correspondence (`step_corr`) | 300-500 | MED-HIGH | R2.3a; `termClone_id`; head-fan-out helper |
| R2.3c | fuel-loop correspondence (`reduce_loop_spec`, `reduce_with_fuel_corr`) | 120-200 | MEDIUM | `loop_cont`/`loop_fin`/`next_*` idiom (proven ×2) |
| R2.3d | assemble `AppCommandRefines`; preservation companion → `ApplyPreservesWS` | 200-350 | MED (gated on ruling #1) | `closedAbove_shift` (DerivClosed) |
| **Total** | | **~900-1500** | | |

Against Grove's 12× proof:code this is favorable: the subst/step Rust is ~200 LOC, so 900-1500
Lean lines is ~5-7×, better than 12× **because the hand model is a deliberate mirror of the Rust**
— the correspondence is homomorphic, not a semantic gap.

**Single riskiest step: R2.3a subst/shift faithfulness** (tied with the R2.3d preservation companion
it feeds). Everything else routes through it, and it carries all the `U32`/`I32`/`I64`↔`Nat`
arithmetic. If the fence question (ruling #1) resolves wrong, the preservation half of R2.3d could
be *unprovable* (flat `WellScopedTm` is not shift-stable) — that is the failure mode that turns
R2.3 from ~1200 lines into a re-litigation of the landed squares.

**What could force this much larger:**
- If ruling #1 forces redefining `WellScopedTm` and the landed squares turn out to *inspect* (not
  merely assume) the predicate's shape, all four squares + their witnesses need re-proof (+400-600 lines).
- If the generated `partial_fixpoint` functional-induction principles for `subst.shift`/`reduce.step`
  are unusable as-emitted (a known Aeneas rough edge for deeply-nested monadic matches — cf. the
  lean4 equational-lemmas RFC), the arms must be driven by manual `loop`/`unfold`-style equational
  rewriting like the witness `apply_command_dup` does — multiplying R2.3a/b line count 2-3×.
- If the App/Delegate head fan-out cannot be collapsed by a single helper (26 arms × 2 forms), R2.3b
  balloons.

---

## §6. OPEN QUESTIONS needing a ruling (I did not decide these)

1. **The fence: strengthen `WellScopedTm` to closedness, or keep it flat?** My analysis (§1.2, §4)
   says the flat index-bound `WellScopedTm` is (a) insufficient for no-fail (misses the `I32` depth
   cast → needs an AST-height bound) and (b) **not preserved by `shift`** (so `ApplyPreservesWS` is
   likely *false* as currently fenced). The honest fix is `WellScopedTm' := ClosedAbove (decTm t) 0
   ∧ heightB t < 2^31`, reusing `DerivClosed.ClosedAbove`. **This changes the predicate the four
   landed squares assume.** The squares only *consume* `WellScopedTm` hypotheses (they never
   destruct it), so strengthening should be monotone and non-breaking — but I have not re-verified
   that, and it touches governed, byte-frozen theorems. Ruling needed: (a) redefine `WellScopedTm`
   in place and re-verify the squares; (b) introduce `WellScopedTm'` as a *separate* predicate and
   prove `WellScopedTm' → WellScopedTm` so the squares are invoked at the stronger fence without
   editing them (my lean: **(b)** — zero-touch to the landed squares, closedness lives only in R2.3);
   or (c) something else. This is the highest-leverage decision.

2. **Height-bound: decidable `heightB < 2^31`, or derive depth-bound another way?** The `I32`
   depth-cast needs `depth < 2^31`. Cleanest is a decidable `heightB t < 2^31` conjunct. Alternative:
   carry an explicit `depth < 2^31` hypothesis threaded through the subst recursion (no height
   predicate, but pollutes every lemma signature). Ruling: add the height conjunct to the fence, or
   thread a depth bound?

3. **Fuel-mismatch in the discarded second component — confirm we may ignore it.** Aeneas
   `reduce_with_fuel` returns `(term, range-index-at-stop-or-fuel)`; hand `reduceWithFuel` returns
   `(term, steps-actually-taken)`. These second components **differ** but are both discarded by
   `apply_command` / `applyCommand.1`. R2.3 as designed proves correspondence of the FIRST component
   only. Confirm this is acceptable (I believe it is — nothing downstream reads the count), or do you
   want a bonus lemma relating the counts (materially more work, no consumer)?

4. **Witness compatibility.** Should the existing `appCommandRefines_witness`/`applyPreservesWS_witness`
   (stated against `decTm₀`) be (a) kept, with a `decTm ∘ fragment = decTm₀` compatibility lemma, or
   (b) restated against the full `decTm`? I lean (b) (one source of truth), but (a) preserves the
   frozen witness bytes.

5. **`partial_fixpoint` proof driver.** Proceed assuming `fun_induction` works on the emitted
   `subst.*`/`reduce.step`; if it does not, fall back to manual equational unfolding (the
   `apply_command_dup` style). Do you want R2.3a to first *spike* `fun_induction` on `subst.shift`
   (cheap, de-risks the whole arc) before committing to the full decomposition?

---

## Appendix — exact file:line anchors (verified against HEAD 3ea4c32)

**CODE side** (`lean/DLC/Aeneas/DlcCore/Funs.lean`, `partial_fixpoint`, do NOT `rfl`-reduce):
- `subst.shift` — 2790 (Var/I64 arm 2795-2805; binder bumps `+1` 2808/2836/2900, `+2` 2894)
- `subst.subst_at` — 2919 (Var trichotomy `OrdU32.cmp` 2924-2932; eq-arm `hcast .I32 depth; shift` 2929-2930)
- `subst.subst` — 3047 (= `subst_at body value 0#u32`)
- `reduce.step` — 3054 (App head fan-out via `Box…as_ref` from 3058; Lam→`subst.subst` 3068; Delegate 187-rel…)
- `reduce.reduce_with_fuel_loop.body` — 4791 (range `next`; `done`/`cont` on `step`)
- `reduce.reduce_with_fuel_loop` — 4810 (`loop` combinator)
- `reduce.reduce_with_fuel` — 4821 (clones term, loops `[0,fuel) fuel`)
- `rsm.apply_command` — 6114 (clones payload+store, `reduce_with_fuel (App …) APPLY_FUEL`, discards count)
- `rsm.APPLY_FUEL` — 4943 (`= 1024#u32`)

**HAND side:**
- `DLC.shift` — `lean/DLC/Subst.lean:23`; `DLC.substAt` — 80; `DLC.subst` — 140
- existing subst metatheory (reusable): `shift_zero` 187, `shift_shift_comm` 262, `shift_shift_merge`
  381, `shift_substAt_commute` 499, `substAt_shift_cancel` 632, `substAt_substAt` 748
- `DLC.step` — `lean/DLC/Reduce.lean:27` (11 elim arms + values); `DLC.reduceWithFuel` — 173 (Nat fuel)
- `DLC.ReduceMeta` — `lean/DLC/ReduceMeta.lean` (Steps/determinism/Joinable — reuse for confluence-adjacent needs)
- **closedness metatheory (reuse for preservation):** `DLC.ClosedAbove`, `closedAbove_mono` 28,
  `closedAbove_shift` 36, `deriv_closedAbove` 186 — `lean/DLC/DerivClosed.lean`
- `DLCD.applyCommand` — `lean/DLCD/Rsm.lean:161` (`= (reduceWithFuel (app payload s) applyFuel).1`);
  `applyFuel` 155 (`= 1024`); `applyPrefix` 166; `deliver` 172; `worldStep` 181

**No existing Aeneas↔hand bridge for subst/step/reduce** — `function_correspondence_subst` appears
only as a to-do comment (`Subst.lean:12`); R2.3 is net-new.

**Decode/obligation targets** (`lean/DLCD/Correspondence.lean`): `DecTm`/`DecPr` seam 79-81;
`WellScopedTm`/`wsTermB` 259-288; `AppCommandRefines` 301; `ApplyPreservesWS` 610; fragment decode
`decTm₀`/`decPr₀` 315-326; witnesses 427/619.
