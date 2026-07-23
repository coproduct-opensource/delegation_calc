# R2-inc3c — the fuel-loop correspondence: is `AppCommandRefines` provable as stated?

**Status:** ANALYSIS + design pass. No implementation. Nothing merged. Author decides.
**Scope:** whether `reduce_with_fuel_corr`'s discharge of `AppCommandRefines`
(`lean/DLCD/Correspondence.lean:407`) is achievable AS STATED, and if not the minimal honest fix —
*before* grinding `reduce_with_fuel_corr`.
**Investigated at:** worktree `agent-a00952ea8a0697fd1` (branch `worktree-agent-…`, HEAD `690bb39`);
the DLC-D sources read live from the shared `dlc-d/phase0-carve` checkout
(`/Users/bcrisp/coproduct/delegation_calc/lean/DLCD/…`). The task named branch `dlc-d/phase0-carve`
HEAD `3777cda`; the read tree is a few commits along, the finding is unchanged. Toolchain Lean 4.31.0
(Aeneas `Std` pinned under `lean/.lake/packages/aeneas`).

---

## 0. VERDICT (one line)

**`AppCommandRefines` is FALSE as stated** — the `= Result.ok …` shape asserts *no-fail over the whole
1024-step fuel loop*, and no-fail is not a theorem: a closed, `WellScopedTm` payload/store whose
β-reduction grows binder-depth past the `U32` ceiling makes `reduce_with_fuel` genuinely `.fail`, so
`LHS = .fail ≠ .ok`. The prompt's *intuition* (no-fail cannot hold over the loop) is CORRECT. Its
*mechanism* is wrong on two counts (see §2), and — decisively — **no machine-checkable counterexample
exists** (any witness term has ≥ 2³¹ nodes; it cannot be built or evaluated). The refutation is a
paper argument, not an R2.3b-style landed witness.

**Recommendation:** adopt **fix (i) in its partial-correctness form** — condition the refinement on the
generated reducer *returning `ok`* and drop the no-fail claim. It is honest, is provable from
closedness-preservation *alone* (no height fence, no growth bound), matches Aeneas idiom, and turns
R2.4 G1–G4 into "for executions in which the bounded reducer does not overflow" — a class the existing
anti-vacuity witnesses already inhabit on the real store-transformer payloads. Confidence **HIGH**.

---

## 1. What the obligation actually claims, and where it must be discharged

```lean
-- lean/DLCD/Correspondence.lean:407
def AppCommandRefines (decTm : DecTm) (decPr : DecPr) : Prop :=
  ∀ (c : rsm.Command) (s : syntax.Term),
    WellScopedTm s → WellScopedTm c.payload →
    (decTm <$> rsm.apply_command c s)
      = Result.ok (DLCD.applyCommand (decCmd decTm decPr c) (decTm s))
```
`rsm.apply_command c s = (reduce_with_fuel (App c.payload s) 1024).1` (Funs.lean:6507; `APPLY_FUEL = 1024`,
`applyFuel = 1024` — confirmed equal). `WellScopedTm t := ClosedAbove (decTermC t) 0 ∧ heightB t < 2³¹`
(`:393`).

`decTm <$> _ = Result.ok _` forces the `Result` on the left to be `.ok` — i.e. the equation *encodes
no-fail* over the full loop. `map_ok_inv` (`:540`) and §4 of the design memo
(`spec/r2-inc3-reducer-correspondence-design.md:349`) make this explicit: "proving the map-equation
*is* proving no-fail." So the obligation is (value-refinement) ∧ (no-fail-over-1024-steps), conjoined.

**Where R2.3 must discharge it:** `reduce_with_fuel_corr` (R2.3c), by iterating the *already-landed*
`step_corr` (R2.3b, `:2751`) across the loop via the `loop`/`ControlFlow` accumulator idiom. `step_corr`
is genuinely proven, `sorry`-free:
```lean
theorem step_corr : ∀ (t : syntax.Term), WellScopedTm t →
    Option.map decTermC <$> reduce.step t = ok (DLC.step (decTermC t))
```
Note its premise: **`WellScopedTm t`** — closed *and* `heightB t < 2³¹`. To iterate it across the loop
you need `WellScopedTm` to hold at *every* intermediate reduct. That invariant is where R2.3c lives —
and where it breaks.

---

## 2. The prompt's mechanism is wrong twice; the genuine failure is worse

The prompt's worry: `subst.subst_at`'s `hcast .I32 depth` / `U32` index arithmetic *overflows → `.fail`*
once β grows depth past 2³¹.

### 2a. The casts do **not** fail — they truncate (THE decisive fact)

`lean/.lake/packages/aeneas/backends/lean/Aeneas/Std/Scalar/Casts.lean:16-42`:
```lean
def UScalar.cast  (tgt) (x) : UScalar tgt := ⟨ x.bv.zeroExtend tgt.numBits ⟩
def UScalar.hcast (tgt) (x) : IScalar tgt := ⟨ x.bv.zeroExtend tgt.numBits ⟩   -- u32 → i32
def IScalar.cast  (tgt) (x) : IScalar tgt := ⟨ x.bv.signExtend tgt.numBits ⟩
def IScalar.hcast (tgt) (x) : UScalar tgt := ⟨ x.bv.signExtend tgt.numBits ⟩   -- i64 → u32
```
Every cast is a **total** `BitVec` truncation/extension returning a *bare* scalar — never a `Result`.
In the generated body they are wrapped `let i1 ← lift (UScalar.hcast .I32 depth)` (Funs.lean:2929);
`lift` of a pure value is `ok`, so **the cast never `.fail`s** — it faithfully models Rust's `as`, which
truncates and never panics. At `depth ≥ 2³¹` it silently *wraps* `depth` to a negative `i32`; it does
not fail. So the prompt's "`hcast → .fail`" path does not exist.

### 2b. …and even the *wrapped value* is harmless (closedness neutralises it)

The `hcast .I32 depth` feeds `subst.shift value (hcast .I32 depth) 0` in the `Ordering.eq` arm
(Funs.lean:2929-2930). But during reduction of a closed redex `(λ.body) arg`, the substituted `value`
(= `arg`) is `ClosedAbove … 0`. `shift_id_closed` (`:1477`) proves `subst.shift value δ 0 = ok value`
for a *closed* `value` **regardless of `δ`** — the `if i < cutoff` arm always fires, the index-moving
branch is dead. The landed `step_corr` already uses exactly this: it passes the (possibly-wrapped)
`UScalar.hcast .I32 depth` straight into `shift_id_closed` (Correspondence.lean tail, ~:1748). So the
`eq`-arm cast is *value-irrelevant*: generated = hand here even at `depth ≥ 2³¹`. The design memo's §3.2
(`…:328`) is imprecise on this point — it treats the cast as fallible; it is total, and closedness makes
its result moot.

### 2c. The one genuine `.fail`: the `depth + 1#u32` binder bump

The only reduce-internal `.fail` reachable under the closed fence is the **binder-depth bump**
`let i ← depth + 1#u32` (Funs.lean:2935 in `subst_at`; twin `cutoff + 1#u32` in `shift`, Funs.lean:2808).
`U32` addition is fallible and overflows when `depth = U32.max = 2³²−1`. Every other arithmetic site is
safe on closed terms: the `Var/gt` case `i - 1#u32` cannot underflow (`i > depth ≥ 0 ⇒ i ≥ 1`), the
`I64` add `i1 + i2` in `shift` cannot overflow (`u32 + i32 ⊂ i64`), the range iterator runs `0..1024`.

**Consequences that sharpen the prompt:**
- The failing threshold is **2³² (U32 add), not 2³¹**. In the window `depth ∈ [2³¹, 2³²)` the reducer
  still returns `ok` *and still matches the hand model* (casts wrapped-but-neutralised, bumps not yet
  overflowing). The break is a hard `.fail` at `depth = 2³²−1`.
- Because value-correctness rides on **closedness only** (2b), there is *no silent value-mismatch* on
  closed inputs: the generated reducer either matches the hand `Nat` model exactly, or it `.fail`s.
  (The hand model is unbounded — `DLC.Term.var : Nat`, `DLC.shift … : Term → Nat → Nat → Term`,
  `i + delta` on `Nat`; `lean/DLC/Syntax.lean:60`, `lean/DLC/Subst.lean:23-25`.)

So the honest statement of the defect: **`reduce_with_fuel` is a partial function of its input; it
`.fail`s exactly when reduction drives binder-nesting depth to `U32.max`, and `WellScopedTm` bounds only
the *initial* depth, not the mid-reduction depth.**

---

## 3. Why the fence is not loop-invariant (the real R2.3c wall)

`step_corr` needs `WellScopedTm cur` (⇒ `heightB cur < 2³¹` ⇒ `depthB cur ≤ 2·heightB < 2³²`,
via `depthB_le_2heightB`, `:1467`) at each iterate to keep the bumps from overflowing. The loop invariant
`Fence cur` is preserved iff **`heightB`/`depthB` do not cross the ceiling under β**. They do:

- **`heightB` grows multiplicatively.** The landed R2.3b docstring says it outright
  (Correspondence.lean:1413-1418): "`heightB` … grows MULTIPLICATIVELY under substitution
  (`heightB (subst body v) ≤ (heightB body + 1)(heightB v + 1)`) … that intermediate can reach ~2⁶⁰."
- **`depthB` (the composable metric introduced precisely to dodge the `heightB` blow-up) still
  at-most-DOUBLES per β-step.** It is only *subadditive*: `depthB (subst body v) ≤ depthB body + depthB v`
  (docstring `:1425`). Under `(λ.body) arg → subst(body,arg)`, both `depthB body` and `depthB arg` are
  `≤ depthB(redex)`, so `depthB(reduct) ≤ 2·depthB(redex)`. Subadditivity tames a *single* nested
  `LetTensor` substitution (its intended job); it does **not** tame *iterated* β down the fuel loop.

Since one β-step can double binder-depth, over the loop `depthB` can reach `depthB(init)·2^k`. From an
initial term at the fence ceiling (`heightB` just under 2³¹ — permitted), a couple of doubling steps
cross 2³², triggering the `depth+1#u32` `.fail`. **The invariant R2.3c needs is false.**

### The design memo already contains the contradiction

`spec/r2-inc3-reducer-correspondence-design.md` scopes R2.3c to lean on a preservation companion:
- `:264` — "**Fence preservation of `next`** … feeds the IH."
- `:303` — "Plus a **`heightB`-preservation (height does not increase under β/subst)** — or, more
  cheaply, re-derive the height bound of the reduct from closedness + a coarse size bound."
- `:311` — "if the fence stays flat `WellScopedTm`, **preservation is likely FALSE**."

"Height does not increase under β/subst" directly contradicts the same author's landed R2.3b docstring
("grows MULTIPLICATIVELY … ~2⁶⁰"). The "coarse size bound" fallback also fails — β can grow term size
exponentially, so no size bound survives the loop. The current landed fence *is* flat `WellScopedTm`, so
by the memo's own §R2.3d hedge the preservation lemma is "likely FALSE." This analysis confirms it: it is
false, and R2.3c cannot be closed in the `= ok` shape it is written in.

---

## 4. Is the RSM's *actual* command shape safe? (yes — the obligation is only wrong on paper)

The real payloads are `φ ⊃ φ` store-transformers that β-reduce in O(1) steps with **no** depth growth:
- `dupGenW = λ_. ⟨var0, var0⟩` (Correspondence.lean:423): one β-step to `⟨s,s⟩`; `depthB` stays ≤ 2.
  The additive pair `⟨,⟩` *shares* its argument — it duplicates a leaf, it does not nest binders.
- `apply_command_dup` (`:476`) computes the whole loop to `ok pair00W` in two iterations by hand; the
  anti-vacuity witnesses `appCommandRefines_witness` (`:514`) and `applyPreservesWS_witness` (`:706`)
  land the consequent on real state-changing inputs, `sorry`/`native_decide`-free.

**The overflow class:** payloads that, applied to a store, drive a *duplicator down a growing spine* —
Church-numeral towers `two two two …` (`two = λf.λx. f (f x)`) are closed DLC terms (`Lam/App/Var` only,
so DLC's β + app-congruence reduces them exactly as standard CBN λ-calculus) whose CBN reduction sequence
has unbounded height. These are exactly the payloads the RSM never issues but the *universally quantified*
`WellScopedTm` obligation still ranges over. So the gap is **spec-completeness / honest-conditioning**, not
a live soundness hole in the deployed transition — mirroring the `says-E` finding of inc3b: the statement
overclaims relative to the deployed use.

---

## 5. No machine-checked counterexample is possible (and why that matters)

An end-to-end `reduce_with_fuel (App payload s) 1024 = .fail` witness requires the reducer to actually
*reach* binder-depth `2³²−1`. Any term at that depth has ≥ 2³² constructor nodes on a single spine
(≈ tens of GB); the redex feeding it has ≥ 2³¹ nodes even at the `heightB`-doubling shortcut from the
fence ceiling. **The witnessing term cannot be constructed or evaluated in Lean** (kernel or `#eval`).
The value-mismatch route is *closed off entirely* (§2b), so there is not even a *small* wrong-value
witness. This is a substantive finding: **the R2.3b-style "land the refutation as a witness" move is
unavailable here** — the falseness is real but non-finitely-manifestable. I did **not** build a
counterexample; doing so is physically infeasible, not merely expensive. The `.fail` *site* itself
(`depth + 1#u32` at `U32.max`; casts total-truncating) is certain by inspection of Casts.lean +
Funs.lean and needs no build.

---

## 6. The three fixes, evaluated

### Fix (i) — condition the refinement on success (RECOMMENDED)

Two equivalent honest framings; the **partial-correctness** one is cleanest:

```lean
-- reframed obligation: match-on-success, no-fail NOT claimed
def AppCommandRefines' (decTm) (decPr) : Prop :=
  ∀ (c) (s) (t), WellScopedTm s → WellScopedTm c.payload →
    rsm.apply_command c s = Result.ok t →
    decTm t = DLCD.applyCommand (decCmd decTm decPr c) (decTm s)
```
(equivalently, keep the `= ok` shape but add a hypothesis `hok : rsm.apply_command c s ≠ .fail`).

**Why it is provable — and provable *without any height fence*.** If the whole loop returns `ok t`, then
every intermediate `reduce.step` returned `ok _` (no `U32` bump overflowed anywhere along the way — that
is *given*, not proved). Value-correctness then rides on **closedness alone**:
- closedness is preserved along the loop (`closedAbove_shift` EXISTS in `DerivClosed.lean:36`; the
  `substAt`/`step` closedness companions are the standard de-Bruijn results, `:298-300` of the design
  memo);
- on closed terms every cast is dead-branch or identity-neutralised (§2b), so each *successful* step's
  decoded value equals the hand step.
Concretely, refactor the landed lemmas to *success-conditioned* variants:
`subst.shift t δ c = ok r → ClosedAbove (decTermC t) c.val → r = t` (drops the `heightB` fence — success
discharges the bumps); likewise a success-conditioned `step_corr`
(`reduce.step t = ok r → ClosedAbove (decTermC t) 0 → Option.map decTermC r = DLC.step (decTermC t)`).
These reuse the *existing* per-form case analysis with the arithmetic obligations discharged *from the
`ok` hypothesis* instead of from `scalar_tac + fence`. `reduce_with_fuel_corr'` then iterates the
success-conditioned `step_corr` under the closedness invariant (no height invariant needed → nothing
false to prove).

**Cascade to the 6 squares + R2.4.** The reducer-routed squares — `deliver_square` (`:550`),
`world_step_square` (`:671`), `apply_prefix_square` (`:787`), and the two loop specs — currently *consume*
`hcmd : AppCommandRefines` via `map_ok_inv happly` to turn a generated `apply_command` into `ok _ ∧ decode`.
Their *conclusions* `decode <$> generated = ok (hand)` themselves assert no-fail, so they inherit the same
weakening: either
  (a) conclusions become `generated = ok g' → decode g' = hand` (partial squares), or
  (b) each square gains a premise "every `apply_command` in this step returns `ok`" (a per-input
      no-overflow hypothesis threaded through the fold/map).
`commit_square` (`:804`) routes through no reducer — unchanged. The consensus squares in
`CorrespondenceConsensus.lean` carry no `hcmd` — unchanged. **R2.4 G1–G4** then read: *for executions in
which the RSM's bounded reducer does not overflow (returns `ok`), the generated distributed transitions
refine the model, hence convergence / NI / linearizability / termination hold of the Rust artifact.* The
no-overflow side-condition is discharged in practice by §4 (real payloads return `ok` in ≤ a few steps;
the anti-vacuity witnesses prove it on the concrete `dup`).

Cost: MEDIUM. Reuses all landed case-work; the labor is the success-conditioned re-statement of
`shift`/`substAt`/`step` corr (mechanical) + closedness preservation (standard) + weakening the four
reducer squares. Nothing false is attempted.

### Fix (ii) — a stronger *static* depth fence (REJECT as proposed; essentially vacuous if made sound)

The prompt's candidate `depthB s + 1024·maxArgDepth < 2³¹` assumes **additive** growth. Growth is
**geometric** (§3: `depthB` at-most-doubles per β-step; `heightB` is multiplicative). A duplicating
payload blows past any linear `+1024·maxArgDepth` bound within a handful of steps, so this fence does
**not** bound the loop — it is *unsound* (states a false invariant). The only *sound* static bound over
1024 steps is of the form `depthB(init)·2^1024 < 2³²`, which forces `depthB(init) = 0` — payloads with no
binders, which cannot β-reduce at all. So a sound static depth fence is vacuous/unusable. Reject.

### Fix (iii) — restrict to the RSM store-transformer shape / to *typed* payloads (viable, heavier)

Narrow the obligation to a class `C` of payloads for which no-fail provably holds, keeping the strong
`= ok` conclusions on `C`. The principled `C` is **typability**: require a `CDeriv Γ payload (φ⊃φ)`
witness. DLC is substructural (linear/DILL); well-typed terms are strongly normalising and linearity
forbids the structural duplication that drives depth-explosion (additive `⟨,⟩` *shares*, it does not
nest). Typed ⟹ bounded reduction ⟹ no-fail, so the `= ok` form is recoverable on `C`. Cost: this couples
the operational layer to typing, which `dlc_core::rsm` deliberately keeps opaque (the `cap` slot is
Phase-1.0 abstract; `Rsm.lean:54-60`, CLAUDE.md). A real strong-normalisation-with-bounded-height proof
for DLC is a large increment. Best positioned as the *eventual* upgrade if an unconditional no-fail
guarantee is ever wanted; **(i) is the right move now**, and (iii) can layer on top later (a typed payload
is one that provably never triggers (i)'s overflow escape hatch).

---

## 7. `reduce_with_fuel_corr` structure sketch (for fix (i))

```lean
-- second components (step counts) are discarded both sides: rsm.apply_command binds
-- `let (t2, _) ← reduce_with_fuel …`; hand `applyCommand … = (reduceWithFuel …).1`.
-- So the loop corr reconciles the FINAL TERM only.

theorem reduce_loop_spec :
  ∀ (rem : Nat) (k : Std.U32) (cur : syntax.Term) (t : syntax.Term),
    DLC.ClosedAbove (decTermC cur) 0 →                 -- invariant: closedness ONLY
    k.val + rem = fuel.val →
    reduce.reduce_with_fuel_loop {start := k, «end» := fuel} fuel cur = ok (t, _) →   -- success given
    decTermC t = (DLC.reduceWithFuel (decTermC cur) rem).1
```
Induction on `rem` (the `loop`/`ControlFlow` accumulator idiom, third in-tree instance after
`world_step_loop_spec` / `apply_prefix_loop_spec`; reuse `loop_cont`/`loop_fin`/`next_succ`/`next_done`,
`U32` variants trivially added):
- `rem = 0` (`k = fuel`): `next` → `none` → `done (cur, fuel)`; hand `reduceWithFuel _ 0 = (cur,0)`.
  Both `.1 = decTermC cur`.
- `rem = m+1`: `next` → `some k`, then `reduce.step cur`. From the *success* hypothesis on the outer
  loop, this inner `step` returned `ok _`, and the loop recursed on its `ok` result:
  - `step cur = ok none` (normal form): `done (cur, k)`; success-conditioned `step_corr` gives
    `DLC.step (decTermC cur) = none`, hand `(cur,0)`, `.1 = decTermC cur`. ✔
  - `step cur = ok (some next)`: `cont (iter1, next)`; success-conditioned `step_corr` gives
    `decTermC next = DLC.step (decTermC cur)`; **closedness of `next`** (from `step_preserves_closed`,
    NOT a height fence) feeds the IH at fuel `m`. ✔
- Wrapper: `reduce_with_fuel` prepends a `clone` (`termClone_id`, total); `App` decode commutes (`rfl`);
  `decCmd`'s `.payload = decTermC c.payload` (`rfl`). Assemble `AppCommandRefines'`.

Key contrast with the design memo's sketch: the invariant is **closedness only**; there is no
`heightB`/`depthB`/fence-preservation lemma (that lemma is false), and no-fail is a *hypothesis fed by
the outer success*, not a conclusion proved from a fence.

---

## 8. Recommendation, confidence, the single decisive fact

**Recommendation:** reframe `AppCommandRefines` (and the four reducer-routed squares, and R2.4 G1–G4)
per **fix (i)** — refinement conditioned on the bounded reducer returning `ok`; no-fail explicitly *not*
claimed. Keep the strong-`= ok` witnesses (`appCommandRefines_witness`, `applyPreservesWS_witness`) as
the *satisfiability* anchors; they show the consequent is achieved on real payloads. Optionally note
fix (iii)/typing as the future unconditional-no-fail upgrade.

**Confidence:** HIGH that `AppCommandRefines` is false as stated and that fix (i) is both honest and
provable from closedness alone. Residual uncertainty is only quantitative-and-immaterial: whether a
*concrete* overflowing term crosses 2³² in ≤ 1024 steps (it does in principle — `heightB` doubling from
the fence ceiling needs ≤ ~2 steps; Church towers give unbounded height with `Lam/App/Var` only) — but
this does not change the verdict, and no concrete witness is buildable regardless (§5).

**The single decisive fact:** the Aeneas integer casts `UScalar.hcast`/`IScalar.hcast` are **total,
truncating** `BitVec` operations (`⟨x.bv.zeroExtend/​signExtend …⟩`, `Casts.lean:16-42`), never
`Result`s — so the reducer's *only* `.fail` site is the `depth + 1#u32` binder-depth bump (overflow at
`depth = 2³²−1`, Funs.lean:2935), and its operand `depth` is **not bounded across the fuel loop** because
β-reduction at-most-*doubles* binder-depth per step. Hence unconditional no-fail is not a theorem, while
partial correctness (match-on-success) is — carried by closedness-preservation, with the height fence
irrelevant.

---

## Appendix — web prior-art (mandate)

Web-search budget for this session was **exhausted (200/200)** before the targeted queries could run; a
single Aeneas-overview query completed. Recorded:
- Aeneas: Rust Verification by Functional Translation — https://arxiv.org/abs/2206.07185 ;
  ACM DOI https://dl.acm.org/doi/10.1145/3547647 ; repo https://github.com/AeneasVerif/aeneas .
  (Establishes Aeneas' LLBC→pure-λ functional translation and the `Result`/`fail`/`div` monad in which
  the partial-correctness framing of fix (i) is the standard idiom.)

Prior-art queries deferred for a future iteration (budget permitting): "de Bruijn term-height growth under
β / bounded-fuel interpreters"; "no-fail modulo a runtime integer bound in Aeneas refinement proofs";
"verified interpreters bounding term-size growth". The relevant *in-tree* prior art
(`spec/r2-inc3-reducer-correspondence-design.md` §R2.3c/§3/§4, and the landed `world_step_loop_spec` /
`apply_prefix_loop_spec` loop-combinator proofs) is the load-bearing reference and is cited throughout.
