# The linear lever — design for extending the metatheory to full `Deriv`

> **SUPERSEDED IN PART (2026-07-20).** Rungs **L1 and L2 are retired** and
> the `{additive, linear}` context representation with them. L3a proved 26 of
> 28 cases over that representation and then failed on `tensorE` for a
> structural reason (linear binders consume zero de Bruijn slots while `shift`
> reserves two). See **[`carve-context-design-2026-07.md`](carve-context-design-2026-07.md)**
> for the replacement and the machine-checked validation. The L3b/L4/L5
> staging below still stands; only the representation changed.

**Controller tick #1 (autonomous, 2026-07-03).** The persona controller's Observe
step ranked `substitution_lemma` (full `Deriv`, linear cases) as the highest-leverage
open item: it is the shared root that unblocks **subject_reduction-full → T3-full,
T1-full, progress-full** — four theorems on one lever, exactly the abstraction the
rubric prizes. This doc is the design that must precede the proof, and it surfaces
the real blocker (below) the way `t3-two-run-design`'s FINDING did for T3.

Nothing here is proven; statuses live in `lean/theorem-status.json`.

## THE BLOCKER (2026-07-03): additive and linear variables share one de Bruijn space

`Deriv`'s two variable rules (`lean/DLC/Judgment.lean`):

```
varA : Γ.additive[i]? = some φ  →  Deriv Γ (Term.var i) φ
varL :                              Deriv {additive := Γₐ, linear := [φ]} (Term.var 0) φ
```

`Term.var 0` is therefore **ambiguous** — it can be `additive[0]` (via `varA`) *or*
the sole linear hypothesis (via `varL`). Additive (re-usable) and linear
(single-use) hypotheses are indexed into the *same* `Term.var` space, with
overlapping lookup. Consequences:

* **This is why the propositional fragment closed and full `Deriv` did not.**
  `PropDeriv` is **additive-only** (`Γₐ[i]?`, no linear context) — it never meets the
  overlap, so rungs 1–3c went through. Full `Deriv` mixes both, and the substitution
  lemma cannot even be *stated* cleanly: "substitute `N` for the variable at index
  `k`" is ill-posed when index `k` might be additive (duplicable — `N` must be usable
  in every premise) or linear (single-use — `N`'s own linear resources must route to
  exactly the one consuming premise, splitting the `Γ₁ ++ Γ₂`).
* It is the same wall behind T1-full, T4-multiset, and subject-reduction-full. Knock
  it down once; four theorems advance.

## The resolution: formalize the invariant the checker already enforces

The Rust `infer` / `decideLean` **already disambiguates**
(`crates/dlc-core/src/decide.rs`): a `var i` resolves to `additive[i]` when that
exists, and only *else* to the linear context. So there is an operative discipline —
**additive lookup takes precedence; linear variables live at indices beyond the
additive context** — that is merely not yet a Lean invariant. Making it one
(`CtxWellFormed`: linear hypotheses occupy `var` indices ≥ `additive.length`, never
colliding with an additive index) makes the substitution lemma well-posed **without a
syntax or wire-format change** — the cheaper of the two paths:

| path | cost | verdict |
|---|---|---|
| Separate syntax (`Term.lvar` / tagged linear index) | `Term` change → wire format → full spec→Tamarin→wire→code ceremony | rejected for now — too heavy, and the checker doesn't need it |
| **`CtxWellFormed` invariant (additive-first, linear-beyond)** | Lean-only; mirrors the shipped checker | **chosen** |

## Rung decomposition (the campaign, in dependency order)

- **L1 — disambiguation invariant.** `CtxWellFormed Γ`: `Γ.linear` occupies `var`
  indices `≥ Γ.additive.length`. Prove every `Deriv` rule preserves it (the split
  `Γ₁ ++ Γ₂` distributes the linear suffix). *Bounded; this is the next dispatch.*
  **Two binding constraints (from the D-review of this doc, PR #101):**
  (i) `varL` as written permits *nonempty* `Γₐ` — `var 0 → linear` even when
  `additive[0]` exists, which the checker does NOT honor. L1 must therefore
  actually **restrict** `varL` under the invariant (linear singleton only when it
  cannot collide with an additive index), not merely add an orthogonal predicate.
  (ii) `CtxWellFormed`'s additive-first lookup order must be **proven equivalent** to
  `decide.rs`'s (`additive.get` then linear-on-miss) — machine-checked, not asserted
  in prose — so "mirrors the shipped checker" is a theorem.
- **L2 — linear context split algebra.** The `++` bookkeeping every linear
  elimination uses (`impE`, `saysE`, `delegate`, `tensorE`, `boxI`/discharge):
  membership/partition/associativity over `Γ₁ ++ Γ₂`, and the "resources are
  consumed exactly once" accounting. Pure `List Prop'`; bounded.
> **L3 SCOPE CORRECTION (2026-07-20).** The description below says L3 "reuses
> that induction shape" from the proven `PropDeriv` result. Two things make
> that understate the work, both checked rather than assumed:
>
> 1. **There is no `Deriv`-level metatheory at all.** Every shift and
>    substitution lemma in the repo is `PropDeriv`-only
>    (`DLC/Decidability.lean`). L3 needs a `Deriv` shift lemma
>    (`deriv_shift`, additive weakening-in-the-middle) that does not exist,
>    exactly as `propDeriv_substAt_aux` needs `propDeriv_shift`. L3 therefore
>    splits: **L3a** = `deriv_shift`, **L3b** = `deriv_substAt_additive`.
>
> 2. **`Deriv` has 28 constructors; `PropDeriv` has 22.** The six extra are
>    `varL`, `weakenA`, `saysE`, `boxI`, `withinE`, `tensorE` — and two of
>    them sit precisely on the additive/linear boundary this lever is about,
>    so they cannot be mirrored from anything.
>
> **`weakenA` is a genuine obstruction, not a tedious case.** It concludes at
> `Ctx.consA φ' Γ`, i.e. it PREPENDS to the additive context. A
> middle-insertion statement of the form
>
>     Γfull = ⟨Γl ++ Γr, Λ⟩  →  Deriv ⟨Γl ++ Γm ++ Γr, Λ⟩ (shift M Γm.length Γl.length) φ
>
> forces `Γl ++ Γr = φ' :: Γ.additive` in that case, and the `Γl = []` branch
> then needs `Γm` inserted BEFORE `φ'` — which is not what the premise's IH
> provides. The statement shape and the rule shape disagree. Options, in
> rough order of preference:
>
> - restate L3a as END-insertion (`Γm` appended) and derive middle-insertion
>   from it plus exchange, if exchange is available for additive contexts;
> - prove `weakenA` ADMISSIBLE (derivable from `varA`'s index arithmetic) and
>   remove it from `Deriv`, which would also shrink every future induction;
> - carry a strengthened IH that quantifies over the insertion position.
>
> This is a design decision about `Deriv`'s presentation, not a proof tactic,
> and it should be settled before L3a is attempted. Recorded here rather than
> discovered again inside a half-written 28-case induction.
>
> **What IS confirmed to work:** the `varL` arithmetic, which is the case the
> L1 invariant exists for. `varL` concludes at `Term.var Γₐ.length`, so
> resizing the additive context moves the linear variable; inserting `Γm`
> makes the context length `Γₐ.length + Γm.length`, and
> `shift (var Γₐ.length) Γm.length Γl.length` fires (the index is at or above
> the cutoff) yielding exactly `var (Γₐ.length + Γm.length)`. Those agree
> ONLY because L1 restricted `varL` to `var(additive.length)`. Without L1
> this case would be false, not merely hard.

- **L3 — additive substitution preservation over full `Deriv`.** The *easier* half:
  an additive hypothesis is shared across all premises (same `Γₐ` everywhere), so its
  substitution recurses uniformly, threading the linear contexts along unchanged. The
  28-constructor analog of the PropDeriv result already proven; reuses that induction
  shape. `N` typed additive-only (`linear := []`) so it may be duplicated.
> **L3a BLOCKER (2026-07-20, loop 4): `saysE` is metatheoretically ill-formed.**
>
> `deriv_shift` is provable for the structural cases — the `impE` pattern
> (`injection` the `Ctx` equality, then feed each premise's IH the matching
> linear half) compiles, and `varL`'s arithmetic works. It is NOT provable
> for `saysE`, and the reason is a defect in the rule rather than in the
> proof.
>
> `saysE` BINDS on the additive context but does not record the binder in
> its term:
>
>     dM : Deriv ⟨Γₐ, Γ₁⟩ M (says p φ)
>     dN : Deriv ⟨φ :: Γₐ, Γ₂⟩ N ψ          -- binds φ
>     ------------------------------------------------
>          Deriv ⟨Γₐ, Γ₁ ++ Γ₂⟩ (Term.app M N) (says p ψ)
>
> The conclusion term is `Term.app M N`, and `shift` does not bump the
> cutoff for `app` (`Subst.lean` line 29) — only for real binders such as
> `letSays` (line 64). So the shift lemma's goal carries
> `shift N Γm.length Γl.length` while `dN`'s induction hypothesis can only
> supply `shift N Γm.length (Γl.length + 1)`, since `dN`'s context is
> `(φ :: Γl) ++ Γr`. Off by one, structurally — machine-checked by
> inspecting the goal, not inferred.
>
> The rule's own source comment concedes the shape is provisional
> ("placeholder; the real term is a let-binder"), and `Correspondence.lean`
> already refers to "the placeholder-subject `saysE`/`boxI`". This is the
> same defect class as the `weakenA` unsoundness fixed in PR #122: a rule
> whose TERM does not match its BINDING STRUCTURE. `weakenA` had a one-line
> fix (shift the term); `saysE` does not, because the correct term would be
> a binder form and `Term.letSays` is already taken by `letSaysE`.
>
> **Recommendation: remove `saysE`.** It has zero uses as a constructor;
> `letSaysE` already carries the same premise structure with a correct
> binder term and correct shift handling. The two differ only in the
> conclusion — `saysE` keeps the modality (`says p ψ`) where `letSaysE`
> strips it (`ψ`) — so removing `saysE` loses the modality-preserving bind.
> If that is wanted it should be recovered as `letSaysE` followed by
> `saysI`, or given its OWN binder term constructor; what it must not do is
> keep a term shape that contradicts its premise. An ill-formed rule that
> nothing uses is worse than a missing one, because every future induction
> over `Deriv` has to confront it.
>
> This is a decision about `Deriv`'s rule set, so it is recorded here rather
> than taken unilaterally. L3a is blocked on it: the remaining cases are
> mechanical, and `saysE` is the only one that cannot be discharged.

- **L4 — linear substitution preservation (the hard case).** Substituting for a
  *linear* hypothesis: the variable lands in exactly one side of each `Γ₁ ++ Γ₂`
  split; `N`'s own linear resources merge into that side. Needs L1+L2. This is the
  genuine substructural core — the multi-week piece.
- **L5 — subject reduction over full `Deriv`**, then **T3-full / T1-full /
  progress-full** follow by re-running the existing fragment proofs over the extended
  substitution/reduction machinery, with `declassify` still excluded by design.

## STOP — L1's invariant does not survive context splitting (2026-07-20, loop 5)

The doc's own escape hatch says: *"If L4 proves impossible under the
shared-index invariant, revisit path 1 — but only then, and with the full
ceremony."* This is the trigger, and the evidence is machine-checked.

### The chain

1. `varL` requires a SINGLETON linear context (`linear := [φ]`), and
   addresses the variable at `Term.var Γₐ.length`. That is L1's resolution.
2. `ctxLookup_nonsingleton_linear_none` — the repo's own L1 lemma — proves a
   NON-singleton linear context resolves to `none` at every index
   `≥ Γₐ.length`.
3. So any `Deriv` conclusion carrying two or more linear hypotheses has NO
   resolvable linear variable at all.
4. But every split rule (`impE`, `tensorI`, `delegate`, `discharge`,
   `letSaysE`, `tensorE`) produces exactly such a conclusion, by splicing two
   singleton premises into `Γ₁ ++ Γ₂`.

### The witness

Both halves type-check independently, each using `varL` at index
`Γₐ.length = 0`; `impE` splices them:

    dM : Deriv ⟨[], [imp A B]⟩ (var 0) (imp A B)     -- var 0 means `imp A B`
    dN : Deriv ⟨[], [A]⟩       (var 0) A             -- var 0 means `A`
    -------------------------------------------------------------------
    Deriv ⟨[], [imp A B, A]⟩ (app (var 0) (var 0)) B

The conclusion is derivable. Its two `var 0` occurrences denote DIFFERENT
hypotheses, and `ctxLookup ⟨[], [imp A B, A]⟩ 0 = none` — neither resolves in
the conclusion's own context. A well-typed term whose free variables are not
readable against the context it is typed in.

### Why L2 did not catch it

`linearSplitRoutes_holds` (L2, PR #120) is TRUE, but its hypothesis
`ctxLookup ⟨Γₐ, Γ₁ ++ Γ₂⟩ i = some φ` forces `Γ₁ ++ Γ₂ = [φ]`. It therefore
only bites when ONE HALF OF THE SPLIT IS EMPTY — i.e. on the degenerate
splits. Genuine two-sided splits are exactly the ones it says nothing about.
That is not a defect in L2; it is L2 correctly describing a calculus in which
only one linear variable is ever addressable.

### What this means

Every split branch has the SAME additive length, so every branch addresses
its linear hypothesis at the SAME index. Splicing branches cannot preserve
the reading. L1's "linear lives at `additive.length`" is well-defined per
premise and ill-defined at the conclusion — so **L4 (linear substitution) is
not merely hard under this representation; it is ill-posed**, because
"the variable at index i" has no meaning in a spliced conclusion.

### DECISION (owner, 2026-07-20): option (A), de Bruijn LEVELS.

Validated in `lean/DLC/CtxWellFormed.lean` BEFORE any rule change:

- `ctxLookupL` addresses a linear hypothesis at position `k` by
  `Term.var (additive.length + k)` — its ABSOLUTE position in the spliced
  context, not its position relative to whichever premise introduced it.
- `ctxLookupL_varL` — agrees with `varL`'s address on the singleton contexts
  L1 already handles, so nothing depending on L1 moves yet.
- `ctxLookupL_resolves_split` — the counterexample above resolves, and
  resolves DISTINCTLY (index 0 → φ, index 1 → ψ).
- `ctxLookup_fails_on_split` — kept beside it, showing the OLD lookup
  resolves NEITHER index in that same context. Before/after of one context,
  so the migration is demonstrably necessary rather than cosmetic.

**Still owed, and NOT done there:** the split rules must shift the right
premise's term by `Γ₁.length` so its addresses land in the right half of
`Γ₁ ++ Γ₂` — e.g. `impE` concluding at
`Term.app M (shift N Γ₁.length Γₐ.length)`. That touches `impE`, `tensorI`,
`delegate`, `discharge`, `letSaysE` and `tensorE`, and is the next rung. The
arithmetic is validated: with `Γₐ = []` and `Γ₁ = [imp A B]`,
`shift (var 0) 1 0 = var 1` — exactly the right half's address in the splice.

### Options as they stood (B and C not taken)

- **(A) de Bruijn LEVELS for linear variables.** The literature's answer:
  levels do not need reindexing when the context changes. Addressing linear
  hypotheses by level rather than index makes the reading splice-stable.
- **(B) Separate the namespaces — revisit "path 1".** Give linear variables
  their own term constructor (e.g. `Term.lvar`) so they never share the index
  space with additive variables. The doc rejected this to avoid a `Term` /
  wire-format change; that rejection was explicitly conditional on L4 being
  possible without it, and it is not.
- **(C) Accept the single-linear-variable fragment.** State plainly that only
  one linear hypothesis is ever addressable, and scope T3-full to that
  fragment. Honest, cheap, and much weaker than the campaign intends.

L3a is separately blocked on `saysE` (see above). Both blockers are decisions
about `Deriv`'s presentation rather than proof effort, and neither should be
taken unilaterally.

## L3a: patterns validated, and a loop-4 claim RETRACTED (2026-07-20, loop 11)

### `weakenA` is NOT a structural obstruction — I was wrong

The loop-4 note recorded `weakenA` as "a genuine obstruction, not a tedious
case", on the reasoning that its `Ctx.consA` conclusion forces
`Γl ++ Γr = φ' :: Γ.additive` and the `Γl = []` branch then needs `Γm`
inserted BEFORE `φ'`, "which the premise's IH does not provide". Three
options were proposed for working around it.

That reasoning was wrong, and the case is now PROVEN. The induction
hypothesis quantifies over `Γm`, so the `Γl = []` branch simply absorbs `φ'`
into the inserted block:

    ih [] (Γm ++ [φ']) Γ.additive Γ.linear  -- Γm := Γm ++ [φ']

which yields exactly `⟨Γm ++ φ' :: Γ.additive, Λ⟩`, closing with
`shift_shift_merge` for the doubled shift at cutoff 0. The `Γl = χ :: Γl'`
branch closes with `shift_shift_comm` (loop 10), since
`shift (shift M Γm.length Γl'.length) 1 0
   = shift (shift M 1 0) Γm.length (Γl'.length + 1)`
and `Γl'.length + 1 = Γl.length`.

None of the three proposed workarounds is needed. Recording the retraction
because a wrong "this is impossible" is more expensive than a wrong "this
should work" — it stops people trying.

### Cases proven this loop

`weakenA` (both branches), `varA` (the `List.getElem?_append_left/right`
index arithmetic, mirroring `propDeriv_shift_aux`), and `impI` (the binder
case, IH at `χ :: Γl` with `Ctx.consA` unfolded). `varL` is provable but has
`Nat` association friction inside `Term.var` that needs `convert`/`omega`
tuning rather than `simpa`.

So the L3a patterns are established for all four structural classes:
VAR-shaped conclusions (`subst hΓ`), record-shaped (`injection hΓ`),
`consA`-shaped (case split on `Γl`), and binders (IH at `χ :: Γl`).

### `saysE` is now the ONLY structural blocker

Every other case is a known pattern. `saysE` cannot be proven at all: its
premise binds on the additive context while its conclusion term is
`Term.app M N`, which `shift` does not treat as a binder, so the goal's
cutoff and the IH's cutoff differ by one with no way to reconcile them (loop
4, PR #123).

Because a Lean `induction` demands every constructor, **L3a cannot be
completed while `saysE` remains in `Deriv`** — not for want of effort, but
because one case is unprovable as stated. The decision recorded in #123 is
therefore no longer a nice-to-have: it is the single thing blocking L3a.

## Non-goals / honest scope

- No `Term` / wire-format change (path 1 rejected). If L4 proves impossible under the
  shared-index invariant, revisit path 1 — but only then, and with the full ceremony.
- `declassify` stays excluded (NI modulo declassification, as in T3).
- Complexity bound (`O(|M|·log|Γ|)`) is a *separate* open item, not on this lever.

**Next tick:** dispatch L1 (`CtxWellFormed` + per-rule preservation + the two
binding constraints above) — bounded, hand-verifiable, and the gate that makes L4's
statement well-posed.
