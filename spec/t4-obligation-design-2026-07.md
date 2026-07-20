# T4 obligation soundness — design (2026-07, Phase 2)

Status: design document. Nothing here is proven until the ledger says
so; statuses live in `lean/theorem-status.json`.

## The defect is one missing constructor argument

`t4_no_new_obligation` is a real ~180-line case analysis over `step`'s
redexes. It is also vacuous, and the reason is narrower than "obligations
are unimplemented".

Obligations already exist in the **type** system:

* `Prop'.boxed : Obligation → Prop' → Prop'` — the type `□_O φ`.
* `Deriv.discharge` (Judgment.lean) — the elimination, consuming
  obligation evidence through a linear context split.
* `Obligation` itself is fully populated: `top`, `bot`, `actOf`,
  `within`, `tensor`, `lolli`.

What is missing is that obligations never reach the **term** syntax.
`Deriv.boxI` concludes at `Term.app M N`:

```lean
| boxI (Γ : Ctx) (O : Obligation) (φ : Prop') (M N : Term)
    (dM : Deriv Γ M φ)
    (dN : Deriv Ctx.empty N (Prop'.atom 0)) :
    Deriv Γ (Term.app M N)          -- ← O does not appear
          (Prop'.boxed O φ)
```

`O` is bound by the rule and used in the conclusion *type*, but the
conclusion *term* is an ordinary application. Since
`pendingObligations : Term → List Obligation` is a function of syntax
alone, no input can ever yield a non-empty list — proven explicitly as
`pendingObligations_eq_nil`. T4 then quantifies over members of `[]`.

The theorem is not wrong. It is true and empty, which is worse than
false: it reads as discharged in every summary.

## The spec already records the gap — and shows it structurally

Two things were found while scoping this, both of which shrink R1:

**`spec/typing-rules.md` is already honest.** It states outright that
`discharge-β` is NOT implemented and names this exact blocker: *"discharge-β
awaits the obligation-carrying constructor (T4 non-vacuity package)"*. It
even records that an earlier revision listed it as a reduction rule and
that doing so "overstated the semantics". No correction is owed there;
R1 flips that paragraph when the constructor lands.

**`spec/syntax.md`'s term grammar is missing the introduction form.** The
grammar lists `discharge(M, N)` — the eliminator for `□_O φ` — but there is
no `box` production at all. That is the defect stated structurally: the
calculus has an elimination rule for a connective it cannot introduce.
Everything downstream (`Deriv.boxI` borrowing `Term.app`,
`pendingObligations ≡ []`, a vacuous T4) follows from that one omission.

Note also that `check-spec-drift.sh` does not catch this. It reconciles
rule *indices* across spec/Rust/Lean, and explicitly tolerates rules staged
in the spec ahead of the encodings (Phase-1 staging). A connective whose
introduction form is absent from the grammar is not an index mismatch, so
the gate passes. Worth knowing before trusting it as coverage.

## What has to change, in order

1. **`Term.boxI : Obligation → Term → Term → Term`** — the introduction
   form carries its obligation. `Deriv.boxI` retargets to
   `Term.boxI O M N`, so the obligation is recoverable from syntax.
2. **`pendingObligations` gains its base case**:
   `pendingObligations (Term.boxI O m n) = O :: (pendingObligations m ++ pendingObligations n)`.
   Only now can the list be non-empty.
3. **A discharge-β redex in `Reduce.lean`.** `Term.discharge (Term.boxI O M N) P`
   must step, removing exactly one occurrence of `O`. Today `discharge`
   is verifier-checked rather than computed (Reduce.lean:124-127), so
   there is no redex to reason about.
4. **The real T4 — multiset accounting.**
   `obligations(M') = obligations(M) − discharged + introduced`.
   The non-introduction direction proven today becomes one inequality of
   this statement, and the existing case machinery (`substAt` subset
   lemma, per-redex membership arithmetic) is reused verbatim.

## Blast radius — this is not a local change

`Term` has 22 constructors and is matched exhaustively across the stack.
Adding one reopens work that landed within the last three weeks:

| Surface | Impact |
|---|---|
| Lean, pattern-matching on `Term` | 14 files, incl. `Decidability.lean` (~2000 lines), `Subst.lean`, `Reduce.lean`, `Progress.lean`, `NonInterference*.lean`, `CtxWellFormed.lean` |
| `crates/dlc-core` | `syntax.rs`, `judgment.rs` — must stay Aeneas-translatable (no trait objects, no `async`, no third-party deps) |
| Shipped checker | `decide.rs` — a new term form the checker must classify |
| Spec | `spec/syntax.md`, `spec/typing-rules.md`, gated by `spec-drift.yml` |
| Aeneas | `lean/DLC/Aeneas/DlcCore/` regenerated; non-clean diff blocks merge |
| **T1 subject reduction** | new redex ⇒ new preservation case |
| **T3 fundamental lemma** | new term form ⇒ new `LRel` case, and `progress` needs the `boxI` form to be a value or step |

The last two rows are the reason this is a ladder and not a patch. T3's
fundamental lemma landed 2026-07-03; extending `Term` reopens its
induction. Per `CLAUDE.md`: *"Update any affected theorem; if it breaks,
that's a real result — file an issue and discuss before silently
weakening the statement."*

## Toolchain constraint — Aeneas regen round-trips through CI

`scripts/aeneas-translate.sh` needs `charon` + `aeneas`, and
`.github/workflows/aeneas.yml` pins a **coherent triple**: the
`charon-version` must be the `aeneas-version`'s own `charon-pin`, and the
lakefile's `require aeneas` rev must match the binary that generated the
tree. A locally-installed charon/aeneas pair that is not that exact triple
will produce spurious drift.

So the Rust→Lean regeneration is not verifiable on a dev machine unless
the pins happen to match. The `aeneas-ci` action uploads the regenerated
tree as the `aeneas-generated-lean` artifact when it detects drift; the
rung that touches `dlc-core` should take that artifact as ground truth
rather than a local regen.

## The ladder

Each rung is one PR, green before the next starts — the shape the T3
campaign used.

* **R0 (this PR)** — this design note. No code. Records the defect, the
  order, and the blast radius before any constructor moves.
* **R1** — `spec/syntax.md`: add the missing `box_O(M, N)` production to
  the term grammar; `spec/typing-rules.md`: flip the discharge-β paragraph.
  Smaller than expected — see above; the spec already documents the gap.
* **R2** — `dlc-core`: `syntax.rs` + `judgment.rs` mirror; `decide.rs`
  classification; Aeneas regen via the CI artifact; `check-drift.sh` clean.
* **R3** — hand-written Lean `Syntax.lean` + `Judgment.lean` mirror, and
  make all 14 matching files *compile*. No theorem content changes; this
  rung is deliberately mechanical so a break is unambiguous.
* **R4** — discharge-β in `Reduce.lean`; repair `progress` and the T1
  subject-reduction cases. Expect real work here, not a rename.
* **R5** — `pendingObligations` base case, a non-vacuity witness
  (`DLC/Witness/T4.lean`: a term with a non-empty obligation list, which
  today *cannot exist*), then the multiset accounting theorem.
* ~~**R6** — T3's `LRel` case for the new form; re-establish the
  fundamental lemma.~~ **NON-TASK. The ladder is complete at R5.**

  This rung was mis-scoped when the note was written. `LRel` is indexed by
  the TYPE, not the term constructor —
  `LRel : Prop' → Term → Term → Prop` — and `Prop'.boxed` already had its
  clause long before this ladder. Adding a *term* constructor required
  nothing in `NonInterferenceLR.lean` or `NonInterferenceFundamental.lean`,
  which is exactly why R3 and R4 built `NonInterference` clean with no
  changes to either file.

  The abort condition never fired, and could not have: T3's fundamental
  lemma was never in the blast radius. R3 and R4 needed added cases only in
  structural helpers (`usesVar`, `ClosedAbove`), and axiom snapshots held at
  34/34 across the whole ladder.

  **What R6 was reaching for is real, but it is not a T4 rung.** See the
  caveat now recorded in `NonInterferenceLR.lean`'s docstring:
  `LRel ℓLow (.boxed O φ) M N = True`, sound today only because
  `Prop'.boxed` is uninhabited in `PropDeriv`. When T3 extends to the full
  `Deriv` judgment — which has `boxI`, now inhabited by `Term.boxed` — that
  `True` stops being unreachable and becomes a hole. Giving `.boxed` a real
  clause is a prerequisite of that extension, which is T3's own open item
  and a months-scale campaign in its own right, not a rung here.

Status discipline: T4 stays at its current status until R5's witness
builds. `scripts/ledger.sh` will not accept `proven*` without one, and
`check-claims.sh` will not let README, the paper, or the draft-ietf claim
ahead of it.

## What would make this not worth doing

Recorded so the decision is revisitable: if R3 or R4 shows that the new
constructor forces a weakening of the T3 fundamental lemma — rather than
just an additional case — the honest move is to stop and mark T4
`vacuous` (a status the vocabulary already supports) instead of trading a
proven two-run non-interference result for an obligation-accounting one.
T3 is the stronger asset.
