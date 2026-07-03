# T3 two-run non-interference — design (2026-07, Phase 2)

Status: design document. Nothing here is proven until the ledger says
so; statuses live in `lean/theorem-status.json`.

## Why the current relation cannot carry the fundamental lemma

`Indistinguishable` (NonInterference.lean) as it stands:

1. **Non-projective `and`/`tensor`/`or` cases.** `R[φ ∧ ψ] M N =
   R[φ] M N ∧ R[ψ] M N` applies BOTH component types to the WHOLE
   term. Consider `M = pair x_low x_high : atom ∧ (χ @ ℓhigh)` under
   two substitutions for the high hypothesis: the two instances differ
   syntactically, so the `atom` conjunct — which demands syntactic
   equality of the whole pair — is false. The standard projective form
   `R[φ](fst M)(fst N) ∧ R[ψ](snd M)(snd N)` is required.
2. **Diagonal arrow case.** `R[imp α β] M N = ∀ M', R[α] M' M' → …`
   only relates applications to the SAME argument. The `imp-E` case of
   a binary fundamental lemma needs the standard binary form
   `∀ N₁ N₂, R[α] N₁ N₂ → R[β] (app M N₁) (app N N₂)` — which in turn
   makes reflexivity non-trivial and forces the atom case to be
   equality UP TO REDUCTION (joinability under `Reduce.step`), because
   `app (lam b) N₁` and `app (lam b) N₂` are never syntactically equal.

So the full T3 requires, in order:
* redefine the LR: projective products, binary arrows, atoms =
  joinability (`∃ V, M ↠ V ∧ N ↠ V`) — Kripke-style over reduction;
* fundamental lemma by induction on `PropDeriv`, using the proven
  substitution-preservation machinery (Decidability.lean);
* the confinement corollary as the headline NI statement.

Dependencies that must land first or alongside: multi-step reduction
(`↠`) with congruence lemmas; subject reduction is already proven for
the propositional fragment. Strong normalization is NOT required for
joinability-at-atoms, but confluence of `step` on the fragment is
(else joinability is not transitive). This is the months-scale core;
it proceeds fragment-by-fragment.

## The first rung (this PR): intro-fragment confinement

A genuine two-run statement, provable now, no LR redesign needed:

**Observability.** `Observable ℓLow : Prop' → Prop`, structural:
atoms/top/bot/speaksFor observable; `at φ ℓ` observable iff
`Label.le ℓ ℓLow` and `φ` observable; `says p φ` iff `φ`; compounds
pointwise; `boxed`/`within` structural on the body.

**High hypothesis.** Context slot `i` is high iff `¬ Observable ℓLow
Γₐ[i]`.

**Fragment.** Introduction-only derivations (`IntroOnly`):
`varA`, `saysI`, `andI`, `orI_L/R`, `tensorI`, `withinI`,
`liftLabel`, `now`. Every premise type is an immediate subformula of
the conclusion type, so observability propagates downward — this is
what makes the induction go through without cut elimination or
normalization. (Eliminations reintroduce the general problem:
`fst (pair x_low x_high)` derives a low type THROUGH a high
intermediate type; handling that is exactly the reduction-closure work
above.)

**Theorem (confinement).** If `d : PropDeriv Γₐ M φ` is intro-only and
`Observable ℓLow φ`, then `M` references no high variable of `Γₐ`.

**Corollary (two-run).** For any two substitutions that agree on low
slots and differ arbitrarily on high slots, the two instances of `M`
are literally equal — the observable output is INDEPENDENT of high
inputs. This is non-interference for the intro fragment, at syntactic
strength (stronger than LR-relatedness, on a smaller fragment).

**Non-vacuity witness** (`lean/DLC/Witness/T3.lean`): (a) a concrete
intro-only derivation whose term provably omits its high variable;
(b) the conclusion FAILS for an ill-typed/atypical term that does
reference a high variable — the typing hypothesis is load-bearing,
unlike the retired reflexivity "T3".

**Ledger effect.** T3 remains `stated` overall; `proven_content`
gains "intro-fragment confinement (two-run, syntactic)". The
reflexivity lemmas stay labeled as infrastructure.

## Rung ladder after this PR

1. ~~Add multi-step reduction + confluence~~ DONE (rung 2,
   `DLC/ReduceMeta.lean`: `Steps`, semi-confluence by determinism,
   `Joinable` transitive).
2. ~~Substitution composition~~ DONE (rung 3a, `substAt_substAt` +
   shift-lemma stack in `DLC/Subst.lean`).
3. ~~Congruence rules in `step`~~ DONE (rung 3b-0,
   `DLC/Reduce.lean` + `DLC/Progress.lean`: nested eliminations
   evaluate; progress proven).
4. ~~Redefine LR (value-style positives, binary arrows over CLOSED
   args, Joinable atoms); PER (symm/trans); anti-reduction~~ DONE
   (rung 3b, `DLC/NonInterferenceLR.lean`).
5. ~~Fundamental lemma~~ DONE (rung 3c,
   `DLC/NonInterferenceFundamental.lean`: `fundamental` over all 22
   `PropDeriv` cases with the closedness/msubst infrastructure in
   `DLC/NonInterferenceEnv.lean`; corollary `t3_two_run_general`;
   witness in `DLC/Witness/T3.lean`). The proof is over the
   *computational core* — the four frozen eliminations
   (verify/attenuate/declassify/discharge) are excluded because they
   produce stuck non-values no reduction-based relation can connect;
   that exclusion is `progress`'s `CoreTerm` gate, not an omission.
6. Declassify: excluded throughout (NI modulo declassification is the
   correct statement; unrestricted declassify falsifies the lemma, as
   it must).

## LADDER COMPLETE (2026-07-03)

T3 is proven for the propositional computational core: the first
mechanized non-interference theorem for a says-logic in Lean, on
`[propext, Quot.sound]`. What remains open is the extension from the
propositional fragment (`PropDeriv`) to the full `Deriv` with linear
context splitting — a strictly larger calculus, tracked in the ledger.

## FINDING (2026-07-02, blocks rung 3b): `step` is head-redex-only —
## progress FAILS; congruence rules are prerequisite

`Reduce.step` fires ONLY head redexes (β, delegate-β, fst/snd of a
LITERAL pair, case of a literal injection, letTensor of a literal
tensor, letSays/sfExtract of a literal sign); every other shape is
`none`. Consequently:

* `fst (fst (pair (pair a b) c))` is STUCK — the outer projection
  demands a literal pair and nothing reduces the inner one. Closed,
  well-typed, and unevaluable: PROGRESS fails for the propositional
  fragment under the current semantics.
* Therefore NO logical-relation formulation can carry the fundamental
  lemma's elimination cases: value-style relations need `fst M ↠
  fst (pair …)` when `M ↠ pair …` (a congruence step), and projective
  relations need anti-reduction at nested types (also congruence).
  This is a defect of the operational semantics, not of any candidate
  relation.

**Rung 3b-0 (new, prerequisite):** extend `step` with deterministic
evaluation contexts — reduce the scrutinee/function position when the
head rule does not yet fire: `app` (function position), `fst`/`snd`,
`case` (scrutinee), `delegate` (left, then right), `letSays`/
`sfExtract` (scrutinee), `letTensor` (scrutinee). Keep it a FUNCTION
(fixed order ⇒ determinism ⇒ `ReduceMeta` survives verbatim).
Process per CLAUDE.md: spec first (reduction section), then
`dlc-core/src/reduce.rs`, then `Reduce.lean`; wire format untouched
(no Tamarin change needed — reduction is not on the wire). Proof
repairs required and expected: `propDeriv_subject_reduction`
(congruence cases = inversion + IH; PropDeriv is syntax-directed so
inversion is available) and `t4_no_new_obligation` (congruence cases
= list-membership through one reduced component, by IH). Progress for
the closed propositional fragment becomes provable afterwards and
should be proven as the rung's witness.
