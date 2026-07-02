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

1. Add multi-step reduction + confluence for the propositional
   fragment (independent value: first `Reduce`-metatheory).
2. Redefine LR (projective, binary-arrow, joinable atoms); re-prove
   refl/symm/trans.
3. Fundamental lemma: binder-free fragment first (no impI/impE), then
   arrows via reduction closure.
4. Declassify: excluded throughout (NI modulo declassification is the
   correct statement; unrestricted declassify falsifies the lemma, as
   it must).
