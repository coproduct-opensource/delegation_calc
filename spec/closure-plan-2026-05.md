# Closure Plan — T1, T2, T3, T4 Realistically Considered

> **SUPERSEDED (2026-07).** The sequence below was executed in a way
> that produced degenerate closures (a refutable T2 axiom, a vacuous
> T4, a reflexivity-only T3, tautological T1 full-calculus statements)
> — its completion criteria were grep-shaped, not content-shaped. The
> 2026-07 truth-reconciliation pass (see `RELEASES.md` and
> `lean/theorem-status.json`) reset statuses honestly and added
> machine-enforced gates (`scripts/check-tautologies.sh`,
> `scripts/check-claims.sh`, witness-gated statuses in
> `scripts/ledger.sh`). Kept for the per-theorem precedent research,
> which remains useful.

**Premise:** The honest assessment in `spec/honest-assessment-2026-05.md`
identified T1-T4 closure as the gap between "infrastructure" and "named
artifact." This document plans **what's autonomously achievable** vs.
**what needs collaborator engagement**, with concrete next moves.

**Method:** For each theorem we evaluate (a) what closure means, (b) the
nearest published precedent, (c) what's autonomously reachable, (d) what
needs collaborator pairing, and (e) the concrete next PR.

---

## T4 — Obligation soundness (closest to closure)

### What closure means

The non-introduction direction we already stated:
```
∀ M M' o, step M = some M' →
  o ∈ pendingObligations M' → o ∈ pendingObligations M
```

This says reduction never invents an obligation. The mature form would
add multiplicity tracking (multiset semantics) to capture discharge —
but that requires the runtime layer (`Discharged` evidence in
`dlc-core::obligation`) which is the M3 product layer.

### Nearest precedent

Garg-Pfenning (CSF '06) prove preservation lemmas of similar shape by
case analysis over reduction. Our case set is 7 redexes (β, delegate-β,
fst/snd, case-inl/inr, letTensor, letSays, sfExtract). Each is ~20 lines
of Lean.

### What we already have

- `pendingObligations_shift` (proven; 22-case induction on Term)
- Statement `T4_ObligationSoundnessStatement` in canonical form
- 340-line proof attempt at `proof-t4-obligation-soundness` branch
  commit `b2768fb` (kept in history; specific tactic-detail bugs)

### What's autonomously reachable

**Closure of T4 non-introduction direction: realistic in 2-3 focused PRs.**
The previous attempt failed not on the mathematical content but on
tactic-level detail (`injection h` vs `Option.some.inj`, nested `cases`
shape, `split` on hypothesis pattern). Lessons learned:

1. Start with the substitution helper lemma alone (`pendingObligations
   _substAt_subset`) — that's the 21-case induction. Land it first.
2. Then the case analysis on `step` (7 cases) — each is small.
3. Use `decide`-discharged unit tests in Lean as fixtures to catch
   regressions per case.

### What needs pairing

Multiplicity-tracking (multiset semantics for obligations) and the
discharge-bookkeeping form of T4 — needs the M3 runtime layer designed
first, which is a different engineering chunk.

### Concrete next PR

`proof-t4-step-case-analysis` — close `t4_no_new_obligation` by
re-attempting the 7-case `step` analysis, but with the substitution
subset lemma proven *first* on its own PR. Two PRs total.

**Effort estimate:** 1-2 days of focused proof engineering.

---

## T1 — Decidability (closest practical path)

### What closure means

```
∀ Γ M φ, M.isPropositional = true → Decidable (Nonempty (Deriv Γ M φ))
```

For the propositional fragment first; extension to the full calculus
follows the same induction with extra cases.

### Nearest precedent

- **`Intuitionistic modal logic LIK4 is decidable`** (arXiv 2512.04687,
  Dec 2025) — direct precedent for modal-logic decidability. Their proof
  pattern: convert to a decidable sequent calculus, prove every Deriv
  inhabitant maps to a decidable sequent proof.
- **NAL** (2011) — 3000 LOC Coq decidability for says-modality. Older
  but established pattern.

### What we already have

- Rust `decide_pure` works on the **full 21-constructor calculus** with
  9 unit tests (positive + negative cases including no-chain-splicing).
- `Term.isPropositional` predicate in Lean.
- Statement `T1_PropositionalDecidabilityStatement` canonicalized.

### What's autonomously reachable

**A Lean-side `decide` function and partial decidability for the
propositional fragment: realistic in 3-4 PRs.**

Plan:
1. Define `decideLean : Ctx → Term → Prop' → Bool` in Lean mirroring
   the Rust `infer` function. ~150 LOC.
2. Prove `decideLean Γ M φ = true → Nonempty (Deriv Γ M φ)` — soundness
   direction. ~200 LOC of structural induction.
3. State (but defer) the completeness direction (`Nonempty (Deriv ...)
   → decideLean ... = true`) — harder, often deferred in NAL too.
4. The Decidable instance follows from soundness.

### What needs pairing

The full-calculus T1 (including modal `says`, time, IFC labels, linear
context-splitting) — significantly harder. NAL's 3000 LOC covers a
smaller calculus. Pfenning's group is the natural collaborator.

### Concrete next PR

`proof-t1-propositional-decideLean` — port Rust `infer` to Lean
`decideLean`, prove the soundness direction. Single focused PR.

**Effort estimate:** 2-3 days of focused proof engineering.

---

## T3 — Non-interference (hardest of the four)

### What closure means

```
∀ ℓ_low Γ M φ,
  Deriv Γ M φ →
  ContextHasLabelAtLeast Γ ℓ_low →
  Indistinguishable ℓ_low φ M M
```

The logical-relation `Indistinguishable` says low-label observations are
preserved across the entire derivation.

### Nearest precedent

- **LLMbda Calculus** (Garby et al., arXiv 2602.20064, Feb 2026) —
  termination-insensitive non-interference for an LLM-invoking λ. **The
  search results couldn't confirm Lean 4 mechanization** of LLMbda's
  proof; the paper appears to present the calculus and theorem
  semantically. So LLMbda may have a *paper proof*, not a mechanized one
  yet. This means DLC's gap vs. LLMbda may be **smaller** than the
  honest assessment suggested.
- **Mechanized Noninterference for Gradual Security** (arXiv
  2211.15745) — concrete Coq mechanization template.
- **Garg-Pfenning** (CSF '06) — original constructive-authorization-
  logic non-interference, paper proof.

### What we already have

- `Indistinguishable` relation stub.
- `T3_NonInterferenceStatement` canonical form.
- The `Galois` connection proofs are in nucleus's portcullis-core (we
  import them via `IFCLabel`).

### What's autonomously reachable

**Closure of T3 is genuinely hard.** Logical relations require:
1. Defining the relation by structural induction over propositions.
2. The fundamental lemma (every well-typed term is related to itself).
3. The fundamental lemma needs case analysis over all Deriv constructors.

Realistically: this is 500-1000 LOC of Lean for a working logical-
relations proof. Each constructor case can have subtle bookkeeping.

A *partial* T3 — say, restricted to atomic propositions and lifts — is
achievable as a starting point. ~3-5 PRs.

### What needs pairing

Full T3 closure with the IFC monad's strength axioms in the picture
needs Myers-style expertise (JFlow / Fabric heritage). Per the plan's
§8, Myers is the named collaborator.

### Concrete next PR

`proof-t3-atomic-fragment` — define the logical relation just for
atomic propositions and `lift_ℓ` introduction; prove non-interference
for that fragment. Establishes the proof pattern; extension to other
constructors follows.

**Effort estimate:** 1-2 weeks of focused proof engineering for the
full theorem.

---

## T2 — Cryptographic correspondence (HARDEST; needs collaboration)

### What closure means

```
∀ Γ M φ K, Γ ⊢ M : φ ⇔ Γ ⊢_K M : φ
```

The two judgments — logical and cryptographic — coincide. Conceptually:
a proof term is well-typed in the logic iff its cryptographic
verification succeeds under the named keyring.

### Nearest precedent

- **Blanchet "Computationally Sound Mechanized Proofs of Correspondence
  Assertions"** (eprint 2007/128) — the canonical computational-
  soundness paper. Uses CryptoVerif (not EasyCrypt). Game-hopping
  proofs of correspondence in the computational model.
- **SSProve** (Rocq framework) — modular cryptographic formalization.
- The plan's §2 (M2.M13) was explicit: this is Blanchet engagement
  territory.

### What we already have

- `models/easycrypt/Game.eca` — EUF-CMA game definition + symbolic-
  forgery game + reduction lemma sketched (4-step game hop documented;
  no `proof` body).
- Tamarin + ProVerif symbolic side proven.

### What's autonomously reachable

**T2 closure is NOT autonomously reachable.** The EasyCrypt reduction
proof is a research-grade game-hop sequence requiring deep familiarity
with EasyCrypt's tactic language, probabilistic relational Hoare logic,
and the EUF-CMA reduction template. The plan was explicit: M2.M13,
Blanchet pairing.

What IS autonomously reachable:
1. Refining the `Game.eca` skeleton with additional structure — define
   the reduction-adversary module precisely, state the advantage bound
   as an `axiom`, document the game-hop steps inline.
2. State a **symbolic-side T2** in Lean: assuming the EUF-CMA reduction
   holds (as an `axiom Ed25519_EUF_CMA`), conclude the logical-
   cryptographic correspondence. This is the *if-then* version of T2
   that the M2.M13 work would discharge the antecedent of.

### What needs pairing

Everything past skeleton-refinement. Blanchet engagement is the
critical-path milestone the plan named.

### Concrete next PR

`proof-t2-conditional` — state and prove in Lean the *conditional*
form: `axiom Ed25519_EUF_CMA → (Γ ⊢ M : φ ⇔ Γ ⊢_K M : φ)` for the
propositional fragment. This is achievable autonomously: the symbolic
side has the structural ingredients; only the crypto-step is
axiomatized.

**Effort estimate:** 3-5 days for the conditional form; full closure
needs Blanchet (M2.M13 per plan).

---

## Summary table

| Theorem | Autonomous closure | Effort | Pairing needed |
|---|---|---|---|
| T4 (non-introduction) | **Yes** — 2-3 PRs | 1-2 days | Multiset/discharge form |
| T1 (propositional, soundness) | **Yes** — 3-4 PRs | 2-3 days | Full-calculus completeness |
| T3 (atomic fragment) | **Partial** — 3-5 PRs | 1-2 weeks | Full theorem (Myers) |
| T2 (conditional form) | **Yes** — 1-2 PRs | 3-5 days | EUF-CMA reduction (Blanchet) |
| T2 (full, EasyCrypt proof) | **No** | — | M2.M13 with Blanchet |
| T3 (full theorem) | **No** | — | Myers engagement |

## Recommended sequence

If continuing autonomously, the highest-value sequence is:

1. **T4 full non-introduction** (closest to closure; lessons from prior
   attempt apply).
2. **T1 propositional decidability soundness** (mirrors the Rust
   `infer` already shipped).
3. **T2 conditional form** (lifts to full T2 once Blanchet closes the
   EUF-CMA reduction).
4. **T3 atomic fragment** (proves the logical-relations pattern works
   for DLC; full closure stays with Myers).

This sequence converts four `stated` theorems into:
- T4 → **proven** (non-introduction form; full multiset still stated)
- T1 → **proven_partial** (propositional, soundness direction only)
- T2 → **proven_conditional** (modulo EUF-CMA axiom)
- T3 → **proven_partial** (atomic fragment only)

The remaining gaps (multiset T4, full T1, computational T2, modal T3)
are explicit, scoped, and named with the right collaborators per the
plan's §8.

## What this changes about the artifact's citability

After the recommended sequence:

- **Four headline theorems all have proven content**, even if not full.
- The DLC artifact moves from "12 small lemmas proven" to **"4 of the 4
  headline theorems have proven non-trivial content, with explicit
  gaps to collaborator-led closure."**
- This is the difference between "promising substrate" and "submittable
  result" — the latter is what gets a paper into POPL/CSF.

**Honest read:** this sequence brings DLC from ~20% to maybe ~40% of
the way to "named paradigm" status — still gated on full closure +
paper + adoption, but materially past the credibility threshold for
external review.

---

**Generated:** 2026-05-27. Reviewer stance: realistic-but-ambitious.
