# T2 and T3 in Lean 4 — SOTA Feasibility (May 2026)

> **Status note (2026-07).** Written before the truth-reconciliation
> audit; status language herein reflects May 2026 plans, not current
> reality. Validated statuses: `lean/theorem-status.json`.

**Question:** Could T2 (EUF-CMA reduction) and T3 (non-interference under
delegation) actually be done in **Lean 4**, autonomously, without
collaborator pairing?

**Answer:** **Yes for T2**, **yes-but-much-harder for T3**. The picture is
materially different from my previous "needs Blanchet / Myers" framing,
which underestimated current Lean infrastructure.

---

## T2 — EUF-CMA reduction in Lean 4

### SOTA: VCVio (Tuma et al., eprint 2026/899)

**VCVio** is a Lean 4 framework published May 2026:
- Repository: [Verified-zkEVM/VCV-io](https://github.com/Verified-zkEVM/VCV-io)
- Paper: [eprint 2026/899](https://eprint.iacr.org/2026/899)
- Provides `OracleComp` (monadic oracle-access computations) and
  `ProbComp` (probabilistic computations as uniform-selection oracles).
- Extends the Loom framework (POPL 2026) to the relational setting.
- Three case studies, one of which is **the Schnorr signature scheme
  establishing EUF-CMA security in Lean 4**.
- API for "compact examples showing how the framework layers compose on
  concrete schemes" exists at `docs/agents/end-to-end-examples.md`.

### What this changes about T2

The previous assessment ("M2.M13, Blanchet pairing required") was based
on the assumption that EUF-CMA reductions require EasyCrypt or
CryptoVerif — tools with proof-engineering communities Lean doesn't
match. **VCVio invalidates that assumption for Lean 4 in May 2026.**

What VCVio mechanizes:
- A signature scheme's EUF-CMA security as a **probabilistic relational
  Hoare logic statement**.
- The reduction technique: prove that an adversary winning game G_DLC
  reduces to an adversary winning the EUF-CMA game.
- The Schnorr proof is a concrete template; a Ed25519-or-abstract
  signature reduction follows the same shape.

### Closure path for T2 in Lean

1. Add VCVio as a Lean dependency (`require VCVio from git ...` in lakefile).
2. Define DLC's `Signature` type as a VCVio signature scheme instance —
   abstractly, parameterized over `sign`/`verify`/`pk`.
3. State an abstract `axiom Sig_EUF_CMA : EUF_CMA_secure Signature` —
   the cryptographic assumption (Ed25519 satisfies it; this is *not*
   what we prove, but rather what we assume).
4. State the DLC symbolic-forgery game in VCVio's `OracleComp` monad.
5. Prove the reduction: an adversary breaking DLC's NonSplicing
   reduces to an EUF-CMA adversary, hence by `Sig_EUF_CMA` the
   DLC adversary has negligible advantage.

**This is the same proof structure I documented in
`models/easycrypt/Game.eca`.** The reason for the EasyCrypt skeleton
was M2.M13 expectation of Blanchet pairing. **With VCVio, the
EasyCrypt detour is unnecessary** — we can prove T2 in the same Lean
development that holds T1/T3/T4.

### Effort estimate

- VCVio API ramp-up: 1-2 weeks (read the paper, study the Schnorr
  example, understand `OracleComp`).
- Define DLC's signature scheme as a VCVio instance: 1 week.
- State the DLC symbolic-forgery game: 1 week.
- Prove the reduction: 2-4 weeks (game-hop sequence; the documented
  4-step sketch in `Game.eca` translates directly).

**Total: 5-8 weeks of focused proof engineering.** Doable autonomously.

### What still benefits from pairing (but doesn't require it)

- **Blanchet review** of the reduction's tightness (concrete advantage
  bound, not just asymptotic).
- **Cremers cross-check** between the Lean VCVio reduction and the
  Tamarin symbolic model — making sure the games agree.

Neither is required to *close* T2; both make the result publication-
grade rather than tech-report-grade.

---

## T3 — Non-interference in Lean 4

### SOTA: iris-tini (Gregersen & Bay, POPL 2021)

**iris-tini** is the canonical mechanized non-interference work:
- Repository: [logsem/iris-tini](https://github.com/logsem/iris-tini)
- Termination-insensitive non-interference for a higher-order language
  with recursive types, existential types, label polymorphism,
  impredicative polymorphism, and higher-order state.
- Uses **Iris**, a Coq library providing higher-order step-indexed
  separation logic.
- Defines a novel "Modal Weakest Precondition" theory to capture
  termination-insensitivity.

### What this changes about T3

The previous assessment ("needs Myers engagement") was correct that T3
is hard, but the reason is **infrastructure, not expertise**. The
proof technique (logical relations + fundamental lemma) is well-
understood. The barrier is that **Iris does not exist in Lean 4**.

Specifically:
- Iris's higher-order separation logic uses features (step-indexing,
  impredicative ghost state) that Mathlib does not currently provide.
- A direct port of iris-tini's proof would require porting Iris's
  underlying infrastructure to Lean — multiple person-years of work
  by the Iris Foundation team. Out of scope.

### Closure path for T3 in Lean

Two viable approaches:

#### Option A: Hand-rolled simpler logical relations (DLC-appropriate)

DLC's calculus does **not** include:
- Higher-order state (mutable references) — we don't have them.
- Recursive types — we don't have them.
- Impredicative polymorphism — we don't have it.
- Termination-sensitive control flow — our reduction is bounded.

So DLC could use a **simpler unary logical relations construction**
without Iris's apparatus. The pattern:
- Define `V⟦φ⟧[ℓ_low]` (values related at proposition φ from ℓ_low's
  perspective) by induction on φ.
- Define `E⟦φ⟧[ℓ_low]` (expressions related at φ from ℓ_low) as the
  closure under one step.
- Prove the fundamental lemma: `Γ ⊢ M : φ → ⟦Γ⟧[ℓ_low] M M`.
- Conclude non-interference: low-label observations are preserved.

Without Iris, the proof would be ~1500-2500 LOC of Lean (vs. iris-tini's
~5000 LOC of Coq+Iris that includes the higher-order machinery).

**Effort estimate: 3-5 months autonomous, including the
infrastructure layer.**

#### Option B: Port the relevant Iris fragment to Lean

The minimum Iris infrastructure needed for DLC's T3:
- Step-indexed equality / approximate relations.
- Modal weakest preconditions for termination-insensitivity.
- A binary logical relations framework.

These are all formalizable in Lean Mathlib but would themselves be a
publication. **Out of scope for an autonomous arc.**

### What still benefits from pairing (Option A)

- **Myers's expertise** on the lattice algebra interaction with
  delegation — the IFC label propagation across `says` and `delegate`
  rules has subtle cases.
- **Garg's expertise** on the constructive-authorization-logic
  variant of non-interference proven in Garg-Pfenning CSF '06.

For Option A to land cleanly autonomously, neither is required, but
both would catch design subtleties early.

---

## Summary table — what's the actual Lean feasibility

| Theorem | Lean Feasibility | Required Infrastructure | Effort | Pairing Helpful? |
|---|---|---|---|---|
| T2 EUF-CMA reduction | **Yes** | VCVio (exists, 2026) | 5-8 weeks | Yes for review |
| T3 non-interference (Option A: hand-rolled LR) | **Yes** | None beyond Mathlib | 3-5 months | Yes for design |
| T3 (Option B: port Iris) | **No (autonomously)** | Port iris-tini to Lean | 2+ years | Required |
| T1 full-calculus decidability | **Yes** | Bool checker + induction | 1-2 months | No |
| T4 full obligation soundness | **Yes** | Multiset semantics | 2-3 weeks | No |

The previous assessment said T2 and T3 needed expert pairing. The
revised picture: **both can be done in Lean autonomously**, but with
very different effort profiles. T2 became reachable via VCVio (a 2026
breakthrough); T3 became reachable by accepting a simpler logical-
relations approach than iris-tini's industrial-grade framework.

---

## Revised "strongest autonomous artifact" — extended arc

If we extend the autonomous arc from 3 weeks to **3 months**, the
realistic deliverable changes:

| Component | Previous 3-week arc | Extended 3-month arc |
|---|---|---|
| Four headline theorems | Partial closures | **All four fully proven** (modulo design choices) |
| Paper | 15-20 page tech report | **20-25 page submission to POPL or CCS** |
| `dlc` CLI | Working basic | Production-quality |
| WASM verifier | Browser demo | Full <2000 LOC verified bridge |
| Reference impls | Rust + minimal Go + minimal TS | All three production |
| IETF draft | -00 individual submission | -01 with feedback addressed |
| Aeneas pipeline | Differential testing substitute | Actual extraction wired |

**Estimated honest position after the 3-month arc: ~70% of named-
paradigm status.**

The remaining 30% is:
- Multi-quarter community engagement (IETF WG adoption, W3C tracking).
- Cremers/Blanchet review and any iterations they suggest.
- Pfenning/Garg/Myers review of the four theorem proofs.
- Initial citations from adjacent work (out of our control).

**This is a fundamentally different game from "20% → 50%".** The 3-week
arc clears the credibility threshold; the 3-month arc clears the
submitability-to-top-venues threshold.

---

## Strategic recommendation

The current artifact is at ~20%. Two reasonable arcs:

1. **3-week sprint** → ~50% (arXiv preprint + partial closures + demos +
   standards drafts). Strong foundation for collaborator engagement.
2. **3-month sprint** → ~70% (top-venue-submittable preprint + full
   closures + production verifier + standards adoption track).

The 3-month version is achievable **autonomously** given the SOTA
revisions above. The single biggest unlock since the previous plan is
**VCVio enabling T2 in Lean without EasyCrypt detour**.

The decision is whether the 3-month effort is worth it before any
collaborator engagement happens. Arguments for going long:

- The 3-month artifact is **substantively closer to citable**.
- VCVio's window may not stay open — the API is new (May 2026); pinning
  to a stable commit early reduces future churn.
- Pfenning/Cremers/Blanchet have substantially better material to
  engage with at 70% than at 50%.

Arguments for going short:

- Cremers/Blanchet review at 50% is faster (less to read).
- Faster external feedback de-risks long-effort directions.
- The 3-week arc compounds; the next 9 weeks can be done with
  collaborator input on what to prioritize.

**My honest recommendation: do the 3-week arc first.** Then evaluate
whether the next 9 weeks should be the rest of the 3-month plan or
collaborator-paired iteration. The 3-week arc is the **minimum credible
artifact**; everything after is optimization.

---

**Generated:** 2026-05-27. Reviewer stance: optimistic with infrastructure
visibility. Frame: "what would I tell a researcher considering whether to
spend a quarter on this autonomously?"
