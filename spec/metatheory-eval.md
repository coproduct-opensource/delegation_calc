# Evaluation: Metatheory Lean 4 Framework (arXiv 2512.09280)

**Status:** Phase-1 decision pending. This document captures the evaluation
of whether to depend on the *Metatheory* Lean 4 library for DLC's subject-
reduction, confluence, and strong-normalization proofs.

**Recommendation: import as a Phase-1 dependency, evaluation-status pending
review of the published Lakefile at the project's adoption point (target:
M1.Q3 end).**

---

## What it is

Ramos, Oliveira, de Queiroz, de Veras (December 2025) ship a comprehensive
Lean 4 library implementing three classical confluence techniques in a
single generic framework:

- The diamond property via parallel reduction.
- Newman's lemma for terminating systems.
- The Hindley-Rosen lemma for unions of relations.

Instantiated across six case studies: untyped λ-calculus, combinatory logic,
simple term rewriting, string rewriting, simply-typed λ-calculus (STLC),
**and STLC extended with products and sums**.

All theorems mechanized with zero `sorry`. **The de Bruijn substitution
infrastructure — including the substitution composition lemma — is
completely proved.**

## What we need

| DLC milestone | Required machinery |
|---|---|
| M1.Q2.a substitution lemma proof closure | de Bruijn substitution composition (✓ in Metatheory) |
| M1.Q2.c subject reduction | Logical relations + β-reduction lemmas (✓ for STLC-with-products) |
| M1.Q3.d T4 obligation soundness | Multiset-pending lemma + reduction-induction discipline |
| M1.Q4 T3 non-interference | Logical relations across IFC labels (STLC pattern, extensible) |
| Termination side of T1 | Strong normalization via logical relations (✓ for STLC) |

DLC's connective surface beyond STLC: `says`, `⊓` (acting), `□_O`, `◇_τ`,
linear `⊗`/`⊸`, IFC labels. Each must be added on top of Metatheory's STLC
backbone.

## Fit assessment

**Goods:**
- de Bruijn machinery is *exactly* what `lean/DLC/Subst.lean` mirrors. Reusing
  Metatheory's `subst_comp` lemma eliminates M1.Q2.a's load-bearing closure
  work — months of avoided proof effort.
- The STLC-with-products+sums instance is the closest published baseline to
  DLC's connective inventory. The remaining gap (modal + linear + temporal)
  is additive: each modality adds new constructors and new rules but does
  not change the substitution infrastructure.
- "Zero axioms or sorry" matches our `expected-axioms.json` discipline and
  the `lean.yml` CI gate.

**Risks:**
- API stability. The library is two months old as of the M1.Q1 milestone;
  Lean 4 / Mathlib pins may churn. Mitigation: pin to a specific commit
  hash in `lean/lakefile.lean`, same pattern we use for Aeneas (commit
  `b2b5e3d`).
- Conceptual fit for modalities. Whether `says` and `◇_τ` admit the same
  parallel-reduction setup is an open question; if they don't, the modal
  fragment needs its own confluence argument.
- License compatibility. We must confirm the published library carries an
  MIT-or-Apache-2.0-compatible license before importing. If it doesn't,
  rolling our own substitution composition is the fallback (~weeks, not
  months — Aeneas-translatable code without proofs).

## Decision

**Adopt at M1.Q4.a alongside the nucleus PortcullisCore re-export.**

Reasoning: Q4 is when the cross-repo imports get wired into the lakefile
anyway. Bundling the Metatheory import with the PortcullisCore re-export
keeps Lake's dependency graph simple — one cross-repo edge per quarter, not
two interleaved. Q3 work (this branch) can land without it; the substitution
lemma's *proof* closure depends on Metatheory but the *statement* does not,
so M1.Q2.a's "stated" status is unaffected.

Action items for Q3 close:
1. Confirm license (probably MIT — typical for a Lean library).
2. Identify the stable commit hash to pin.
3. Open a stub PR adding the `require Metatheory from git ... @ "<hash>"`
   to `lean/lakefile.lean`.
4. Update this evaluation doc with the actual lake-manifest entry.

If Metatheory turns out to be incompatible (license, conceptual fit, or
ongoing churn), we fall back to hand-rolled substitution composition. The
lakefile would lose one `require` line; nothing else changes.
