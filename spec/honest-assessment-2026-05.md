# DLC Honest Self-Assessment vs. SOTA (May 2026)

This is a skeptical, evidence-based comparison of what we've built against the
initial moonshot specification. Treat every claim as adversarial review.

## What the spec promised

The spec set a single bar: **a named artifact a graduate student cites in
2036**. The mechanism was three-axis unification (logic + type theory +
cryptographic protocol) joined by **T2, the cryptographic correspondence
theorem** — the property that makes citation *necessary* rather than optional.

Four headline theorems all mechanized in Lean 4 with zero `sorry`:
- **T1** Decidability of proof-checking, `O(|M| · log |Γ|)`.
- **T2** Cryptographic correspondence: `Γ ⊢ M : φ ⇔ Γ ⊢_K M : φ`.
- **T3** Non-interference across delegation under IFC labels.
- **T4** Obligation soundness across reduction.

Plus the §4.4 protocol-logic correspondence to Tamarin traces, the categorical
heart (indexed strong monad), the <2000 LOC WASM verifier, the IETF draft, the
three reference impls.

## What 2026 SOTA looks like

| Work | Year | Mechanized? | Property | Tool |
|---|---|---|---|---|
| **AITH** (Chen) | 2026 | yes — 5 thms | Post-quantum agent delegation security | Tamarin |
| **LLMbda Calculus** (Garby et al.) | 2026 | yes — TINI proven | Information-flow control for LLM-invoking λ | Coq/Lean (unclear) |
| **Google DeepMind DCTs** | Feb 2026 | no | Macaroon-based agent delegation, industrial | none |
| **IETF draft-niyikiza-oauth-attenuating-agent-tokens-00** | 2026 | no | Standards-track attenuating tokens for agent chains | none |
| **Authorization Propagation** (arXiv 2605.05440) | 2026 | no | Workflow-level authorization properties | none |
| **NAL** (Schneider et al., older) | 2011 | yes — 3000 LOC Coq | `says`-modality soundness | Coq |
| **Garg-Pfenning** (older) | 2006 | partial | Constructive authorization logic + non-interference | hand proofs |

The peers DLC must beat to be cited:
- **AITH** dominates the "Tamarin-verified delegation protocol" axis with 5
  closed theorems vs. our 3.
- **LLMbda** dominates non-interference (T3) — they have it *mechanized*; we
  have it `stated`.
- **NAL** dominates the mechanized authorization-logic axis at 3000 lines of
  Coq with full soundness; we have ~800 lines of Lean, most of which is
  scaffolding or skeleton statements.
- **DeepMind / IETF** dominate the practical / standards axis; we have none.

## Brutally honest scorecard

### What we genuinely have (citable)

1. **Tamarin + ProVerif double-prover agreement on NonSplicing** — three
   lemmas verified in each prover, including the RFC-8693-chain-splicing-
   defeating property. Independent prover cross-check found two real
   modeling gaps single-prover work would have missed (honest-key table,
   `HonestSk` event). **This is genuinely novel** — AITH uses Tamarin only.

2. **Unified-artifact infrastructure** — Lean calculus + Rust scaffold +
   Tamarin/ProVerif/EasyCrypt models + wire format + reproducible CI ledger
   all in one repo, all building together on every commit. The verification
   ledger (`make ledger`) is itself a contribution as a software-engineering
   pattern.

3. **Chain-splicing-defeating delegation rule** — Lean `Deriv.delegate`
   constructor enforcing same-`q` matching, Tamarin/ProVerif both proving
   non-splicing. This is the right answer to the RFC 8693 issue the IETF
   identified in March 2026.

4. **12 small proven Lean theorems, 0 `sorry`** — graded comonad laws,
   indexed monad laws + strength, four structural substitution lemmas,
   `pendingObligations_shift`. None are headline; collectively they are
   the calculus's worked sanity.

5. **Wire format with 22 round-trip tests covering all 21 Term
   constructors** — operational evidence that the encoding is sound for the
   full calculus.

### What we stated but did NOT prove (the load-bearing claims)

| Theorem | Status | Comparable SOTA |
|---|---|---|
| T1 full-calculus decidability | `stated`; Rust `decide_pure` runs | NAL has decidability |
| **T2 cryptographic correspondence** | `stub` | *No one has this for delegation logics* |
| T3 non-interference | `stated` | **LLMbda has this proven** |
| T4 obligation soundness | partial (`pendingObligations_shift` only) | Garg-Pfenning has variants |
| §4.4 protocol-logic correspondence | `stated` | AITH has Tamarin-only auth proofs |
| Subject reduction | `stated` | Standard for STLC |
| Substitution composition lemma | `stated` (canonical form adopted) | Ramos et al. 709 lines |
| Strong indexed monad strength | proven for left-unit only | Atkey PhD has it |

### What the spec promised that DOES NOT EXIST

- **Paper draft** (POPL/CSF target) — not started.
- **Engaged collaborators** (Pfenning/Garg/Myers/Cremers/Blanchet named in
  the plan's §8) — zero contacted.
- **IETF draft** — `draft-crisp-dlc-token` stem locked in IDENTIFIERS.md;
  no actual XML written.
- **W3C VC JSON-LD context** — URI locked; file is empty.
- **Three reference impls** — Rust only.
- **<2000 LOC WASM verifier** — placeholder at 24 LOC. The actual checker
  is in `dlc-core::decide_pure`, not in `dlc-verifier`.
- **The category-theoretic heart** — defined as `abbrev IndexedT`; only
  proven for identity-functor case (label parameter erased). The real
  categorical content (Kleisli structure, Eilenberg-Moore) is absent.
- **Aeneas Rust↔Lean drift gate** — workflow exists; pipeline is stub.
  Rust `decide_pure` is NOT extracted to Lean; the function-correspondence
  theorem cannot fire.
- **Symbolic-protocol-verification community bridge** (Tamarin traces ↔
  DLC proofs as a real lemma, §4.4 of the spec) — `liftToDeriv` is
  declared `opaque`, body is the M2.M15 closure work.

## Position vs. "paradigm creation"

The spec's bar:

> Ten years from now, a graduate student writes "we extend DLC [Foo et al. 2026]
> with..." and the field knows what that means.

For that to be true, four prerequisites:

1. **A citable paper.** ❌ Does not exist.
2. **Load-bearing theorems proven, not stated.** ❌ T1, T2, T3, T4 all
   open. We have *statements*, not *theorems*.
3. **Adopted by adjacent work.** ❌ No IETF/W3C uptake, no other research
   group has built on DLC because there is nothing to build on yet.
4. **Necessary to cite.** ❌ T2 is the necessity claim; T2 is `stub`.

**Honest grade: ~20% of the way to named-paradigm status.**

The substrate is real and useful. The load-bearing claims that would make
DLC necessary-to-cite are not closed. Compared to AITH (2026), LLMbda
(2026), NAL (2011, mature), and the active IETF/standards work, we are
**competitive in ambition** but **lag in closed results**.

## The honest path forward

The plan's §8 was right: the headline theorems close with collaborator
engagement, not autonomous loop work. Specifically:

1. **Pfenning / Garg engagement** for T1, T3, subject reduction (their
   group has the exact expertise — NAL's 3000 lines of Coq is the
   template).
2. **Cremers engagement** for the Tamarin model formalization in the
   threat-model.md sign-off (the plan says M2.M7).
3. **Blanchet engagement** for the EasyCrypt L2.4 reduction proof (the
   plan says M2.M13).
4. **POPL or CSF submission** drafting once two of the four headline
   theorems are closed.

What this session delivered: **the foundation those collaborators can
work from**. Not the paradigm; the substrate the paradigm would build on.

## Where DLC is uniquely positioned (the actual contribution claim)

If we had to name one thing DLC would be cited for if the work closed
fully, it is this:

**The unification of (a) Tamarin-side symbolic non-splicing, (b) ProVerif
cross-prover agreement, (c) Lean type-theoretic enforcement, (d) Rust
wire-format with content-addressed Merkle DAG, and (e) reproducible CI
ledger — in a single auditable artifact with the §4.4 correspondence
theorem as the load-bearing claim.**

No existing work spans all five axes. AITH is Tamarin-only; LLMbda is
Lean-only; macaroons/biscuits are wire-only; OAuth drafts are standards-
only. **The diagonal is the contribution.** But the diagonal needs §4.4
proven to be the contribution. Today it is sketched, not proven.

The substrate is here. The theorem isn't.

---

**Generated:** 2026-05-27 (Phase 2 close)
**Reviewer stance:** adversarial; written to be read by an external
program-committee referee, not by the project's advocates.
