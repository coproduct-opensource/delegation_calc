# The Strongest Autonomous Artifact — Realistic Maximum

**Question asked:** What is the strongest artifact we can deliver before
pairing with experts (Pfenning, Garg, Myers, Cremers, Blanchet)?

**Premise:** Autonomous loop work cannot close the full headline
theorems (T2 EUF-CMA reduction, T3 full non-interference, full subject
reduction) — those are research-grade collaborator items. But the gap
between "stated" and "submittable for external review" is substantially
reachable.

**Target:** A self-contained technical-report-grade deliverable that an
external reviewer could read, run, and form an opinion on. Specifically:
**an arXiv preprint with full reproducible artifact**, not a POPL
submission. arXiv has no gatekeeper; the bar is "credibly defensible
under expert review", which is achievable.

---

## What an arXiv preprint requires (the bar to clear)

Concretely:

1. A 12-20 page LaTeX document with:
   - Motivation (the agent-economy delegation problem + RFC 8693 gap)
   - The calculus (syntax, judgments, key rules)
   - Four headline theorems (statements + proven content + gaps)
   - Symbolic verification (Tamarin + ProVerif)
   - Computational bridge (EasyCrypt sketch)
   - Wire format + content addressing
   - Related work (AITH, LLMbda, NAL, Garg-Pfenning, macaroons)
   - Limitations + future work
2. A reproducible artifact with single-command `make ledger` validation.
3. A working demonstration — a `dlc` CLI that performs a real delegation.
4. Bonus credibility: IETF Internet-Draft, W3C VC context, multi-language
   reference impls.

The audience for arXiv submission is the **academic delegate community
+ adjacent practitioners**. The acceptance is automatic; the *citation*
depends on substance.

---

## The 9 components of the strongest autonomous deliverable

### Tier 1 — load-bearing for any submission

#### 1. The four-theorem partial closures (from `closure-plan-2026-05.md`)

- T4 non-introduction (proven for the calculus as written).
- T1 propositional decidability (soundness direction, mirrors Rust
  `decide_pure`).
- T2 conditional form (modulo Ed25519 EUF-CMA axiom).
- T3 atomic fragment + lift_ℓ case (logical-relations skeleton).

**Effort:** 2-4 weeks of focused proof engineering.
**Value:** turns four `stub`/`stated` entries into proven content
with named gaps. Single largest credibility boost.

#### 2. The paper / tech report

`paper/main.tex` — 15-20 page document targeting arXiv. Sections:

1. Introduction (2 pages): problem, contributions, paper structure.
2. The calculus (3 pages): syntax, judgments, key typing rules, the
   `delegate` rule with the no-chain-splicing condition.
3. Metatheory (4 pages): T1-T4 statements, what's proven, what's
   stated, citations to the Lean development.
4. Symbolic verification (3 pages): Tamarin + ProVerif models, the
   NonSplicing lemma, the cross-prover modeling-gap story
   (`HonestSk` event, honest-key table).
5. Wire format (1 page): CBOR + content addressing, round-trip
   verification.
6. Computational bridge (1 page): EasyCrypt skeleton, what's stated
   conditionally on EUF-CMA.
7. Related work (2 pages): AITH, LLMbda, NAL, Garg-Pfenning,
   macaroons/biscuits, RFC 8693, the IETF March-2026 chain-splicing
   thread.
8. Conclusion + future work (1 page): explicit gaps to collaborator
   work (Pfenning/Garg/Myers/Cremers/Blanchet engagement).

**Effort:** 5-7 days of focused writing.
**Value:** transforms repo into a citable document.

### Tier 2 — concrete demonstration

#### 3. A working `dlc` CLI

`crates/dlc-cli/src/main.rs` — actual subcommands:
- `dlc issue --as <pkfile> --prop <propfile> -o token.cbor`
- `dlc delegate --speaks-for-token <file> --says-token <file> -o
  delegated.cbor`
- `dlc verify --token <file> --keyring <jwks.json>`

Implementation: Ed25519 via `ed25519-dalek`, wire format from
`dlc-protocol::wire`, keyring loading via `serde_json`. ~500 LOC.

**Effort:** 2-3 days.
**Value:** reviewers can run a real example end-to-end. Concrete
demonstration kills "is this just an idea or actually working?"
question instantly.

#### 4. WASM verifier binary + browser demo

`crates/dlc-verifier-wasm` actually built. `wasm-bindgen` to expose
`verify(token: &[u8], pk: &[u8]) -> bool` to JS. A static `demo.html`
page that loads the wasm and verifies sample tokens.

Target: <50KB gzipped wasm. The plan promised <2000 LOC for the
verifier; with `ed25519-dalek` (uncounted dep) and our minimal
`dlc-verifier::check`, this is achievable. Currently `dlc-verifier` is
24 LOC of placeholder; needs ~300-500 LOC of actual verification logic.

**Effort:** 2-3 days.
**Value:** the plan's marketing claim ("a ~2000-line Rust program
compiled to WASM") becomes literally true. Browser demo is the kind of
"show, don't tell" artifact reviewers remember.

### Tier 3 — standards presence

#### 5. IETF Internet-Draft body

`draft-ietf/draft-crisp-dlc-token-00.md` (mmark → XML via `kdrfc`).
Sections required by RFC 7322:
- Abstract
- Introduction
- Conventions and Definitions (RFC 8174 BCP14)
- The DLC token format (CBOR + COSE_Sign1)
- Delegation chain composition (the no-splicing rule)
- Security Considerations (cites our threat model)
- IANA Considerations (request COSE labels TBD-D1..D4)
- References

~5,000 words of markdown.

**Effort:** 2-3 days.
**Value:** standards-track presence cited in the tech report. Even
without WG adoption, an Individual Submission is a citable URI.

#### 6. W3C VC JSON-LD context

`vc-context/dlc-v1.jsonld` — the JSON-LD context file at the URI
locked in `spec/IDENTIFIERS.md`. Defines `DlcAffirmationCredential`
type, `delegationChain`, `obligationSet`, `ifcLabel`, `timeWindow`
terms.

**Effort:** half a day.
**Value:** W3C VC integration claim becomes concrete.

### Tier 4 — reference impl diversity

#### 7. Go reference verifier (minimal)

`reference-impls/go/dlc-verifier-go/` — ~500 LOC of Go that:
- Parses CBOR via `fxamacker/cbor`.
- Verifies Ed25519 signatures via stdlib `crypto/ed25519`.
- Implements the structural Deriv-checking subset.

**Effort:** 2 days.
**Value:** the plan's 3-language commitment becomes 2-of-3.
Multi-language interop demonstration.

#### 8. TypeScript reference verifier (browser-targeted)

`reference-impls/typescript/dlc-verifier-ts/` — ~500 LOC of TypeScript
using `cbor-x` and `@noble/ed25519`. Targets the W3C VC ecosystem.

**Effort:** 2 days.
**Value:** all three reference impl languages present. The argument
"DLC works across the ecosystem" becomes evidence-backed.

### Tier 5 — formal-method credibility multipliers

#### 9. Differential testing infrastructure

`crates/dlc-fuzz/fuzz_targets/` — actually wire `cargo-fuzz`:
- `fuzz_decide_pure`: random `Term` → run `decide_pure` → must not
  panic.
- `fuzz_wire_round_trip`: random bytes → `wire::decode` → must error
  cleanly; random `Term` → `encode` → `decode` → equality.
- `fuzz_export_round_trip`: random `Term` → `term_to_tamarin` → must
  not panic.

Plus a **differential test** comparing Rust `decide_pure` against a
Lean-side `decideLean`: shared property-based test generates random
terms, both checkers must agree. This is *operational* evidence of the
Aeneas function correspondence, even before Aeneas extraction works.

**Effort:** 2-3 days.
**Value:** evidence of correctness *without* relying on collaborator-
proven theorems. Reviewers find fuzz-tested code substantially more
credible than untested formal claims.

---

## Sequencing — the optimal ~3-week autonomous arc

### Week 1: Theorems + Paper draft

- Day 1-2: T4 non-introduction closure (substAt subset lemma + step
  case analysis, split across two PRs).
- Day 3-4: T1 propositional soundness (port Rust `infer` to Lean
  `decideLean`, prove `Bool → Nonempty Deriv`).
- Day 5-7: Paper outline + Introduction + Calculus sections.

### Week 2: Demo + Theorems

- Day 8-9: `dlc` CLI implementation + tests.
- Day 10-11: WASM verifier real build + browser demo HTML.
- Day 12-13: T2 conditional form (axiom EUF-CMA → equivalence).
- Day 14: T3 atomic-fragment logical relation.

### Week 3: Standards + Multi-impl + Paper finish

- Day 15-16: IETF draft body + W3C VC context.
- Day 17-18: Go reference verifier.
- Day 19-20: TypeScript reference verifier.
- Day 21: Differential testing + fuzz harnesses.
- Day 22: Paper finalize, related work, conclusion.

End-state: 30+ PRs merged, 4 partial-closure theorems, paper draft,
working CLI, WASM verifier, IETF draft, two extra language impls,
fuzz/differential testing.

---

## What this artifact IS and IS NOT

### IS:
- A self-contained, externally-reviewable, citable artifact.
- A credible foundation for collaborator engagement.
- A working demonstration of the calculus + protocol unification.
- Strong enough for arXiv submission.
- Strong enough that Pfenning/Garg/Myers/Cremers/Blanchet would see a
  legitimate body of work to engage with (rather than a half-finished
  prototype).
- Strong enough to position for IETF SECDISPATCH presentation.

### IS NOT:
- A POPL/CSF acceptance. Those require full theorems closed; we'd be
  at partial. Acceptance probability without expert pairing: probably
  rejected on "incremental" grounds.
- A "named paradigm" yet. That requires the full theorems closed and
  external adoption.
- The `<2000 LOC` verifier claim *unless* we count `ed25519-dalek` as
  the uncounted dep (which is reasonable — same convention as the
  plan).
- A full Aeneas pipeline. The differential-testing substitute gives
  similar evidence but isn't the formal correspondence.

---

## What is the strongest *credible* version of the contribution claim?

After this arc, the defensible claim becomes:

> DLC is a **delegation calculus** unifying (a) authorization logic
> with proof terms, (b) cryptographic protocol verified independently
> in Tamarin and ProVerif, (c) a runtime wire format with content-
> addressed serialization, and (d) a reproducible verification ledger.
> Four headline theorems are stated; **two are proven outright** (T4
> non-introduction, graded comonad laws, indexed monad laws), **two
> are proven conditionally or partially** (T1 propositional soundness,
> T2 modulo EUF-CMA, T3 atomic fragment). The full theorems are
> open work with named collaborator pairings (Pfenning, Myers,
> Blanchet).
>
> The novelty is the **diagonal**: no existing work spans all four
> axes with reproducible mechanical verification of each. The chain-
> splicing-defeating delegation rule (`Delegate_Accept` in Tamarin,
> `Deriv.delegate` in Lean, `Term::Delegate` in Rust) is a concrete
> answer to the RFC 8693 vulnerability identified in IETF
> March 2026.

This is a **defensible** claim. It is not "named paradigm" — it is
"credible candidate for future paradigm status pending collaborator
engagement". For arXiv, that's enough. For POPL, that's borderline.

---

## Risk register

| Risk | Mitigation |
|---|---|
| Theorem proofs fail due to Lean tactic detail | Smaller PRs (1 lemma per PR), prior T4 attempt lessons applied |
| WASM bundle exceeds 50 KB | Strip default features, `opt-level=z`, `wasm-opt` post-build |
| `ed25519-dalek` not Aeneas-translatable | It doesn't need to be — Aeneas covers `dlc-core` only; `dlc-verifier` (where `ed25519-dalek` is) is outside the Aeneas target |
| IETF draft adopted before paper submission would force naming churn | Lock the stem name in `spec/IDENTIFIERS.md` (already done) |
| arXiv submission gets ignored | Cross-post to OAUTH WG mailing list + IETF SECDISPATCH; gives non-academic visibility |
| Reference impls disagree with Rust on edge cases | Differential testing surfaces these before submission |

---

## What happens if the arc completes

After ~3 weeks of focused autonomous work, the artifact reads:

- 30+ PRs, all CI-green
- Four headline theorems with proven content (not full)
- Paper draft (15-20 pages) on arXiv
- Working `dlc` CLI demonstrating end-to-end delegation
- Browser-runnable WASM verifier
- Three reference verifiers (Rust, Go, TypeScript)
- IETF Internet-Draft (Individual Submission)
- W3C VC JSON-LD context published
- Differential + fuzz testing across the whole verifier
- Reproducible `make ledger` reporting every result

The artifact is **submittable for external review**. The collaborator
engagement at this point has something real to evaluate, not a sketch.

**Estimated honest position vs. named-paradigm bar: ~50%**.

The remaining 50% is exactly what the plan's §8 names: closed full
theorems + adoption by adjacent work. Neither is autonomously
reachable. Both compound from the foundation this arc builds.

---

**Generated:** 2026-05-27. Reviewer stance: optimistic-but-honest.
This is the maximum autonomous deliverable; not the maximum possible
deliverable.
