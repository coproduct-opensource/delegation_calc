# DLC Releases

## Unreleased — Phase 0: truth reconciliation (2026-07)

An external audit (2026-07-01) found the v1.5.0-phase2 theorem claims
below materially overstated, and one axiom refutable in-system. This
entry records the corrections; the table in v1.5.0-phase2 is
annotated rather than rewritten, so the record of what was claimed
stays visible.

**Corrections:**

- **T2's axiom was inconsistent.** `Sig_EUF_CMA_propositional`
  quantified over all `isPropositional` terms while the 6-constructor
  `DerivCrypto` could only inhabit `var`/`lam`/`app`/`sign` subjects;
  the theory including the axiom proved `False`. The refutation is now
  machine-checked in `lean/DLC/Witness/AxiomAudit.lean`. The axiom is
  **deleted**, and T2 is restated axiom-free at its honest strength: a
  symbolic characterization — crypto typing ⇔ logical typing ∧ every
  embedded signature verifies (`t2_propositional_correspondence`).
  The attacker-based T2 (Dolev-Yao adversary, key compromise, wire
  injectivity, EUF-CMA reduction) is **open**. The claimed "discharged
  at M2.M13 by EasyCrypt game-hop" did not exist: the EasyCrypt
  security axiom's body was literally `true`.
- **T3 was not non-interference.** `t3_non_interference` is one-run
  reflexivity of the logical relation with the typing derivation
  discarded; it holds for ill-typed terms. Status: **stated**. The
  two-run theorem with a fundamental lemma is open (Phase-2 scope).
- **T4 was vacuous.** `pendingObligations` is provably the constant
  empty list (`pendingObligations_eq_nil`, now proven in-file): no
  `Term` constructor carries an `Obligation`, so the "proven"
  non-introduction direction quantified over members of `[]`. Status:
  **stated** until the calculus gains an obligation-carrying
  constructor and a discharge redex.
- **T1 was overstated.** What is proven — genuinely, sorry-free — is
  decidability (soundness + completeness of `decideLean`) for the
  propositional fragment `PropDeriv`: 22 constructors, additive
  contexts, **no linear splitting**. The former "full calculus"
  statement was the literal tautology `Γ = Γ ∧ M = M ∧ φ = φ` and the
  complexity-bound statement was literally `True`; both are deleted.
  The `O(|M|·log|Γ|)` bound is unproven in any form and is now
  described as a target. Status: **proven_fragment (propositional)**.
- **Placeholder purge.** The identity-serializer wire round-trip
  witness, the `protocol_correspondence_stub : True` alias, the
  tautological substitution "statements", and the grep-bait
  `PrincipalCategory` instance are deleted.

**New enforcement (so this cannot recur silently):**

- `lean/theorem-status.json` — single source of truth for theorem
  statuses; `scripts/ledger.sh` validates it (proven statuses require
  sorry-free files + non-vacuity witnesses in `lean/DLC/Witness/`).
- `scripts/check-tautologies.sh` — CI tripwire for `True`-bodied and
  self-equality placeholder statements.
- `scripts/check-claims.sh` — CI gate: README/RELEASES/paper/IETF-draft
  may not claim more than `theorem-status.json` records.

## v1.5.0-phase2 — Crypto + Protocol Correspondence (Phase 2)

**Milestone tag**: M2.M15.
**Status (as claimed at release)**: ~~all four headline theorems
machine-checked in Lean 4 (T2 modulo one discharged-later axiom)~~ —
**superseded by the Phase-0 corrections above**: T1 proven for the
propositional fragment; T2/T3/T4 stated only.

### Theorems (table as claimed at release — see corrections above)

| Theorem | Claimed status | Actual status (2026-07 audit) | Source |
|---|---|---|---|
| **T1** decidability of proof-checking | "proven (22/22 Term constructors)" | proven_fragment: propositional, additive contexts only; complexity bound unproven | `lean/DLC/Decidability.lean` |
| **T2** cryptographic correspondence | "proven, conditional on EUF-CMA" | stated; former axiom was inconsistent (see Witness/AxiomAudit.lean); axiom-free symbolic characterization proven instead | `lean/DLC/Correspondence.lean` |
| **T3** non-interference under delegation | "proven (with refl, symm, trans)" | stated; the "proof" was one-run reflexivity | `lean/DLC/NonInterference.lean` |
| **T4** obligation soundness across reduction | "proven" | stated; vacuous over a provably-empty obligation list | `lean/DLC/ObligationSoundness.lean` |

### Models (table as claimed at release — 2026-07 annotations in parens)

| Component | Status |
|---|---|
| Tamarin (`models/tamarin/dlc.spthy`) — symbolic-model fidelity (L2.1) | green (5 rules, 3 lemmas — deliberately small) |
| ProVerif (`models/proverif/dlc.pv`) — cross-check (L2.2) | green |
| Wire encoding (`crates/dlc-protocol::wire`) — round-trip (L2.3) | green in Rust unit tests (the Lean-side round-trip "witness" was the identity serializer; deleted 2026-07, L2.3 open in Lean) |
| EasyCrypt skeleton (`models/easycrypt/`) — computational bridge (L2.4) | skeleton only: parse-checks; placeholder axiom body is literally `true`; no proof content |
| Trace-to-derivation lifting (L2.5) | covers exactly the singleton `[Says P φ]` trace shape |

### Rust ↔ Lean correspondence (M1.Q1.d)

- Charon + Aeneas pipeline wired via `coproduct-opensource/aeneas-ci@v1.0.2`
- `lean/DLC/Aeneas/DlcCore/` committed: 4,764 lines of Aeneas-generated Lean (Types, Funs, FunsExternal_Template) — **generated but never imported or built by any Lean target; no correspondence theorem exists yet**
- `fail-on-drift: true` — any change to `crates/dlc-core/` without matching Aeneas regeneration is a hard CI failure

### Verifier surface

- `dlc-verifier` reference checker: <2000 LOC (CI-gated) — **the budget is currently trivially met because the verifier is a stub that rejects everything; the ledger reports `implemented: false`**
- `dlc-verifier-wasm` builds clean

### Key PR sequence (this release)

- #41 Deriv inductive for all 21 Term constructors
- #42–#46 Phase 2 load-bearing lemmas (L2.1–L2.5)
- #47–#48 closure plan + 3-week sprint paper draft
- #49 T4 substAt subset lemma + step-case analysis
- #51–#56 T1 propositional + T1 full-calculus PropDeriv extensions, T3 statement refinement, transitivity
- #57 Aeneas pipeline wired
- #58 Aeneas bootstrap commit (`fail-on-drift: true`)

### Outstanding (Phase 3 scope, as listed at release)

- ~~T2 axiom discharge: EasyCrypt game-hop closing `Sig_EUF_CMA_propositional` (M2.M13, in flight)~~ — superseded: the axiom was inconsistent and is deleted (see Phase-0 corrections above); nothing was in flight
- Wasm verifier hard-gate at 2000 LOC (currently soft)
- Function-correspondence Lean theorem (mapping `DLC.decideLean` to Aeneas-emitted `dlc_core::decide::infer`) — Phase 3

---

## v0.0.1-skeleton

Initial scaffold.
