# DLC Releases

## v1.5.0-phase2 — Crypto + Protocol Correspondence (Phase 2)

**Milestone tag**: M2.M15.
**Status**: all four headline theorems machine-checked in Lean 4 (T2 modulo one discharged-later axiom).

### Theorems

| Theorem | Status | Source | Axioms |
|---|---|---|---|
| **T1** decidability of proof-checking, `O(\|M\|·log\|Γ\|)` | proven (22/22 Term constructors) | `lean/DLC/Decidability.lean` | — |
| **T2** cryptographic correspondence `Γ ⊢ M : φ ↔ Γ ⊢_K M : φ` | proven, conditional on EUF-CMA | `lean/DLC/Correspondence.lean` | `Sig_EUF_CMA_propositional` (discharged at M2.M13 by EasyCrypt game-hop) |
| **T3** non-interference under delegation | proven (with refl, symm, **trans**) | `lean/DLC/NonInterference.lean` | — |
| **T4** obligation soundness across reduction | proven | `lean/DLC/ObligationSoundness.lean` | — |

### Models (Phase 2 load-bearing)

| Component | Status |
|---|---|
| Tamarin (`models/tamarin/dlc.spthy`) — symbolic-model fidelity (L2.1) | green |
| ProVerif (`models/proverif/dlc.pv`) — cross-check (L2.2) | green |
| Wire encoding (`crates/dlc-protocol::wire`) — round-trip (L2.3) | green |
| EasyCrypt skeleton (`models/easycrypt/`) — computational bridge (L2.4) | skeleton complete |
| Trace-to-derivation lifting (L2.5) | skeleton + exporters complete |

### Rust ↔ Lean correspondence (M1.Q1.d)

- Charon + Aeneas pipeline wired via `coproduct-opensource/aeneas-ci@v1.0.2`
- `lean/DLC/Aeneas/DlcCore/` committed: 4,764 lines of Aeneas-generated Lean (Types, Funs, FunsExternal_Template)
- `fail-on-drift: true` — any change to `crates/dlc-core/` without matching Aeneas regeneration is a hard CI failure

### Verifier surface

- `dlc-verifier` reference checker: <2000 LOC (CI-gated)
- `dlc-verifier-wasm` builds clean

### Key PR sequence (this release)

- #41 Deriv inductive for all 21 Term constructors
- #42–#46 Phase 2 load-bearing lemmas (L2.1–L2.5)
- #47–#48 closure plan + 3-week sprint paper draft
- #49 T4 substAt subset lemma + step-case analysis
- #51–#56 T1 propositional + T1 full-calculus PropDeriv extensions, T3 statement refinement, transitivity
- #57 Aeneas pipeline wired
- #58 Aeneas bootstrap commit (`fail-on-drift: true`)

### Outstanding (Phase 3 scope)

- T2 axiom discharge: EasyCrypt game-hop closing `Sig_EUF_CMA_propositional` (M2.M13, in flight)
- Wasm verifier hard-gate at 2000 LOC (currently soft)
- Function-correspondence Lean theorem (mapping `DLC.decideLean` to Aeneas-emitted `dlc_core::decide::infer`) — Phase 3

---

## v0.0.1-skeleton

Initial scaffold.
