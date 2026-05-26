# DLC — Delegation Logic Calculus

[![CI](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ci.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ci.yml)
[![Lean 4](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/lean.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/lean.yml)
[![Aeneas Drift](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/aeneas.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/aeneas.yml)
[![Ledger](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ledger.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ledger.yml)
[![Audit](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/audit.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/audit.yml)
[![OSSF Scorecard](https://api.scorecard.dev/projects/github.com/coproduct-opensource/delegation_calc/badge)](https://scorecard.dev/viewer/?uri=github.com/coproduct-opensource/delegation_calc)


A decidable modal-linear-temporal authorization logic in which proof terms are
**simultaneously** logical proofs, cryptographic witnesses, IFC labels, and
obligation ledgers. The artifact unifies three lineages that have so far been
attacked separately:

1. **Authorization logics** (Garg-Pfenning, BL, ICL, DKAL) — the `says` modality,
   speaks-for, and constructive proof terms.
2. **Capability tokens** (macaroons, biscuits, ZCAP-LD, UCAN) — chained
   attenuation, decentralized verification.
3. **Authenticated delegation for AI agents** (South et al. 2025; HDP; AIP;
   IETF on-behalf-of) — multi-hop agent chains, splice-resistance.

DLC's contribution is the **correspondence theorem** (T2): the calculus and the
cryptographic protocol agree exactly. Logical validity is verifiable validity is
checkable validity.

## Status

Week-1 skeleton. Phase-1 closure (`v1.0.0-phase1`) is the first artifact gate.
See `spec/IDENTIFIERS.md` for the locked identifiers and the plan at
`../../.claude/plans/let-s-web-search-and-sequential-forest.md` for the full
roadmap.

## Layout

```
crates/              Rust workspace
  dlc-core           Logic kernel (Aeneas-translatable, zero-dep)
  dlc-crypto         Ed25519, VDF/drand anchors, transparency log
  dlc-protocol       Wire format + Tamarin/ProVerif exporters
  dlc-verifier       Reference checker (<2000 LOC budget)
  dlc-verifier-wasm  wasm32 cdylib
  dlc-cli            `dlc` CLI
  dlc-bench          Criterion benches (T1 bound regression)
  dlc-fuzz           Fuzz harnesses
lean/                Lake project; the four theorems live here
spec/                Frozen syntax, typing rules, threat model, ABNF
models/              Tamarin / ProVerif / EasyCrypt models
paper/               POPL/CCS submission
draft-ietf/          IETF draft (xml2rfc v3)
vc-context/          W3C VC JSON-LD context
scripts/             ledger.sh, check-drift.sh, aeneas-translate.sh
```

## The four theorems

| | Theorem                              | File                                  |
|-|--------------------------------------|---------------------------------------|
|T1| Decidability — `O(|M|·log|Γ|)`       | `lean/DLC/Decidability.lean`          |
|T2| Cryptographic correspondence         | `lean/DLC/Correspondence.lean`        |
|T3| Non-interference under delegation    | `lean/DLC/NonInterference.lean`       |
|T4| Obligation soundness                 | `lean/DLC/ObligationSoundness.lean`   |

`make ledger` runs every check in `scripts/ledger.sh` and prints the current
proof status. Reproducible under `nix run .#ledger`.

## Relation to nucleus

DLC builds on `../nucleus/`:
- `portcullis-core::PermissionLattice` is DLC's IFC label algebra.
- `portcullis-core::DischargedBundle` is the runtime realization of `□_O φ`.
- `portcullis-core::delegation` is extended so chains carry a term denotation.
- `nucleus-identity` provides the SPIFFE-bound Ed25519 signing for `says-I`.
- `nucleus-lineage` is the transparency-log substrate for offline revocation.

DLC does not modify nucleus. Coupling is via path deps in this workspace's
`Cargo.toml` and Lean re-exports in `lean/PortcullisCoreImport.lean`.

## Licensing

Dual MIT / Apache 2.0 (matching nucleus).
