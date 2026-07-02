# DLC — Delegation Logic Calculus

[![CI](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ci.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ci.yml)
[![Lean 4](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/lean.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/lean.yml)
[![Aeneas Drift](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/aeneas.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/aeneas.yml)
[![Ledger](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ledger.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/ledger.yml)
[![Audit](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/audit.yml/badge.svg)](https://github.com/coproduct-opensource/delegation_calc/actions/workflows/audit.yml)
[![OSSF Scorecard](https://api.scorecard.dev/projects/github.com/coproduct-opensource/delegation_calc/badge)](https://scorecard.dev/viewer/?uri=github.com/coproduct-opensource/delegation_calc)


A modal-linear-temporal authorization logic designed so that proof terms are
**simultaneously** logical proofs, cryptographic witnesses, IFC labels, and
obligation ledgers. (Design intent, partially realized: decidability is proven
for the propositional fragment; the verifier's verify path is real — Ed25519
over canonical bytes, exactly the two conjuncts of the proven T2
characterization — while time anchors, transparency log, COSE envelope, and
the obligation layer remain stubs/stated — see the status table below.) The
artifact unifies three lineages that have so far been attacked separately:

1. **Authorization logics** (Garg-Pfenning, BL, ICL, DKAL) — the `says` modality,
   speaks-for, and constructive proof terms.
2. **Capability tokens** (macaroons, biscuits, ZCAP-LD, UCAN) — chained
   attenuation, decentralized verification.
3. **Authenticated delegation for AI agents** (South et al. 2025; HDP; AIP;
   IETF on-behalf-of) — multi-hop agent chains, splice-resistance.

DLC's target contribution is the **correspondence theorem** (T2): the calculus
and the cryptographic protocol agree exactly — logical validity is verifiable
validity is checkable validity. **Status honesty:** what is proven today is an
axiom-free symbolic characterization at the calculus level (crypto typing ⇔
logical typing ∧ signature validity); the attacker-based statement about the
executable verifier and real wire bytes is open. See the theorem table below
and `lean/theorem-status.json` — CI rejects any doc in this repo that claims
more than that file records.

## Why categorical — the protobuf thesis

The objection "category theory is ceremony with no payoff" was always
**anthropocentric**: CT's cost is the *human* (reader cognition + author labor),
and both fall toward zero as the consumer gets smarter — the Rust + Lean (and
Aeneas-extracted proofs) in this very repo are the proof that *"hard for humans"
stopped being a binding constraint*. The benefit — guaranteed composition,
machine-checkable integrity, a canonical merge (the colimit) — is invariant to
who reads. Cost falls, benefit constant ⟹ the ratio improves monotonically with
consumer intelligence. For machine and **adversarial** readers the sign flips:
loose human-friendly formats rely on good-faith interpretation an adversary won't
honor, so CT's rigidity becomes the *low-friction, necessary* choice — which is
exactly why DLC's proof terms are *simultaneously* logical proofs, cryptographic
witnesses, IFC labels, and obligation ledgers (T2). We therefore treat category
theory as the **protobuf for agent-to-agent knowledge** — and `delegation_calc`
is that wire format for **authority** (the `says` modality + checkable proof
terms). Worst case the bet is wrong and we merely hold more structure than anyone
else; best case it is an isomorphism of mathematical reality as foundational as
the Peano axioms. Full argument: `coproduct-doctrine/CATEGORICAL-FOUNDATIONS.md`
(internal sibling repo; not public).

## Status

Early-stage. 2026-07: Phase 0 (truth reconciliation) landed — theorem
statuses are machine-validated (`lean/theorem-status.json`), overclaims
fail CI, and the corrections are recorded in `RELEASES.md`. Phase 1
(working end-to-end verifier) is next. See `spec/IDENTIFIERS.md` for the
locked identifiers.

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

Statuses are the machine-validated ones from `lean/theorem-status.json`
(2026-07 truth-reconciliation audit; see `RELEASES.md` for the corrections):

| | Theorem | Status | File |
|-|---------|--------|------|
|T1| Decidability | **proven_fragment** — propositional fragment (additive contexts, no linear splitting); the `O(\|M\|·log\|Γ\|)` bound is a target, unproven | `lean/DLC/Decidability.lean` |
|T2| Cryptographic correspondence | **stated** — axiom-free symbolic characterization proven; attacker-based form open (the former EUF-CMA axiom was inconsistent — refutation machine-checked in `Witness/AxiomAudit.lean`) | `lean/DLC/Correspondence.lean` |
|T3| Non-interference under delegation | **stated** — current lemmas are one-run reflexivity, not NI | `lean/DLC/NonInterference.lean` |
|T4| Obligation soundness | **stated** — non-introduction direction proven but vacuous (`pendingObligations ≡ []`) | `lean/DLC/ObligationSoundness.lean` |

`make ledger` runs every check in `scripts/ledger.sh` and prints the current
proof status. Reproducible under `nix run .#ledger`. The ledger VALIDATES
statuses (proven claims require sorry-free files plus non-vacuity witnesses in
`lean/DLC/Witness/`), and `scripts/check-claims.sh` fails CI if any public
document claims more.

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
