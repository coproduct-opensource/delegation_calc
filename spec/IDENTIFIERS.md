# DLC — Locked Identifiers

These are the **irreversible** identifiers downstream consumers will pin against.
Once published in any external artifact (paper, IETF draft, JSON-LD context, registry
entry), changing them breaks every existing consumer. They are frozen at workspace
inception (Week 1 of the Phase-1 roadmap).

## Crate names (crates.io, when published)

| Identifier   | Purpose                                            |
|--------------|----------------------------------------------------|
| `dlc-core`   | Logic kernel; Aeneas-targetable; zero-dep AST      |
| `dlc-crypto` | Cryptographic realization (Ed25519, VDF, drand)    |
| `dlc-protocol` | Wire format + Tamarin/ProVerif exporters         |
| `dlc-verifier` | Reference checker (<2000 LOC budget)             |
| `dlc-verifier-wasm` | wasm32 cdylib wrapper                       |
| `dlc-cli`    | `dlc` binary                                       |
| `dlc-d`      | DLC-D facade: `#[dlc_d::agent_service]` + Tier-1 vocabulary + runtime `admit` PEP |
| `dlc-d-macro` | The `agent_service` proc-macro (out of the TCB)   |
| `dlc-d-rsm`  | DLC-D consensus surface (Aeneas-clean; RSM core lives in `dlc_core::rsm`) |
| `dlc-d-node` | Runnable node: tokio shell over the verified transition core |

The `dlc-d*` rows were reserved 2026-07-30 (R6.2 inc4) — the `#[dlc_d::agent_service]`
attribute path was already shipping in examples/tests, so the crate-root path `dlc_d`
is load-bearing. Reservation here is the FILE claim only; crates.io registration is a
separate, escalation-gated act.

## Lean namespace

`DLC.*` — every Lean module under `lean/DLC/` lives in this namespace. Imports from
nucleus's `PortcullisCore` re-export under `DLC.IFC.*` rather than reaching into the
upstream namespace directly. `DLCD.*` — every module under `lean/DLCD/` (the DLC-D
distributed layer: RSM model, guarantees, transport) — reserved on the same terms.

## JSON-LD context URI (W3C VC integration)

`https://dlc.coproduct.dev/contexts/dlc-v1.jsonld`

- The `v1` segment is the only versioning surface; v1 is stable for the lifetime of
  the artifact. Breaking changes require a new context URI and parallel publication.
- Served from the `vc-context/` directory under a CDN-friendly path; immutable once
  any third party fetches it.

## IETF draft stem

`draft-crisp-dlc-token`

- Individual Submission under SECDISPATCH / OAUTH cluster.
- On WG adoption, becomes `draft-ietf-<wg>-dlc-token-<NN>` but the *stem* (`dlc-token`)
  remains stable so cross-references resolve.
- ABNF source of truth: `spec/abnf.md`.

## COSE label allocations (request at M4.M18)

| Label   | Purpose                                |
|---------|----------------------------------------|
| TBD-D1  | DLC proof term envelope (COSE_Sign1)   |
| TBD-D2  | DLC obligation set                     |
| TBD-D3  | DLC IFC label                          |
| TBD-D4  | DLC time-anchor commitment             |

Requested from IANA via the standardization track; placeholders until the IETF
draft is adopted.

## Versioning policy

- **Calculus version** (logic + typing rules) follows semver. Major bumps require a
  new JSON-LD context URI and a new IETF draft stem revision.
- **Wire format version** is independent and tagged by IETF draft revision.
- **Verifier crate version** can churn freely so long as it accepts every prior wire
  format that is still within its support window.

## Rationale for these choices

- `dlc-core` (not `delegation-calculus-core` or similar) — three-letter prefix is the
  standard for namespaces that may be cited in academic prose. Short enough to use as
  a tactic-name prefix in Lean too (`dlc_check`, `dlc_verify`).
- `DLC.*` namespace — title-case follows Lean / Mathlib convention; matches the
  paper's name for the calculus.
- `coproduct.dev` for the JSON-LD URI — the org domain is stable, dedicated subdomain
  for context publishing keeps the registry footprint clean.
- `crisp-dlc-token` — author-prefixed Individual Submission per IETF conventions; the
  `dlc-token` suffix survives WG adoption.
