# DLC — Engineering Notes for AI Collaborators

## Hard constraints

- **`dlc-core` MUST stay Aeneas-translatable.** No trait objects, no `async`,
  no third-party deps, no `unsafe`. CI regenerates the Lean translation on
  every PR; non-clean diffs block merge.
- **The four theorems are load-bearing.** Any change that breaks a Lean proof
  is a soundness break. Don't paper over with `sorry`; fix the proof or revert.
- **<2000 LOC verifier budget.** `dlc-verifier` is hard-gated at 2000 lines by
  `scripts/check-loc-budget.sh`. The number is in the marketing.
- **Identifiers in `spec/IDENTIFIERS.md` are irreversible.** Crate names, Lean
  namespace, JSON-LD URI, IETF stem. Treat as published API from day one.

## Architecture

DLC's logic, cryptography, and protocol live in separate crates so each can be
audited independently:

- `dlc-core` is the calculus. It knows about propositions, terms, contexts.
  It knows *nothing* about Ed25519, CBOR, COSE, drand, or the wire format.
- `dlc-crypto` is the realization of `Γ ⊢_K M : φ`. It knows about signatures,
  time anchors, and transparency logs. It depends on `dlc-core` for its types
  but is not depended on by it.
- `dlc-protocol` is the wire format and the bridge to Tamarin/ProVerif. It
  depends on both above but neither depends on it.
- `dlc-verifier` composes the three above into the reference checker.

This is the same principle that lets nucleus formally verify `portcullis-core`
without dragging in `nucleus-node`'s tokio runtime.

## Coupling to nucleus

Path deps; nucleus is treated as an upstream library. Do not modify nucleus
crates from this workspace. If a change to nucleus is required, send a PR to
the nucleus repo and pin the new revision here.

The reverse dependency — a DLC test in nucleus's CI — protects against
accidental wire-shape changes to `nucleus-lineage::proof::canonical_edge_bytes`.

## When extending the calculus

1. Update `spec/syntax.md` and `spec/typing-rules.md` first.
2. Mirror in `dlc-core/src/syntax.rs` and `dlc-core/src/judgment.rs`.
3. Mirror in `lean/DLC/Syntax.lean` and `lean/DLC/Judgment.lean`.
4. Run `scripts/check-drift.sh` to confirm Aeneas regeneration matches.
5. Update any affected theorem; if it breaks, that's a real result — file an
   issue and discuss before silently weakening the statement.

## When extending the protocol

Tamarin model first. Then ProVerif cross-check. Then wire format. Then code.
Wire-format changes that don't have a corresponding Tamarin-model change are
banned — they break the §4.4 correspondence theorem.

## Verification ledger

`make ledger` is the single command. It produces `ledger.json` with the status
of every theorem, every model, the Aeneas drift state, and the verifier LOC
count. Treat this as the artifact's resume.
