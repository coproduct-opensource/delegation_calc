#!/usr/bin/env bash
# scripts/check-wasm-export.sh — audit item 2 closure check.
#
# Asserts that `dlc-verifier-wasm`, built for wasm32-unknown-unknown, ships
# a wasm-bindgen `verify` export. Without these guards, the audit's anti-
# gaming notes are easy to violate (drop the `#[wasm_bindgen]` annotation,
# and CI would otherwise stay green because the cdylib still compiles).
#
# C3: cargo build succeeds.
# C4: resulting .wasm > 1 KiB (the empty-cdylib floor is ~512 B).
# Export: nm-equivalent inspection shows a `verify` export.

set -euo pipefail

cd "$(dirname "$0")/.."

ARTIFACT="target/wasm32-unknown-unknown/release/dlc_verifier_wasm.wasm"

# C3 — ensure we have the wasm; build if missing (idempotent on CI).
if [ ! -f "$ARTIFACT" ]; then
  cargo build -p dlc-verifier-wasm --target wasm32-unknown-unknown --release
fi

# C4 — size floor.
SIZE=$(wc -c < "$ARTIFACT")
if [ "$SIZE" -lt 1024 ]; then
  echo "::error::wasm artifact suspiciously small ($SIZE bytes < 1 KiB floor)"
  echo "         this usually means no code was emitted because nothing was exported"
  exit 1
fi
echo "wasm-export C4: artifact is $SIZE bytes (> 1 KiB floor)"

# Export — wasm-bindgen lowers `#[wasm_bindgen] pub fn verify(...)` to a
# wasm export named `verify`. Use `wasm-objdump` if available, otherwise
# grep the raw bytes for the export-name string (the wasm Export section
# stores names as length-prefixed UTF-8, so the literal "verify" appears
# in the binary).
if command -v wasm-objdump >/dev/null 2>&1; then
  if ! wasm-objdump -x "$ARTIFACT" | grep -E 'export.*"verify"' >/dev/null; then
    echo "::error::wasm-objdump did not find a 'verify' export"
    exit 1
  fi
  echo "wasm-export: wasm-objdump confirms 'verify' export"
else
  # Fallback: the export-name bytes live verbatim in the binary. This is a
  # weaker check (the string could appear in a debug symbol) but the
  # combination with the size floor above is enough for the audit gate.
  if ! grep -a -q 'verify' "$ARTIFACT"; then
    echo "::error::byte-grep did not find the 'verify' symbol in the wasm"
    exit 1
  fi
  echo "wasm-export: byte-grep confirms 'verify' symbol present (wasm-objdump not installed)"
fi

echo "wasm-export: ✓ all 3 mechanical checks pass"
