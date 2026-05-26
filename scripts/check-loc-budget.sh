#!/usr/bin/env bash
# scripts/check-loc-budget.sh — hard gate on the dlc-verifier LOC budget.
#
# The "~2000-line Rust verifier compiled to WASM" claim is load-bearing for
# DLC's standardization narrative. This script counts the Rust code lines
# (excluding blanks and comments) in `crates/dlc-verifier/src/` and exits
# non-zero if the count exceeds 2000.

set -euo pipefail

cd "$(dirname "$0")/.."

BUDGET=2000
SRC="crates/dlc-verifier/src"

if [[ ! -d "$SRC" ]]; then
  echo "ERROR: $SRC not found" >&2
  exit 1
fi

if ! command -v tokei >/dev/null 2>&1; then
  echo "ERROR: tokei is not installed (cargo install tokei)" >&2
  exit 1
fi

LINES=$(tokei -o json "$SRC" \
  | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d.get("Rust",{}).get("code",0))')

echo "dlc-verifier code lines: $LINES (budget: $BUDGET)"

if [[ "$LINES" -gt "$BUDGET" ]]; then
  echo "::error::dlc-verifier exceeds the $BUDGET LOC budget ($LINES lines)."
  echo "  The verifier's LOC count is part of DLC's standardization claim."
  echo "  Refuse to merge; split or trim instead."
  exit 1
fi

echo "OK — within budget."
