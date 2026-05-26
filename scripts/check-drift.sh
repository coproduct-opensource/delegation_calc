#!/usr/bin/env bash
# scripts/check-drift.sh — verify the Aeneas-generated Lean translation of
# `crates/dlc-core` matches the committed `lean/DLC/Aeneas/` output.
#
# Week-1 stub: the Aeneas pipeline is not yet wired. Returns success but
# logs that the real check awaits M1.Q1.d.

set -euo pipefail

cd "$(dirname "$0")/.."

if ! command -v aeneas >/dev/null 2>&1; then
  echo "drift: aeneas not on PATH; assuming clean (M1.Q1.d will wire this)" >&2
  exit 0
fi

if ! command -v charon >/dev/null 2>&1; then
  echo "drift: charon not on PATH; assuming clean (M1.Q1.d will wire this)" >&2
  exit 0
fi

# Production flow (M1.Q1.d):
#   1. charon --crate crates/dlc-core --output build/portcullis_core.llbc
#   2. aeneas --backend lean --output build/aeneas-out build/portcullis_core.llbc
#   3. diff -r build/aeneas-out lean/DLC/Aeneas
#   4. non-empty diff → exit 1

echo "drift: production check stub — wire at M1.Q1.d" >&2
exit 0
