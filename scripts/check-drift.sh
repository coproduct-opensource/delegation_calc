#!/usr/bin/env bash
# scripts/check-drift.sh — verify the Aeneas-generated Lean translation of
# `crates/dlc-core` matches the committed `lean/DLC/Aeneas/DlcCore/` output.
#
# Drift here is a soundness break: T1 would prove a Lean function no longer
# corresponding to the Rust.
#
# Bootstrap mode: if `lean/DLC/Aeneas/DlcCore/` doesn't exist yet, the
# pipeline hasn't been bootstrapped. In that case we still run the
# translation and report generated content as artifacts, but don't fail.

set -euo pipefail

cd "$(dirname "$0")/.."

CORE_DIR="crates/dlc-core"
COMMITTED_DIR="lean/DLC/Aeneas/DlcCore"
STAGE_DIR="build/aeneas-stage"

# Tool-availability gate.
if ! command -v aeneas >/dev/null 2>&1; then
  echo "drift: aeneas not on PATH; skipping (CI installs it)" >&2
  exit 0
fi
if ! command -v charon >/dev/null 2>&1; then
  echo "drift: charon not on PATH; skipping (CI installs it)" >&2
  exit 0
fi

# Stage Aeneas output fresh.
rm -rf "$STAGE_DIR"
mkdir -p "$STAGE_DIR"

# Run Charon to produce the LLBC.
(
  cd "$CORE_DIR"
  charon cargo --preset aeneas
)

# Locate the .llbc Charon emitted. For a cargo *workspace member*, Charon
# serializes with cwd = the workspace root (cargo's build cwd), so the file
# lands at the repo root, NOT in $CORE_DIR. Search both — this mirrors the
# canonical `coproduct-opensource/aeneas-ci` action's own fallback search.
LLBC_FILE=""
for cand in "$CORE_DIR/dlc_core.llbc" "./dlc_core.llbc"; do
  if [ -f "$cand" ]; then LLBC_FILE="$cand"; break; fi
done
if [ -z "$LLBC_FILE" ]; then
  echo "drift: Charon did not produce dlc_core.llbc (searched $CORE_DIR/ and repo root)" >&2
  exit 1
fi

# Run Aeneas. dlc-core's surface is deliberately Aeneas-translation-friendly,
# so we expect a clean run; capture the exit code anyway for diagnostics.
AENEAS_EXIT=0
aeneas -backend lean -split-files "$LLBC_FILE" -dest "$STAGE_DIR" || AENEAS_EXIT=$?

if [ "$AENEAS_EXIT" -ne 0 ]; then
  echo "drift: Aeneas exited with code $AENEAS_EXIT (partial translation)" >&2
  echo "  See $STAGE_DIR/ for what was generated. Refine the dlc-core surface" >&2
  echo "  to keep the Aeneas image clean."
  exit 1
fi

# Bootstrap mode: first run, nothing committed yet.
if [ ! -d "$COMMITTED_DIR" ]; then
  echo "drift: $COMMITTED_DIR/ does not exist (bootstrap mode)" >&2
  echo "  Aeneas produced:" >&2
  ls -la "$STAGE_DIR/" >&2
  echo "  Run scripts/aeneas-translate.sh locally and commit the result." >&2
  echo "  CI treats this as a soft-fail until bootstrap." >&2
  exit 0
fi

# Diff committed vs freshly-generated.
MISMATCH=0
for f in "$STAGE_DIR"/*.lean; do
  [ -f "$f" ] || continue
  base="$(basename "$f")"
  committed="$COMMITTED_DIR/$base"
  if [ ! -f "$committed" ]; then
    echo "drift: committed file missing for generated $base" >&2
    MISMATCH=1
    continue
  fi
  if ! diff -q "$committed" "$f" >/dev/null 2>&1; then
    echo "drift: MISMATCH on $base" >&2
    diff "$committed" "$f" || true
    MISMATCH=1
  fi
done

# Also detect files committed but no longer generated (dead translations).
for f in "$COMMITTED_DIR"/*.lean; do
  [ -f "$f" ] || continue
  base="$(basename "$f")"
  if [ ! -f "$STAGE_DIR/$base" ]; then
    echo "drift: committed $base not produced by current Aeneas run" >&2
    MISMATCH=1
  fi
done

if [ "$MISMATCH" -eq 1 ]; then
  echo "" >&2
  echo "ERROR: Aeneas-generated Lean does not match committed version." >&2
  echo "Run: scripts/aeneas-translate.sh" >&2
  exit 1
fi

echo "drift: ✓ committed Aeneas output matches current Rust source"
