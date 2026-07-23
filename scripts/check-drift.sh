#!/usr/bin/env bash
# scripts/check-drift.sh — verify the Aeneas-generated Lean translations of the
# Charon target crates match their committed trees. DUAL-DIFF (two targets):
#
#   1. crates/dlc-core   → lean/DLC/Aeneas/DlcCore     (the calculus kernel; T1)
#   2. crates/dlc-d-rsm  → lean/DLCD/Aeneas/DlcDRsm     (the DLC-D runtime core;
#                                                        R2.1 — no proof yet)
#
# Drift on EITHER target is a soundness break: the Lean we prove about would no
# longer correspond to the Rust. A single invocation re-emits BOTH and diffs
# each against its committed tree; the script fails if either drifts.
#
# `dlc-d-rsm` path-depends on `dlc-core`, so `charon cargo --preset aeneas` run
# in `crates/dlc-d-rsm` emits ONE `dlc_d_rsm.llbc` (at the cargo WORKSPACE ROOT,
# per the workspace-member serialization rule) that INLINES `dlc_core`; Aeneas
# turns it into a single self-contained `DlcDRsm` tree. The two targets are thus
# translated independently (one charon+aeneas pass each), not carved from one
# llbc.
#
# Bootstrap mode: if a committed tree doesn't exist yet, the pipeline hasn't
# been bootstrapped for that target — we still run the translation and report
# generated content, but don't fail.
#
# Toolchain: charon-driver needs the PINNED nightly active (CHARON_TOOLCHAIN,
# default nightly-2026-06-01 — matches .github/workflows/aeneas.yml's Charon
# pin) plus a forced recompile so it intercepts MIR. Both are handled here.

set -euo pipefail

cd "$(dirname "$0")/.."

STAGE_ROOT="build/aeneas-stage"
CHARON_TOOLCHAIN="${CHARON_TOOLCHAIN:-nightly-2026-06-01}"

# Prefer the PINNED cached Charon/Aeneas binaries (same pins as
# .github/workflows/aeneas.yml) so the LOCAL gate reproduces CI bit-for-bit.
# Unpinned binaries on PATH produce a subtly different translation (e.g. pruned
# vs emitted `PartialEq::ne` axiom stubs) and would report spurious drift.
# Override with CHARON_PIN / AENEAS_PIN, or ignore by pre-placing binaries on PATH.
CHARON_PIN="${CHARON_PIN:-$HOME/.aeneas-ci-cache/charon-cb50ff16b9f1066b8a97dc06da704de2da2fa41c/bin}"
AENEAS_PIN="${AENEAS_PIN:-$HOME/.aeneas-ci-cache/aeneas-nightly-2026.07.23-ad905f5/bin}"
[ -x "$CHARON_PIN/charon" ] && PATH="$CHARON_PIN:$PATH"
[ -x "$AENEAS_PIN/aeneas" ] && PATH="$AENEAS_PIN:$PATH"
export PATH

# Target table: "<pkg-name>|<crate-dir>|<llbc-stem>|<committed-dir>".
# The order matters only for reporting; both are independent.
TARGETS=(
  "dlc-core|crates/dlc-core|dlc_core|lean/DLC/Aeneas/DlcCore"
  "dlc-d-rsm|crates/dlc-d-rsm|dlc_d_rsm|lean/DLCD/Aeneas/DlcDRsm"
)

# Tool-availability gate.
if ! command -v aeneas >/dev/null 2>&1; then
  echo "drift: aeneas not on PATH; skipping (CI installs it)" >&2
  exit 0
fi
if ! command -v charon >/dev/null 2>&1; then
  echo "drift: charon not on PATH; skipping (CI installs it)" >&2
  exit 0
fi

OVERALL_MISMATCH=0

for target in "${TARGETS[@]}"; do
  IFS='|' read -r PKG CRATE_DIR STEM COMMITTED_DIR <<<"$target"
  STAGE_DIR="$STAGE_ROOT/$STEM"

  echo "=== drift target: $PKG ($CRATE_DIR → $COMMITTED_DIR) ==="

  rm -rf "$STAGE_DIR"
  mkdir -p "$STAGE_DIR"

  # Force a recompile so charon-driver intercepts fresh MIR. `cargo clean -p`
  # is INSUFFICIENT: `charon cargo` caches under its own RUSTC_WRAPPER
  # fingerprint (separate from the normal profile), so a plain clean leaves the
  # charon build cached and charon emits no .llbc. Touching the sources bumps
  # mtime and invalidates the fingerprint for every profile, forcing the
  # intercept.
  find "$CRATE_DIR/src" -name '*.rs' -exec touch {} + 2>/dev/null || true

  # Run Charon under the pinned nightly.
  (
    cd "$CRATE_DIR"
    RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" charon cargo --preset aeneas
  )

  # Locate the .llbc Charon emitted. For a cargo *workspace member*, Charon
  # serializes with cwd = the workspace root (cargo's build cwd), so the file
  # lands at the repo root, NOT in $CRATE_DIR. Search both.
  LLBC_FILE=""
  for cand in "$CRATE_DIR/$STEM.llbc" "./$STEM.llbc"; do
    if [ -f "$cand" ]; then LLBC_FILE="$cand"; break; fi
  done
  if [ -z "$LLBC_FILE" ]; then
    echo "drift: Charon did not produce $STEM.llbc (searched $CRATE_DIR/ and repo root)" >&2
    exit 1
  fi

  # Run Aeneas. These surfaces are deliberately Aeneas-translation-friendly, so
  # we expect a clean run; capture the exit code for diagnostics.
  AENEAS_EXIT=0
  RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" \
    aeneas -backend lean -split-files "$LLBC_FILE" -dest "$STAGE_DIR" || AENEAS_EXIT=$?

  if [ "$AENEAS_EXIT" -ne 0 ]; then
    echo "drift: Aeneas exited with code $AENEAS_EXIT on $PKG (partial translation)" >&2
    echo "  See $STAGE_DIR/ for what was generated. Refine the $PKG surface" >&2
    echo "  to keep the Aeneas image clean." >&2
    exit 1
  fi

  # Bootstrap mode: first run for this target, nothing committed yet.
  if [ ! -d "$COMMITTED_DIR" ]; then
    echo "drift: $COMMITTED_DIR/ does not exist (bootstrap mode for $PKG)" >&2
    echo "  Aeneas produced:" >&2
    ls -la "$STAGE_DIR/" >&2
    echo "  Run scripts/aeneas-translate.sh locally and commit the result." >&2
    echo "  Treated as a soft-fail until bootstrap." >&2
    continue
  fi

  # Diff committed vs freshly-generated.
  MISMATCH=0
  for f in "$STAGE_DIR"/*.lean; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    committed="$COMMITTED_DIR/$base"
    if [ ! -f "$committed" ]; then
      echo "drift: committed file missing for generated $base ($PKG)" >&2
      MISMATCH=1
      continue
    fi
    if ! diff -q "$committed" "$f" >/dev/null 2>&1; then
      echo "drift: MISMATCH on $base ($PKG)" >&2
      diff "$committed" "$f" || true
      MISMATCH=1
    fi
  done

  # Also detect files committed but no longer generated (dead translations).
  for f in "$COMMITTED_DIR"/*.lean; do
    [ -f "$f" ] || continue
    base="$(basename "$f")"
    if [ ! -f "$STAGE_DIR/$base" ]; then
      echo "drift: committed $base not produced by current Aeneas run ($PKG)" >&2
      MISMATCH=1
    fi
  done

  if [ "$MISMATCH" -eq 1 ]; then
    OVERALL_MISMATCH=1
    echo "drift: ✗ $PKG DRIFTED" >&2
  else
    echo "drift: ✓ $PKG committed Aeneas output matches current Rust source"
  fi
done

if [ "$OVERALL_MISMATCH" -eq 1 ]; then
  echo "" >&2
  echo "ERROR: Aeneas-generated Lean does not match committed version." >&2
  echo "Run: scripts/aeneas-translate.sh" >&2
  exit 1
fi

echo "drift: ✓ ALL targets clean (dlc-core + dlc-d-rsm)"
