#!/usr/bin/env bash
# scripts/aeneas-translate.sh — regenerate the committed Aeneas Lean trees from
# the current Rust source via the Charon + Aeneas pipeline. DUAL TARGET:
#
#   1. crates/dlc-core   → lean/DLC/Aeneas/DlcCore
#   2. crates/dlc-d-rsm  → lean/DLCD/Aeneas/DlcDRsm
#
# Prerequisites (any one of):
#   - `charon` and `aeneas` binaries on PATH
#   - `nix` (uses `nix run github:aeneasverif/aeneas#...`)
#
# Charon nightly + Aeneas release are pinned in `.github/workflows/aeneas.yml`
# (CHARON_TOOLCHAIN / the aeneas-version pin). When regenerating locally,
# install matching versions to avoid drift between local and CI output.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
CHARON_TOOLCHAIN="${CHARON_TOOLCHAIN:-nightly-2026-06-01}"

# Prefer the PINNED cached Charon/Aeneas binaries (same pins as
# .github/workflows/aeneas.yml) so local regeneration reproduces CI bit-for-bit.
CHARON_PIN="${CHARON_PIN:-$HOME/.aeneas-ci-cache/charon-cb50ff16b9f1066b8a97dc06da704de2da2fa41c/bin}"
AENEAS_PIN="${AENEAS_PIN:-$HOME/.aeneas-ci-cache/aeneas-nightly-2026.07.23-ad905f5/bin}"
[ -x "$CHARON_PIN/charon" ] && PATH="$CHARON_PIN:$PATH"
[ -x "$AENEAS_PIN/aeneas" ] && PATH="$AENEAS_PIN:$PATH"
export PATH

# Charon `--opaque` patterns (name-matcher syntax). These keep the derived
# `Debug`/`Hash` trait impls for the *recursive* core types OPAQUE, i.e. their
# method bodies are not emitted; they become external axioms in
# `FunsExternal_Template.lean` instead. Aeneas emits a recursive derived
# `Debug`/`Hash` `fmt`/`hash` body that self-references the impl's own instance
# with a FORWARD reference and no `mutual` block, which does not elaborate under
# Lean 4.31 (`Unknown constant …Insts.CoreFmtDebug`). Opacifying the impl keeps
# the instance record (referencing the now-axiom method) but drops the offending
# body. `Debug`/`Hash` are off every correspondence compute path
# (formatting/hashing only), so the axioms are sound (see FunsExternal.lean).
# The Rust `#[derive(Debug, Hash)]` is UNCHANGED — tests still get real `Debug`.
# MUST stay identical to the list in scripts/check-drift.sh so local == CI.
CHARON_OPAQUE=(
  --opaque 'dlc_core::principal::{impl core::fmt::Debug for dlc_core::principal::Principal}'
  --opaque 'dlc_core::obligation::{impl core::fmt::Debug for dlc_core::obligation::Obligation}'
  --opaque 'dlc_core::syntax::{impl core::fmt::Debug for dlc_core::syntax::Prop}'
  --opaque 'dlc_core::syntax::{impl core::fmt::Debug for dlc_core::syntax::Term}'
  --opaque 'dlc_core::principal::{impl core::hash::Hash for dlc_core::principal::Principal}'
)

# Target table: "<pkg-name>|<crate-dir>|<llbc-stem>|<committed-subdir>".
# `committed-subdir` is relative to lean/ .
TARGETS=(
  "dlc-core|crates/dlc-core|dlc_core|DLC/Aeneas/DlcCore"
  "dlc-d-rsm|crates/dlc-d-rsm|dlc_d_rsm|DLCD/Aeneas/DlcDRsm"
)

charon_run() {
  # $1 = crate dir (absolute)
  cd "$1"
  if command -v charon &>/dev/null; then
    RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" charon cargo --preset aeneas "${CHARON_OPAQUE[@]}"
  elif command -v nix &>/dev/null; then
    echo "  (using nix run for charon)"
    nix run github:aeneasverif/aeneas#charon -- cargo --preset aeneas "${CHARON_OPAQUE[@]}"
  else
    echo "ERROR: Neither 'charon' nor 'nix' found in PATH." >&2
    exit 1
  fi
}

aeneas_run() {
  # $1 = llbc file, $2 = dest dir
  if command -v aeneas &>/dev/null; then
    RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" aeneas -backend lean -split-files "$1" -dest "$2"
  elif command -v nix &>/dev/null; then
    echo "  (using nix run for aeneas)"
    nix run github:aeneasverif/aeneas -- -backend lean -split-files "$1" -dest "$2"
  else
    echo "ERROR: Neither 'aeneas' nor 'nix' found in PATH." >&2
    exit 1
  fi
}

for target in "${TARGETS[@]}"; do
  IFS='|' read -r PKG CRATE_DIR STEM OUT_SUBDIR <<<"$target"
  CRATE_ABS="$ROOT_DIR/$CRATE_DIR"
  OUT_DIR="$ROOT_DIR/lean/$OUT_SUBDIR"
  STAGE_DIR="$ROOT_DIR/build/aeneas-stage/$STEM"

  echo "=== Aeneas Pipeline: $PKG → Lean 4 ==="
  echo ""

  # Step 1: Charon MIR extraction (forced recompile for a clean intercept).
  echo "Step 1: Extracting Rust MIR with Charon ($PKG)..."
  # Touch sources to force a recompile: `charon cargo` caches under its own
  # RUSTC_WRAPPER fingerprint, so a plain `cargo clean -p` leaves it cached and
  # charon emits no .llbc. Bumping mtime invalidates every profile's fingerprint.
  find "$CRATE_ABS/src" -name '*.rs' -exec touch {} + 2>/dev/null || true
  ( charon_run "$CRATE_ABS" )

  # For a workspace member, Charon serializes the .llbc to the workspace root.
  LLBC_FILE=""
  for cand in "$CRATE_ABS/$STEM.llbc" "$ROOT_DIR/$STEM.llbc"; do
    if [ -f "$cand" ]; then LLBC_FILE="$cand"; break; fi
  done
  if [ -z "$LLBC_FILE" ]; then
    echo "ERROR: Charon did not produce $STEM.llbc (searched $CRATE_DIR/ and repo root)" >&2
    exit 1
  fi
  echo "  ✓ MIR extracted: $LLBC_FILE"

  # Step 2: Aeneas translation to a staging dir.
  echo ""
  echo "Step 2: Translating LLBC → Lean 4 with Aeneas ($PKG)..."
  rm -rf "$STAGE_DIR"
  mkdir -p "$STAGE_DIR"
  aeneas_run "$LLBC_FILE" "$STAGE_DIR"
  echo "  ✓ Lean files generated in $STAGE_DIR/"

  # Step 3: Sync into the committed location.
  echo ""
  echo "Step 3: Syncing Aeneas output to $OUT_DIR/..."
  mkdir -p "$OUT_DIR"
  for f in "$STAGE_DIR"/*.lean; do
    [ -f "$f" ] && cp "$f" "$OUT_DIR/$(basename "$f")"
  done
  echo "  ✓ Committed location updated: $OUT_DIR/"
  ls -la "$OUT_DIR/" 2>/dev/null || true
  echo ""
done

echo "=== Pipeline complete (dlc-core + dlc-d-rsm) ==="
echo ""
echo "Next steps:"
echo "  1. Review generated files under lean/DLC/Aeneas/DlcCore/ and lean/DLCD/Aeneas/DlcDRsm/"
echo "  2. Ensure the re-export modules (DlcCore.lean / DlcDRsm.lean) import them"
echo "  3. bash scripts/check-drift.sh  (must be clean for BOTH targets)"
echo "  4. Commit and push"
