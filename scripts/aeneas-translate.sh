#!/usr/bin/env bash
# scripts/aeneas-translate.sh — regenerate `lean/DLC/Aeneas/DlcCore/` from
# the current `crates/dlc-core` source via the Charon + Aeneas pipeline.
#
# Prerequisites (any one of):
#   - `charon` and `aeneas` binaries on PATH
#   - `nix` (uses `nix run github:aeneasverif/aeneas#...`)
#
# Charon nightly + Aeneas release are pinned in `.github/workflows/aeneas.yml`
# (CHARON_NIGHTLY and AENEAS_RELEASE env vars). When regenerating locally,
# install matching versions to avoid drift between local and CI output.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
CORE_DIR="$ROOT_DIR/crates/dlc-core"
OUTPUT_DIR="$ROOT_DIR/lean/DLC/Aeneas"

echo "=== Aeneas Pipeline: dlc-core → Lean 4 ==="
echo ""

# Step 1: Charon MIR extraction.
echo "Step 1: Extracting Rust MIR with Charon..."
cd "$CORE_DIR"

if command -v charon &>/dev/null; then
    charon cargo --preset aeneas
elif command -v nix &>/dev/null; then
    echo "  (using nix run for charon)"
    nix run github:aeneasverif/aeneas#charon -- cargo --preset aeneas
else
    echo "ERROR: Neither 'charon' nor 'nix' found in PATH."
    echo "Install Nix: https://nixos.org/download.html"
    echo "Or build Charon: https://github.com/AeneasVerif/charon"
    exit 1
fi

LLBC_FILE="$CORE_DIR/dlc_core.llbc"
if [ ! -f "$LLBC_FILE" ]; then
    echo "ERROR: Charon did not produce $LLBC_FILE"
    exit 1
fi
echo "  ✓ MIR extracted: $LLBC_FILE"

# Step 2: Aeneas translation.
echo ""
echo "Step 2: Translating LLBC → Lean 4 with Aeneas..."

# Stage Aeneas output, then sync into the committed location.
STAGE_DIR="$ROOT_DIR/build/aeneas-stage"
rm -rf "$STAGE_DIR"
mkdir -p "$STAGE_DIR"

if command -v aeneas &>/dev/null; then
    aeneas -backend lean -split-files "$LLBC_FILE" -dest "$STAGE_DIR"
elif command -v nix &>/dev/null; then
    echo "  (using nix run for aeneas)"
    nix run github:aeneasverif/aeneas -- -backend lean -split-files "$LLBC_FILE" -dest "$STAGE_DIR"
else
    echo "ERROR: Neither 'aeneas' nor 'nix' found in PATH."
    exit 1
fi

echo "  ✓ Lean files generated in $STAGE_DIR/"
ls -la "$STAGE_DIR/"

# Step 3: Sync into the committed location.
echo ""
echo "Step 3: Syncing Aeneas output to $OUTPUT_DIR/DlcCore/..."
mkdir -p "$OUTPUT_DIR/DlcCore"
for f in "$STAGE_DIR"/*.lean; do
    [ -f "$f" ] && cp "$f" "$OUTPUT_DIR/DlcCore/$(basename "$f")"
done
echo "  ✓ Committed location updated: $OUTPUT_DIR/DlcCore/"
ls -la "$OUTPUT_DIR/DlcCore/" 2>/dev/null || true

# Step 4: Verify with lake (if available).
echo ""
if command -v lake &>/dev/null && [ -f "$ROOT_DIR/lean/lakefile.lean" ]; then
    echo "Step 4: Verifying with lake build..."
    cd "$ROOT_DIR/lean"
    if lake build DLC.Aeneas.DlcCore; then
        echo "  ✓ Lean verification passed"
    else
        echo "  ⚠ lake build failed — update DlcCore.lean to re-export the generated modules"
    fi
else
    echo "Step 4: Skipped (lake not in PATH)"
fi

echo ""
echo "=== Pipeline complete ==="
echo ""
echo "Next steps:"
echo "  1. Review generated files in $OUTPUT_DIR/DlcCore/"
echo "  2. Ensure $OUTPUT_DIR/DlcCore.lean re-exports them"
echo "  3. Commit and push"
