#!/usr/bin/env bash
# scripts/aeneas-translate.sh — regenerate `lean/DLC/Aeneas/DlcCore.lean` from
# the current `crates/dlc-core` source. Forked from `nucleus/scripts/`.
#
# Week-1 stub. Real pipeline lands at M1.Q1.d.

set -euo pipefail

cd "$(dirname "$0")/.."

echo "aeneas-translate: stub. Wire at M1.Q1.d."
echo "  Production pipeline:"
echo "    1. charon --crate crates/dlc-core --output build/dlc_core.llbc"
echo "    2. aeneas --backend lean build/dlc_core.llbc -o lean/DLC/Aeneas/"
echo "    3. Commit the regenerated file."

exit 0
