#!/usr/bin/env bash
# scripts/check-decide-coverage.sh — ratchet on the decide-coverage fraction.
#
# `decide_pure` implements an arm for every `Term` constructor. `DecideSquare.PropFrag` —
# the fragment `rust_infer_sound` is proved over — covers a subset. That fraction is the
# honest answer to "is DLC verified", and until it is a number in CI it is a thing people
# round up.
#
# Both sets are DERIVED from source (crates/dlc-core/src/syntax.rs and
# lean/DLC/DecideSquare.lean), never declared in a third place that can go stale. The
# baseline pins the SET, not the count: deleting an unproven arm would raise the
# percentage without proving anything, and the ratchet refuses that.
#
# Fails in BOTH directions. A rise must be recorded deliberately with `--update`, or an
# improvement silently becomes the new allowance and the next fall back to it reads clean.

set -euo pipefail

cd "$(dirname "$0")/.."

cargo run -q -p dlc-coverage
