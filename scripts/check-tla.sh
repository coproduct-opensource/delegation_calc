#!/usr/bin/env bash
# scripts/check-tla.sh — TLC model-checks the DLC-D view-change TEMPORAL liveness.
#
# The Tamarin models (dlcd-viewchange{,-byz}.spthy) give REACHABILITY (progress is
# possible). This gives the temporal <> (progress is INEVITABLE under fairness) —
# `Liveness == <>decided`, checked by TLC over the complete state space, plus the
# `DecidedStable` safety property. Non-vacuous: the partial-synchrony ASSUME is
# load-bearing (an all-faulty config trips it — see models/tla/README.md).
#
# Needs a JRE (TLC is Java). Downloads tla2tools.jar on first run.

set -euo pipefail
cd "$(dirname "$0")/.."

JAR="tools/tla2tools.jar"
if [ ! -f "$JAR" ]; then
  mkdir -p tools
  echo "check-tla: fetching tla2tools.jar…"
  curl -sL -o "$JAR" https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
fi

if ! command -v java >/dev/null 2>&1; then
  echo "ERROR: java not found — TLC needs a JRE (e.g. apt-get install default-jre / brew install openjdk)"
  exit 1
fi

LOG="$(mktemp)"
trap 'rm -f "$LOG"' EXIT

( cd models/tla && java -cp "../../$JAR" tlc2.TLC -config DlcdViewChange.cfg DlcdViewChange.tla ) 2>&1 | tee "$LOG"

if ! grep -q "Model checking completed. No error has been found." "$LOG"; then
  echo "::error::TLC found a counterexample / error in DlcdViewChange — liveness (<>decided) or safety failed"
  exit 1
fi

echo "check-tla: ✓ Liveness (<>decided) + DecidedStable + TypeOK verified by TLC"
