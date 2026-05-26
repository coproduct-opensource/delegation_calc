#!/usr/bin/env bash
# scripts/ledger.sh — emit ledger.json with the current state of every check.
#
# This is the single command that produces DLC's verification artifact. Runs
# every Lean build, every model checker, every drift check, and the LOC
# budget gate. Outputs `ledger.json` at the repo root.
#
# Week-1 stub: most checks return "pending" because the theorems and models
# don't yet exist. The shape of `ledger.json` is locked here so downstream
# consumers can pin against it.

set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$PWD"

commit_sha="$(git rev-parse HEAD 2>/dev/null || echo 'no-git')"
timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# --- Lean theorem statuses ---
# Each theorem file is a separate lake_lib target; we report status per file.
# Week-1: all `pending` (stubs only).

lean_status() {
  local file="$1"
  if [[ ! -f "lean/$file" ]]; then
    echo '{"status":"missing"}'
    return
  fi
  # In production: `lake build $(basename ...)` && `lean --print-axioms`.
  # Week-1: report "stub" since each file contains only a `_stub : True := trivial`.
  echo '{"status":"stub","axioms":[]}'
}

# --- Model statuses ---
# Tamarin / ProVerif / EasyCrypt scripts not yet present. Report "pending".

model_status() {
  local dir="$1"
  if [[ ! -d "models/$dir" ]] || [[ -z "$(ls -A "models/$dir" 2>/dev/null)" ]]; then
    echo '{"status":"pending"}'
  else
    echo '{"status":"present","note":"runner not yet wired"}'
  fi
}

# --- Verifier LOC budget ---
# Hard gate at 2000. Uses `tokei` if available, else `wc -l` as a coarse fallback.
loc_status() {
  local src="crates/dlc-verifier/src"
  if [[ ! -d "$src" ]]; then
    echo '{"lines":0,"budget":2000,"status":"missing"}'
    return
  fi
  local lines
  if command -v tokei >/dev/null 2>&1; then
    # tokei's JSON uses `"code":N` (no space). Parse the Rust subtree's top-level code count.
    lines="$(tokei -o json "$src" 2>/dev/null \
      | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d.get("Rust",{}).get("code",0))' \
      2>/dev/null)"
    [[ -z "$lines" ]] && lines=0
  else
    lines="$(find "$src" -name '*.rs' -exec wc -l {} + | tail -1 | awk '{print $1}')"
  fi
  local status="ok"
  if [[ "$lines" -gt 2000 ]]; then status="over_budget"; fi
  printf '{"lines":%s,"budget":2000,"status":"%s"}' "$lines" "$status"
}

# --- Aeneas drift ---
# Production runs `scripts/check-drift.sh`. Week-1 reports "pending".
drift_status() {
  if [[ -x scripts/check-drift.sh ]]; then
    scripts/check-drift.sh && echo '{"clean":true}' || echo '{"clean":false}'
  else
    echo '{"clean":null,"note":"drift check not yet wired"}'
  fi
}

# --- Emit ledger.json ---
cat > ledger.json <<EOF
{
  "schema_version": 1,
  "commit": "$commit_sha",
  "generated_at": "$timestamp",
  "theorems": {
    "T1_decidability":    $(lean_status DLC/Decidability.lean),
    "T2_correspondence":  $(lean_status DLC/Correspondence.lean),
    "T3_noninterference": $(lean_status DLC/NonInterference.lean),
    "T4_obligation":      $(lean_status DLC/ObligationSoundness.lean),
    "protocol_correspondence": $(lean_status DLC/ProtocolCorrespondence.lean)
  },
  "models": {
    "tamarin":   $(model_status tamarin),
    "proverif":  $(model_status proverif),
    "easycrypt": $(model_status easycrypt)
  },
  "aeneas_drift":  $(drift_status),
  "verifier_loc":  $(loc_status)
}
EOF

echo "ledger.json written:"
cat ledger.json
