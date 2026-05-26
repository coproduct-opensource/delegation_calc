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
# Each theorem file is a separate lake_lib target; status has four levels:
#
#   stub             — file contains only `_stub : True := trivial`
#   stated           — theorem statement exists (as `def Statement : Prop`)
#                      but proof is not yet inhabited
#   proven_partial   — proven for a restricted fragment (e.g. propositional)
#   proven           — full theorem proven, no `sorry` axioms
#
# Detection is heuristic by source-file scan. Production (post-M1.Q1.d) runs
# `lake build && lean --print-axioms` and compares to expected-axioms.json.

lean_status() {
  local file="$1"
  local path="lean/$file"
  if [[ ! -f "$path" ]]; then
    echo '{"status":"missing"}'
    return
  fi

  # Heuristic (no proper parser; production runs `lake build && lean
  # --print-axioms` instead). We use four signal greps directly on the file:
  #   * `:= sorry` or `:= by sorry`  → `sorry_present`
  #   * `theorem foo_stub` or stub theorem → `stub`
  #   * `theorem` (non-stub)         → `proven_partial`
  #   * `def *Statement *:.*Prop`     → `stated`
  #
  # The `sorry` check uses `:= sorry` / `:= by sorry` patterns specifically
  # so the word appearing in a doc-comment phrase doesn't false-positive.

  local has_sorry
  has_sorry=$(grep -Ec '(:=[[:space:]]+sorry|:=[[:space:]]+by[[:space:]]+sorry)' "$path" || true)
  local has_stub_theorem
  has_stub_theorem=$(grep -Ec '^theorem [a-zA-Z0-9_]+_stub' "$path" || true)
  local has_real_theorem
  # Require `theorem IDENT (` or `theorem IDENT :` to avoid matching prose
  # like "theorem reads:" that wraps into a doc comment.
  has_real_theorem=$(grep -E '^theorem [a-zA-Z0-9_][a-zA-Z_0-9]*[[:space:]]*[:({]' "$path" 2>/dev/null \
                     | grep -Evc '_stub\b' || true)
  local has_statement
  has_statement=$(grep -Ec '^def [A-Z][a-zA-Z0-9_]*Statement.*:.*Prop' "$path" || true)

  if [[ "$has_sorry" -gt 0 ]]; then
    echo '{"status":"sorry_present","axioms":["sorry"]}'
  elif [[ "$has_real_theorem" -gt 0 ]]; then
    echo '{"status":"proven_partial","axioms":[]}'
  elif [[ "$has_statement" -gt 0 ]]; then
    echo '{"status":"stated","axioms":[]}'
  elif [[ "$has_stub_theorem" -gt 0 ]]; then
    echo '{"status":"stub","axioms":[]}'
  else
    echo '{"status":"unknown","axioms":[]}'
  fi
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

# --- Rust test summary ---
# Counts passing tests across the workspace. A quick smoke; the ledger.json
# this generates is for *status visibility*, not regression detection (that's
# CI's job).
rust_tests_status() {
  if ! command -v cargo >/dev/null 2>&1; then
    echo '{"status":"cargo_unavailable"}'
    return
  fi
  local out
  out=$(cargo test --workspace 2>&1 || true)
  # Sum across all test binaries: `\d+ passed; \d+ failed`.
  local passed
  passed=$(echo "$out" | grep -oE '[0-9]+ passed' | grep -oE '[0-9]+' | awk '{s+=$1} END {print s+0}')
  local failed
  failed=$(echo "$out" | grep -oE '[0-9]+ failed' | grep -oE '[0-9]+' | awk '{s+=$1} END {print s+0}')
  printf '{"passed":%s,"failed":%s}' "${passed:-0}" "${failed:-0}"
}

# --- Emit ledger.json ---
cat > ledger.json <<EOF
{
  "schema_version": 2,
  "commit": "$commit_sha",
  "generated_at": "$timestamp",
  "theorems": {
    "T1_decidability":         $(lean_status DLC/Decidability.lean),
    "T2_correspondence":       $(lean_status DLC/Correspondence.lean),
    "T3_noninterference":      $(lean_status DLC/NonInterference.lean),
    "T4_obligation":           $(lean_status DLC/ObligationSoundness.lean),
    "protocol_correspondence": $(lean_status DLC/ProtocolCorrespondence.lean),
    "substitution_lemma":      $(lean_status DLC/Subst.lean),
    "subject_reduction":       $(lean_status DLC/Reduce.lean)
  },
  "models": {
    "tamarin":   $(model_status tamarin),
    "proverif":  $(model_status proverif),
    "easycrypt": $(model_status easycrypt)
  },
  "aeneas_drift":  $(drift_status),
  "verifier_loc":  $(loc_status),
  "rust_tests":    $(rust_tests_status)
}
EOF

echo "ledger.json written:"
cat ledger.json
