#!/usr/bin/env bash
# scripts/ledger.sh — emit ledger.json with the current state of every check.
#
# This is the single command that produces DLC's verification artifact.
#
# Since 2026-07 (Phase 0, truth reconciliation) theorem statuses are no
# longer inferred by grep heuristics: they are DECLARED in
# `lean/theorem-status.json` (the single source of truth) and VALIDATED
# here —
#   * a status of `proven` / `proven_fragment` requires the file to be
#     sorry-free AND its declared non-vacuity witness module to exist
#     (CI builds the `Witness` lib, so a broken witness fails there);
#   * outward-facing docs may not claim more than the status file says
#     (scripts/check-claims.sh);
#   * tautological placeholder statements are a build failure
#     (scripts/check-tautologies.sh).
#
# The ledger also emits `phase_gates`: machine-checked exit criteria for
# the current roadmap phase. Phase 0 (truth reconciliation) passes when
# every hygiene check above is green.

set -euo pipefail

cd "$(dirname "$0")/.."
REPO_ROOT="$PWD"

commit_sha="$(git rev-parse HEAD 2>/dev/null || echo 'no-git')"
timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

# --- Theorem statuses: declared + validated -------------------------------

theorems_json="$(python3 - <<'PY'
import json, os, re, sys

status = json.load(open("lean/theorem-status.json"))
out, problems = {}, []

SORRY_RE = re.compile(r'(:=\s+sorry|:=\s+by\s+sorry|^\s*sorry(\s|$))',
                      re.MULTILINE)

for key, entry in status.items():
    if key.startswith("_"):
        continue
    st = entry.get("status", "open")
    path = os.path.join("lean", entry.get("file", ""))
    rec = {"status": st}
    for f in ("fragment", "proven_content", "note"):
        if f in entry:
            rec[f] = entry[f]
    rec["open"] = entry.get("open", [])

    if not os.path.isfile(path):
        problems.append(f"{key}: declared file {path} missing")
        rec["status"] = "invalid"
    elif st in ("proven", "proven_fragment"):
        src = open(path, encoding="utf-8").read()
        if SORRY_RE.search(src):
            problems.append(f"{key}: status {st} but {path} contains sorry")
            rec["status"] = "invalid"
        wit = entry.get("witness")
        if not wit:
            problems.append(f"{key}: status {st} requires a witness module")
            rec["status"] = "invalid"
        elif not os.path.isfile(os.path.join("lean", wit)):
            problems.append(f"{key}: witness {wit} missing")
            rec["status"] = "invalid"
        else:
            rec["witness"] = wit
    out[key] = rec

print(json.dumps({"entries": out, "problems": problems}))
PY
)"

statuses_valid=true
if [[ "$(echo "$theorems_json" | python3 -c 'import json,sys; print(len(json.load(sys.stdin)["problems"]))')" != "0" ]]; then
  statuses_valid=false
  echo "ledger: THEOREM STATUS VALIDATION PROBLEMS:" >&2
  echo "$theorems_json" | python3 -c 'import json,sys; [print("  " + p, file=sys.stderr) for p in json.load(sys.stdin)["problems"]]'
fi

# --- Hygiene gates ---------------------------------------------------------

taut_ok=true
scripts/check-tautologies.sh || taut_ok=false

claims_ok=true
scripts/check-claims.sh || claims_ok=false

# --- Model statuses --------------------------------------------------------

model_status() {
  local dir="$1"
  if [[ ! -d "models/$dir" ]] || [[ -z "$(ls -A "models/$dir" 2>/dev/null)" ]]; then
    echo '{"status":"pending"}'
    return
  fi
  local files
  files=$(find "models/$dir" -maxdepth 1 -type f 2>/dev/null | wc -l | tr -d ' ')
  if [[ "$files" -gt 0 ]]; then
    printf '{"status":"present","files":%s,"runner":"docker_ghcr_eikendev"}' "$files"
  else
    echo '{"status":"pending"}'
  fi
}

# --- Verifier LOC budget + stub detection ----------------------------------
# The LOC gate is meaningless while the verifier is a stub, so the ledger
# reports BOTH the line count and whether an actual implementation exists
# (no unconditional `Err`/`todo!`/"not implemented" in the verify path).

loc_status() {
  local src="crates/dlc-verifier/src"
  if [[ ! -d "$src" ]]; then
    echo '{"lines":0,"budget":2000,"status":"missing","implemented":false}'
    return
  fi
  local lines
  if command -v tokei >/dev/null 2>&1; then
    lines="$(tokei -o json "$src" 2>/dev/null \
      | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d.get("Rust",{}).get("code",0))' \
      2>/dev/null)"
    [[ -z "$lines" ]] && lines=0
  else
    lines="$(find "$src" -name '*.rs' -exec wc -l {} + | tail -1 | awk '{print $1}')"
  fi
  local status="ok"
  if [[ "$lines" -gt 2000 ]]; then status="over_budget"; fi
  # "implemented" targets the VERIFY path (check.rs): true iff it has no
  # unconditional-failure stub markers. The auxiliary replay entry point
  # (§4.4 scope) is tracked separately and does not gate this.
  local implemented=true
  if grep -qE 'not implemented|todo!|unimplemented!' "$src/check.rs" 2>/dev/null; then
    implemented=false
  fi
  printf '{"lines":%s,"budget":2000,"status":"%s","implemented":%s}' \
    "$lines" "$status" "$implemented"
}

# --- Aeneas drift ----------------------------------------------------------

drift_status() {
  if [[ -x scripts/check-drift.sh ]]; then
    scripts/check-drift.sh && echo '{"clean":true}' || echo '{"clean":false}'
  else
    echo '{"clean":null,"note":"drift check not yet wired"}'
  fi
}

# --- Rust test summary ------------------------------------------------------

rust_tests_status() {
  if ! command -v cargo >/dev/null 2>&1; then
    echo '{"status":"cargo_unavailable"}'
    return
  fi
  local out
  out=$(cargo test --workspace 2>&1 || true)
  local passed
  passed=$(echo "$out" | grep -oE '[0-9]+ passed' | grep -oE '[0-9]+' | awk '{s+=$1} END {print s+0}')
  local failed
  failed=$(echo "$out" | grep -oE '[0-9]+ failed' | grep -oE '[0-9]+' | awk '{s+=$1} END {print s+0}')
  printf '{"passed":%s,"failed":%s}' "${passed:-0}" "${failed:-0}"
}

# --- Phase gates ------------------------------------------------------------
# Machine-checked exit criteria per roadmap phase. Later phases extend this
# object (phase2: T3/T4 witnesses flip to required; phase3: DLCAeneas
# equivalence built in CI).

phase0_ok=false
if [[ "$statuses_valid" == "true" && "$taut_ok" == "true" && "$claims_ok" == "true" ]]; then
  phase0_ok=true
fi

# Phase 1 sub-criteria (the gate is their conjunction):
#   verifier_implemented — verify path has no stub markers (see loc_status)
#   test_vectors         — golden vectors are committed (CI runs them)
#   benchmarks           — criterion results vs JWT/Biscuit committed
#   datatracker          — draft submitted (external-artifact evidence file)
p1_vectors=false
[[ -f test-vectors/phase1-vectors.json ]] && p1_vectors=true
p1_impl=false
if ! grep -qE 'not implemented|todo!|unimplemented!' crates/dlc-verifier/src/check.rs 2>/dev/null; then
  p1_impl=true
fi
p1_bench=false
[[ -f test-vectors/bench-results.json ]] && p1_bench=true
p1_datatracker=false
[[ -f draft-ietf/datatracker-url.txt ]] && p1_datatracker=true
phase1_ok=false
if [[ "$p1_impl" == "true" && "$p1_vectors" == "true" && "$p1_bench" == "true" && "$p1_datatracker" == "true" ]]; then
  phase1_ok=true
fi

theorems_entries="$(echo "$theorems_json" | python3 -c 'import json,sys; print(json.dumps(json.load(sys.stdin)["entries"], indent=4))')"

# --- Emit ledger.json -------------------------------------------------------
cat > ledger.json <<EOF
{
  "schema_version": 3,
  "commit": "$commit_sha",
  "generated_at": "$timestamp",
  "theorems": $theorems_entries,
  "hygiene": {
    "statuses_valid": $statuses_valid,
    "tautology_check": $taut_ok,
    "claims_consistency": $claims_ok
  },
  "models": {
    "tamarin":   $(model_status tamarin),
    "proverif":  $(model_status proverif),
    "easycrypt": $(model_status easycrypt)
  },
  "aeneas_drift":  $(drift_status),
  "verifier_loc":  $(loc_status),
  "rust_tests":    $(rust_tests_status),
  "phase_gates": {
    "phase0_truth_reconciliation": $phase0_ok,
    "phase1_working_verifier": $phase1_ok,
    "phase1_detail": {
      "verifier_implemented": $p1_impl,
      "test_vectors": $p1_vectors,
      "benchmarks": $p1_bench,
      "datatracker_submission": $p1_datatracker
    },
    "phase2_first_of_kind_theorems": false,
    "phase3_diagonal": false
  }
}
EOF

echo "ledger.json written:"
cat ledger.json

if [[ "$phase0_ok" != "true" ]]; then
  echo "" >&2
  echo "ledger: Phase-0 gate FAILING (see hygiene checks above)." >&2
  exit 1
fi
