#!/usr/bin/env bash
# scripts/check-tamarin-bite.sh — the replication bite is a CONTROLLED experiment.
#
# `models/tamarin/dlcd-replication.spthy` proves slot agreement holds;
# `models/tamarin/dlcd-replication-bite.spthy` proves disagreement is reachable
# once the one-vote-per-(replica,slot) guard is removed. Run separately, both
# come back "verified" and CI is green — which is exactly the shape of a gate
# that checks nothing. Two ways that pair can rot silently:
#
#   1. The guard gets removed from the MAIN model too (or the models drift
#      apart some other way). Then the bite is no longer isolating the guard,
#      it is comparing two different protocols.
#   2. The bite's attack becomes reachable in the main model for an unrelated
#      reason. The bite still says "verified" while proving nothing about the
#      guard.
#
# So this script asserts the DIFFERENTIAL directly:
#
#   (a) the two theories have byte-identical RULES — the only difference is
#       the removed restriction (perturb the information, never the shape);
#   (b) the bite's own attack lemma, transplanted verbatim into the GUARDED
#       model, is FALSIFIED there.
#
# (b) is the one that matters: it is the machine-checked statement that the
# guard is what makes agreement true, rather than an unrelated feature of the
# encoding. Requires `tamarin-prover` on PATH.

set -euo pipefail
cd "$(dirname "$0")/.."

MAIN="models/tamarin/dlcd-replication.spthy"
BITE="models/tamarin/dlcd-replication-bite.spthy"

for f in "$MAIN" "$BITE"; do
  [ -f "$f" ] || { echo "ERROR: missing $f"; exit 1; }
done

if ! command -v tamarin-prover >/dev/null 2>&1; then
  echo "ERROR: tamarin-prover not found on PATH"
  echo "  macOS: brew tap tamarin-prover/tap && brew install tamarin-prover/tap/tamarin-prover"
  exit 1
fi

# ---------------------------------------------------------------------------
# (a) The rules must be identical; only restrictions/lemmas/comments may differ.
# ---------------------------------------------------------------------------
python3 - "$MAIN" "$BITE" <<'PY'
import re, sys

def strip(s):
    s = re.sub(r'/\*.*?\*/', '', s, flags=re.S)   # block comments
    s = re.sub(r'//[^\n]*', '', s)                # line comments
    return s

def rules(path):
    s = strip(open(path).read())
    found = re.findall(r'rule\s+\w+:.*?(?=\nrule |\nlemma |\nrestriction |\Z)', s, flags=re.S)
    return [re.sub(r'\s+', ' ', r).strip() for r in found]

def restrictions(path):
    return re.findall(r'restriction (\w+):', strip(open(path).read()))

main, bite = sys.argv[1], sys.argv[2]
rm, rb = rules(main), rules(bite)
if rm != rb:
    print("ERROR: the bite is not a controlled experiment — RULES differ.")
    for a, b in zip(rm, rb):
        if a != b:
            print("  main:", a[:200]); print("  bite:", b[:200])
    if len(rm) != len(rb):
        print(f"  rule counts differ: {len(rm)} vs {len(rb)}")
    sys.exit(1)

sm, sb = set(restrictions(main)), set(restrictions(bite))
removed = sm - sb
if removed != {'unique_slot_open'}:
    print(f"ERROR: expected exactly {{'unique_slot_open'}} to be removed in the bite, got {removed}")
    print(f"  main restrictions: {sorted(sm)}")
    print(f"  bite restrictions: {sorted(sb)}")
    sys.exit(1)
if sb - sm:
    print(f"ERROR: the bite ADDS restrictions {sb - sm} — not a controlled experiment")
    sys.exit(1)

print(f"tamarin-bite: ✓ rules identical ({len(rm)} rules); only 'unique_slot_open' removed")
PY

# ---------------------------------------------------------------------------
# (b) The bite's attack lemma must be FALSIFIED in the guarded model.
# ---------------------------------------------------------------------------
CONTROL="$(mktemp -t dlcd-control-XXXXXX).spthy"
trap 'rm -f "$CONTROL"' EXIT

python3 - "$MAIN" "$CONTROL" <<'PY'
import sys
src = open(sys.argv[1]).read()
lemma = '''
// INJECTED BY scripts/check-tamarin-bite.sh — not part of the committed model.
// This is dlcd-replication-bite.spthy's `disagreement_reachable`, verbatim,
// asked of the GUARDED model. It must be FALSIFIED here.
lemma disagreement_reachable_control:
  exists-trace
  "Ex A1 A2 s c1 c2 #i #j.
       Applied(A1, s, c1) @ #i
     & Applied(A2, s, c2) @ #j
     & not(c1 = c2)
     & not (Ex X #r. Reveal(X) @ #r)"

end
'''
open(sys.argv[2], 'w').write(src[:src.rindex('end')] + lemma)
PY

LOG="$(mktemp -t dlcd-control-log-XXXXXX)"
trap 'rm -f "$CONTROL" "$LOG"' EXIT

set +e
tamarin-prover --prove=disagreement_reachable_control "$CONTROL" > "$LOG" 2>&1
set -e

if ! grep -q "summary of summaries" "$LOG"; then
  echo "ERROR: control run did not reach a summary — truncated or crashed"
  tail -20 "$LOG"
  exit 1
fi

if grep -qE "disagreement_reachable_control.*: +verified" "$LOG"; then
  echo "ERROR: the attack is REACHABLE in the guarded model — slot agreement is broken,"
  echo "       or the guard was removed from $MAIN."
  grep -E "disagreement_reachable_control" "$LOG"
  exit 1
fi

if ! grep -qE "disagreement_reachable_control.*: +falsified" "$LOG"; then
  echo "ERROR: control lemma neither verified nor falsified (incomplete/timeout)."
  grep -E "disagreement_reachable_control" "$LOG" || tail -20 "$LOG"
  exit 1
fi

echo "tamarin-bite: ✓ the bite's attack is falsified in the guarded model"
echo "tamarin-bite: ✓ the one-vote-per-slot guard is what buys slot agreement"
