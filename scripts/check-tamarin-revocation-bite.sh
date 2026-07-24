#!/usr/bin/env bash
# scripts/check-tamarin-revocation-bite.sh — the revocation bite is a CONTROLLED experiment.
#
# `models/tamarin/dlcd-revocation.spthy` proves revocation soundness (an accepted
# credential was not revoked before acceptance). `dlcd-revocation-bite.spthy` proves
# post-revocation REPLAY is REACHABLE once the `RevocationCheck` restriction is
# removed. Run separately, both come back "verified" and CI is green — the shape of
# a gate that checks nothing. So this script asserts the DIFFERENTIAL directly:
#
#   (a) the two theories have byte-identical RULES — the only difference is the
#       removed `RevocationCheck` restriction (perturb the information, never the shape);
#   (b) the bite's own attack lemma `revoked_replay_reachable`, transplanted verbatim
#       into the GUARDED model, is FALSIFIED there.
#
# (b) is the one that matters: it is the machine-checked statement that the revocation
# check is what makes post-revocation replay impossible, rather than an unrelated
# feature of the encoding. Requires `tamarin-prover` on PATH.

set -euo pipefail
cd "$(dirname "$0")/.."

MAIN="models/tamarin/dlcd-revocation.spthy"
BITE="models/tamarin/dlcd-revocation-bite.spthy"

for f in "$MAIN" "$BITE"; do
  [ -f "$f" ] || { echo "ERROR: missing $f"; exit 1; }
done

if ! command -v tamarin-prover >/dev/null 2>&1; then
  echo "ERROR: tamarin-prover not found on PATH"
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
if removed != {'RevocationCheck'}:
    print(f"ERROR: expected exactly {{'RevocationCheck'}} to be removed in the bite, got {removed}")
    print(f"  main restrictions: {sorted(sm)}")
    print(f"  bite restrictions: {sorted(sb)}")
    sys.exit(1)
if sb - sm:
    print(f"ERROR: the bite ADDS restrictions {sb - sm} — not a controlled experiment")
    sys.exit(1)

print(f"revocation-bite: ✓ rules identical ({len(rm)} rules); only 'RevocationCheck' removed")
PY

# ---------------------------------------------------------------------------
# (b) The bite's attack lemma must be FALSIFIED in the guarded model.
# ---------------------------------------------------------------------------
CONTROL="$(mktemp -t dlcd-revocation-control-XXXXXX).spthy"
LOG="$(mktemp -t dlcd-revocation-control-log-XXXXXX)"
trap 'rm -f "$CONTROL" "$LOG"' EXIT

python3 - "$MAIN" "$CONTROL" <<'PY'
import sys
src = open(sys.argv[1]).read()
lemma = '''
// INJECTED BY scripts/check-tamarin-revocation-bite.sh — not part of the committed
// model. This is dlcd-revocation-bite.spthy's `revoked_replay_reachable`, verbatim,
// asked of the GUARDED model. It must be FALSIFIED here.
lemma revoked_replay_reachable_control:
  exists-trace
  "Ex I cid #r #a.
       Revoked(I, cid) @ #r
     & Accept(I, cid) @ #a
     & #r < #a
     & not (Ex X #x. Reveal(X) @ #x)"

end
'''
open(sys.argv[2], 'w').write(src[:src.rindex('end')] + lemma)
PY

set +e
tamarin-prover --prove=revoked_replay_reachable_control "$CONTROL" > "$LOG" 2>&1
set -e

if ! grep -q "summary of summaries" "$LOG"; then
  echo "ERROR: control run did not reach a summary — truncated or crashed"
  tail -20 "$LOG"
  exit 1
fi

if grep -qE "revoked_replay_reachable_control.*: +verified" "$LOG"; then
  echo "ERROR: post-revocation replay is REACHABLE in the guarded model — revocation is broken,"
  echo "       or the RevocationCheck restriction was removed from $MAIN."
  grep -E "revoked_replay_reachable_control" "$LOG"
  exit 1
fi

if ! grep -qE "revoked_replay_reachable_control.*: +falsified" "$LOG"; then
  echo "ERROR: control lemma neither verified nor falsified (incomplete/timeout)."
  grep -E "revoked_replay_reachable_control" "$LOG" || tail -20 "$LOG"
  exit 1
fi

echo "revocation-bite: ✓ the post-revocation replay attack is falsified in the guarded model"
echo "revocation-bite: ✓ the RevocationCheck restriction is what buys revocation soundness"
