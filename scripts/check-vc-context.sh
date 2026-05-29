#!/usr/bin/env bash
# scripts/check-vc-context.sh — mechanical checks for vc-context/dlc-v1.jsonld
# per the audit closure checklist (item 1):
#   C1: jq parses the file as JSON
#   C2: PyLD compacts a smoke graph against the context
#   C3: each required term resolves to an absolute IRI
#   C4: top-level @protected is true

set -euo pipefail

cd "$(dirname "$0")/.."

CTX="vc-context/dlc-v1.jsonld"

# C1
jq -e '.' "$CTX" > /dev/null
echo "vc-context C1: jq parse OK"

# C2 — PyLD compaction smoke
python3 -c "
from pyld import jsonld
import json
ctx = json.load(open('$CTX'))
out = jsonld.compact({'@context': ctx, '@id': 'urn:smoke'}, ctx)
assert '@context' in out, out
"
echo "vc-context C2: PyLD compaction OK"

# C3 — each required term is an absolute IRI
for term in DlcAffirmationCredential delegationChain obligationSet ifcLabel timeWindow; do
  jq -e --arg t "$term" '
    .["@context"][$t] // .[$t]
    | (if type == "string" then . else .["@id"] end)
    | test("^https?://")
  ' "$CTX" > /dev/null
done
echo "vc-context C3: all 5 required terms map to absolute IRIs"

# C4 — top-level @protected is true
jq -e '.["@context"]["@protected"] == true' "$CTX" > /dev/null
echo "vc-context C4: @protected: true"

echo "vc-context: ✓ all 4 mechanical checks pass"
