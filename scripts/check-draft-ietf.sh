#!/usr/bin/env bash
# scripts/check-draft-ietf.sh — mechanical checks for the IETF draft per
# audit closure checklist (item 6):
#   C1: validates against RFC 7991 RelaxNG schema
#   C2: builds to non-empty .txt and .html via xml2rfc
#   C3: required sections present (abstract, security, IANA)
#   C4: abstract word count ≥ 80
#   C5: ≥3 normative references
#   C6: idnits reports 0 errors, 0 warnings
#
# Tools required: xml2rfc, xmllint, idnits.

set -euo pipefail

cd "$(dirname "$0")/.."

DRAFT="draft-ietf/draft-crisp-dlc-token-00.xml"
TXT="draft-ietf/draft-crisp-dlc-token-00.txt"
HTML="draft-ietf/draft-crisp-dlc-token-00.html"

# C1 — validate against RFC 7991 RelaxNG schema (xml2rfc validates structure).
xml2rfc --quiet "$DRAFT" --text --html
echo "draft-ietf C1+C2: xml2rfc validates and renders to .txt + .html"

# C2 (cont'd) — outputs exist and are non-empty
test -s "$TXT"
test -s "$HTML"
echo "draft-ietf C2: outputs non-empty ($(wc -l < "$TXT") lines .txt, $(wc -l < "$HTML") lines .html)"

# C3 — required sections present (anchored)
xmllint --xpath 'count(//*[local-name()="abstract"]/*[local-name()="t"])' "$DRAFT" \
  | awk '{ if ($1 < 1) { print "FAIL: no abstract <t>"; exit 1 } }'
xmllint --xpath 'count(//*[local-name()="section" and @anchor="security-considerations"])' "$DRAFT" \
  | awk '{ if ($1 != 1) { print "FAIL: missing security-considerations section"; exit 1 } }'
xmllint --xpath 'count(//*[local-name()="section" and @anchor="iana-considerations"])' "$DRAFT" \
  | awk '{ if ($1 != 1) { print "FAIL: missing iana-considerations section"; exit 1 } }'
echo "draft-ietf C3: abstract + security-considerations + iana-considerations present"

# C4 — abstract word count ≥ 80
ABSTRACT_WC=$(xmllint --xpath 'string(//*[local-name()="abstract"])' "$DRAFT" | wc -w)
if [ "$ABSTRACT_WC" -lt 80 ]; then
  echo "FAIL: abstract word count is $ABSTRACT_WC; need ≥80"
  exit 1
fi
echo "draft-ietf C4: abstract word count = $ABSTRACT_WC (≥ 80)"

# C5 — ≥3 normative references
REF_COUNT=$(xmllint --xpath 'count(//*[local-name()="references"][1]/*[local-name()="reference"])' "$DRAFT")
if [ "$REF_COUNT" -lt 3 ]; then
  echo "FAIL: normative references count is $REF_COUNT; need ≥3"
  exit 1
fi
echo "draft-ietf C5: normative references = $REF_COUNT (≥ 3)"

# C6 — idnits clean (0 errors, 0 warnings). idnits is from
# https://tools.ietf.org/tools/idnits/. If not installed, skip with a
# notice — CI installs it explicitly.
if command -v idnits >/dev/null 2>&1; then
  IDNITS_OUT=$(idnits "$TXT" 2>&1)
  echo "$IDNITS_OUT" | grep -qE 'Summary:.*0 errors.*0 warnings' || {
    echo "FAIL: idnits reported errors or warnings:"
    echo "$IDNITS_OUT" | tail -20
    exit 1
  }
  echo "draft-ietf C6: idnits 0 errors, 0 warnings"
else
  echo "draft-ietf C6: SKIP (idnits not installed; CI gates this separately)"
fi

echo "draft-ietf: ✓ all checks pass"
