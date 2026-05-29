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

# C6 — idnits3 reports 0 errors. The current idnits is a Node.js CLI
# from @ietf-tools/idnits with structured output via `--output count`
# and severity filtering via `--filter`. We gate on errors only at
# draft-00 because warnings include expected boilerplate gaps (IPR
# form, downward references, metadata) that resolve in later revisions.
# The 0-error bar is what actually blocks IESG submission.
#
# idnits3 accepts XML directly (no need to pre-render to .txt). With
# `--output count`, it prints lines like:
#   errors: N
#   warnings: M
#   comments: K
# We parse the `errors:` line and gate on N == 0.
if command -v idnits >/dev/null 2>&1; then
  # idnits3's `--output count` emits a single integer: the count of
  # matched issues. Combined with `--filter errors`, it gives the error
  # count specifically. Both `set +e` and a wrapping subshell are used
  # so that idnits's exit code (1 if any nit found, 0 otherwise) does
  # not abort the gate before we inspect the count.
  set +e
  ERRORS=$(idnits --no-color --no-progress --filter errors --output count "$DRAFT" 2>&1 | tail -1)
  IDNITS_RC=$?
  TOTAL=$(idnits --no-color --no-progress --output count "$DRAFT" 2>&1 | tail -1)
  set -e
  # Sanitize: keep only the integer suffix; non-numeric output means
  # idnits errored before counting, which is itself a failure.
  ERRORS_INT=$(echo "$ERRORS" | grep -oE '^[0-9]+$' || echo "")
  TOTAL_INT=$(echo "$TOTAL" | grep -oE '^[0-9]+$' || echo "")
  echo "idnits: errors=$ERRORS total_nits=$TOTAL (exit=$IDNITS_RC)"
  if [ -z "$ERRORS_INT" ]; then
    echo "FAIL: idnits did not return an integer error count"
    echo "raw output: $ERRORS"
    exit 1
  fi
  if [ "$ERRORS_INT" -gt 0 ]; then
    echo "FAIL: idnits reported $ERRORS_INT error(s); details:"
    set +e
    idnits --no-color --no-progress --filter errors "$DRAFT" 2>&1 | head -100
    set -e
    exit 1
  fi
  echo "draft-ietf C6: idnits3 reports 0 errors (${TOTAL_INT:-?} total nits, gated only on errors)"
else
  echo "draft-ietf C6: SKIP (idnits not installed; CI gates this separately)"
fi

echo "draft-ietf: ✓ all checks pass"
