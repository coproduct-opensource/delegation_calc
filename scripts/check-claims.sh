#!/usr/bin/env bash
# scripts/check-claims.sh — public claims may not exceed the ledger.
#
# Cross-references outward-facing documents (README.md, RELEASES.md,
# paper/, draft-ietf/, spec/, models/easycrypt/, vc-context/) against
# lean/theorem-status.json. Any claim-pattern asserting more than the
# recorded status fails CI.
#
# Matching is over a sliding TWO-LINE window (so wrapping a claim across
# a line break does not evade the gate), with honesty-marker qualifiers
# exempting windows that describe status accurately. This is a tripwire,
# not a proof of honesty: it catches the claim shapes that have actually
# occurred (2026-07 audit), and the qualifier list is deliberately
# generous to keep honest prose green. New overclaim shapes should be
# added here as rules when found.

set -euo pipefail
cd "$(dirname "$0")/.."

python3 - <<'PY'
import json, re, sys, glob

status = json.load(open("lean/theorem-status.json"))
def st(k): return status.get(k, {}).get("status", "open")

DOCS = (
    ["README.md", "RELEASES.md"]
    + glob.glob("paper/**/*.tex", recursive=True)
    + glob.glob("paper/README.md")
    + glob.glob("draft-ietf/**/*.xml", recursive=True)
    + glob.glob("draft-ietf/**/*.md", recursive=True)
    + glob.glob("spec/**/*.md", recursive=True)
    + glob.glob("models/easycrypt/**/*.eca", recursive=True)
    + glob.glob("vc-context/**/*.md", recursive=True)
)

# Each rule: (regex, condition_fn, qualifiers, explanation). A window
# matching the regex is a violation UNLESS the condition holds OR the
# window contains one of the qualifiers (honesty markers) — a sentence
# that says "proven ... for the propositional fragment" or "stated;
# ... open" is describing status accurately, not overclaiming.
four = ["T1_decidability", "T2_correspondence", "T3_noninterference", "T4_obligation"]
HONESTY_COMMON = ["stated", "open", "overstated", "vacuous", "unproven",
                  "superseded", "correction", "inconsistent", "audit",
                  "was claimed", "as claimed", "intended", "target",
                  "refutation", "refutable", "not ", "placeholder",
                  "skeleton only", "does not exist", "encodes nothing"]
RULES = [
    (r"all four (headline )?theorems.*(machine.checked|proven|verified)",
     lambda: all(st(k) == "proven" for k in four), HONESTY_COMMON,
     "requires status=proven for T1–T4"),
    (r"four mechanized.*theorems|four.*theorems.*mechanized",
     lambda: all(st(k) == "proven" for k in four), HONESTY_COMMON,
     "requires status=proven for T1–T4"),
    (r"\bT1\b.*\bproven\b",
     lambda: st("T1_decidability") == "proven",
     HONESTY_COMMON + ["fragment", "propositional"],
     "T1 is proven only for the propositional fragment — say so"),
    (r"\bT2\b.*\b(proven|machine.checked)\b",
     lambda: st("T2_correspondence") == "proven",
     HONESTY_COMMON + ["symbolic characterization", "characterization"],
     "T2 is stated; only the symbolic characterization is proven"),
    (r"\bT3\b.*\b(proven|machine.checked)\b",
     lambda: st("T3_noninterference") == "proven",
     HONESTY_COMMON + ["reflexivity"],
     "T3 is stated; the current lemma is one-run reflexivity"),
    (r"\bT4\b.*\b(proven|machine.checked)\b",
     lambda: st("T4_obligation") == "proven",
     HONESTY_COMMON + ["non-introduction"],
     "T4 is stated; the proven direction is vacuous"),
    # `discharg` (no suffix) also catches "discharge ... in flight" and
    # "discharges the gap" shapes; the EasyCrypt reduction does not exist.
    (r"discharg\w*\s+(at\s+M2\.M13|by\s+(the\s+)?easycrypt)|easycrypt\s+bridge.*discharg|discharg\w*\s+the\s+gap",
     lambda: False, HONESTY_COMMON,
     "the EasyCrypt discharge does not exist (axiom body was `true`); do not claim it"),
    # Complexity bound: Unicode `·`, LaTeX `\cdot`, and plain-space forms.
    (r"O\(\|?M\|?\s*(·|\\cdot|\*)?\s*(\\?log)",
     lambda: False, HONESTY_COMMON + ["designed", "bound is a"],
     "the complexity bound is unproven in any form — mark it as a target, not a fact"),
    # "structurally complete" for the EasyCrypt skeleton was audit-flagged.
    (r"structurally complete",
     lambda: False, HONESTY_COMMON,
     "the EasyCrypt file is a shape-only skeleton; 'structurally complete' oversells it"),
]

violations = []
for path in DOCS:
    try:
        lines = open(path, encoding="utf-8").read().splitlines()
    except OSError:
        continue
    reported = set()
    for i in range(len(lines)):
        window = lines[i] + " " + (lines[i + 1] if i + 1 < len(lines) else "")
        # Qualifiers are searched one line beyond the match window on
        # each side, so a claim whose honesty marker lands just across
        # a line break is not a false positive.
        scope = " ".join(lines[max(0, i - 1):i + 3]).lower()
        for pat, ok, qualifiers, why in RULES:
            if re.search(pat, window, re.IGNORECASE) and not ok() \
                    and not any(q in scope for q in qualifiers):
                key = (i // 2, why)  # avoid double-reporting overlapping windows
                if key not in reported:
                    reported.add(key)
                    violations.append(
                        f"{path}:{i + 1}: [{why}] {window.strip()[:120]}")

if violations:
    print("check-claims: PUBLIC CLAIMS EXCEED LEDGER STATUS", file=sys.stderr)
    for v in violations:
        print("  " + v, file=sys.stderr)
    print(f"\n{len(violations)} violation(s). Align the document with "
          "lean/theorem-status.json (or, if a theorem really closed, "
          "update the status file in the same PR).", file=sys.stderr)
    sys.exit(1)

print("check-claims: ✓ public claims match ledger status")
PY
