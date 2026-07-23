#!/usr/bin/env bash
# scripts/check-tautologies.sh — tripwire against "no-sorry theater".
#
# The 2026-07 audit found a recurring pattern: placeholder `Statement`
# definitions whose bodies were tautologies (`True`, `x = x ∧ y = y`
# chains, identity-serializer existentials), which let files pass the
# no-sorry gate while proving nothing. This script fails CI when the
# pattern reappears.
#
# Detection is intentionally conservative (pattern-class, not a prover);
# comments are stripped before scanning, and self-equalities are only
# flagged when they stand alone as a proposition (start of a body, or a
# conjunct) — `f a a = a` (idempotence laws etc.) is NOT flagged.
#
# A hit must either be removed or added to
# `scripts/tautology-allowlist.txt` (one `file:line-identifier —
# justification` per line). The allowlist is expected to stay empty.

set -euo pipefail
cd "$(dirname "$0")/.."

python3 - <<'PY'
import os, re, sys, glob

ALLOWLIST = "scripts/tautology-allowlist.txt"
allow = set()
if os.path.isfile(ALLOWLIST):
    for line in open(ALLOWLIST, encoding="utf-8"):
        line = line.strip()
        if line and not line.startswith("#"):
            allow.add(line.split(" ")[0].split("—")[0].strip())

def strip_comments(src: str) -> str:
    # Remove nested block comments /- ... -/ and line comments,
    # preserving line count so line numbers stay accurate.
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        two = src[i:i+2]
        if two == "/-":
            depth += 1; i += 2; continue
        if two == "-/" and depth > 0:
            depth -= 1; i += 2; continue
        if depth == 0 and two == "--":
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(src[i] if depth == 0 or src[i] == "\n" else ("\n" if src[i] == "\n" else " "))
        i += 1
    return "".join(out)

IDENT = r"[A-Za-z_Ͱ-Ͽἀ-῿][A-Za-z0-9_'Ͱ-Ͽἀ-῿₀-₉]*"
# Self-equality as a standalone proposition: preceded by := , ∧ ( or line
# start (possibly whitespace), NOT by another identifier (application).
SELF_EQ = re.compile(
    r"(?:^|:=|∧|→|\(|,)\s*(" + IDENT + r")\s*=\s*\1(?![\w'₀-₉])",
    re.MULTILINE)
# True-bodied bindings (`:= True`, newline-tolerant) and declarations
# typed at `True`.
TRUE_BODY = re.compile(
    r":=\s*True(?![\w'.₀-₉])|"
    r"^\s*(?:def|abbrev|theorem)\s+(?:" + IDENT + r")\s*:\s*True(?![\w'.₀-₉])",
    re.MULTILINE)

violations = []
scan_paths = sorted(
    glob.glob("lean/DLC/**/*.lean", recursive=True)
    + glob.glob("lean/DLCD/**/*.lean", recursive=True)
)
for path in scan_paths:
    if "/Witness/" in path or "/Aeneas/" in path:
        continue
    src = strip_comments(open(path, encoding="utf-8").read())
    for m in SELF_EQ.finditer(src):
        ln = src[:m.start()].count("\n") + 1
        key = f"{path}:{ln}"
        if key not in allow:
            violations.append((key, f"self-equality `{m.group(1)} = {m.group(1)}`"))
    for m in TRUE_BODY.finditer(src):
        ln = src[:m.start()].count("\n") + 1
        key = f"{path}:{ln}"
        if key not in allow:
            violations.append((key, "True-bodied declaration"))

if violations:
    print("check-tautologies: TAUTOLOGY PATTERN(S) FOUND", file=sys.stderr)
    for key, why in violations:
        print(f"  {key}: {why}", file=sys.stderr)
    print("\nRemove the placeholder (state the real theorem or an explicit\n"
          "open-problem marker) or justify it in scripts/tautology-allowlist.txt.",
          file=sys.stderr)
    sys.exit(1)

print("check-tautologies: ✓ no tautological placeholders")
PY
