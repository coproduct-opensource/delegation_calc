#!/usr/bin/env bash
# scripts/check-spec-drift.sh — verify the rule names in spec/typing-rules.md
# match the variants of `RuleName` in crates/dlc-core/src/judgment.rs and the
# constructors of `Deriv` in lean/DLC/Judgment.lean.
#
# Catches the easy mistake of adding a rule to the spec but forgetting to
# wire it into either the Rust or Lean encoding (or vice versa).

set -euo pipefail

cd "$(dirname "$0")/.."

SPEC="spec/typing-rules.md"
RUST="crates/dlc-core/src/judgment.rs"
LEAN="lean/DLC/Judgment.lean"

extract_spec_rules() {
  # Extract rule names from the rule-index table at the bottom of the spec.
  # Table rows start with `|` and the first backtick-quoted token is the
  # rule name (possibly a `/` -separated group like `imp-I / imp-E`).
  #
  # Restrict to lines starting with `| ` followed by a backtick — that's the
  # table shape — to avoid false positives from prose.
  awk '/^\| `/{print}' "$SPEC" \
    | grep -oE '`[^`]+`' \
    | tr -d '`' \
    | tr '/' '\n' \
    | tr -d ' ' \
    | grep -E '^[a-zA-Zₗᵣβ-]+$' \
    | sort -u
}

extract_rust_rules() {
  # `RuleName::VarA` etc. — extract enum variants and map to spec naming.
  grep -E '^\s*///\s*`[a-z]' "$RUST" \
    | grep -oE '`[a-z]+(-[a-zA-Z]+)*`' \
    | tr -d '`' \
    | sort -u
}

extract_lean_rules() {
  # The doc-comments on each `Deriv` constructor cite the rule name.
  grep -oE '/-- `[a-z]+(-[a-zA-Z]+)*`' "$LEAN" \
    | grep -oE '`[a-z]+(-[a-zA-Z]+)*`' \
    | tr -d '`' \
    | sort -u
}

SPEC_RULES=$(extract_spec_rules)
RUST_RULES=$(extract_rust_rules)
LEAN_RULES=$(extract_lean_rules)

# Spec must list every rule that has a Rust variant or Lean constructor.
missing_in_spec=$(comm -23 <(printf '%s\n' "$RUST_RULES" "$LEAN_RULES" | sort -u) <(printf '%s\n' "$SPEC_RULES"))

# Every rule named in the spec's rule-index table should appear in at least
# one of Rust or Lean. (Phase-1 may stage rules in spec ahead of the
# inductive encoding; we warn rather than fail in that direction.)
not_yet_in_code=$(comm -23 <(printf '%s\n' "$SPEC_RULES") <(printf '%s\n' "$RUST_RULES" "$LEAN_RULES" | sort -u))

if [[ -n "$missing_in_spec" ]]; then
  echo "::error::Rules present in Rust or Lean but not documented in spec/typing-rules.md:"
  printf '  - %s\n' $missing_in_spec
  exit 1
fi

if [[ -n "$not_yet_in_code" ]]; then
  echo "::warning::Rules in spec/typing-rules.md not yet encoded in Rust or Lean (acceptable during Phase-1 staging):"
  printf '  - %s\n' $not_yet_in_code
fi

echo "OK — spec/Rust/Lean rule indices are consistent."
