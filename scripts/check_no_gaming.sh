#!/usr/bin/env bash
# Fails if any proof-escape hatch appears outside the single declared trusted
# function `signature_ok`. Run on every verification (scripts/verify.sh calls it).
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PATTERN='assume[[:space:]]*\(|admit[[:space:]]*\(|external_body|verifier::external\b|verifier\(external|exec_allows_no_decreases_clause|assume_specification|external_fn_specification|verifier::assume|--no-verify|no_auto_trigger_assume|external_type_specification|\bunsafe\b'

FILES=$(find src mutants -name '*.rs' 2>/dev/null)
fail=0
allowed=0
for f in $FILES; do
  # strip // line comments before matching, keep line numbers
  while IFS= read -r hit; do
    ln="${hit%%:*}"
    line="${hit#*:}"
    # the one allowed occurrence: `#[verifier::external_body]` directly followed by `fn signature_ok`
    if [[ "$line" =~ ^[[:space:]]*#\[verifier::external_body\][[:space:]]*$ ]]; then
      next=$(sed -n "$((ln+1))p" "$f")
      if [[ "$next" =~ fn[[:space:]]+signature_ok[[:space:]]*\( ]]; then
        allowed=$((allowed+1)); continue
      fi
    fi
    echo "GAMING: $f:$ln: $line"; fail=1
  done < <(sed 's#//.*$##' "$f" | grep -nE "$PATTERN")
done

if [ "$allowed" -gt 1 ]; then
  echo "GAMING: external_body allowed once (signature_ok), found $allowed"; fail=1
fi
if [ "$fail" -ne 0 ]; then echo "check_no_gaming: FAIL"; exit 1; fi
echo "check_no_gaming: OK (trusted external_body occurrences: $allowed)"
