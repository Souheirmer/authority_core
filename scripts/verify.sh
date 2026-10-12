#!/usr/bin/env bash
# The ONLY sanctioned way to run Verus in this project.
# Usage: scripts/verify.sh [crate|mutants] "short note"
# Appends one line per run to logs/verus_runs.csv:
#   timestamp,result,errors,verified,target,note
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
TARGET="${1:-crate}"
NOTE="${2:-}"
VERUS="$ROOT/.tools/verus-x86-linux/verus"
LOG="$ROOT/logs/verus_runs.csv"
mkdir -p logs
[ -f "$LOG" ] || echo "timestamp,result,errors,verified,target,note" > "$LOG"

TS=$(date -u +%FT%TZ)
GAMING_OUT=$(scripts/check_no_gaming.sh 2>&1); GAMING_RC=$?
echo "$GAMING_OUT"

case "$TARGET" in
  crate)   ROOTFILE=src/lib.rs ;;
  mutants) ROOTFILE=mutants/lib.rs ;;
  *) echo "unknown target $TARGET"; exit 2 ;;
esac

# EXTRA_VERUS_ARGS (optional), e.g. "--emit=dep-info" for line counting
OUT=$("$VERUS" "$ROOTFILE" --crate-type=lib ${EXTRA_VERUS_ARGS:-} 2>&1); RC=$?
echo "$OUT"
mkdir -p logs/runs
echo "$OUT" > "logs/runs/${TS//:/-}_${TARGET}.txt"

SUMMARY=$(echo "$OUT" | grep -oE 'verification results:: [0-9]+ verified, [0-9]+ errors' | tail -1)
VERIFIED=$(echo "$SUMMARY" | grep -oE '[0-9]+ verified' | grep -oE '[0-9]+'); VERIFIED=${VERIFIED:-0}
ERRORS=$(echo "$SUMMARY" | grep -oE '[0-9]+ errors' | grep -oE '[0-9]+')
if [ -z "$ERRORS" ]; then
  # no summary line: compile/type error before verification
  ERRORS=$(echo "$OUT" | grep -E '^error' | grep -vc 'aborting due to')
fi
if [ "$RC" -eq 0 ] && [ "$GAMING_RC" -eq 0 ] && [ "$ERRORS" -eq 0 ]; then RESULT=pass; else RESULT=fail; fi
[ "$GAMING_RC" -ne 0 ] && NOTE="GAMING-CHECK-FAILED; $NOTE"
CLEAN_NOTE=$(echo "$NOTE" | tr ',\n' ';;')
echo "$TS,$RESULT,$ERRORS,$VERIFIED,$TARGET,$CLEAN_NOTE" >> "$LOG"
echo "== logged: $TS,$RESULT,$ERRORS,$VERIFIED,$TARGET,$CLEAN_NOTE"
[ "$RESULT" = pass ]
