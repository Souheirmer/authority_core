#!/usr/bin/env bash
# Runs the trace checker and logs to logs/trace_runs.csv (same columns as run_tlc.sh;
# the mismatch counts go into the note).
# Usage: scripts/run_checker.sh <real|mutant> <cfg> <trace dir> "<note>"
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
MODE="$1"; CFG="$2"; DIR="$3"; NOTE="$4"
BIN="$ROOT/target/release/trace_check"
LOG="$ROOT/logs/trace_runs.csv"
TS=$(date -u +%FT%TZ)
TIMEF=$(mktemp)
OUT=$(/usr/bin/time -v -o "$TIMEF" "$BIN" "$MODE" "$CFG" "$DIR" 2>&1); RC=$?
echo "$OUT" | tail -5
WALL=$(awk -F': ' '/Elapsed \(wall clock\)/{n=split($2,a,":"); s=0; for(i=1;i<=n;i++) s=s*60+a[i]; print s}' "$TIMEF")
CPU=$(awk -F': ' '/User time/{u=$2} /System time/{s=$2} END{printf "%.2f", u+s}' "$TIMEF")
RSS=$(awk -F': ' '/Maximum resident set size/{print $2}' "$TIMEF"); rm -f "$TIMEF"
R=$(echo "$OUT" | grep '^RESULT')
TRACES=$(echo "$R" | grep -oE 'traces=[0-9]+' | cut -d= -f2)
STEPS=$(echo "$R" | grep -oE ' steps=[0-9]+' | cut -d= -f2)
MIS=$(echo "$R" | grep -oE '(cache_mismatch_steps|decision_mismatch_steps|traces_with_mismatch|skipped_absent|delivered|polls|comparisons|allow_true)=[0-9]+' | tr '\n' ' ')
if [ $RC -ne 0 ] || [ -z "$R" ]; then RESULT=error
elif echo "$R" | grep -q 'cache_mismatch_steps=0 decision_mismatch_steps=0'; then RESULT=conform
else RESULT=mismatch; fi
ROW="$TS,checker-$MODE,$RESULT,$(basename "$CFG"),$(echo "$NOTE; $MIS" | tr ',\n' ';;'),$WALL,$CPU,$RSS,${TRACES:-NA},${STEPS:-NA}"
echo "$ROW" >> "$LOG"; echo "== logged: $ROW"
[ $RC -eq 0 ]
