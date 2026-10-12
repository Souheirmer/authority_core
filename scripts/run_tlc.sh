#!/usr/bin/env bash
# The ONLY sanctioned way to run TLC in this project. Logs to logs/trace_runs.csv:
#   timestamp,tool,result,target,note,wall_s,cpu_s,max_rss_kb,traces,states
# Usage: scripts/run_tlc.sh <workdir> "<note>" <tlc args...>
#   <workdir> must already contain the .tla modules and .cfg; TLC runs there.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$1"; NOTE="$2"; shift 2
JAR="$ROOT/.tools/tla/tla2tools-v1.7.4.jar"
LOG="$ROOT/logs/trace_runs.csv"
[ -f "$LOG" ] || echo "timestamp,tool,result,target,note,wall_s,cpu_s,max_rss_kb,traces,states" > "$LOG"
TS=$(date -u +%FT%TZ)
TIMEF=$(mktemp)
OUT=$(cd "$WORK" && /usr/bin/time -v -o "$TIMEF" java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC "$@" 2>&1); RC=$?
mkdir -p "$ROOT/logs/runs"; echo "$OUT" > "$ROOT/logs/runs/${TS//:/-}_tlc.txt"
echo "$OUT" | grep -vE 'JAVA_TOOL|^\s*$' | tail -12
WALL=$(awk -F': ' '/Elapsed \(wall clock\)/{n=split($2,a,":"); s=0; for(i=1;i<=n;i++) s=s*60+a[i]; print s}' "$TIMEF")
CPU=$(awk -F': ' '/User time/{u=$2} /System time/{s=$2} END{printf "%.2f", u+s}' "$TIMEF")
RSS=$(awk -F': ' '/Maximum resident set size/{print $2}' "$TIMEF"); rm -f "$TIMEF"
if [ $RC -eq 0 ]; then RESULT=ok; elif echo "$OUT" | grep -q 'is violated'; then RESULT=violation; else RESULT=error; fi
TRACES=NA; for a in "$@"; do case "$a" in file=*) d=$(echo "$a" | sed 's/^file=\([^,]*\).*/\1/'); TRACES=$(ls "$(dirname "$d")" 2>/dev/null | wc -l);; esac; done
STATES=$(echo "$OUT" | grep -oE '([0-9]+ states (generated|checked))|(states checked: [0-9]+)|(Progress: [0-9]+ states checked)' | grep -oE '[0-9]+' | tail -1)
TARGET=$(echo "$@" | grep -oE '[^ ]+\.cfg' | head -1)
ROW="$TS,tlc,$RESULT,$TARGET,$(echo "$NOTE" | tr ',\n' ';;'),$WALL,$CPU,$RSS,$TRACES,${STATES:-NA}"
echo "$ROW" >> "$LOG"; echo "== logged: $ROW"
[ $RC -eq 0 ]
