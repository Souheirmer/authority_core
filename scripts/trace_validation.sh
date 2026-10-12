#!/usr/bin/env bash
# Reproduces Extension B: unpacks (or regenerates with --regen) the TLC traces and
# runs every checker mode, logging each run to logs/trace_runs.csv.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
G="${TRACE_WORK:-/tmp/trace_validation_work}"; rm -rf "$G"; mkdir -p "$G"
export PATH="$HOME/.cargo/bin:$PATH"
cargo +1.98.1-x86_64-unknown-linux-gnu build --release -p trace_validation >/dev/null
seed=101
for c in A8_c1_paper A8_c2_skew1 A8_c3_skew12 A8_c4_sync A3_c1_paper A3_c2_skew1 A3_c4_sync; do
  W="$G/$c"; mkdir -p "$W/traces"
  if [ "${1:-}" = "--regen" ]; then
    case $c in A8*) n=400;; *) n=300;; esac
    cp model/Provisioning.tla trace_validation/tla/TraceGen.tla "trace_validation/tla/$c.cfg" "$W/"
    scripts/run_tlc.sh "$W" "TraceGen simulation $c: num=$n depth=31 seed=$seed" \
      -simulate "file=$W/traces/tr,num=$n" -depth 31 -seed $seed -config "$c.cfg" TraceGen.tla
  else
    tar -C "$W" -xzf "trace_validation/traces/$c.tar.gz"
  fi
  seed=$((seed+1))
done
for c in A8_c1_paper A8_c2_skew1 A8_c3_skew12 A8_c4_sync; do
  scripts/run_checker.sh real          "$G/$c/$c.cfg" "$G/$c/traces" "real code vs A8 traces $c"
  scripts/run_checker.sh mutant        "$G/$c/$c.cfg" "$G/$c/traces" "NON-VACUITY: receipt-timed mutant vs A8 traces $c" || true
  scripts/run_checker.sh poll-as-apply "$G/$c/$c.cfg" "$G/$c/traces" "NON-VACUITY (cache comparison): poll via apply vs A8 traces $c" || true
done
for c in A3_c1_paper A3_c2_skew1 A3_c4_sync; do
  scripts/run_checker.sh real "$G/$c/$c.cfg" "$G/$c/traces" "NON-VACUITY: real (A8) code vs A3 traces $c" || true
done
