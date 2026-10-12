#!/usr/bin/env bash
# Runs the executable tests (P6 witness, mutant counterexample) with the Verus toolchain.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.cargo/bin:$PATH"
cargo +1.98.1-x86_64-unknown-linux-gnu test "$@"
