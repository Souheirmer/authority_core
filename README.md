# authority_core

A small `no_std`-style Rust library, verified with [Verus](https://github.com/verus-lang/verus), that implements authorization rule A8 (the "origin-timed lease") for a decision point holding a bounded cache of `N = 64` devices.

- `src/spec.rs`: the human-approved specification (data model, wire format, rule A8, property statements P1–P5)
- `src/decode.rs`, `src/cache.rs`, `src/decide.rs`: verified implementation
- `src/lemmas.rs`: proofs of the spec-level properties
- `mutants/`: the receipt-timed lease mutant (expected **not** to verify)
- `tests/`: P6 witness and the mutant counterexample trace (tests, not proofs)

## Usage

```sh
scripts/setup.sh                     # install rustup, pinned Verus and its toolchain
scripts/verify.sh crate "note"       # verify the crate (always via this script)
scripts/verify.sh mutants "note"     # attempt to verify the mutant (expected to fail)
```

Every run is appended to `logs/verus_runs.csv`. See `PROVENANCE.md`, `MEASUREMENTS.md`, `SPEC_CHANGES.md` and `RESULTS.md`.
