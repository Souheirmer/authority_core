# authority_core

A small `no_std`-style Rust library, verified with [Verus](https://github.com/verus-lang/verus), that implements authorization rule A8 (the "origin-timed lease") for a decision point holding a bounded cache of `N = 64` devices.

- `src/spec.rs`: the human-approved specification (data model, wire format, rule A8, property statements P1–P5)
- `src/decode.rs`, `src/cache.rs`, `src/decide.rs`: verified implementation
- `src/lemmas.rs`: proofs of the spec-level properties
- `mutants/`: the receipt-timed lease mutant (expected **not** to verify)
- `tests/`: P6 witness, the mutant counterexample trace, and the 50 ✗ cells of Extension A (tests, not proofs)
- `src/system_spec.rs`, `src/rules_spec.rs`: Provisioning.tla transcribed (state, actions, rules A1–A8, properties S1–AVPD)
- `src/rules_proofs.rs`, `src/rules_cex.rs`, `src/rules_table.rs`, `src/rules_exec.rs`: the paper's 8×10 table, machine-checked (see `RESULTS_RULES.md`)
- `trace_validation/`: conformance testing of the code against TLC traces of the model (see `trace_validation/REPORT.md`)
- `model/`: the TLA+ model and the paper's expected results (ground truth)

## Wire format

A notification is exactly 21 bytes, signed with Ed25519 by the authority key over the domain prefix `authority_core/notification/v1` followed by the 21 bytes (64-byte signature, strict verification; spec v5): status (0 = Revoked, 1 = Enrolled, 2 = Suspended; anything else is invalid), device id (big-endian u32, < N = 64), ver (big-endian u64), orig (big-endian u64). Since spec v4 the cache also accepts verified poll answers (`Cache::poll_update`, mirroring the model's `PdpPoll`).

## Assumptions (from the TLA+/TLAPS model)

The rule is implemented exactly as stated; these are the assumptions under which its soundness argument (P5) applies:

- **Bounded clock error.** Registry origin stamps (`orig`) are at most `sigma` ahead of the decision point's clock, as in the TLA+ model. P5 additionally requires the configured bound to cover the real one: `sigma <= sigma_hat`. P6 (a test) shows this margin is necessary.
- **Configuration.** The paper's precondition `sigma_hat <= delta` is not assumed. It is a conjunct of `a8` instead, so a misconfigured decision point (`sigma_hat > delta`) denies every request.
- **Versions start at 1.** An empty slot holds `(Unknown, ver = 0, orig = 0)`, and `apply` overwrites only on a strictly greater version, so the registry's first record for a device must have `ver >= 1`. A `ver = 0` notification is ignored.
- **Signatures (spec v5).** `signature_ok(pk, bytes, sig)` is trusted (`#[verifier::external_body]`, the only one in the crate): its contract is that it returns exactly `sig_valid(pk, bytes, sig)`. Its body calls `src/sig_impl.rs`, a thin unverified wrapper over the `ed25519-dalek` library (pinned 2.2.0), which is also trusted. Ed25519's cryptographic security is an assumption. Under Verus a stub replaces the wrapper, so the proofs depend only on the contract.

## Usage

```sh
scripts/setup.sh                     # install rustup, pinned Verus and its toolchain
scripts/verify.sh crate "note"       # verify the crate (always via this script)
scripts/verify.sh mutants "note"     # attempt to verify the mutant (expected to fail)
```

Every run is appended to `logs/verus_runs.csv`. See `PROVENANCE.md`, `MEASUREMENTS.md`, `SPEC_CHANGES.md` and `RESULTS.md`.
