# Results

Verus `0.2026.10.04.426d8b0`, Rust `1.98.1`, Ubuntu 24.04 x86_64. Specification: `src/spec.rs` v2 (human-approved, see `SPEC_CHANGES.md`).
Final verification of the crate: **28 verified, 0 errors** (`logs/verus_runs.csv`, run 2026-10-12T00:08:49Z). The no-gaming check passed on every run, with exactly one trusted `external_body` (`signature_ok`).

## 1. What was proved (accepted by Verus)

| Property | Where | Statement (in `src/spec.rs`) |
|---|---|---|
| P1 safe decoding | `decode.rs::decode` | `decode_post(bytes@, r)`: `r == decode_spec(bytes@)`, `r is Some <==> well_formed(bytes@)`, a `Some` result is a valid notification. No overflow, no out-of-bounds indexing, termination: Verus checks these on all executable code. |
| P1 round trip | `lemmas.rs::lemma_p1_round_trip` | `p1_round_trip()`: `decode_spec(encode_spec(m)) == Some(m)` for every valid `m` (spec level) |
| P2 monotonic versions | `cache.rs::Cache::apply` | `apply_post(old, new, m)`: `new == apply_spec(old, m)`; every `ver` is ≥ its old value; entry `i` changes iff `i == m.device && m.ver > old[i].ver` |
| P3 decision correctness | `decide.rs::allow`, `cache.rs::Cache::allow_device` | `allow_post`: `b == a8(e, now, delta, sigma_hat, critical)`; `allow_device_post`: `b == (d < N && a8(cache[d], ...))`. No overflow or underflow (checked by Verus). |
| P4 deny by default | `lemmas.rs::lemma_p4_deny_by_default` | Unknown slot, Revoked status, active critical event, or `sigma_hat > delta` ⇒ `!a8(...)` |
| P5 soundness core | `lemmas.rs::lemma_p5_soundness_core` | For all values, over unbounded integers: `since_rev <= (now - orig) + sigma ∧ a8(...) ∧ sigma <= sigma_hat ⇒ since_rev <= delta`. The case `orig > now` is covered: `now - orig` is negative. |
| Mutant negation | `mutants/receipt_timed.rs::lemma_p5_receipt_timed_is_false` | The P5-style statement for the receipt-timed lease is **false**, shown with a concrete witness. |

Sanity check that the contracts have teeth: two bugs were planted on purpose (`<` instead of `<=` in `allow`; `>=` instead of `>` in `apply`). Verus rejected both with "postcondition not satisfied" (logged runs 00:06:35Z and 00:06:36Z).

## 2. What was only tested (`cargo test`, via `scripts/test.sh`; 3 tests pass)

- **P6, necessity of the margin** (`tests/p6_margin_necessity.rs`). Witness: `delta = 100`, `sigma_hat = 10`, `sigma = 30`; Enrolled with `orig = 0`; `now = 90`; `since_rev = 120`. The invariant holds (`120 <= 90 + 30`), `allow_device` returns true, yet `since_rev = 120 > delta = 100`. A second test sweeps a small grid (`delta = 20`, every `sigma_hat <= delta`, `sigma` from −5 to `sigma_hat`, `orig` and `now` in `0..40`) and finds no violation when `sigma <= sigma_hat`. This is a test only; the general statement is P5.
- **Mutant counterexample trace** (`tests/mutant_counterexample.rs`). See §6.

## 3. Trusted assumptions (not proved)

1. `signature_ok(bytes, sig)` in `src/lib.rs`: `#[verifier::external_body]`, no specification. Nothing proved depends on its result. The placeholder returns `false`. It is used only by `Cache::handle`.
2. The specification `src/spec.rs` faithfully captures rule A8 and the paper's properties. This was reviewed and approved by the human; it cannot be verified.
3. Model-level facts used as hypotheses, not established by this code: the invariant `since_rev <= (now - orig) + sigma` (origin stamp precedes revocation, up to clock error), `sigma <= sigma_hat`, and registry versions starting at 1. These come from the TLA+/TLAPS model; see README "Assumptions".
4. Tool soundness: Verus, Z3, rustc 1.98.1, and `vstd` (including its specifications of slices and arrays).
5. The `cargo test` binaries are compiled by plain rustc from the same source against crates.io `vstd = 0.0.0-2026-10-04-0306`, which is assumed to match the vstd in the pinned release. Ghost code is erased.
6. `Cache::handle` (decode, then signature check, then apply) is a convenience function. Its contract is verified but is stated in `cache.rs`, not in the approved spec.

## 4. Size

From Verus' `line_count` tool (`line_count --deps lib.d`) on the crate, lines by category:

| | Trusted | Spec | Proof | Exec | Comment | Other (blank etc.) |
|---|---|---|---|---|---|---|
| total | 5 | 177 | 89 | 103 | 111 | 109 |

- **Executable code: 103 lines.** 21 of these are the type and constant declarations in `spec.rs`; the other 82 are in `decode.rs`, `cache.rs` and `decide.rs`.
- **Spec: 177 lines.** 120 of these are in `spec.rs`; the rest are pre/postconditions, loop invariants and proof-helper spec functions.
- **Proof: 89 lines.** 65 in `lemmas.rs`, 24 inside `decode.rs`.
- **Trusted: 5 lines** (`signature_ok`).

The mutant crate (`mutants/`) is not included in these counts.

## 5. Verifier runs (`logs/verus_runs.csv`)

**Total 14 runs: 6 passed, 8 failed.**

| Failed run | Kind |
|---|---|
| 00:06:01Z | Development: parse error (`acc as nat < ...` read as generic). Logged as 2 errors, but it was 1 error plus the "aborting" line; `verify.sh` was fixed right after. |
| 00:06:07Z | Development: new Verus `&mut` syntax requires `final(self)` in postconditions (2 errors) |
| 00:06:12Z | Development: possible overflow in `off + n` (loop condition) |
| 00:06:18Z | Development: possible overflow in `off + n` (hoisted); fixed by calling `b.len()` |
| 00:06:35Z | Deliberate sanity check: planted bug in `allow` |
| 00:06:36Z | Deliberate sanity check: planted bug in `apply`. `decide.rs` still had the first planted bug because a `git checkout` restore failed on an uncommitted file, so 2 errors. |
| 00:06:37Z | Same leftover planted bug in `decide.rs` (the note says "restored", which was wrong); fixed in the next run |
| 00:07:28Z | Expected: the mutant crate, whose P5-style lemma fails |

So: 4 development failures, 3 failures caused by the deliberate sanity check, 1 expected mutant failure. No proof needed manual hints beyond what is in the source; the first passing run of the full implementation came 5 runs (23 s) after the first attempt.

## 6. Receipt-timed mutant

`mutants/receipt_timed.rs` starts the lease at the receipt time `recv` (the decision point's clock when the entry is written) instead of at `orig`. Everything else is identical to A8.

**Verus failure** for `lemma_p5_receipt_timed_attempt` (same hypotheses as P5, mutant rule):

```
error: postcondition not satisfied
   --> mutants/receipt_timed.rs:110:9
    |
102 | / pub proof fn lemma_p5_receipt_timed_attempt(
103 | |     e: RtEntry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int,
104 | | )
    | |_- at the end of the function body
...
110 |           since_rev <= delta as int,
    |           ^^^^^^^^^^^^^^^^^^^^^^^^^ failed this postcondition
verification results:: 12 verified, 1 errors
```

A failed proof attempt alone does not show that the statement is unprovable. The crate therefore also proves the negation, `lemma_p5_receipt_timed_is_false`, which Verus accepted (it is among the 12 verified items).

**Counterexample trace** (test `receipt_timed_lease_outlives_revocation`). Parameters: `delta = 100`, `sigma_hat = 10`, `sigma = 0` (clocks agree).

| true time | event | origin-timed A8 | receipt-timed mutant |
|---|---|---|---|
| 0 | registry issues Enrolled (ver 1, orig 0); delivery delayed | | |
| 10 | registry issues Revoked (ver 2, orig 10); delivery delayed further | | |
| 200 | ver 1 arrives; version-ordered (1 > 0), so accepted by both | deny (age 200 > 90) | allow (`recv = 200`) |
| 200–290 | revocation is 190–280 ticks old (> delta) | deny | **allow** |
| 280 | the instance proved in Verus: `since_rev = 270`, invariant `270 <= 280 - 0 + 0` holds | deny | **allow** |
| 291–299 | | deny | deny (lease expired) |
| 300 | Revoked (ver 2) arrives | deny | deny |

## 7. Human and wall-clock time

See `MEASUREMENTS.md`.

- **Human:** 3 min before session 1 (reading the brief, GitHub and session setup) and 1 min reviewing and approving the spec. Session 2 time: _awaiting the human's answer_.
- **Independent AI review:** about 2 min, kept separate from human minutes.
- **Agent wall-clock:**
  - Session 1: 23:15:20Z to 23:20:53Z (about 6 min).
  - Session 2: 00:03:49Z to about 00:10Z (about 6 min).
  - Between them, about 43 min elapsed waiting for human review.
- **Cost:** about $2 reported for session 1; session 2 not yet reported.

## 8. What did not work / caveats

- The 4 development failures in §5 were all small: one parse error, one syntax change in this Verus version (`final(self)`), and two overflow obligations.
- A procedural mistake during the sanity check: restoring `decide.rs` with `git checkout` failed because the file was not yet committed, so a planted bug stayed in place for 2 more runs. It was caught from the run output and fixed by hand. The logged notes at 00:06:36Z and 00:06:37Z describe what I intended, not what actually ran; §5 gives the correction.
- P5 is the arithmetic core only. Verus does not prove that a running system keeps the invariant `since_rev <= (now - orig) + sigma`; that is the TLA+ model's job.
- The crate is `#![no_std]` and verifies under Verus, but no build was tested on an actual embedded no_std target.
- Token usage is not visible inside the sandbox.
