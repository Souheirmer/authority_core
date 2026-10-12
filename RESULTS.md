# Results

Verus `0.2026.10.04.426d8b0`, Rust `1.98.1`, Ubuntu 24.04 x86_64. Specification: `src/spec.rs` v4 (human-approved, see `SPEC_CHANGES.md`). Sections 1–8 report sessions 1–3 (spec v3); session 4 changes are in §9.
Final verification of the crate: **28 verified, 0 errors** (`logs/verus_runs.csv`, final run 2026-10-12T00:18:24Z on spec v3; 2.46 s wall, 3.08 s CPU, 316 MiB peak RSS). The no-gaming check passed on every run, with exactly one trusted `external_body` (`signature_ok`).

## 1. What was proved (accepted by Verus)

| Property | Where | Statement (in `src/spec.rs`) |
|---|---|---|
| P1 safe decoding | `decode.rs::decode` | `decode_post(bytes@, r)`: `r == decode_spec(bytes@)`, `r is Some <==> well_formed(bytes@)`, a `Some` result is a valid notification. No overflow, no out-of-bounds indexing, termination: Verus checks these on all executable code. |
| P1 round trip | `lemmas.rs::lemma_p1_round_trip` | `p1_round_trip()`: `decode_spec(encode_spec(m)) == Some(m)` for every valid `m` (spec level) |
| P2 monotonic versions | `cache.rs::Cache::apply` | `apply_post(old, new, m)`: `new == apply_spec(old, m)`; every `ver` is ≥ its old value; entry `i` changes iff `i == m.device && m.ver > old[i].ver` |
| P3 decision correctness | `decide.rs::allow`, `cache.rs::Cache::allow_device` | `allow_post`: `b == a8(e, now, delta, sigma_hat, critical)`; `allow_device_post`: `b == (d < N && a8(cache[d], ...))`. No overflow or underflow (checked by Verus). |
| P4 deny by default | `lemmas.rs::lemma_p4_deny_by_default` | Unknown slot, Revoked status, active critical event, or `sigma_hat > delta` ⇒ `!a8(...)` |
| P5 soundness core | `lemmas.rs::lemma_p5_soundness_core` | For all values, over unbounded integers: `since_rev <= (now - orig) + sigma ∧ a8(...) ∧ sigma <= sigma_hat ⇒ since_rev <= delta`. The case `orig > now` is covered: `now - orig` is negative. |
| `handle` (spec v3) | `cache.rs::Cache::handle` | `handle_post`: accepted ⇒ the bytes decode to some `m` and the new cache is `apply_spec(old, m)`; rejected ⇒ cache unchanged. The trusted `signature_ok` can only cause a rejection; it cannot make malformed input be accepted. |
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

## 4. Size

From Verus' `line_count` tool (`line_count --deps lib.d`) on the crate, lines by category:

| | Trusted | Spec | Proof | Exec | Comment | Other (blank etc.) |
|---|---|---|---|---|---|---|
| total | 5 | 179 | 89 | 103 | 116 | 110 |

- **Executable code: 103 lines.** 21 of these are the type and constant declarations in `spec.rs`; the other 82 are in `decode.rs`, `cache.rs` and `decide.rs`.
- **Spec: 179 lines.** 124 of these are in `spec.rs`; the rest are pre/postconditions, loop invariants and proof-helper spec functions.
- **Proof: 89 lines.** 65 in `lemmas.rs`, 24 inside `decode.rs`.
- **Trusted: 5 lines** (`signature_ok`).

The mutant crate (`mutants/`) is not included in these counts.

## 5. Verifier runs (`logs/verus_runs.csv`)

**Total 19 runs: 9 passed, 10 failed.**

Runs 15–16 (00:11:02Z, 00:11:03Z) repeat the crate and mutant verification with resource measurement. Results are unchanged.

Runs 17–19 (session 3, spec v3):
- 00:18:14Z: crate, pass, 28 verified.
- 00:18:23Z: mutant, the expected failure, 12 verified and 1 error.
- 00:18:24Z: crate, pass, 28 verified; this is the final run.

Resources for the measured runs:

| Run | Wall | CPU | Peak RSS |
|---|---|---|---|
| crate 00:11:02Z | 1.61 s | 2.24 s | 317 MiB |
| crate 00:18:14Z | 3.90 s | 4.55 s | 311 MiB |
| crate 00:18:24Z (final) | 2.46 s | 3.08 s | 316 MiB |
| mutant 00:11:03Z | 0.82 s | 0.92 s | 308 MiB |
| mutant 00:18:23Z | 0.91 s | 1.00 s | 305 MiB |

Hardware: 4-core Intel Xeon @ 2.80GHz, 15 GiB RAM (see `MEASUREMENTS.md`). Total Verus wall time over the 5 measured runs: 9.70 s.

**Passed runs (9):** 23:20:25Z, 23:20:31Z, 00:04:32Z, 00:06:24Z, 00:06:42Z, 00:08:49Z, 00:11:02Z, 00:18:14Z, 00:18:24Z.

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
| 00:11:03Z | Expected: the same mutant run, repeated with resource measurement |
| 00:18:23Z | Expected: the mutant re-run after spec v3 (the mutant crate includes `spec.rs`) |

So: 4 development failures, 3 failures caused by the deliberate sanity check, 3 expected mutant failures. Total failed: 4 + 3 + 3 = 10. No proof needed manual hints beyond what is in the source; the first passing run of the full implementation came 5 runs (23 s) after the first attempt.

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

Details and sources are in `MEASUREMENTS.md`.

| Human activity | Minutes |
|---|---|
| Reading the brief; GitHub and session setup (before session 1) | 3 |
| Approving the spec, including reading the independent review (session 1) | 1 |
| Reading the review and sending instructions (session 2) | 2 |
| Session 3 | 0.65 (39 s) |
| **Total reported** | **6 min 39 s** |

**Agent wall-clock** (exact; from commit, log and sandbox-clock timestamps):

| Session | Duration | Detail |
|---|---|---|
| 1 | 5 min 32 s | |
| 2 | 6 min 29 s | two turns: 5 min 50 s + 39 s |
| 3 | 1 min 28 s | |
| **Total** | **13 min 29 s** | |

**Total elapsed**, from the first command to the last content commit, including waiting for the human: 1 h 4 min 7 s.

**Independent AI review** (reviewer's clock, kept separate from human minutes):
- Review 1: 2 min, human-measured.
- Review 2: 18 s.
- Review 3: 1 s.
- Review 4: 2 s.

**Cost** (reported by human): about $2 (session 1), about $1 (session 2), about $1 (session 3). Total: about $4, confirmed by the human (the "about $3 so far" said mid-session 3 was the cumulative total). Token usage is not visible to the agent.

## 8. What did not work / caveats

- The 4 development failures in §5 were all small: one parse error, one syntax change in this Verus version (`final(self)`), and two overflow obligations.
- A procedural mistake during the sanity check: restoring `decide.rs` with `git checkout` failed because the file was not yet committed, so a planted bug stayed in place for 2 more runs. It was caught from the run output and fixed by hand. The logged notes at 00:06:36Z and 00:06:37Z describe what I intended, not what actually ran; §5 gives the correction.
- P5 is the arithmetic core only. Verus does not prove that a running system keeps the invariant `since_rev <= (now - orig) + sigma`; that is the TLA+ model's job.
- The crate is `#![no_std]` and verifies under Verus, but no build was tested on an actual embedded no_std target.
- Token usage is not visible inside the sandbox.

## 9. Session 4: spec v4 and Extension B (trace validation)

**Spec v4** (human-approved; see `SPEC_CHANGES.md`):
- `Suspended` status, wire byte 2.
- `poll_spec`/`poll_post` and a verified `Cache::poll_update`, mirroring `PdpPoll`.
- P4 generalised to "status ≠ Enrolled, or a critical event, or σ̂ > Δ ⇒ deny".

Crate: **29 verified, 0 errors**, on the first attempt (run 01:15:32Z). Mutant crate: 13 verified, 1 error (the expected lemma failure, run 01:15:41Z). The 3 tests pass.

**Extension B** (details in `trace_validation/REPORT.md`; mapping in `trace_validation/MAPPING.md`). This is conformance testing, not a refinement proof.
- The verified code against **1,600 TLC traces of `RULE = "A8_OriginLease"`** (4 configurations, including σ = σ̂ = 1 and the paper's default; 30 steps each; 48,000 steps; 99,200 device comparisons): **0 cache mismatches and 0 decision mismatches.**
- Non-vacuity: the receipt-timed mutant disagrees on 54 steps in 8 traces; the verified code against 900 A3 traces disagrees on 2,471 steps in 290 traces; poll answers routed through `apply` produce 8,330 cache-mismatch steps and 24 decision-mismatch steps.
- TLC and checker runs: 23 in `logs/trace_runs.csv`, with time and memory.
  - Of the 23 rows: 4 exploratory TLC runs by hand (no measurements), 7 generation runs, 1 reproducibility run, 4 + 4 + 3 + 4 checker runs.
  - Generation: 1.5–2.9 s wall each, up to 383 MiB peak.
  - Each checker run: under 0.2 s and about 2.6 MiB.

## 10. Session 4: Extension A (all eight rules)

See **`RESULTS_RULES.md`**. All 80 cells of the paper's 8×10 table are machine-checked and agree with `model/EXPECTED_RESULTS.md`; this is proved by the theorem `lemma_paper_table`. There are 0 disagreements and 0 open cells.
- **30 ✓ cells:** inductive invariants over the transcribed transition system. They include the model's `OriginPrecedesRevocation`; A8/S3 reuses P5.
- **50 ✗ cells:** Verus-checked counterexample executions, also replayed as Rust tests.
- **Executable rules:** A1–A8, proved equal to their spec functions. A8 is the original verified `decide::allow`.
- **Size:** the crate now has 112 verified items, 0 errors.
- **Runs:** 20 Verus runs for Extension A (12 passed, 8 failed: 5 development, 2 deliberate sanity, 1 expected mutant).
