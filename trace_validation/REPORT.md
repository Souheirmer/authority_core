# Extension B: trace validation of authority_core against Provisioning.tla

**This is conformance testing (trace validation), not a refinement proof.** It shows that on 1,600 random model executions, the verified code produced exactly the model's decision-point state and decisions at every step. It does not prove that this holds for all executions. The proofs about the code are those in `RESULTS.md` (P1–P5); the proofs about the model are the paper's TLAPS proofs.

## Setup

- **Model:** `model/Provisioning.tla`, unchanged. TLC v1.7.4 (2.19), simulation mode.
- **Generator:** `trace_validation/tla/TraceGen.tla`. It `EXTENDS Provisioning` and adds two auxiliary variables: `act`, the action and its parameters, and `allowed`, TLC's value of `AllowRule(d)`.
- **Checker:** `trace_validation/src/main.rs`, which drives the verified `authority_core` code: wire `encode` → `decode` → `apply` for deliveries, `poll_update` for polls, and `allow_device` for decisions.
- **Mapping:** `trace_validation/MAPPING.md`.
- **Traces:** archived in `trace_validation/traces/*.tar.gz` (SHA-256 in `SHA256SUMS`). Regeneration with the same seed was checked to be byte-identical (logged run 01:19:19Z: 0 of 400 traces differ).
- **Reproduce:** `scripts/trace_validation.sh` (add `--regen` to regenerate the traces with TLC).
- **Configurations** (every trace has 31 states, i.e. 30 steps; `CRITICAL = {e1}`):

| Config | RULE | DEVICES | EVENTTYPES | LEASE (Δ) | SKEW (σ) | SKEWBOUND (σ̂) | MAXAGE | MAXVER | MAXNET | MAXUSE | MAXBAD | MAXT | traces | seed |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| A8_c1_paper | A8 | {d1} | {e1} | 1 | 0 | 0 | 3 | 2 | 1 | 1 | 3 | 3 | 400 | 101 |
| A8_c2_skew1 | A8 | {d1,d2} | {e1,e2} | 3 | **1** | **1** | 6 | 4 | 2 | 2 | 5 | 40 | 400 | 102 |
| A8_c3_skew12 | A8 | {d1,d2,d3} | {e1,e2} | 4 | 1 | 2 | 8 | 6 | 2 | 2 | 5 | 60 | 400 | 103 |
| A8_c4_sync | A8 | {d1,d2} | {e1} | 2 | 0 | 0 | 5 | 4 | 1 | 2 | 5 | 40 | 400 | 104 |
| A3_c1_paper | A3 | as A8_c1 | | | | | | | | | | | 300 | 105 |
| A3_c2_skew1 | A3 | as A8_c2 | | | | | | | | | | | 300 | 106 |
| A3_c4_sync | A3 | as A8_c4 | | | | | | | | | | | 300 | 107 |

`A8_c1_paper` is exactly the paper's default configuration. With `MAXT = 3` the clock stops at 3, but traces still have 30 steps of other actions. `MAXNET = 2` only matters for `TypeOK`, which is not checked in simulation (`NetStates`, line 121, assumes `MAXNET = 1`).

## Results (from `logs/trace_runs.csv`)

| Run | Traces | Steps | Device comparisons | Steps with cache mismatch | Steps with decision mismatch | Traces with a mismatch |
|---|---|---|---|---|---|---|
| **Verified code vs A8 traces** | **1,600** | **48,000** | **99,200** | **0** | **0** | **0** |
| Receipt-timed mutant vs A8 traces | 1,600 | 48,000 | 99,200 | 0 | **54** | **8** |
| Verified (A8) code vs A3 traces | 900 | 27,000 | 46,500 | 0 | **2,471** | **290** |
| Poll answers via `apply` (rejected mapping 1(b)) vs A8 traces | 1,600 | 48,000 | 99,200 | **8,330** | **24** | **611** |

What the verified-code runs exercised (A8, all 4 configurations): 875 deliveries through the wire, 4,570 polls, and 945 skipped `Absent` notifications, all of which had version 0 as asserted. Of the 99,200 comparisons, 5,233 were states where the model **allows**; the rest were denials.

Per configuration:

| Config | Real: decision mismatches | Mutant: steps (traces) | Poll-as-apply: cache steps / decision steps |
|---|---|---|---|
| A8_c1_paper | 0 | 2 (1) | 2,231 / 10 |
| A8_c2_skew1 | 0 | 43 (4) | 1,937 / 5 |
| A8_c3_skew12 | 0 | 3 (1) | 1,555 / 0 |
| A8_c4_sync | 0 | 6 (2) | 2,607 / 9 |

A3 traces, verified A8 code: A3_c1 378 steps (69 traces), A3_c2 1,113 (112), A3_c4 980 (109). The cache never disagrees there: the cache transitions are the same under every rule. Only the decisions differ.

### Example detections

- **Mutant** (`A8_c1_paper`, trace `tr_0_146`):
  1. The registry enrols d1 and pushes `(Enrolled, ver 1, orig 0)`.
  2. A Tick follows.
  3. The notification is delivered at `now = 1`.
  4. At `now = 2`, A8 denies (2 − 0 > Δ = 1), but the receipt-timed mutant allows (2 − 1 ≤ 1).

  This is the same delayed-delivery mechanism as the paper's A3 finding and as the counterexample in `tests/mutant_counterexample.rs`.
- **Mutant in the other direction** (`A8_c3_skew12`, `tr_0_263`): the mutant **denies** where A8 allows. A stamp ahead of the local clock (σ = 1) gives A8 a longer lease than the receipt time does. So the mutant differs from A8 both ways, not only by being more permissive.
- **A3 traces** (`A3_c1_paper`, `tr_0_104`, state 13): the model's A3 allows at `now = 0` and the A8 code denies. This happens for example when a critical event is active (A3 has no context check) or when the cache was written recently with an old origin.
- **Poll via `apply`**: the first detection is a poll of an `Absent` entry. The model writes `pdpOrig := now`; `apply` (strict `>`) ignores it. The 24 decision mismatches come from same-version polls that renew a lease in the model and not in the code. This is the divergence that motivated spec v4.

## Limitations (honest reading)

- **Testing, not proof.** 1,600 traces of 30 steps over small constants. Zero mismatches is evidence, not a guarantee.
- **The mutant is detected rarely:** 54 of 48,000 steps, 8 of 1,600 traces. Random simulation seldom delivers a notification late *and* then asks for a decision in the window where the two leases differ. The detection is real (example above), but the traces are not targeted. Directed generation, for example a TLC invariant asking for "delivered with `orig < now`", would raise the rate. This was not done.
- **Not compared:** variables with no code counterpart (`reg`, `regVer`, `dev`, `pdpAge`, `useCnt`, `badGrants`, `sinceRev`, `link`, `net`); see `MAPPING.md`. `Absent` notifications are skipped, not executed, because they have no wire encoding.
- **Trusted parts of the checker:** the checker itself (TLA+ value parser, action dispatch, wire encoder) is unverified test code. Its ability to detect disagreements was demonstrated by the three non-vacuity modes.
- **Exploratory runs:** the first 4 TLC rows of `logs/trace_runs.csv` were exploratory, run by hand before the logging script existed, so they have no time or memory figures.
