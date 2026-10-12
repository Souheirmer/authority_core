# Extension A: all eight rules of the paper on verified code

**Result: all 80 cells of the paper's 8×10 table are machine-checked, and every one agrees with `model/EXPECTED_RESULTS.md`. There are 0 disagreements and 0 open cells.** The agreement itself is a theorem: `lemma_paper_table` (`src/rules_table.rs`) proves, for every rule and property, that `paper_expected(rule, prop)` implies `cell_holds(paper_params(), rule, prop)` and that its negation implies `cell_violated(paper_params(), rule, prop)`.

## What the evidence is

- **Model:** `src/system_spec.rs` and `src/rules_spec.rs`, transcribed from `model/Provisioning.tla` with line citations. Human-approved (review 8); see `SPEC_CHANGES.md`, "ExtA v1".
- **✓ cell:** `cell_holds(p, rule, prop)`, the property holds in **every reachable state**. Reachable means: at the end of any finite execution from `Init`, of any length.
  - Proof: an inductive invariant, `inv` (`src/rules_proofs.rs`), plus `rule_inv` for S7. Init establishes it (`lemma_inv_init`), every action preserves it (`lemma_inv_step`), and induction over the execution gives it for every reachable state (`lemma_reachable_inv`).
  - `inv` contains the model's own IndInv conjuncts: `CacheNotAheadOfRegistry`, `RegistryVersionConsistent`, `CacheVersionConsistent`, `NotificationVersionConsistent`, `CacheMatchesCurrentVersion`, `NotificationMatchesCurrentVersion`, `ClockCoherence` (first conjunct), `NotificationsWellFormed`, `NotificationOriginBounded`, `NotificationPrecedesRevocation` and **`OriginPrecedesRevocation`**.
  - It adds 4 facts of my own: origin stamps ≤ MAXT; `pdpAge ≤ now − pdpOrig + SKEW`; `reg = Absent ⇒ dev = Unprov`; `|net| ≤ MAXNET`.
- **✗ cell:** `cell_violated(p, rule, prop)`, a concrete execution in the paper's configuration. Verus checks that it starts in `Init`, that every action is in range, enabled, and produces exactly the next state, and that the last state violates the property (`src/rules_cex.rs`).
  - The same 50 executions are replayed in `tests/rules_counterexamples.rs` (test `all_50_counterexamples_replay_and_violate`). That test runs an unverified executable copy of the transitions, which panics if an action is not enabled, and makes its decisions with the verified executable rules.
  - A control test (`check_mark_rules_are_not_violated_by_these_traces`) checks that the same traces do *not* violate ✓ cells.
- **Configuration:** the paper's default, `paper_params()`: one device, one event type that is critical, Δ = LEASE = 1, MAXAGE = MAXT = 3, MAXVER = 2, MAXNET = 1, MAXUSE = 1, MAXBAD = 3, σ = σ̂ = 0. Many ✓ results are proved more generally; see the "Scope" column.

## The table (✓ holds, ✗ violated; every cell matches the paper)

| Property | A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8 |
|---|---|---|---|---|---|---|---|---|
| S1 Authoritative soundness | ✗ T1 | ✗ T10 | ✗ T10 | ✓ a | ✗ T10 | ✓ a | ✗ T10 | ✗ T10 |
| S2 Immediate revocation | ✗ T1 | ✗ T10 | ✗ T10 | ✓ a | ✗ T10 | ✓ a | ✗ T10 | ✗ T10 |
| S3 Bounded revocation | ✗ T1 | ✗ T2 | ✗ T3 | ✓ a | ✗ T3 | ✓ a | ✗ T2 | **✓ c** |
| S4 Deny absent | ✓ b | ✓ b | ✓ b | ✓ a | ✓ b | ✓ a | ✓ b | ✓ b |
| S5 Context denial | ✗ T4 | ✗ T5 | ✗ T5 | ✗ T6 | ✓ a | ✓ a | ✓ a | ✓ a |
| S6 Deny suspended | ✗ T12 | ✗ T11 | ✗ T11 | ✓ a | ✗ T11 | ✓ a | ✗ T11 | ✗ T11 |
| S7 Damage bound | ✗ T13 | ✗ T13 | ✗ T13 | ✓ e | ✗ T13 | ✓ e | **✓ f** | ✗ T13 |
| AV Availability | ✗ T14 | ✗ T14 | ✗ T14 | ✓ a | ✗ T14 | ✓ a | ✗ T14 | ✗ T14 |
| AVP Avail. under partition | ✗ T14 | ✗ T14 | ✗ T14 | ✗ T15 | ✗ T14 | ✗ T15 | ✗ T14 | ✗ T14 |
| AVPD Bounded avail. under partition | ✗ T7 | ✓ b | ✓ d | ✗ T8 | ✓ d | ✗ T8 | ✗ T9 | ✓ b |

Totals: 30 ✓, 50 ✗. The paper's key result, that **A8 is the only rule with S3, S5 and AVPD together**, follows from the A8 column and the S3, S5 and AVPD rows.

### Evidence for the ✓ cells (lemmas in `src/rules_proofs.rs`)

| Mark | Cells | Lemma(s) | Scope (what is proved) |
|---|---|---|---|
| a | S1, S2, S3, S4, S6, AV for A4 and A6; S5 for A5–A8 | `lemma_cell_s1_a4`, `…_s1_a6`, `…_s2_a4/a6`, `…_s3_a4/a6`, `…_s4_a4/a6`, `…_s6_a4/a6`, `…_av_a4/a6`, `…_s5_a5/a6/a7/a8` | **Any Params, any state.** The rule's definition contradicts the property's premise, so no invariant is needed. |
| b | S4 for A1, A2, A3, A5, A7, A8; AVPD for A2, A8 | `lemma_cell_s4(p, rule)`, `lemma_cell_avpd_a2`, `lemma_cell_avpd_a8` | **Any Params satisfying ConstAssumptions.** S4 uses `LifecycleVersion`: reg Absent ⇒ regVer 0 ⇒ pdpVer 0 ⇒ pdpSt Absent, and reg Absent ⇒ dev Unprov. AVPD uses `CacheMatchesCurrentVersion`. |
| c | **S3 for A8** | `lemma_cell_s3_a8` | **Any Params with ConstAssumptions, SKEW ≤ SKEWBOUND and MAXT ≤ 2⁶⁴−1.** The inductive invariant contains the model's `OriginPrecedesRevocation`. The final step **calls P5** (`lemma_p5_soundness_core`, `src/lemmas.rs`) on the code's `Entry` type, which is why the clock must fit in u64. This mechanizes, in Verus, the statement the paper proves in TLAPS. |
| d | AVPD for A3, A5 | `lemma_cell_avpd_a3`, `lemma_cell_avpd_a5` | **Any Params with ConstAssumptions and SKEW ≤ SKEWBOUND**, using `pdpAge ≤ now − pdpOrig + SKEW`. Without SKEW ≤ SKEWBOUND the cell can fail; that case is outside the paper's configuration and was not explored. |
| e | S7 for A4, A6 | `lemma_cell_s7_a4`, `lemma_cell_s7_a6` (via `rule_inv`) | **Any Params with ConstAssumptions and MAXBAD > 0.** These rules grant only when reg is Enrolled, so `badGrants` stays 0. |
| f | **S7 for A7** | `lemma_cell_s7_a7` (via `rule_inv`, `a7_budget`) | **The paper's configuration only.** Invariant: once the registry has made its last change (to Suspended or Revoked at version MAXVER = 2), badGrants + [one unused cached grant] + [one pending, still-acceptable Enrolled notification] ≤ 1. So badGrants ≤ 1 < MAXBAD = 3. The bound for other constants depends on MAXUSE, MAXVER and MAXNET (the model's `DamageBelow2/3`, L490–493) and is not claimed. |

### Evidence for the ✗ cells (lemmas in `src/rules_cex.rs`, `paper_params()`, device d1, event e1)

| Trace | Actions | Cells | Lemma |
|---|---|---|---|
| T1 | Enroll; SyncFromRegistry; Revoke; Tick; Tick | S1, S2, S3 for A1 | `lemma_cell_s1_a1_violated`, `…_s2_a1_…`, `…_s3_a1_…` |
| T2 | Enroll; PdpPoll; Revoke; Tick; Tick | S3 for A2, A7 | `lemma_cell_s3_a2_violated`, `…_s3_a7_…` |
| T3 | Enroll; PushNotify(t=0); Revoke; Tick; Tick; DeliverNotify(⟨d1, Enrolled, 1, 0⟩) — **the paper's A3 finding**: a version-ordered but delayed notification renews the lease | S3 for A3, A5 | `lemma_cell_s3_a3_violated`, `…_s3_a5_…` |
| T4 | Enroll; SyncFromRegistry; ObserveEvent(e1) | S5 for A1 | `lemma_cell_s5_a1_violated` |
| T5 | Enroll; PdpPoll; ObserveEvent(e1) | S5 for A2, A3 | `lemma_cell_s5_a2_violated`, `…_s5_a3_…` |
| T6 | Enroll; ObserveEvent(e1) | S5 for A4 | `lemma_cell_s5_a4_violated` |
| T7 | Enroll; PdpPoll | AVPD for A1 | `lemma_cell_avpd_a1_violated` |
| T8 | Enroll; PdpPoll; Partition | AVPD for A4, A6 | `lemma_cell_avpd_a4_violated`, `…_avpd_a6_…` |
| T9 | Enroll; PdpPoll; RecordAccess | AVPD for A7 | `lemma_cell_avpd_a7_violated` |
| T10 | Enroll; PdpPoll; Revoke | S1, S2 for A2, A3, A5, A7, A8 | `lemma_cell_cache_rules_violated(rule, S1/S2)` |
| T11 | Enroll; PdpPoll; Suspend | S6 for A2, A3, A5, A7, A8 | `lemma_cell_cache_rules_violated(rule, S6)` |
| T12 | Enroll; SyncFromRegistry; Suspend | S6 for A1 | `lemma_cell_s6_a1_violated` |
| T13 | Enroll; (Sync for A1, PdpPoll otherwise); Revoke; RecordAccess ×3 | S7 for A1, A2, A3, A5, A8 | `lemma_cell_s7_a1_violated`, `lemma_cell_s7_cache_violated(rule)` |
| T14 | Enroll | AV, AVP for A1, A2, A3, A5, A7, A8 | `lemma_cell_av_avp_violated(rule, AV/AVP)` |
| T15 | Enroll; Partition | AVP for A4, A6 | `lemma_cell_avp_failclosed_violated(rule)` |

## Executable rules (step 2)

`src/rules_exec.rs`: `exec_a1` … `exec_a8` and the dispatcher `exec_allow_rule`. Each is proved equal to its spec function for every state and device whose components match the inputs (`inputs_match`).
- `exec_a8` **delegates to the original verified `decide::allow`** (P3). It equals the model's A8 under `SKEWBOUND ≤ LEASE`, which the model `ASSUME`s (L81); the code's own a8 additionally denies when σ̂ > Δ.
- Sanity check: two planted bugs were rejected by Verus (logged run 01:52:25Z): `<` for `<=` in A3, and A6 ignoring the critical flag.

## Comparison with `EXPECTED_RESULTS.md`

All 80 cells agree. **No disagreement was found**, so nothing points to a mistake in the code, the Verus model, the TLA+ model or the paper for these cells in this configuration. Notes:
- **Several ✓ cells are proved beyond the paper's configuration** (Scope column above). In particular, A8/S3 holds for any constants with σ ≤ σ̂ and a u64 clock. This matches the paper's TLAPS theorem and is now also checked in Verus against the transcribed model.
- **A7/S7 is the only ✓ cell proved for the paper's configuration alone.**
- **AVPD for A3/A5 needs σ ≤ σ̂** in my proof. The paper's table assumes σ = σ̂ = 0, so this is consistent. I did not check whether the cell actually fails when σ > σ̂.

## Sanity checks (the proofs can fail)

- Run 01:44:55Z: claimed A3/S3 ✓ (with the A8 proof) and A8/S3 ✗ (with trace T3). Both were rejected.
- Run 01:52:25Z: two planted bugs in the executable rules. Both were rejected.
- `tests/rules_counterexamples.rs::check_mark_rules_are_not_violated_by_these_traces`.

## Size (Verus `line_count`, Extension A files only)

| File | Spec | Proof | Exec | Comment |
|---|---|---|---|---|
| `system_spec.rs` (model transcription) | 175 | 0 | 48 (type declarations) | 82 |
| `rules_spec.rs` (rules, properties, cells, paper table) | 119 | 0 | 2 | 48 |
| `rules_proofs.rs` (invariants, 30 ✓ cells) | 155 | 303 | 0 | 68 |
| `rules_cex.rs` (50 ✗ cells) | 135 | 368 | 0 | 73 |
| `rules_table.rs` (table theorem) | 13 | 86 | 0 | 6 |
| `rules_exec.rs` (executable rules) | 33 | 0 | 73 | 12 |
| **Extension A total** | **630** | **757** | **123** | **289** |

Whole crate: 112 verified items, 0 errors. Trusted 5 lines (`signature_ok`, unchanged), spec 820, proof 846, exec 237. Plus `tests/rules_counterexamples.rs` (unverified test code, 221 lines).

## Verifier runs for Extension A (`logs/verus_runs.csv`, 01:29:10Z – 01:53:55Z)

| | Count |
|---|---|
| Runs | **20** (12 passed, 8 failed) |
| Development failures | 5: a trigger instantiation in the induction (01:42:54Z); a missing per-device fact for PushNotify (01:47:09Z); the A7 budget asserted in the wrong phase (01:48:30Z); a resource-limit timeout on the S7 damage trace (01:49:38Z); sequence lengths after splitting that trace (01:50:13Z) |
| Deliberate sanity failures | 2 (01:44:55Z, 01:52:25Z) |
| Expected mutant failure | 1 (01:53:55Z) |
| Verus wall time, all 20 runs | 195.3 s (CPU 238.6 s); peak memory 370 MiB; a full crate verification takes about 14 s |

Hardware: 4-core Intel Xeon @ 2.80GHz, 15 GiB RAM.

## Time

- Agent wall-clock for Extension A (commit timestamps and the sandbox clock):
  - Spec files: 01:27:42Z (clock) to 01:29:24Z (commit `2eb8914`).
  - Proofs, executable rules, tests and this report: 01:40:42Z (clock) to the final commit of this session (see `git log`).
- Human minutes: 25 s approving the Extension A spec. The session 4 total is in `MEASUREMENTS.md`.
- Cost: reported by the human; not visible to the agent.

## What did not work, or is limited

- The 5 development failures above were each fixed in the next run or two. No proof was weakened; the no-gaming check passed on every run.
- **Scope of the evidence.** The table is established for the paper's configuration. ✗ cells are shown only there; ✓ cells there and, where marked, more generally. Fairness and liveness (L1, L2) were not transcribed.
- **The transcription is trusted.** `system_spec.rs` and `rules_spec.rs` are only as faithful as the human and AI review (review 8) found them. Verus checks consistency with them, not with the TLA+ file.
- **The Rust replay is unverified.** The executable transition copy in `tests/rules_counterexamples.rs` is test code; the Verus lemmas are the evidence.
