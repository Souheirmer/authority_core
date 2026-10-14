# Measurements

## Toolchain (pinned)

| Item | Value |
|---|---|
| OS | Ubuntu 24.04.5 LTS, x86_64 (cloud sandbox) |
| Verus | `0.2026.10.04.426d8b0` (commit `426d8b01e7ffb910a36c15e1f870ff985bb61eef`), release asset `verus-0.2026.10.04.426d8b0-x86-linux.zip` |
| Rust toolchain required by Verus | `1.98.1-x86_64-unknown-linux-gnu` |
| Z3 | bundled with the Verus release |
| Java (for TLC) | OpenJDK `21.0.12.1` (2026-08-18), preinstalled in the sandbox; `setup.sh` installs `openjdk-21-jre-headless` if missing |
| TLA+ tools | `tla2tools.jar` from release `v1.7.4` (TLC 2.19 of 08 August 2024, rev 5a47802), SHA-256 `936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88` (checked by `setup.sh`). The `v1.8.0` tag was not used: its asset is a rolling build (TLC 2026.10.06), so it can't be pinned. |

Installed by `scripts/setup.sh`.

## Hardware

| Machine | Role | CPU | Cores | RAM |
|---|---|---|---|---|
| Cloud sandbox (agent + Verus) | runs the agent's tools and every Verus run | Intel(R) Xeon(R) Processor @ 2.80GHz (`lscpu`) | 4 (`nproc`; 4 cores per socket, 1 thread per core) | 15 GiB (`free -h`), no swap |
| Human reviewer's machine | runs the independent AI review client | Apple M1 Pro | 10 | 16 GB (macOS 26.6.2) |

The models themselves run on the providers' servers, whose hardware is not visible to either side.

Each Verus run's wall time, CPU time (user + system) and peak resident memory are measured with `/usr/bin/time -v` by `scripts/verify.sh` and stored in `logs/verus_runs.csv` (columns `wall_s`, `cpu_s`, `max_rss_kb`). Runs logged before 2026-10-12T00:11Z predate this and have `NA` in those columns.

## Human time

Human minutes are as reported by the human. Costs are as reported by the human (cloud credits); token usage is not visible to the agent.

| Session | Activity | Minutes | Source |
|---|---|---|---|
| before 1 | Reading the brief; setting up GitHub and the session | 3 | reported by human |
| 1 | Approving the spec: reviewing v1, including reading the independent AI review | 1 | reported by human |
| 2 | Reading the review and sending instructions | 2 | reported by human |
| 3 | Session 3 activity (not broken down) | 0.65 (39 s) | reported by human |
| before 4 | Uploading the model to GitHub; sending the session 4 prompt | 2 | reported by human |
| 4 | Approving spec v4 (with the P4 generalisation) | 0.33 (20 s) | reported by human |
| 4 | Reviewing Extension B and deciding to continue | 0.57 (34 s) | reported by human; the human puts session 4 so far at about 1 min (20 s + 34 s = 54 s) |
| 4 | Approving the Extension A spec files and proof plan | 0.42 (25 s) | reported by human |
| 4 | Reviewing Extension A and closing session 4 | 0.27 (16 s) | reported by human |
| **Total** | | **10 min 14 s** | before session 1, sessions 1–4 |

| Session | Cost (reported by human) |
|---|---|
| 1 | about $2 of cloud credits |
| 2 | about $1 |
| 3 | about $1 |
| **Total, sessions 1–3** | **about $4** (confirmed by the human; the "about $3 so far" said mid-session 3 was the cumulative total of sessions 1–2) |
| 4 (so far, at the spec v4 approval, 01:15Z) | cumulative total about $6, i.e. about $2 in session 4 so far (reported by human) |
| 4 (Extension B complete, 01:21Z) | about $4 for session 4 so far (all of Extension B); cumulative total about $8 (reported by human) |
| 4 (final) | **about $9 for session 4** (Extension B about $4, Extension A about $5); **cumulative total about $13** (reported by human) |

## Wall-clock time (exact, UTC)

Sources:
- `commit`: the commit timestamp (`git log --format=%cI`).
- `log`: the timestamp of a run in `logs/verus_runs.csv`.
- `clock`: the sandbox clock (`date -u`) printed by the agent's first command of the turn. Session starts have no commit or log entry, so the clock reading is used; the earliest commit or log evidence is given beside it.

| Session | Start | End | Agent duration | Contents |
|---|---|---|---|---|
| 1 | 2026-10-11T23:15:20Z (clock; first log 23:20:25Z) | 2026-10-11T23:20:52Z (commit `b1516aa`) | 5 min 32 s | setup, scripts, `spec.rs` v1; stopped for approval |
| (human review) | 23:20:52Z | 2026-10-12T00:03:49Z | 42 min 57 s elapsed | human reports 1 min active review |
| 2, turn 1 | 2026-10-12T00:03:49Z (clock; first log 00:04:32Z) | 00:09:39Z (commit `0113f33`) | 5 min 50 s | spec v2, implementation, proofs, mutant, tests, `RESULTS.md` |
| 2, turn 2 | 00:10:39Z (clock; first log 00:11:02Z) | 00:11:18Z (commit `da9933c`) | 39 s | resource measurement, hardware record |
| (between sessions) | 00:11:18Z | 00:17:59Z | 6 min 41 s elapsed | |
| 3 | 00:17:59Z (clock; first log 00:18:14Z) | 00:19:27Z (commit `67601c9`) | 1 min 28 s | spec v3 (`handle_post`), exact times, final `RESULTS.md` |

Session 2 spans two agent turns; the second turn (resource measurement) is counted in session 2.

- **Total agent wall-clock:** 13 min 29 s.
- **Total elapsed**, from the session 1 start to the session 3 end: 1 h 4 min 7 s.

### Verus run resources

See columns `wall_s`, `cpu_s` and `max_rss_kb` in `logs/verus_runs.csv`. These are measured from 2026-10-12T00:11:02Z on; earlier runs show `NA`.

### Session 4: 2026-10-12

- Human minutes before session 4: 2 (uploading the model, sending the prompt).
- Human minutes during session 4: 20 s + 34 s + 25 s + 16 s = **1 min 35 s** (spec v4 approval, Extension B review, Extension A spec approval, Extension A review).
- Cost (reported by human): **about $9 for session 4**: about $4 for Extension B (including setup and spec v4), so about $5 for Extension A (derived). Cumulative total about $13.
- Agent turns (start = sandbox clock at the turn's first command; end = last commit of the turn):

| Turn | Start | End | Duration | Work |
|---|---|---|---|---|
| 4.1 | 00:53:28Z | 00:56:05Z (`e8e20b8`) | 2 min 37 s | setup (Java, TLA+ tools), TraceGen, mapping question; stopped for the human |
| 4.2 | 01:01:20Z | 01:01:42Z (`cad3538`) | 22 s | spec v4 draft; stopped for approval |
| 4.3 | 01:15:08Z | 01:20:02Z (`028b37f`) | 4 min 54 s | spec v4 verified; Extension B (trace validation) |
| 4.4 | 01:27:42Z | 01:29:24Z (`2eb8914`) | 1 min 42 s | Extension A spec files; stopped for approval |
| 4.5 | 01:40:42Z | 01:55:22Z (merge `293d83d`) | 14 min 40 s | Extension A proofs, executable rules, tests, `RESULTS_RULES.md`, merge into main |
| 4.6 | 02:16:35Z | 02:17:10Z (`40ef70d`) | 0 min 35 s | close-out: review 9, measurements, merge |

- **Agent wall-clock, session 4:** 24 min 50 s. That is Extension B 7 min 53 s (turns 4.1–4.3) and Extension A 16 min 22 s (turns 4.4–4.5), plus the close-out.
- **Elapsed, session 4:** 00:53:28Z to 02:17:10Z (`40ef70d`) (1 h 23 min 42 s), including the waits for the human.
- TLC and checker runs are logged in `logs/trace_runs.csv` (wall time, CPU time, peak RSS), on the same 4-core Xeon sandbox.

## Independent AI review

Kept separate from human minutes. These are reviews by an AI system other than the one doing the work, arranged by the human. Times are the reviewer's clock as reported by the human; the reviewer's clock and the sandbox clock are not synchronised.

| Review | Scope | Wall-clock (reviewer's clock) | Result |
|---|---|---|---|
| 1 (spec v1) | Checked against rule A8 and the paper's soundness argument, plus scripts and logs | 2 min, as measured by the human (no start/end timestamps were recorded) | Approved with 4 changes (see `SPEC_CHANGES.md`, v2) |
| 2 (session 2) | Spec v2 diff, implementation, proofs, mutant, logs | 2026-10-12T00:10:56Z – 00:11:14Z (18 s) | Approved with follow-ups: put `handle` into the spec, compute the measurements, use exact times |
| 3 (commit `da9933c`) | Resource measurement: scripts and logs, no source changes | 00:14:19Z – 00:14:20Z (1 s) | Approved |
| 4 (session 3) | Spec v3 diff, `handle` contract, logs, no-gaming check | 00:20:30Z – 00:20:32Z (2 s) | Approved |
| 5 (session 4 setup) | Model unchanged vs. upload, TraceGen wrapper, PdpPoll semantics, mapping questions | 00:57:09Z – 00:57:11Z (2 s) | Approved, with decisions 1(a) (verified `poll_update`) and 2(a) (`Suspended`, wire byte 2) |
| 6 (spec v4 diff) | `Suspended`, `poll_spec`/`poll_post`, checked against PdpPoll lines 268–279 and CacheNotAheadOfRegistry line 557 | 01:03:38Z – 01:03:40Z (2 s) | Approved with the P4 generalisation |
| 7 (Extension B) | Spec v4 change, `poll_update`, logs, trace runs, non-vacuity runs, no-gaming check | 01:21:19Z – 01:21:21Z (2 s) | Approved |
| 8 (Extension A spec) | Rules A1–A8, properties S1–AVPD, Init, all 12 actions, `paper_params`, compared line by line with Provisioning.tla and the TLC configuration files | 01:30:22Z – 01:30:52Z (30 s) | Approved |
| 9 (Extension A) | Spec files unchanged since approval, `lemma_paper_table` statement, no-gaming check, final verification log, mutant re-run, merge | 01:56:49Z – 01:56:57Z (8 s) | Approved |

The review client runs on the human's MacBook Pro (Apple M1 Pro, 10 cores, 16 GB RAM, macOS 26.6.2). The reviewing model runs on the provider's servers, whose hardware is not visible.

## Session 5 (2026-10-14): signed input path

Environment: `ubuntu:24.04` linux/amd64 container under emulation on the human's Apple M1 Pro (16 GB); same pinned Verus and Rust. Verus runs (wall / CPU / peak RSS, from `logs/verus_runs.csv`): baseline 51.2 s / 68.3 s / 569 MiB; spec v5 49.8 s / 66.8 s / 569 MiB; planted bug 44.9 s / 62.6 s / 563 MiB; re-run 47.9 s / 64.7 s / 569 MiB. One Verus attempt of spec v5, accepted first time; no failed attempts other than the planted bug.

| Activity | Human minutes | Source |
|---|---|---|
| Instruction to tag the pilot and add the signature path, and approval of spec v5 (with the `pk` assumption and P7 scope) | about 2 | reported by human (whole session) |

## Session 6 (2026-10-14): D witness

Same environment as session 5. Verus runs (wall / CPU / peak RSS): first attempt 52.7 s / 70.8 s / 572 MiB (passed); planted bug D-1 49.1 s / 67.9 s; planted bug D-2 47.4 s / 66.1 s; final 49.6 s / 68.0 s / 573 MiB. The spec, code and proofs verified on the first attempt; no failed attempts other than the two planted bugs.

| Activity | Human minutes | Source |
|---|---|---|
| Instruction to build the D witness, and approval of the D-witness spec with clarifications | about 2 | reported by human (whole session) |

## Session 7 (2026-10-14): B witness

Same environment as session 5. Verus runs (wall / CPU / peak RSS): first attempt 51.4 s / 70.8 s / 577 MiB (passed); planted bug B-1 and B-2 (both rejected, see `logs/verus_runs.csv`); final 52.0 s / 71.4 s / 577 MiB. The spec, code and proofs verified on the first attempt; no failed attempts other than the two planted bugs.

| Activity | Human minutes | Source |
|---|---|---|
| Instruction to build the B witness (given with the D approval) | included in session 6 | reported by human |
| Approval of the B-witness spec | pending | — |
