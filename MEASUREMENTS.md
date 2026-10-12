# Measurements

## Toolchain (pinned)

| Item | Value |
|---|---|
| OS | Ubuntu 24.04.5 LTS, x86_64 (cloud sandbox) |
| Verus | `0.2026.10.04.426d8b0` (commit `426d8b01e7ffb910a36c15e1f870ff985bb61eef`), release asset `verus-0.2026.10.04.426d8b0-x86-linux.zip` |
| Rust toolchain required by Verus | `1.98.1-x86_64-unknown-linux-gnu` |
| Z3 | bundled with the Verus release |

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
| 3 | _asked at session end; awaiting answer_ | ? | |
| **Total so far** | | **6** | sessions before 1, 1 and 2 |

| Session | Cost (reported by human) |
|---|---|
| 1 | about $2 of cloud credits |
| 2 | about $1 |
| 3 | about $3 so far at its start (as reported); final figure awaiting answer |

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

## Independent AI review

Kept separate from human minutes. These are reviews by an AI system other than the one doing the work, arranged by the human. Times are the reviewer's clock as reported by the human; the reviewer's clock and the sandbox clock are not synchronised.

| Review | Scope | Wall-clock (reviewer's clock) | Result |
|---|---|---|---|
| 1 (spec v1) | Checked against rule A8 and the paper's soundness argument, plus scripts and logs | 2 min, as measured by the human (no start/end timestamps were recorded) | Approved with 4 changes (see `SPEC_CHANGES.md`, v2) |
| 2 (session 2) | Spec v2 diff, implementation, proofs, mutant, logs | 2026-10-12T00:10:56Z – 00:11:14Z (18 s) | Approved with follow-ups: put `handle` into the spec, compute the measurements, use exact times |
| 3 (commit `da9933c`) | Resource measurement: scripts and logs, no source changes | 00:14:19Z – 00:14:20Z (1 s) | Approved |

The review client runs on the human's MacBook Pro (Apple M1 Pro, 10 cores, 16 GB RAM, macOS 26.6.2). The reviewing model runs on the provider's servers, whose hardware is not visible.
