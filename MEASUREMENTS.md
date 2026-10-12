# Measurements

## Toolchain (pinned)

| Item | Value |
|---|---|
| OS | Ubuntu 24.04.5 LTS, x86_64 (cloud sandbox) |
| Verus | `0.2026.10.04.426d8b0` (commit `426d8b01e7ffb910a36c15e1f870ff985bb61eef`), release asset `verus-0.2026.10.04.426d8b0-x86-linux.zip` |
| Rust toolchain required by Verus | `1.98.1-x86_64-unknown-linux-gnu` |
| Z3 | bundled with the Verus release |

Installed by `scripts/setup.sh`.

## Human time

Human minutes are as reported by the human. Wall-clock times come from the sandbox clock (UTC). Token and cost usage are not visible to the agent; they are recorded only when the human supplies them.

| Session | Activity | Minutes | Notes |
|---|---|---|---|
| before 1 | Reading (brief) and setup (GitHub, session) | 3 | reported by human |
| 1 | Approving the spec (reviewing v1, including reading the independent AI review) | 1 | reported by human |

### Session 1: 2026-10-11/12

- Agent work: 2026-10-11T23:15:20Z to 23:20:53Z (about 6 min): environment setup, scripts, `src/spec.rs` v1. Then stopped for spec approval.
- Waiting for human review: 23:20:53Z to 2026-10-12T00:03:49Z (about 43 min elapsed; the human reports 1 min of active review).
- Cost reported by human for the session: about $2 of cloud credits.

### Session 2: 2026-10-12

- Wall-clock start: 2026-10-12T00:03:49Z
- Human minutes at session start: covered by the answers above (no additional time reported).
- Agent work: spec v2, implementation, proofs, mutant, tests, RESULTS.md. Ended about 2026-10-12T00:10Z (about 6 min).
- Human minutes at session end: _asked; awaiting answer_
- Cost: _asked; awaiting answer_

## Independent AI review

Kept separate from human minutes. These are reviews by an AI system other than the one doing the work, arranged by the human.

| Review | Scope | Wall-clock (measured by human) | Result |
|---|---|---|---|
| 1 (spec v1) | Checked against rule A8 and the paper's soundness argument, plus scripts and logs | about 2 min | Approved with 4 changes (see `SPEC_CHANGES.md`, v2) |
