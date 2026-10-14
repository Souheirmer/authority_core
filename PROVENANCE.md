# Provenance

The specification drafts, the code and the proofs in this repository were produced by LLM agents working in a loop with the Verus verifier: the agent wrote spec, code and proof text, ran Verus through `scripts/verify.sh`, read the verifier's output, and revised.

A human reviewed and approved the specification (`src/spec.rs`) before any implementation proofs were written. Every later change to the specification is proposed to the human and logged in `SPEC_CHANGES.md` with its reason.

Only the verifier's acceptance establishes the proofs. No claim in this repository rests on the agent's own judgement that something is correct. Every verifier run, passing or failing, is logged in `logs/verus_runs.csv`, and full outputs are kept in `logs/runs/`. `scripts/check_no_gaming.sh` runs on every verification and rejects `assume`, `admit`, `external_body` and similar escape hatches everywhere except the single declared trusted function `signature_ok`.

Session 5 (2026-10-14, spec v5, branch `signed-input`) was carried out the same way by an LLM agent, running Verus in a local linux/amd64 container instead of the cloud sandbox. The spec change was approved by the human on 2026-10-14 with an explicit key assumption and scope (see `SPEC_CHANGES.md`) before the branch was merged.
