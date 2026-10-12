# Mapping: Provisioning.tla to authority_core

This mapping is used by the trace checker (`trace_validation/src/main.rs`). It was approved by the human before the checker was written (session 4, with decisions 1(a) and 2(a)). Line numbers refer to `model/Provisioning.tla`.

## Constants

| Model | Code | Notes |
|---|---|---|
| `DEVICES = {d1, …, dk}` | device ids `0 … k−1` | model value `d<i>` becomes id `i−1`; requires `k ≤ N = 64` |
| `LEASE` | `delta` | |
| `SKEWBOUND` | `sigma_hat` | the model ASSUMEs `SKEWBOUND <= LEASE` (line 81); the code denies otherwise |
| `CRITICAL`, `activeEv[d]` | `critical` argument of `allow_device` | `critical = (activeEv[d] ∩ CRITICAL ≠ {})`, i.e. `~NoCritical(d)` (line 165) |
| `now` | `now` argument | the model clock is the decision point's clock |
| `SKEW` | — | not a code input. It only bounds the stamps the registry produces (line 240). |

## Decision-point state (compared after every step, for every device)

| Model | Code |
|---|---|
| `pdpSt[d]` | `cache.entries[d].status`: `"Absent"` ↔ `Unknown`, `"Enrolled"` ↔ `Enrolled`, `"Revoked"` ↔ `Revoked`, `"Suspended"` ↔ `Suspended` (spec v4) |
| `pdpVer[d]` | `cache.entries[d].ver` |
| `pdpOrig[d]` | `cache.entries[d].orig` |
| `AllowRule(d)` with `RULE = "A8_OriginLease"` (lines 194–196, 198–206) | `cache.allow_device(d, now, LEASE, SKEWBOUND, critical)` |

TLC evaluates `AllowRule(d)` itself. The wrapper `trace_validation/tla/TraceGen.tla` records it in the auxiliary variable `allowed`, so the checker never re-implements the rule; it only reads TLC's value.

## Actions

| Model action (line) | Code |
|---|---|
| `DeliverNotify(m)` (247–258) | `m` is encoded to the 21-byte wire format, then `decode`, then `Cache::apply`. This exercises the verified decoder too. |
| `DeliverNotify(m)` with `m.st = "Absent"` | **Skipped**, and counted (`skipped_absent`). The model's invariant `LifecycleVersion`, `(st = "Absent") <=> (v = 0)` (line 565, used in `NotificationVersionConsistent`, line 579), means such a notification has version 0, so `m.ver > pdpVer[d]` is false and the model leaves the cache unchanged. "Absent" has no wire encoding. The checker **asserts** `m.ver = 0` for every skipped notification; the assertion never failed. |
| `PdpPoll(d)` (268–279) | `Cache::poll_update(d, reg[d], regVer[d], now)` (spec v4, `poll_spec`), using the pre-state's `reg[d]`, `regVer[d]` and `now`: the registry's answer, stamped with the decision point's own clock. Unconditional, as in the model. A poll of an `Absent` registry entry writes `(Unknown, 0, now)`, exactly as the model writes `("Absent", 0, now)`. |
| `DropNotify(m)` (261–265) | nothing (the message is lost) |
| `RegChange` (217–224), `PushNotify` (234–244), `SyncFromRegistry` (291–294), `ObserveEvent`/`ClearEvent` (296–307), `RecordAccess` (349–357), `Tick` (310–320), `Partition`/`Heal` (323–331) | nothing in the code. These change only model variables the decision point's code does not hold (`reg`, `regVer`, `dev`, `net`, `useCnt`, `badGrants`, `sinceRev`, `link`, `pdpAge`), or the inputs `now` and `activeEv`, which are passed to `allow_device` at comparison time. |

## Model variables with no code counterpart (not compared)

- `reg`, `regVer`, `sinceRev`: registry ground truth. These are the environment; the code receives them only through notifications and polls.
- `dev`: the device-local view (rule A1 only).
- `pdpAge`: time since the cache was written (rules A3 and A5). The A8 code doesn't need it. The receipt-timed mutant keeps its own `recv` instead.
- `useCnt`, `badGrants`: rule A7 and property S7.
- `link`, `net`: the network. The code sees only what is delivered.

## Non-vacuity modes

- `mutant`: the receipt-timed `RtCache` from `mutants/` replays the same A8 traces. On delivery it stamps `recv = now`; on a poll, `recv = orig = now`.
- `real` on A3 traces: the verified A8 code is compared against the traces' `AllowRule` under `RULE = "A3_Lease"`.
- `poll-as-apply`: the verified code, but poll answers go through `apply` instead of `poll_update`. This is the mapping 1(b) that the human rejected. It tests whether the checker can detect cache-state disagreements, and it measures what `poll_update` fixed.
