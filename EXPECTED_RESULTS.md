# Expected results (from the published paper, TLC model checking)

Rules A1–A8 are defined in `Provisioning.tla` (lines 167–198). Properties S1–S7, AV, AVP, AVPD are defined in the paper and in `Provisioning.tla`. ✓ = holds, ✗ = violated, in the paper's default configuration (one device, one critical event type, Δ = 1, MAXAGE = MAXT = 3, MAXVER = 2, MAXNET = 1, n = 1, k = 3, synchronized clocks σ = σ̂ = 0).

| Property | A1 | A2 | A3 | A4 | A5 | A6 | A7 | A8 |
|---|---|---|---|---|---|---|---|---|
| S1 Authoritative soundness | ✗ | ✗ | ✗ | ✓ | ✗ | ✓ | ✗ | ✗ |
| S2 Immediate revocation | ✗ | ✗ | ✗ | ✓ | ✗ | ✓ | ✗ | ✗ |
| S3 Bounded revocation | ✗ | ✗ | ✗ | ✓ | ✗ | ✓ | ✗ | ✓ |
| S4 Deny absent | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| S5 Context denial | ✗ | ✗ | ✗ | ✗ | ✓ | ✓ | ✓ | ✓ |
| S6 Deny suspended | ✗ | ✗ | ✗ | ✓ | ✗ | ✓ | ✗ | ✗ |
| S7 Damage bound | ✗ | ✗ | ✗ | ✓ | ✗ | ✓ | ✓ | ✗ |
| AV Availability | ✗ | ✗ | ✗ | ✓ | ✗ | ✓ | ✗ | ✗ |
| AVP Availability under partition | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ | ✗ |
| AVPD Bounded availability under partition | ✗ | ✓ | ✓ | ✗ | ✓ | ✗ | ✗ | ✓ |

Key results: A8 is the only rule with S3, S5 and AVPD together. A3 (receipt-timed lease) violates S3 because a version-ordered but delayed notification restarts its lease. With σ̂ < σ, A8 violates S3; with σ̂ ≥ σ it holds (TLAPS proof for unbounded parameters in `ProvisioningProofs.tla`).
