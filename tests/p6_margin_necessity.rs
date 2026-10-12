//! P6 (TEST, not a proof): the clock-error margin sigma_hat is necessary.
//! If the real clock error sigma exceeds the configured bound sigma_hat, A8 can
//! allow a device whose revocation is more than delta in the past, even though
//! the model's invariant `since_rev <= (now - orig) + sigma` holds.

use authority_core::cache::Cache;
use authority_core::decide::allow;
use authority_core::decode::decode;
use authority_core::spec::{Entry, Status};

/// Wire encoding (test helper): status, device BE u32, ver BE u64, orig BE u64.
fn encode(status: u8, device: u32, ver: u64, orig: u64) -> [u8; 21] {
    let mut b = [0u8; 21];
    b[0] = status;
    b[1..5].copy_from_slice(&device.to_be_bytes());
    b[5..13].copy_from_slice(&ver.to_be_bytes());
    b[13..21].copy_from_slice(&orig.to_be_bytes());
    b
}

#[test]
fn p6_witness_sigma_hat_below_sigma() {
    let delta: u64 = 100;
    let sigma_hat: u64 = 10;
    let sigma: i128 = 30; // real clock error, larger than sigma_hat
    assert!(sigma_hat <= delta);
    assert!((sigma_hat as i128) < sigma);

    // Registry says: device 7 Enrolled, ver 1, origin time 0.
    let m = decode(&encode(1, 7, 1, 0)).expect("well-formed");
    let mut c = Cache::new();
    c.apply(&m);

    let now: u64 = 90; // now - orig = 90 = delta - sigma_hat, so age_ok holds
    let since_rev: i128 = 120; // device was revoked 120 ticks ago (true time)

    // model invariant holds with the real sigma
    assert!(since_rev <= (now as i128 - m.orig as i128) + sigma);
    // A8 allows ...
    assert!(c.allow_device(7, now, delta, sigma_hat, false));
    // ... although the revocation is older than delta
    assert!(since_rev > delta as i128);
}

/// With sigma <= sigma_hat no witness exists (exhaustive over a small grid).
/// This is only a test; the general statement is P5, proved in src/lemmas.rs.
#[test]
fn p6_no_witness_when_sigma_within_bound() {
    let delta = 20u64;
    for sigma_hat in 0..=delta {
        for sigma in -5i128..=(sigma_hat as i128) {
            for orig in 0u64..40 {
                for now in 0u64..40 {
                    let e = Entry { status: Status::Enrolled, ver: 1, orig };
                    if !allow(&e, now, delta, sigma_hat, false) {
                        continue;
                    }
                    let max_since_rev = (now as i128 - orig as i128) + sigma;
                    assert!(max_since_rev <= delta as i128,
                        "violation: sigma_hat={sigma_hat} sigma={sigma} orig={orig} now={now}");
                }
            }
        }
    }
}
