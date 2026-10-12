//! Mutant check (TEST, not a proof): the receipt-timed lease is unsound.
//! Trace (true time = decision point clock, sigma = 0; delta = 100, sigma_hat = 10):
//!   t=0    registry: device 3 Enrolled (ver 1, orig 0)  -- delivery delayed
//!   t=10   registry: device 3 Revoked  (ver 2, orig 10) -- delivery delayed further
//!   t=200  ver 1 arrives; version-ordered (1 > 0), so it is accepted
//!   t=200..=290  receipt-timed lease ALLOWS device 3 although it was revoked
//!                more than delta = 100 ticks ago; origin-timed A8 denies
//!   t=300  ver 2 arrives; both rules deny from now on

use authority_core::cache::Cache;
use authority_core::decode::decode;
use authority_core_mutants::receipt_timed::RtCache;

fn encode(status: u8, device: u32, ver: u64, orig: u64) -> [u8; 21] {
    let mut b = [0u8; 21];
    b[0] = status;
    b[1..5].copy_from_slice(&device.to_be_bytes());
    b[5..13].copy_from_slice(&ver.to_be_bytes());
    b[13..21].copy_from_slice(&orig.to_be_bytes());
    b
}

const DELTA: u64 = 100;
const SIGMA_HAT: u64 = 10;
const SIGMA: i128 = 0;
const REVOKED_AT: u64 = 10;
const DEV: u32 = 3;

#[test]
fn receipt_timed_lease_outlives_revocation() {
    let enroll = encode(1, DEV, 1, 0);
    let revoke = encode(0, DEV, 2, REVOKED_AT);

    // the mutant crate has its own copy of the spec types, so decode twice
    let m1 = decode(&enroll).unwrap();
    let m2 = decode(&revoke).unwrap();
    let mm1 = authority_core_mutants::spec::Notification {
        device: m1.device, status: authority_core_mutants::spec::Status::Enrolled, ver: m1.ver, orig: m1.orig,
    };
    let mm2 = authority_core_mutants::spec::Notification {
        device: m2.device, status: authority_core_mutants::spec::Status::Revoked, ver: m2.ver, orig: m2.orig,
    };

    let mut good = Cache::new();
    let mut bad = RtCache::new();

    // t = 200: delayed ver 1 arrives and is accepted by both (1 > 0)
    good.apply(&m1);
    bad.apply(&mm1, 200);
    assert_eq!(good.entries[DEV as usize].ver, 1);
    assert_eq!(bad.entries[DEV as usize].ver, 1);

    let mut first_unsound = None;
    for now in 200u64..300 {
        let since_rev = (now - REVOKED_AT) as i128;
        // the model's invariant (origin stamp precedes revocation) holds
        assert!(since_rev <= (now as i128 - m1.orig as i128) + SIGMA);
        // origin-timed A8 denies (lease from orig = 0 expired at 90)
        assert!(!good.allow_device(DEV, now, DELTA, SIGMA_HAT, false));
        let mutant = bad.allow_device(DEV, now, DELTA, SIGMA_HAT, false);
        if now <= 290 {
            // receipt-timed lease from recv = 200 lasts until 290
            assert!(mutant, "mutant should allow at now={now}");
            assert!(since_rev > DELTA as i128);
            first_unsound.get_or_insert(now);
        } else {
            assert!(!mutant);
        }
    }
    assert_eq!(first_unsound, Some(200));

    // the exact instance used in the Verus proof lemma_p5_receipt_timed_is_false
    assert!(bad.allow_device(DEV, 280, DELTA, SIGMA_HAT, false));
    assert_eq!(280 - REVOKED_AT, 270);

    // t = 300: revocation finally arrives; both deny
    good.apply(&m2);
    bad.apply(&mm2, 300);
    assert!(!good.allow_device(DEV, 300, DELTA, SIGMA_HAT, false));
    assert!(!bad.allow_device(DEV, 300, DELTA, SIGMA_HAT, false));
}
