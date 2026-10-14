//! Signed input path (spec v5, P7): tests with real Ed25519 signatures, not
//! proofs. The proved part is `handle_post`: nothing changes the cache unless
//! the bytes decode and `signature_ok` (trusted) accepts them under the pinned
//! key. These tests exercise the trusted wrapper and the replay/expiry
//! behaviour that P2 and A8 give.
use authority_core::cache::Cache;
use authority_core::sig_impl::SIG_DOMAIN;
use ed25519_dalek::{Signer, SigningKey};

const DELTA: u64 = 100;
const SIGMA_HAT: u64 = 10;

fn key(seed: u8) -> SigningKey { SigningKey::from_bytes(&[seed; 32]) }

/// 21-byte notification: status, device (BE u32), ver (BE u64), orig (BE u64).
fn note(status: u8, device: u32, ver: u64, orig: u64) -> [u8; 21] {
    let mut b = [0u8; 21];
    b[0] = status;
    b[1..5].copy_from_slice(&device.to_be_bytes());
    b[5..13].copy_from_slice(&ver.to_be_bytes());
    b[13..21].copy_from_slice(&orig.to_be_bytes());
    b
}

fn sign(k: &SigningKey, bytes: &[u8]) -> [u8; 64] {
    let mut m = SIG_DOMAIN.to_vec();
    m.extend_from_slice(bytes);
    k.sign(&m).to_bytes()
}

fn setup() -> (Cache, SigningKey, [u8; 32]) {
    let k = key(7);
    let pk = k.verifying_key().to_bytes();
    (Cache::new(), k, pk)
}

#[test]
fn correctly_signed_notification_is_accepted() {
    let (mut c, k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    assert!(c.handle(&pk, &n, &sign(&k, &n)));
    assert!(c.allow_device(3, 1050, DELTA, SIGMA_HAT, false));
}

#[test]
fn altered_byte_is_rejected() {
    let (mut c, k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    let sig = sign(&k, &n);
    for i in 0..21 {
        let mut bad = n;
        bad[i] ^= 0x01;
        assert!(!c.handle(&pk, &bad, &sig), "byte {} altered but accepted", i);
    }
    assert!(!c.allow_device(3, 1050, DELTA, SIGMA_HAT, false));
}

#[test]
fn altered_signature_is_rejected() {
    let (mut c, k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    let mut sig = sign(&k, &n);
    sig[10] ^= 0x01;
    assert!(!c.handle(&pk, &n, &sig));
}

#[test]
fn wrong_key_is_rejected() {
    let (mut c, _k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    assert!(!c.handle(&pk, &n, &sign(&key(9), &n)));
    assert!(!c.allow_device(3, 1050, DELTA, SIGMA_HAT, false));
}

#[test]
fn signature_without_domain_prefix_is_rejected() {
    let (mut c, k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    assert!(!c.handle(&pk, &n, &k.sign(&n).to_bytes()));
}

#[test]
fn malformed_key_or_signature_length_is_rejected() {
    let (mut c, k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    let sig = sign(&k, &n);
    assert!(!c.handle(&pk[..31], &n, &sig));
    assert!(!c.handle(&pk, &n, &sig[..63]));
}

#[test]
fn replayed_older_notification_cannot_restore_authority() {
    let (mut c, k, pk) = setup();
    let enrolled = note(1, 3, 2, 1000);
    let revoked = note(0, 3, 3, 1010);
    let s_enrolled = sign(&k, &enrolled);
    assert!(c.handle(&pk, &enrolled, &s_enrolled));
    assert!(c.handle(&pk, &revoked, &sign(&k, &revoked)));
    // authentic, correctly signed, but older: a no-op by P2
    c.handle(&pk, &enrolled, &s_enrolled);
    assert!(!c.allow_device(3, 1020, DELTA, SIGMA_HAT, false));
}

#[test]
fn expired_authority_denies() {
    let (mut c, k, pk) = setup();
    let n = note(1, 3, 1, 1000);
    assert!(c.handle(&pk, &n, &sign(&k, &n)));
    // lease usable while now - orig <= delta - sigma_hat = 90
    assert!(c.allow_device(3, 1090, DELTA, SIGMA_HAT, false));
    assert!(!c.allow_device(3, 1091, DELTA, SIGMA_HAT, false));
}
