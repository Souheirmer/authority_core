//! TRUSTED, NOT VERIFIED: thin wrapper over the ed25519-dalek library, called
//! only from the trusted `signature_ok` (src/lib.rs). It checks a strict
//! Ed25519 signature by a 32-byte public key over SIG_DOMAIN || bytes.
//! Under Verus (cfg `verus_keep_ghost`) a stub replaces it, so the verifier
//! never sees the library; nothing proved depends on this body, only on the
//! `sig_valid` contract of `signature_ok`.

/// Domain-separation prefix: a signature made for any other purpose (or over
/// the bare 21 bytes) does not verify as a notification signature.
pub const SIG_DOMAIN: &[u8; 30] = b"authority_core/notification/v1";
/// Notification length (see README, wire format).
pub const MSG_LEN: usize = 21;

#[cfg(not(verus_keep_ghost))]
pub fn verify(pk: &[u8], bytes: &[u8], sig: &[u8]) -> bool {
    use ed25519_dalek::{Signature, VerifyingKey};
    let pk: &[u8; 32] = match pk.try_into() { Ok(k) => k, Err(_) => return false };
    let vk = match VerifyingKey::from_bytes(pk) { Ok(k) => k, Err(_) => return false };
    let sig = match Signature::from_slice(sig) { Ok(s) => s, Err(_) => return false };
    if bytes.len() != MSG_LEN { return false; }
    let mut msg = [0u8; 30 + MSG_LEN];
    msg[..30].copy_from_slice(SIG_DOMAIN);
    msg[30..].copy_from_slice(bytes);
    vk.verify_strict(&msg, &sig).is_ok()
}

#[cfg(verus_keep_ghost)]
pub fn verify(_pk: &[u8], _bytes: &[u8], _sig: &[u8]) -> bool {
    false
}
