//! authority_core: verified decision core for rule A8 (origin-timed lease).
#![no_std]
#![allow(unused_imports)]

pub mod spec;
pub mod decode;
pub mod cache;
pub mod decide;
pub mod lemmas;
pub mod system_spec;
pub mod rules_spec;
pub mod rules_proofs;
pub mod rules_cex;
pub mod rules_table;
pub mod rules_exec;

use vstd::prelude::*;

verus! {

/// TRUSTED ASSUMPTION (the only one in this crate): signature verification of a
/// 21-byte notification. Out of scope for verification; no specification is
/// given, so nothing proved depends on its result. This placeholder rejects
/// everything (deny by default) until a real verifier is plugged in.
#[verifier::external_body]
pub fn signature_ok(bytes: &[u8], sig: &[u8]) -> bool {
    let _ = (bytes, sig);
    false
}

} // verus!
