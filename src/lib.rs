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
pub mod sig_impl;
pub mod gate_spec;
pub mod gate;
pub mod gate_lemmas;
pub mod fabric_spec;
pub mod fabric;
pub mod fabric_lemmas;

use vstd::prelude::*;

verus! {

/// TRUSTED ASSUMPTION (the only external_body in this crate): Ed25519
/// verification of a 21-byte notification under the authority key `pk`
/// (spec v5). Its contract is that it returns exactly `sig_valid`; the body
/// calls the trusted wrapper in `sig_impl.rs`, which calls ed25519-dalek.
#[verifier::external_body]
pub fn signature_ok(pk: &[u8], bytes: &[u8], sig: &[u8]) -> (b: bool)
    ensures
        b == crate::spec::sig_valid(pk@, bytes@, sig@),
{
    crate::sig_impl::verify(pk, bytes, sig)
}

} // verus!
