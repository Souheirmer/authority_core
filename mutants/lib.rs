//! MUTANT: receipt-timed lease. The lease starts when the cache entry is
//! written (local receipt time `recv`), not at the registry's origin time.
//! This crate is expected NOT to fully verify: `lemma_p5_receipt_timed_attempt`
//! is the P5-style lemma for the mutant and cannot be proved.
#![no_std]
#![allow(unused_imports)]

#[path = "../src/spec.rs"]
pub mod spec;
pub mod receipt_timed;
