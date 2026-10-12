//! P3: executable decision rule A8.
use vstd::prelude::*;
use crate::spec::*;

verus! {

/// Rule A8 on a single cache entry. Deny by default.
pub fn allow(e: &Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool) -> (b: bool)
    ensures
        allow_post(*e, now, delta, sigma_hat, critical, b),
{
    let enrolled = match e.status {
        Status::Enrolled => true,
        _ => false,
    };
    if !enrolled || critical || sigma_hat > delta {
        return false;
    }
    if e.orig > now {
        // origin stamp ahead of our clock (clock error): age_ok holds
        return true;
    }
    // here e.orig <= now and sigma_hat <= delta: neither subtraction underflows
    now - e.orig <= delta - sigma_hat
}

} // verus!
