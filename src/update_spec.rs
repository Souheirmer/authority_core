//! Spec of the A witness (firmware-update admission and policy migration).
//! A small feasibility witness for the update-authorisation proposal, not the
//! proposed component: abstract transcript fields, signature results and roles
//! given as trusted inputs. Human approval required before merge.
use vstd::prelude::*;

verus! {

pub const KEYS: usize = 8;

/// Signature policy: classical only, hybrid (both required), post-quantum only.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Classical,
    Hybrid,
    PostQuantum,
}

pub open spec fn mode_rank(m: Mode) -> int {
    match m {
        Mode::Classical => 0,
        Mode::Hybrid => 1,
        Mode::PostQuantum => 2,
    }
}

/// Device-side update policy: device class, policy epoch, signature mode,
/// security floor (minimum counter) and retired signing keys.
pub struct Policy {
    pub class: u32,
    pub epoch: u64,
    pub mode: Mode,
    pub floor: u64,
    pub retired: Seq<bool>,
}

/// The signed transcript of an image (abstract fields). ASSUMPTION: `digest`
/// stands for a collision-resistant digest of the image; computing it and
/// its collision resistance are not proved here.
#[derive(Clone, Copy)]
pub struct Transcript {
    pub class: u32,
    pub digest: u64,
    pub counter: u64,
    pub epoch: u64,
    pub key_c: u8,
    pub key_pq: u8,
}

/// ASSUMPTION: `sig_c` / `sig_pq` are the results of trusted verification of
/// the classical / post-quantum signature over THIS transcript under keys
/// `key_c` / `key_pq`; no cryptography is done in this witness.
pub open spec fn key_live(p: Policy, k: u8) -> bool {
    (k as int) < (KEYS as int) && !p.retired[k as int]
}

pub open spec fn sigs_ok(p: Policy, t: Transcript, sig_c: bool, sig_pq: bool) -> bool {
    match p.mode {
        Mode::Classical => sig_c && key_live(p, t.key_c),
        Mode::Hybrid => sig_c && key_live(p, t.key_c) && sig_pq && key_live(p, t.key_pq),
        Mode::PostQuantum => sig_pq && key_live(p, t.key_pq),
    }
}

/// A1 admission: same device class, transcript bound to the measured image
/// digest, current policy epoch, counter at or above the floor, and every
/// signature the mode requires valid under a non-retired key.
pub open spec fn admit_spec(p: Policy, t: Transcript, measured: u64, sig_c: bool, sig_pq: bool) -> bool {
    &&& t.class == p.class
    &&& t.digest == measured
    &&& t.epoch == p.epoch
    &&& t.counter >= p.floor
    &&& sigs_ok(p, t, sig_c, sig_pq)
}

/// Who signed a policy-change request. ASSUMPTION: the role is established by
/// trusted verification of the request's signature against role-separated keys.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Role {
    PolicyAuthority,
    Firmware,
}

/// A5 migration: accepted iff requested by the policy authority and strictly
/// forward (classical -> hybrid -> post-quantum); an accepted change advances
/// the epoch; a refused one changes nothing.
pub open spec fn migrate_post(old: Policy, new: Policy, to: Mode, role: Role, ok: bool) -> bool {
    &&& ok == (role == Role::PolicyAuthority && mode_rank(to) > mode_rank(old.mode) && old.epoch < u64::MAX)
    &&& ok ==> (new.mode == to && new.epoch == old.epoch + 1 && new.class == old.class
                && new.floor == old.floor && new.retired == old.retired)
    &&& !ok ==> new == old
}

/// A3 retirement: only the policy authority retires a key; retired keys stay
/// retired.
pub open spec fn retire_post(old: Policy, new: Policy, k: int, role: Role, ok: bool) -> bool {
    &&& ok == (role == Role::PolicyAuthority && 0 <= k < KEYS as int)
    &&& ok ==> (new.retired == old.retired.update(k, true) && new.class == old.class
                && new.epoch == old.epoch && new.mode == old.mode && new.floor == old.floor)
    &&& !ok ==> new == old
}

/// A6 committed floor: after an admitted image is committed, the floor is
/// max(floor, counter); it never decreases.
pub open spec fn commit_post(old: Policy, new: Policy, counter: u64) -> bool {
    &&& new.floor == (if counter > old.floor { counter } else { old.floor })
    &&& new.class == old.class && new.epoch == old.epoch && new.mode == old.mode
    &&& new.retired == old.retired
}

} // verus!
