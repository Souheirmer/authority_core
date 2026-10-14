//! A witness: properties (A2-A6).
use vstd::prelude::*;
use crate::update_spec::*;

verus! {

/// A2 stripped signature: under the hybrid policy, an image missing either
/// signature is rejected.
pub proof fn lemma_a2_stripped_rejected(p: Policy, t: Transcript, m: u64, sig_c: bool, sig_pq: bool)
    requires
        p.mode == Mode::Hybrid,
        !sig_c || !sig_pq,
    ensures
        !admit_spec(p, t, m, sig_c, sig_pq),
{
}

/// A3 retired key: an image whose required key is retired is rejected.
pub proof fn lemma_a3_retired_key_rejected(p: Policy, t: Transcript, m: u64, sig_c: bool, sig_pq: bool)
    requires
        p.mode != Mode::PostQuantum,
        (t.key_c as int) < (KEYS as int),
        p.retired[t.key_c as int],
    ensures
        !admit_spec(p, t, m, sig_c, sig_pq),
{
}

/// A4 binding: a transcript for another image or another device class is rejected.
pub proof fn lemma_a4_binding(p: Policy, t: Transcript, m: u64, sig_c: bool, sig_pq: bool)
    requires
        t.digest != m || t.class != p.class,
    ensures
        !admit_spec(p, t, m, sig_c, sig_pq),
{
}

/// A5 migration only forward, never by a firmware key; an old-epoch
/// transcript is rejected after any accepted migration.
pub proof fn lemma_a5_forward_only(old: Policy, new: Policy, to: Mode, role: Role, ok: bool)
    requires
        migrate_post(old, new, to, role, ok),
    ensures
        mode_rank(new.mode) >= mode_rank(old.mode),
        new.epoch >= old.epoch,
        role == Role::Firmware ==> new == old,
{
}

pub proof fn lemma_a5_old_epoch_rejected(old: Policy, new: Policy, to: Mode, role: Role, t: Transcript, m: u64, sig_c: bool, sig_pq: bool)
    requires
        migrate_post(old, new, to, role, true),
        t.epoch == old.epoch,
    ensures
        !admit_spec(new, t, m, sig_c, sig_pq),
{
}

/// A6 committed floor never decreases; an image below it is rejected.
pub proof fn lemma_a6_floor(old: Policy, new: Policy, counter: u64, t: Transcript, m: u64, sig_c: bool, sig_pq: bool)
    requires
        commit_post(old, new, counter),
        t.counter < counter,
    ensures
        new.floor >= old.floor,
        !admit_spec(new, t, m, sig_c, sig_pq),
{
}

} // verus!
