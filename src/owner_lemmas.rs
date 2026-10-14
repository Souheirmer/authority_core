//! C witness: properties (C1-C5).
use vstd::prelude::*;
use crate::owner_spec::*;

verus! {

/// C1 a voucher for another device, an unverified chain, or a chain verified
/// against any instance other than the current one is refused.
pub proof fn lemma_c1_refusals(old: OwnerState, new: OwnerState, x: Transfer, ok: bool)
    requires
        begin_post(old, new, x, ok),
        x.device != old.device || !x.chain_ok || x.instance != old.instance,
    ensures
        !ok,
        new == old,
{
}

/// C2 staged credentials are not authoritative: staging never changes the
/// active owner.
pub proof fn lemma_c2_staged_not_authoritative(old: OwnerState, new: OwnerState, x: Transfer, ok: bool)
    requires
        begin_post(old, new, x, ok),
    ensures
        new.owner == old.owner,
{
}

/// C4 no reactivation: after a commit, a transfer bound to the retired
/// instance is refused, also after any number of modelled restarts.
pub proof fn lemma_c4_retired_instance_refused(s0: OwnerState, s1: OwnerState, s2: OwnerState, s3: OwnerState, x: Transfer, ok: bool)
    requires
        commit_post(s0, s1, true),
        restart_post(s1, s2),
        begin_post(s2, s3, x, ok),
        x.instance == s0.instance,
    ensures
        !ok,
        s3.owner == s1.owner,
{
}

/// C5 power cut before commit: the modelled restart returns to the prior
/// owner and instance, with nothing staged (under the persisted-record
/// assumption of restart_post).
pub proof fn lemma_c5_cut_before_commit(s0: OwnerState, s1: OwnerState, s2: OwnerState, x: Transfer)
    requires
        begin_post(s0, s1, x, true),
        restart_post(s1, s2),
    ensures
        s2.owner == s0.owner,
        s2.instance == s0.instance,
        !s2.staged,
{
}

/// C3' after a commit the instance has strictly increased, so the generation
/// never goes back under commit and restart.
pub proof fn lemma_c3_instance_increases(s0: OwnerState, s1: OwnerState, s2: OwnerState)
    requires
        commit_post(s0, s1, true),
        restart_post(s1, s2),
    ensures
        s2.instance > s0.instance,
{
}

} // verus!
