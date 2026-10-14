//! Spec of the C witness (device-side ownership transfer).
//! A small feasibility witness for the FDO ownership proposal, not the
//! proposed component: abstract identifiers, chain verification given as a
//! trusted input, and an abstract persisted record. Human approval required
//! before merge.
use vstd::prelude::*;

verus! {

/// Device ownership state. `instance` is the current onboarding instance
/// (generation); every lower instance is retired. `owner` is the active
/// owner credential (abstract id). `staged` / `staged_owner` / `staged_from`
/// describe a transfer in progress, never authoritative before commit.
pub struct OwnerState {
    pub device: u64,
    pub instance: u64,
    pub owner: u64,
    pub staged: bool,
    pub staged_owner: u64,
    pub staged_from: u64,
}

/// A transfer request. ASSUMPTION: `chain_ok` is the result of trusted
/// verification of the voucher chain's signatures for `device`, ending at the
/// key that authenticates this session; no cryptography is done here.
#[derive(Clone, Copy)]
pub struct Transfer {
    pub device: u64,
    pub instance: u64,
    pub new_owner: u64,
    pub chain_ok: bool,
}

/// C1 begin: accepted iff for this device, chain verified, against the
/// CURRENT instance; staging never changes the active owner or instance.
pub open spec fn begin_post(old: OwnerState, new: OwnerState, x: Transfer, ok: bool) -> bool {
    &&& ok == (x.device == old.device && x.chain_ok && x.instance == old.instance)
    &&& ok ==> (new.staged && new.staged_owner == x.new_owner && new.staged_from == old.instance)
    &&& !ok ==> new == old
    &&& new.device == old.device && new.instance == old.instance && new.owner == old.owner
}

/// C3 commit: only a transfer staged against the current instance commits;
/// owner and instance change together (one modelled step), the staged
/// transfer is cleared.
pub open spec fn commit_post(old: OwnerState, new: OwnerState, ok: bool) -> bool {
    &&& ok == (old.staged && old.staged_from == old.instance && old.instance < u64::MAX)
    &&& ok ==> (new.owner == old.staged_owner && new.instance == old.instance + 1 && !new.staged
                && new.device == old.device)
    &&& !ok ==> new == old
}

/// C5 restart: recovery from the persisted record. ASSUMPTION: the persisted
/// record (device, instance, owner) survives the power cut intact and is never
/// rolled back; this witness does NOT prove physical storage, atomic writes or
/// anti-rollback. A transfer in progress is dropped.
pub open spec fn restart_post(old: OwnerState, new: OwnerState) -> bool {
    &&& new.device == old.device && new.instance == old.instance && new.owner == old.owner
    &&& !new.staged
}

} // verus!
