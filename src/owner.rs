//! C witness: executable begin, commit and restart.
use vstd::prelude::*;
use crate::owner_spec::*;

verus! {

pub struct Device {
    pub device: u64,
    pub instance: u64,
    pub owner: u64,
    pub staged: bool,
    pub staged_owner: u64,
    pub staged_from: u64,
}

impl Device {
    pub open spec fn s(&self) -> OwnerState {
        OwnerState { device: self.device, instance: self.instance, owner: self.owner,
                     staged: self.staged, staged_owner: self.staged_owner, staged_from: self.staged_from }
    }

    pub fn new(device: u64, owner: u64) -> (d: Self)
        ensures
            d.s().device == device, d.s().owner == owner, d.s().instance == 1, !d.s().staged,
    {
        Device { device, instance: 1, owner, staged: false, staged_owner: 0, staged_from: 0 }
    }

    pub fn begin(&mut self, x: &Transfer) -> (ok: bool)
        ensures
            begin_post(old(self).s(), final(self).s(), *x, ok),
    {
        if x.device == self.device && x.chain_ok && x.instance == self.instance {
            self.staged = true;
            self.staged_owner = x.new_owner;
            self.staged_from = self.instance;
            true
        } else {
            false
        }
    }

    pub fn commit(&mut self) -> (ok: bool)
        ensures
            commit_post(old(self).s(), final(self).s(), ok),
    {
        if self.staged && self.staged_from == self.instance && self.instance < u64::MAX {
            self.owner = self.staged_owner;
            self.instance = self.instance + 1;
            self.staged = false;
            true
        } else {
            false
        }
    }

    pub fn restart(&mut self)
        ensures
            restart_post(old(self).s(), final(self).s()),
    {
        self.staged = false;
    }
}

} // verus!
