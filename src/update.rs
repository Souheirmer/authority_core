//! A witness: executable admission, migration, retirement and floor commit.
use vstd::prelude::*;
use crate::update_spec::*;

verus! {

pub struct UpdatePolicy {
    pub class: u32,
    pub epoch: u64,
    pub mode: Mode,
    pub floor: u64,
    pub retired: [bool; KEYS],
}

impl UpdatePolicy {
    pub open spec fn p(&self) -> Policy {
        Policy { class: self.class, epoch: self.epoch, mode: self.mode, floor: self.floor, retired: self.retired@ }
    }

    pub fn new(class: u32) -> (u: Self)
        ensures
            u.p().class == class, u.p().epoch == 1, u.p().mode == Mode::Classical, u.p().floor == 0,
            u.p().retired.len() == KEYS,
            forall|k: int| 0 <= k < KEYS as int ==> !(#[trigger] u.p().retired[k]),
    {
        UpdatePolicy { class, epoch: 1, mode: Mode::Classical, floor: 0, retired: [false; KEYS] }
    }

    fn key_live(&self, k: u8) -> (b: bool)
        ensures
            b == key_live(self.p(), k),
    {
        (k as usize) < KEYS && !self.retired[k as usize]
    }

    /// A1: admitted iff admit_spec.
    pub fn check_admission(&self, t: &Transcript, measured: u64, sig_c: bool, sig_pq: bool) -> (b: bool)
        ensures
            b == admit_spec(self.p(), *t, measured, sig_c, sig_pq),
    {
        if t.class != self.class || t.digest != measured || t.epoch != self.epoch || t.counter < self.floor {
            return false;
        }
        match self.mode {
            Mode::Classical => sig_c && self.key_live(t.key_c),
            Mode::Hybrid => sig_c && self.key_live(t.key_c) && sig_pq && self.key_live(t.key_pq),
            Mode::PostQuantum => sig_pq && self.key_live(t.key_pq),
        }
    }

    pub fn migrate(&mut self, to: Mode, role: Role) -> (ok: bool)
        ensures
            migrate_post(old(self).p(), final(self).p(), to, role, ok),
    {
        let rank_old: u8 = match self.mode { Mode::Classical => 0, Mode::Hybrid => 1, Mode::PostQuantum => 2 };
        let rank_to: u8 = match to { Mode::Classical => 0, Mode::Hybrid => 1, Mode::PostQuantum => 2 };
        let is_auth = match role { Role::PolicyAuthority => true, Role::Firmware => false };
        if is_auth && rank_to > rank_old && self.epoch < u64::MAX {
            self.mode = to;
            self.epoch = self.epoch + 1;
            true
        } else {
            false
        }
    }

    pub fn retire(&mut self, k: u8, role: Role) -> (ok: bool)
        ensures
            retire_post(old(self).p(), final(self).p(), k as int, role, ok),
    {
        let is_auth = match role { Role::PolicyAuthority => true, Role::Firmware => false };
        if is_auth && (k as usize) < KEYS {
            self.retired[k as usize] = true;
            true
        } else {
            false
        }
    }

    pub fn commit(&mut self, counter: u64)
        ensures
            commit_post(old(self).p(), final(self).p(), counter),
    {
        if counter > self.floor {
            self.floor = counter;
        }
    }
}

} // verus!
