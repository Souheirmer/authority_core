//! B witness: executable switch (install, forward, reboot, clock loss).
use vstd::prelude::*;
use crate::fabric_spec::*;

verus! {

pub struct Switch {
    pub slots: [Slot; SLOTS],
    pub boot: u64,
    pub clock_ok: bool,
}

impl Switch {
    pub open spec fn st(&self) -> SwitchState {
        SwitchState { slots: self.slots@, boot: self.boot, clock_ok: self.clock_ok }
    }

    /// Empty switch at boot epoch 1 with the clock contract holding.
    pub fn new() -> (sw: Self)
        ensures
            sw.st().boot == 1,
            sw.st().clock_ok,
            sw.st().slots.len() == SLOTS,
            forall|i: int| 0 <= i < SLOTS as int ==> !(#[trigger] sw.st().slots[i]).present,
    {
        Switch { slots: [Slot { present: false, rule: Rule { boot: 0, deadline: 0 } }; SLOTS], boot: 1, clock_ok: true }
    }

    pub fn forward(&self, s: u32, now: u64) -> (b: bool)
        ensures
            b == forward_spec(self.st(), s as int, now),
    {
        if s as usize >= SLOTS {
            return false;
        }
        let sl = self.slots[s as usize];
        self.clock_ok && sl.present && sl.rule.boot == self.boot && now <= sl.rule.deadline
    }

    pub fn install(&mut self, s: u32, r: Rule, now: u64) -> (ok: bool)
        requires
            (s as int) < (SLOTS as int),
        ensures
            install_post(old(self).st(), final(self).st(), s as int, r, now, ok),
    {
        if self.clock_ok && r.boot == self.boot && now <= r.deadline {
            self.slots[s as usize] = Slot { present: true, rule: r };
            true
        } else {
            false
        }
    }

    pub fn reboot(&mut self)
        requires
            old(self).boot < u64::MAX,
        ensures
            reboot_post(old(self).st(), final(self).st()),
    {
        self.boot = self.boot + 1;
    }

    pub fn clock_lost(&mut self)
        ensures
            clock_lost_post(old(self).st(), final(self).st()),
    {
        self.clock_ok = false;
    }
}

} // verus!
