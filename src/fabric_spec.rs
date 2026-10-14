//! Spec of the B witness (switch-local rules with immutable origin deadlines).
//! A small feasibility witness for the "verified authority in control
//! networks" proposal, not the proposed component: one switch, a bounded
//! number of rule slots, no network or controller model. Human approval
//! required before merge (SPEC_CHANGES.md).
use vstd::prelude::*;

verus! {

pub const SLOTS: usize = 8;

/// A rule as issued by the policy authority: the switch boot epoch it is
/// labelled for and its ORIGIN deadline (set by the issuer, in the switch's
/// clock domain under the clock contract below). ASSUMPTION: rule contents
/// are trusted input in this witness; they are not authenticated here.
#[derive(Clone, Copy)]
pub struct Rule {
    pub boot: u64,
    pub deadline: u64,
}

#[derive(Clone, Copy)]
pub struct Slot {
    pub present: bool,
    pub rule: Rule,
}

/// Switch state: rule slots, current boot epoch, and whether the clock
/// contract currently holds.
pub struct SwitchState {
    pub slots: Seq<Slot>,
    pub boot: u64,
    pub clock_ok: bool,
}

/// Forwarding decision for slot s at local time now: a rule is present, the
/// clock contract holds, the rule is labelled for the current boot epoch, and
/// its origin deadline has not passed.
pub open spec fn forward_spec(st: SwitchState, s: int, now: u64) -> bool {
    &&& 0 <= s < SLOTS as int
    &&& st.clock_ok
    &&& st.slots[s].present
    &&& st.slots[s].rule.boot == st.boot
    &&& now <= st.slots[s].rule.deadline
}

/// B1 installation: accepted iff the clock contract holds, the rule is for
/// the current boot epoch and its origin deadline has not passed; an accepted
/// rule is stored EXACTLY as issued (the deadline is never recomputed from the
/// installation time); a refused install changes nothing.
pub open spec fn install_post(old: SwitchState, new: SwitchState, s: int, r: Rule, now: u64, ok: bool) -> bool {
    &&& ok == (old.clock_ok && r.boot == old.boot && now <= r.deadline)
    &&& new.boot == old.boot
    &&& new.clock_ok == old.clock_ok
    &&& new.slots.len() == old.slots.len()
    &&& forall|i: int| 0 <= i < old.slots.len() && i != s ==> #[trigger] new.slots[i] == old.slots[i]
    &&& ok ==> new.slots[s] == (Slot { present: true, rule: r })
    &&& !ok ==> new.slots[s] == old.slots[s]
}

/// B3 reboot: new boot epoch; rules labelled for an earlier epoch no longer forward.
pub open spec fn reboot_post(old: SwitchState, new: SwitchState) -> bool {
    &&& new.boot == old.boot + 1
    &&& new.clock_ok == old.clock_ok
    &&& new.slots == old.slots
}

/// B3 clock loss: the clock contract no longer holds; nothing forwards.
pub open spec fn clock_lost_post(old: SwitchState, new: SwitchState) -> bool {
    &&& new.boot == old.boot
    &&& !new.clock_ok
    &&& new.slots == old.slots
}

} // verus!
