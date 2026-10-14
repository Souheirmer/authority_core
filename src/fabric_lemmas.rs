//! B witness: properties (B1-B4).
use vstd::prelude::*;
use crate::fabric_spec::*;

verus! {

/// B1 delayed or retried installation cannot extend the origin deadline:
/// whenever the installed rule forwards, now <= the deadline AS ISSUED,
/// whatever the installation time.
pub proof fn lemma_b1_no_extension(old: SwitchState, new: SwitchState, s: int, r: Rule, t_install: u64, ok: bool, now: u64)
    requires
        install_post(old, new, s, r, t_install, ok),
        ok,
        forward_spec(new, s, now),
    ensures
        now <= r.deadline,
{
}

/// B1': a rule arriving after its origin deadline never activates.
pub proof fn lemma_b1_late_rule_refused(old: SwitchState, new: SwitchState, s: int, r: Rule, t_install: u64, ok: bool)
    requires
        install_post(old, new, s, r, t_install, ok),
        t_install > r.deadline,
    ensures
        !ok,
        new.slots[s] == old.slots[s],
{
}

/// B2 controller loss does not renew: with no new installation, a slot's
/// forwarding at a later time implies forwarding was allowed by the same
/// deadline; time passing alone can only close a rule, never extend it.
pub proof fn lemma_b2_time_only_closes(st: SwitchState, s: int, t1: u64, t2: u64)
    requires
        t1 <= t2,
        forward_spec(st, s, t2),
    ensures
        forward_spec(st, s, t1),
        t2 <= st.slots[s].rule.deadline,
{
}

/// B3 reboot and clock loss close every rule installed before them.
pub proof fn lemma_b3_reboot_closes(old: SwitchState, new: SwitchState, s: int, now: u64)
    requires
        reboot_post(old, new),
        0 <= s < SLOTS as int,
        old.slots[s].rule.boot <= old.boot,
    ensures
        !forward_spec(new, s, now),
{
}

pub proof fn lemma_b3_clock_loss_closes(old: SwitchState, new: SwitchState, s: int, now: u64)
    requires
        clock_lost_post(old, new),
    ensures
        !forward_spec(new, s, now),
{
}

/// B4 bounded withdrawal (arithmetic core). Issuer contract: a rule for
/// authority withdrawn at real time t_w carries deadline <= t_w + delta - sigma_hat
/// (issued no later than t_w with lifetime at most delta - sigma_hat). Clock
/// contract: the switch clock lags real time by at most sigma <= sigma_hat
/// (now_sw >= now_real - sigma). Then after real time t_w + delta the rule
/// does not forward. Both contracts are assumptions, not proved here.
pub proof fn lemma_b4_bounded_withdrawal(st: SwitchState, s: int, t_w: int, delta: int, sigma: int, sigma_hat: int, now_real: int, now_sw: u64)
    requires
        0 <= s < SLOTS as int,
        st.slots[s].rule.deadline as int <= t_w + delta - sigma_hat,
        0 <= sigma <= sigma_hat,
        now_sw as int >= now_real - sigma,
        now_real > t_w + delta,
    ensures
        !forward_spec(st, s, now_sw),
{
}

} // verus!
