use vstd::prelude::*;
use crate::spec::*;

verus! {

/// Mutant cache entry: also remembers the local clock at write time.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct RtEntry {
    pub status: Status,
    pub ver: u64,
    pub orig: u64,
    /// decision point's clock when this entry was written
    pub recv: u64,
}

/// Mutant rule: identical to a8 except the lease is timed from `recv`.
pub open spec fn rt_a8(e: RtEntry, now: u64, delta: u64, sigma_hat: u64, critical: bool) -> bool {
    &&& e.status == Status::Enrolled
    &&& sigma_hat <= delta
    &&& age_ok(e.recv, now, delta, sigma_hat)
    &&& !critical
}

/// Same monotonic update as apply_spec, but stamps the receipt time.
pub open spec fn rt_apply_spec(c: Seq<RtEntry>, m: Notification, now: u64) -> Seq<RtEntry> {
    let i = m.device as int;
    if m.ver > c[i].ver {
        c.update(i, RtEntry { status: m.status, ver: m.ver, orig: m.orig, recv: now })
    } else {
        c
    }
}

pub struct RtCache {
    pub entries: [RtEntry; N],
}

impl View for RtCache {
    type V = Seq<RtEntry>;

    open spec fn view(&self) -> Seq<RtEntry> {
        self.entries@
    }
}

impl RtCache {
    pub fn new() -> (c: Self)
        ensures
            c@.len() == N,
    {
        RtCache { entries: [RtEntry { status: Status::Unknown, ver: 0, orig: 0, recv: 0 }; N] }
    }

    pub fn apply(&mut self, m: &Notification, now: u64)
        requires
            valid_notification(*m),
        ensures
            final(self)@ == rt_apply_spec(old(self)@, *m, now),
    {
        let i = m.device as usize;
        if m.ver > self.entries[i].ver {
            self.entries[i] = RtEntry { status: m.status, ver: m.ver, orig: m.orig, recv: now };
        }
    }

    pub fn allow_device(&self, d: u32, now: u64, delta: u64, sigma_hat: u64, critical: bool) -> (b: bool)
        ensures
            b == ((d as int) < (N as int) && rt_a8(self@[d as int], now, delta, sigma_hat, critical)),
    {
        if (d as usize) >= N {
            return false;
        }
        let e = &self.entries[d as usize];
        let enrolled = match e.status {
            Status::Enrolled => true,
            _ => false,
        };
        if !enrolled || critical || sigma_hat > delta {
            return false;
        }
        if e.recv > now {
            return true;
        }
        now - e.recv <= delta - sigma_hat
    }
}

/// The P5 statement transplanted to the mutant: same hypothesis (the model's
/// invariant relates since_rev to the ORIGIN stamp), mutant decision rule.
pub open spec fn rt_p5_instance(
    e: RtEntry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int,
) -> bool {
    (since_rev <= (now as int - e.orig as int) + sigma
        && rt_a8(e, now, delta, sigma_hat, critical)
        && sigma <= sigma_hat as int)
        ==> since_rev <= delta as int
}

/// ATTEMPT (expected to FAIL): the P5-style lemma for the receipt-timed lease.
/// The body is left empty, exactly as for the origin-timed lemma that does
/// verify; no proof can succeed (see lemma_p5_receipt_timed_is_false).
pub proof fn lemma_p5_receipt_timed_attempt(
    e: RtEntry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int,
)
    requires
        since_rev <= (now as int - e.orig as int) + sigma,
        rt_a8(e, now, delta, sigma_hat, critical),
        sigma <= sigma_hat as int,
    ensures
        since_rev <= delta as int,
{
}

/// The negation, PROVED: there is a concrete instance satisfying every
/// hypothesis of the P5-style lemma whose conclusion is false. This is the
/// counterexample trace of tests/mutant_counterexample.rs at its final step:
/// delta = 100, sigma_hat = 10, sigma = 0; Enrolled(ver 1, orig 0) delivered
/// late at recv = 200; revocation at true time 10; now = 280; since_rev = 270.
pub proof fn lemma_p5_receipt_timed_is_false()
    ensures
        !(forall|e: RtEntry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int|
            #[trigger] rt_p5_instance(e, now, delta, sigma_hat, critical, since_rev, sigma)),
{
    let e = RtEntry { status: Status::Enrolled, ver: 1, orig: 0, recv: 200 };
    assert(!rt_p5_instance(e, 280, 100, 10, false, 270, 0));
}

} // verus!
