//! P2 (apply) and the cache-level part of P3 (allow_device).
use vstd::prelude::*;
use crate::spec::*;
use crate::decide::allow;
use crate::decode::decode;

verus! {

/// Bounded cache of N device entries.
pub struct Cache {
    pub entries: [Entry; N],
}

impl View for Cache {
    type V = Seq<Entry>;

    open spec fn view(&self) -> Seq<Entry> {
        self.entries@
    }
}

impl Cache {
    /// All slots empty: (Unknown, 0, 0).
    pub fn new() -> (c: Self)
        ensures
            cache_wf(c@),
            forall|i: int| 0 <= i < N as int ==> #[trigger] c@[i] == empty_entry(),
    {
        Cache { entries: [Entry { status: Status::Unknown, ver: 0, orig: 0 }; N] }
    }

    /// P2: monotonic update.
    pub fn apply(&mut self, m: &Notification)
        requires
            valid_notification(*m),
        ensures
            apply_post(old(self)@, final(self)@, *m),
    {
        let i = m.device as usize;
        if m.ver > self.entries[i].ver {
            self.entries[i] = Entry { status: m.status, ver: m.ver, orig: m.orig };
        }
    }

    /// P3 at cache level: out-of-range device ids deny.
    pub fn allow_device(&self, d: u32, now: u64, delta: u64, sigma_hat: u64, critical: bool) -> (b: bool)
        ensures
            allow_device_post(self@, d, now, delta, sigma_hat, critical, b),
    {
        if (d as usize) < N {
            allow(&self.entries[d as usize], now, delta, sigma_hat, critical)
        } else {
            false
        }
    }

    /// Convenience composition (not one of P1-P5): decode, check the trusted
    /// signature, then apply. On any failure the cache is unchanged.
    pub fn handle(&mut self, bytes: &[u8], sig: &[u8]) -> (accepted: bool)
        ensures
            accepted ==> decode_spec(bytes@) is Some
                && final(self)@ == apply_spec(old(self)@, decode_spec(bytes@)->Some_0),
            !accepted ==> final(self)@ == old(self)@,
    {
        match decode(bytes) {
            Some(m) => {
                if crate::signature_ok(bytes, sig) {
                    self.apply(&m);
                    true
                } else {
                    false
                }
            },
            None => false,
        }
    }
}

} // verus!
