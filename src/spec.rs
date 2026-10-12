//! Specification of `authority_core` (rule A8, the "origin-timed lease").
//!
//! This file is the human-reviewed contract. Everything a reader must trust is
//! here: the data model, the spec functions, and the statements of properties
//! P1-P5. The implementation files (decode.rs, cache.rs, decide.rs) and the
//! proof file (lemmas.rs) must establish these statements; the verifier, not a
//! reader, checks that they do.
//!
//! Conventions: all spec arithmetic is over mathematical `int`/`nat`, so
//! nothing in this file can overflow or underflow. Executable code is checked
//! by Verus for overflow, underflow and out-of-bounds indexing separately.

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Number of device slots in the decision point's cache.
pub const N: usize = 64;

/// Size of a wire notification in bytes: 1 status + 4 device + 8 ver + 8 orig.
pub const MSG_LEN: usize = 21;

// ---------------------------------------------------------------------------
// Data model
// ---------------------------------------------------------------------------

/// Status of a cache slot. `Unknown` only ever denotes an empty slot; it cannot
/// be produced by decoding a notification.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Status {
    Unknown,
    Enrolled,
    Revoked,
}

/// One cache slot.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Entry {
    pub status: Status,
    /// Registry version of this device's record.
    pub ver: u64,
    /// Registry origin time (ticks) at which it observed this state.
    pub orig: u64,
}

/// A decoded registry notification.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub struct Notification {
    pub device: u32,
    pub status: Status,
    pub ver: u64,
    pub orig: u64,
}

/// The value of an empty slot.
pub open spec fn empty_entry() -> Entry {
    Entry { status: Status::Unknown, ver: 0, orig: 0 }
}

/// A notification is valid iff it addresses a slot that exists and carries a
/// real status (Enrolled or Revoked). Exactly these are representable on the wire.
pub open spec fn valid_notification(m: Notification) -> bool {
    &&& (m.device as int) < (N as int)
    &&& (m.status == Status::Enrolled || m.status == Status::Revoked)
}

/// Cache well-formedness: exactly N slots.
pub open spec fn cache_wf(c: Seq<Entry>) -> bool {
    c.len() == N as int
}

// ---------------------------------------------------------------------------
// Wire format (big-endian)
// ---------------------------------------------------------------------------

/// Big-endian value of a byte sequence: be_int([b0, ..., bk]) = b0*256^k + ... + bk.
pub open spec fn be_int(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        be_int(s.drop_last()) * 256 + s.last() as nat
    }
}

/// The `n` low-order bytes of `x` in big-endian order (inverse of `be_int`
/// when x < 256^n).
pub open spec fn be_bytes(x: nat, n: nat) -> Seq<u8>
    decreases n,
{
    if n == 0 {
        Seq::empty()
    } else {
        be_bytes(x / 256, (n - 1) as nat).push((x % 256) as u8)
    }
}

/// Field views of a 21-byte message.
pub open spec fn status_byte(s: Seq<u8>) -> u8 { s[0] }
pub open spec fn device_field(s: Seq<u8>) -> nat { be_int(s.subrange(1, 5)) }
pub open spec fn ver_field(s: Seq<u8>) -> nat { be_int(s.subrange(5, 13)) }
pub open spec fn orig_field(s: Seq<u8>) -> nat { be_int(s.subrange(13, 21)) }

/// Well-formed input: exactly 21 bytes, status byte 0 or 1, device id < N.
pub open spec fn well_formed(s: Seq<u8>) -> bool {
    &&& s.len() == MSG_LEN as int
    &&& (status_byte(s) == 0 || status_byte(s) == 1)
    &&& device_field(s) < N as nat
}

/// Status byte meaning: 0 = Revoked, 1 = Enrolled.
pub open spec fn status_of_byte(b: u8) -> Status {
    if b == 1 { Status::Enrolled } else { Status::Revoked }
}

pub open spec fn byte_of_status(st: Status) -> u8 {
    if st == Status::Enrolled { 1 } else { 0 }
}

/// Reference decoder.
pub open spec fn decode_spec(s: Seq<u8>) -> Option<Notification> {
    if well_formed(s) {
        Some(Notification {
            status: status_of_byte(status_byte(s)),
            device: device_field(s) as u32,
            ver: ver_field(s) as u64,
            orig: orig_field(s) as u64,
        })
    } else {
        None
    }
}

/// Reference encoder.
pub open spec fn encode_spec(m: Notification) -> Seq<u8> {
    seq![byte_of_status(m.status)]
        + be_bytes(m.device as nat, 4)
        + be_bytes(m.ver as nat, 8)
        + be_bytes(m.orig as nat, 8)
}

// ---------------------------------------------------------------------------
// Cache update (monotonic reads)
// ---------------------------------------------------------------------------

/// apply(m): overwrite slot m.device iff m.ver > its current ver; else no change.
pub open spec fn apply_spec(c: Seq<Entry>, m: Notification) -> Seq<Entry> {
    let i = m.device as int;
    if m.ver > c[i].ver {
        c.update(i, Entry { status: m.status, ver: m.ver, orig: m.orig })
    } else {
        c
    }
}

// ---------------------------------------------------------------------------
// Decision rule A8 (origin-timed lease)
// ---------------------------------------------------------------------------

/// age_ok: now - orig <= delta - sigma_hat, computed over int. If orig is ahead
/// of now (clock error), age_ok holds.
pub open spec fn age_ok(orig: u64, now: u64, delta: u64, sigma_hat: u64) -> bool {
    (orig as int) > (now as int)
        || (now as int) - (orig as int) <= (delta as int) - (sigma_hat as int)
}

/// Rule A8. The conjunct `sigma_hat <= delta` makes a misconfigured decision
/// point deny rather than rely on a precondition (deny by default).
pub open spec fn a8(e: Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool) -> bool {
    &&& e.status == Status::Enrolled
    &&& sigma_hat <= delta
    &&& age_ok(e.orig, now, delta, sigma_hat)
    &&& !critical
}

// ---------------------------------------------------------------------------
// Property statements. Each is proved in lemmas.rs or by the `ensures`
// clause of the named executable function.
// ---------------------------------------------------------------------------

// P1 (exec, decode.rs): `fn decode(bytes: &[u8]) -> (r: Option<Notification>)`
//      ensures decode_post(bytes@, r); total, no panic/overflow (checked by Verus).
pub open spec fn decode_post(s: Seq<u8>, r: Option<Notification>) -> bool {
    &&& r == decode_spec(s)
    &&& (r is Some <==> well_formed(s))
    &&& (r is Some ==> valid_notification(r->Some_0))
}

// P1 (spec round trip, lemmas.rs): decode(encode(m)) == Some(m) for valid m.
pub open spec fn p1_round_trip() -> bool {
    forall|m: Notification| valid_notification(m) ==> #[trigger] decode_spec(encode_spec(m)) == Some(m)
}

// P2 (exec, cache.rs): `fn apply(&mut self, m: &Notification)` requires
//      valid_notification(m), ensures apply_post(old@, self@, m).
pub open spec fn apply_post(old: Seq<Entry>, new: Seq<Entry>, m: Notification) -> bool {
    &&& new == apply_spec(old, m)
    &&& cache_wf(new)
    // every entry's ver is >= its old ver
    &&& forall|i: int| #![trigger new[i]] 0 <= i < N as int ==> new[i].ver >= old[i].ver
    // an entry changes iff it is the addressed one and m.ver > its old ver
    &&& forall|i: int| #![trigger new[i]] 0 <= i < N as int ==>
            (new[i] != old[i] <==> (i == m.device as int && m.ver > old[i].ver))
}

// P3 (exec, decide.rs): `fn allow(e: &Entry, now, delta, sigma_hat, critical) -> (b: bool)`
//      ensures allow_post(*e, now, delta, sigma_hat, critical, b); no overflow/underflow.
pub open spec fn allow_post(e: Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool, b: bool) -> bool {
    b == a8(e, now, delta, sigma_hat, critical)
}

// P3 (exec, cache.rs): `fn allow_device(&self, d: u32, now, delta, sigma_hat, critical) -> (b: bool)`
//      ensures allow_device_post(self@, d, now, delta, sigma_hat, critical, b);
//      out-of-range device ids deny.
pub open spec fn allow_device_post(
    c: Seq<Entry>, d: u32, now: u64, delta: u64, sigma_hat: u64, critical: bool, b: bool,
) -> bool {
    b == ((d as int) < (N as int) && a8(c[d as int], now, delta, sigma_hat, critical))
}

// P4 (lemmas.rs): deny by default: unknown slot, Revoked status, active
// critical event, or misconfiguration (sigma_hat > delta) always deny.
pub open spec fn p4_deny_by_default() -> bool {
    forall|e: Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool|
        (e.status == Status::Unknown || e.status == Status::Revoked || critical
            || sigma_hat > delta)
            ==> !#[trigger] a8(e, now, delta, sigma_hat, critical)
}

// P5 (lemmas.rs): arithmetic core of soundness. Times are ints, so when
// orig > now the term (now - orig) is negative and the hypothesis is the
// model's invariant read literally.
//   since_rev : ticks elapsed (true time) since the revocation of the device
//   sigma     : actual clock error between registry and decision point
/// One instance of P5.
pub open spec fn p5_instance(
    e: Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int,
) -> bool {
    (since_rev <= (now as int - e.orig as int) + sigma
        && a8(e, now, delta, sigma_hat, critical)
        && sigma <= sigma_hat as int)
        ==> since_rev <= delta as int
}

pub open spec fn p5_soundness_core() -> bool {
    forall|e: Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int|
        #[trigger] p5_instance(e, now, delta, sigma_hat, critical, since_rev, sigma)
}

} // verus!
