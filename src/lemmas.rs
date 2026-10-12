//! Proofs of the spec-level properties (P1 round trip, P4, P5) and helper lemmas.
use vstd::prelude::*;
use crate::spec::*;

verus! {

// ---------------------------------------------------------------------------
// Helpers (proof-only; not part of the trusted spec)
// ---------------------------------------------------------------------------

pub open spec fn pow256(n: nat) -> nat
    decreases n,
{
    if n == 0 { 1 } else { 256 * pow256((n - 1) as nat) }
}

pub proof fn lemma_pow256_values()
    ensures
        pow256(4) == 0x1_0000_0000,
        pow256(7) == 0x100000000000000,
        pow256(8) == 0x1_0000_0000_0000_0000,
{
    reveal_with_fuel(pow256, 9);
}

pub proof fn lemma_pow256_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow256(a) <= pow256(b),
    decreases b,
{
    if a < b {
        lemma_pow256_mono(a, (b - 1) as nat);
    }
}

/// Appending one byte to a big-endian prefix.
pub proof fn lemma_be_int_snoc(s: Seq<u8>, lo: int, i: int)
    requires
        0 <= lo <= i < s.len(),
    ensures
        be_int(s.subrange(lo, i + 1)) == be_int(s.subrange(lo, i)) * 256 + s[i] as nat,
{
    assert(s.subrange(lo, i + 1).drop_last() =~= s.subrange(lo, i));
}

pub proof fn lemma_be_bytes_len(x: nat, n: nat)
    ensures
        be_bytes(x, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_be_bytes_len(x / 256, (n - 1) as nat);
    }
}

/// be_int inverts be_bytes on in-range values.
pub proof fn lemma_be_round_trip(x: nat, n: nat)
    requires
        x < pow256(n),
    ensures
        be_int(be_bytes(x, n)) == x,
    decreases n,
{
    if n == 0 {
    } else {
        let p = pow256((n - 1) as nat);
        assert(x / 256 < p) by (nonlinear_arith)
            requires x < 256 * p;
        lemma_be_round_trip(x / 256, (n - 1) as nat);
        let rest = be_bytes(x / 256, (n - 1) as nat);
        assert(be_bytes(x, n).drop_last() =~= rest);
        assert((x / 256) * 256 + x % 256 == x) by (nonlinear_arith);
    }
}

// ---------------------------------------------------------------------------
// P1 (spec round trip)
// ---------------------------------------------------------------------------

pub proof fn lemma_p1_round_trip()
    ensures
        p1_round_trip(),
{
    assert forall|m: Notification| valid_notification(m) implies
        #[trigger] decode_spec(encode_spec(m)) == Some(m) by {
        lemma_pow256_values();
        let b4 = be_bytes(m.device as nat, 4);
        let bv = be_bytes(m.ver as nat, 8);
        let bo = be_bytes(m.orig as nat, 8);
        lemma_be_bytes_len(m.device as nat, 4);
        lemma_be_bytes_len(m.ver as nat, 8);
        lemma_be_bytes_len(m.orig as nat, 8);
        lemma_be_round_trip(m.device as nat, 4);
        lemma_be_round_trip(m.ver as nat, 8);
        lemma_be_round_trip(m.orig as nat, 8);
        let s = encode_spec(m);
        assert(s.len() == 21);
        assert(s.subrange(1, 5) =~= b4);
        assert(s.subrange(5, 13) =~= bv);
        assert(s.subrange(13, 21) =~= bo);
        assert(status_byte(s) == byte_of_status(m.status));
        assert(well_formed(s));
    }
}

// ---------------------------------------------------------------------------
// P4 (deny by default)
// ---------------------------------------------------------------------------

pub proof fn lemma_p4_deny_by_default()
    ensures
        p4_deny_by_default(),
{
}

// ---------------------------------------------------------------------------
// P5 (arithmetic core of soundness)
// ---------------------------------------------------------------------------

pub proof fn lemma_p5_soundness_core()
    ensures
        p5_soundness_core(),
{
    assert forall|e: Entry, now: u64, delta: u64, sigma_hat: u64, critical: bool, since_rev: int, sigma: int|
        #[trigger] p5_instance(e, now, delta, sigma_hat, critical, since_rev, sigma) by {
        // Case orig > now: now - orig < 0, so since_rev < sigma <= sigma_hat <= delta.
        // Case orig <= now: since_rev <= (delta - sigma_hat) + sigma <= delta.
    }
}

} // verus!
