//! P1: total, overflow-free decoder for the 21-byte wire format.
use vstd::prelude::*;
use crate::spec::*;
use crate::lemmas::*;

verus! {

/// Reads `n <= 8` bytes at `off` as a big-endian integer.
fn read_be(b: &[u8], off: usize, n: usize) -> (r: u64)
    requires
        n <= 8,
        off + n <= b@.len(),
    ensures
        r as nat == be_int(b@.subrange(off as int, off + n)),
{
    let mut acc: u64 = 0;
    let mut i: usize = off;
    let _len = b.len(); // brings b@.len() <= usize::MAX into scope
    let end: usize = off + n;
    proof {
        assert(b@.subrange(off as int, off as int) =~= Seq::<u8>::empty());
        lemma_pow256_values();
    }
    while i < end
        invariant
            end == off + n,
            n <= 8,
            off <= i <= off + n,
            off + n <= b@.len(),
            acc as nat == be_int(b@.subrange(off as int, i as int)),
            (acc as nat) < pow256((i - off) as nat),
            pow256(7) == 0x100000000000000,
        decreases end - i,
    {
        proof {
            lemma_pow256_mono((i - off) as nat, 7);
        }
        let byte = b[i];
        proof {
            let k = (i - off) as nat;
            assert(acc * 256 + byte < 0x10000000000000000) by (nonlinear_arith)
                requires acc < pow256(k), pow256(k) <= 0x100000000000000, byte < 256;
            assert(acc * 256 + byte < pow256(k) * 256) by (nonlinear_arith)
                requires acc < pow256(k), byte < 256;
            lemma_be_int_snoc(b@, off as int, i as int);
        }
        acc = acc * 256 + byte as u64;
        i = i + 1;
    }
    acc
}

/// P1: decodes exactly the well-formed inputs; never panics or overflows.
pub fn decode(bytes: &[u8]) -> (r: Option<Notification>)
    ensures
        decode_post(bytes@, r),
{
    if bytes.len() != MSG_LEN {
        return None;
    }
    let sb = bytes[0];
    if sb > 1 {
        return None;
    }
    let dev = read_be(bytes, 1, 4);
    if dev >= N as u64 {
        return None;
    }
    let ver = read_be(bytes, 5, 8);
    let orig = read_be(bytes, 13, 8);
    let status = if sb == 1 { Status::Enrolled } else { Status::Revoked };
    Some(Notification { device: dev as u32, status, ver, orig })
}

} // verus!
