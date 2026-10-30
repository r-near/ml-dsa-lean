//! decode_roundtrip: Sign with an arbitrary sk byte string of exactly sk_len bytes (skDecode, Algorithm 25, then
//! Sign). Our side must never panic. Upstream's decoder is documented as unvalidated ("can panic if keys are malformed"),
//! so a panic in upstream's decoder is tolerated when the sk is out of range, i.e. some s1/s2 coefficient field decodes
//! outside [-η, η] (the only constraint skDecode's BitUnpack leaves open; t0 fields cover all 13-bit values). In every
//! other case upstream's signature (or its exhaustion of the rejection loop, a panic) must match ours byte for byte,
//! including "ours returned None" (out-of-range sk too, whenever upstream does not panic).
//!
//! Input format: b0 parameter set (mod 3), b1 flags (bit0 deterministic rnd, bit1 take the sk from the seed's keygen
//! and apply the byte edits below instead of reading it), b2 ctx selector (as in sign_diff), then
//!   if bit1: 32 bytes ξ, u8 edit count (mod 33), edits of 3 bytes [off lo, off hi, xor]
//!   else:    sk (sk_len bytes)
//!   32 bytes rnd, u16 ctx length + ctx, rest = message.
#![no_main]

use fz::*;
use libfuzzer_sys::fuzz_target;

/// True iff every s1 and s2 coefficient field of `sk` decodes into [-η, η].
fn sk_in_range(set: Set, sk: &[u8]) -> bool {
    let p = set.params();
    let (bits, eta) = (p.eta_bits, p.eta);
    let mut acc = 0u32;
    let mut nbits = 0;
    let mut o = 128;
    for _ in 0..(p.l + p.k) * 256 {
        while nbits < bits {
            acc |= (sk[o] as u32) << nbits;
            nbits += 8;
            o += 1;
        }
        if acc & ((1 << bits) - 1) > 2 * eta {
            return false;
        }
        acc >>= bits;
        nbits -= bits;
    }
    true
}

fuzz_target!(init: install_panic_hook(), |data: &[u8]| {
    let mut c = Cur::new(data);
    let set = Set::from_byte(c.u8());
    let (flags, ctx_sel) = (c.u8(), c.u8() & 7);
    let sk = if flags & 2 != 0 {
        let xi: [u8; 32] = c.take(32).try_into().unwrap();
        let (_, mut sk) = ours_keygen(set, &xi);
        for _ in 0..c.u8() % 33 {
            let off = c.u16() as usize % sk.len();
            sk[off] ^= c.u8();
        }
        sk
    } else {
        c.take(set.sk_len())
    };
    let mut rnd: [u8; 32] = c.take(32).try_into().unwrap();
    if flags & 1 != 0 {
        rnd = [0u8; 32];
    }
    let mut ctx = c.blob(1024);
    match ctx_sel {
        1 => ctx = Vec::new(),
        2 => ctx = pattern(255, 1),
        3 => ctx = pattern(256, 2),
        4 => ctx = pattern(254, 3),
        _ => {}
    }
    let mut msg = c.rest();
    msg.truncate(4096);
    assert_eq!(sk.len(), set.sk_len());

    // Ours: must not panic, on any sk.
    let ours = ours_sign(set, &sk, &msg, &ctx, &rnd);
    if ctx.len() > 255 {
        assert!(ours.is_none(), "{set:?}: signed with |ctx| = {}", ctx.len());
        return;
    }
    let mp = [ctx_prefix(&ctx), msg.clone()].concat();
    let ours_int = ours_sign_internal(set, &sk, &mp, &rnd);
    assert_eq!(ours, ours_int, "{set:?}: Sign vs Sign_internal(0‖|ctx|‖ctx‖m)");

    let valid = sk_in_range(set, &sk);
    let det_args = (flags & 1 != 0).then_some((&msg[..], &ctx[..]));
    match up_sign(set, &sk, &mp, &rnd, det_args) {
        Ok(up) => {
            assert_eq!(ours, up.internal, "{set:?}: Sign differs from upstream (sk in range: {valid}, ours signed: {})", ours.is_some());
            if let Some(det) = up.det {
                assert_eq!(ours, det, "{set:?}: Sign differs from upstream sign_deterministic (sk in range: {valid})");
            }
        }
        // Documented upstream behavior for unvalidated expanded keys; only unexpected for an in-range sk.
        Err(()) => assert!(!valid, "{set:?}: upstream panicked while decoding an in-range sk; ours signed: {}", ours.is_some()),
    }
});
