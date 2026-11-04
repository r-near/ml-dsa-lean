//! sign_diff: KeyGen (Algorithm 1), Sign (2) and Sign_internal (7) of ml-dsa-lean against upstream RustCrypto
//! `ml-dsa`, byte for byte, plus Verify on the result (ours and upstream's must both accept; a changed message must
//! be rejected by both).
//!
//! Input format (little endian; missing bytes read as zero):
//!   b0 parameter set (mod 3)   b1 flags: bit0 deterministic (rnd = 0^32, and compare with upstream sign_deterministic)
//!   b2 ctx selector (mod 8): 0 explicit, 1 empty, 2 255 bytes, 3 256 bytes, 4 254 bytes, 5-7 explicit
//!   32 bytes ξ      32 bytes rnd (always present, ignored when deterministic)      u16 ctx length + ctx
//!   u16 split point of M′      rest = message (at most 16 KiB).
#![no_main]

use fz::*;
use libfuzzer_sys::fuzz_target;

fuzz_target!(init: install_panic_hook(), |data: &[u8]| {
    let mut c = Cur::new(data);
    let set = Set::from_byte(c.u8());
    let (flags, ctx_sel) = (c.u8(), c.u8() & 7);
    let xi: [u8; 32] = c.take(32).try_into().unwrap();
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
    let split_raw = c.u16() as usize;
    let mut msg = c.rest();
    msg.truncate(16384);

    // Upstream: one key derivation; Sign_internal on the raw message (as M′) and on 0 ‖ |ctx| ‖ ctx ‖ m.
    let mp = if ctx.len() <= 255 { [ctx_prefix(&ctx), msg.clone()].concat() } else { Vec::new() };
    let det_args = (flags & 1 != 0).then_some((&msg[..], &ctx[..]));
    let up = up_all(set, &xi, &[&msg, &mp], &rnd, det_args);

    // Algorithm 1: pk and sk bytes.
    let (pk, sk) = ours_keygen(set, &xi);
    assert_eq!(pk, up.pk, "{set:?}: keygen pk differs");
    assert_eq!(sk, up.sk, "{set:?}: keygen sk differs");

    // Algorithm 7 on an arbitrary M′ (the message bytes, split arbitrarily between prefix and message).
    let split = split_raw % (msg.len() + 1);
    let ours_int = ours_sign_internal(set, &sk, &msg, &rnd);
    let ours_int_split = ours_sign_split(set, &sk, &msg[..split], &msg[split..], &rnd);
    assert_eq!(ours_int, ours_int_split, "{set:?}: M′ split changed Sign_internal");
    assert_eq!(ours_int, up.internals[0], "{set:?}: Sign_internal differs from upstream");
    if let Some(sig) = &ours_int {
        assert!(ours_verify_internal_api(set, &pk, &msg, sig), "{set:?}: own Sign_internal output rejected");
    }

    // Algorithm 2 / 3 with the context string.
    let ours = ours_sign(set, &sk, &msg, &ctx, &rnd);
    if ctx.len() > 255 {
        assert!(ours.is_none(), "{set:?}: signed with |ctx| = {}", ctx.len());
        if let Some(Some(_)) = up.det {
            panic!("{set:?}: upstream signs with |ctx| = {}", ctx.len());
        }
        return;
    }
    assert_eq!(ours, up.internals[1], "{set:?}: Sign differs from upstream (|ctx| = {}, |m| = {})", ctx.len(), msg.len());
    if let Some(det) = up.det {
        assert_eq!(ours, det, "{set:?}: Sign differs from upstream sign_deterministic");
    }
    let sig = ours.expect("signing budget exhausted for a valid key");

    assert!(ours_verify(set, &pk, &msg, &ctx, &sig), "{set:?}: own signature rejected");
    let (up_int, up_ext) = up_verify_both(set, &pk, &sig, &mp, &msg, &ctx);
    assert!(up_int && up_ext, "{set:?}: upstream rejects our signature ({up_int}, {up_ext})");

    // Negative: a different message must be rejected by both.
    let mut bad = msg.clone();
    if bad.is_empty() {
        bad.push(split_raw as u8);
    } else {
        let i = split_raw % bad.len();
        bad[i] ^= 1 << (split_raw >> 8 & 7);
    }
    let bad_mp = [ctx_prefix(&ctx), bad.clone()].concat();
    assert!(!ours_verify(set, &pk, &bad, &ctx, &sig), "{set:?}: accepted a signature on a different message");
    let (b_int, b_ext) = up_verify_both(set, &pk, &sig, &bad_mp, &bad, &ctx);
    assert!(!b_int && !b_ext, "{set:?}: upstream accepted a different message");
});
