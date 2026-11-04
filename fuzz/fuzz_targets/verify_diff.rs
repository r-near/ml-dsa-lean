//! verify_diff: Verify / Verify_internal of ml-dsa-lean against upstream RustCrypto `ml-dsa` on arbitrary
//! pk, signature, message and context bytes. Our side must never panic and must give upstream's verdict.
//!
//! Input format (all multi-byte integers little endian; missing bytes read as zero):
//!   b0 parameter set (mod 3)      b1 base index (mod POOL_SIZE)      b2 flags
//!   b3 length adjustment          b4 ctx selector                    b5 second base index
//!   b6 edit count (mod 41)        edits: 5 bytes each [region, off lo, off hi, value, mode]
//!   u16 split point of M′ between prefix and message (mod |M′| + 1)
//!   u16 pk length, u16 sig length   (only read when the matching length adjustment is 3)
//!   then, per flag: pk (pk_len bytes), sig (sig_len bytes), u16-prefixed message, u16-prefixed context.
//! Flags: 0 pk explicit, 1 sig explicit, 2 message explicit, 3 context explicit (overrides the selector),
//! 4 pk taken from the second base, 5 sig taken from the second base.
//! Length adjustment: bits 0-1 for pk, 2-3 for sig: 0 none, 1 drop the last byte, 2 append a zero, 3 resize to the
//! explicit length. Context selector (mod 8): 0 base ctx, 1 empty, 2 255 bytes, 3 256 bytes, 4 254 bytes,
//! 5 base ctx plus one byte, 6-7 base ctx.
//! Edits: region (see `region_range`; bit 7 targets the message), mode even = xor value (bit flip if value is 0),
//! odd = overwrite with value.
#![no_main]

use fz::*;
use libfuzzer_sys::fuzz_target;

fn apply_edit(set: Set, buf: &mut [u8], region: u8, off: u16, val: u8, mode: u8) {
    let (lo, hi) = region_range(set, region, buf.len());
    if hi == lo {
        return;
    }
    let i = lo + off as usize % (hi - lo);
    if mode & 1 == 0 {
        buf[i] ^= if val == 0 { 1 << (mode >> 1 & 7) } else { val };
    } else {
        buf[i] = val;
    }
}

fn adjust(buf: &mut Vec<u8>, adj: u8, explicit_len: usize) {
    match adj & 3 {
        1 => {
            buf.pop();
        }
        2 => buf.push(0),
        3 => buf.resize(explicit_len, 0xA5),
        _ => {}
    }
}

fuzz_target!(init: install_panic_hook(), |data: &[u8]| {
    let mut c = Cur::new(data);
    let set = Set::from_byte(c.u8());
    let pool = pool(set);
    let base = &pool[c.u8() as usize % POOL_SIZE];
    let (b2, b3, ctx_sel, b5, nedits) = (c.u8(), c.u8(), c.u8() & 7, c.u8(), c.u8() % 41);
    let other = &pool[b5 as usize % POOL_SIZE];
    let edits: Vec<[u8; 5]> = (0..nedits).map(|_| [c.u8(), c.u8(), c.u8(), c.u8(), c.u8()]).collect();
    let split_raw = c.u16() as usize;
    let (pk_new, sig_new) = (c.u16() as usize % 8192, c.u16() as usize % 8192);

    let mut pk = if b2 & 16 != 0 { other.pk.clone() } else { base.pk.clone() };
    let mut sig = if b2 & 32 != 0 { other.sig.clone() } else { base.sig.clone() };
    let mut msg = base.msg.clone();
    let mut ctx = base.ctx.clone();
    if b2 & 1 != 0 {
        pk = c.take(set.pk_len());
    }
    if b2 & 2 != 0 {
        sig = c.take(set.sig_len());
    }
    if b2 & 4 != 0 {
        msg = c.blob(8192);
    }
    match ctx_sel {
        1 => ctx = Vec::new(),
        2 => ctx = pattern(255, 1),
        3 => ctx = pattern(256, 2),
        4 => ctx = pattern(254, 3),
        5 => ctx.push(0x5A),
        _ => {}
    }
    if b2 & 8 != 0 {
        ctx = c.blob(1024);
    }
    for e in &edits {
        let off = u16::from_le_bytes([e[1], e[2]]);
        if e[0] & 0x80 != 0 {
            apply_edit(set, &mut msg, 7, off, e[3], e[4]);
        } else if matches!(e[0] % 8, 5 | 6) {
            apply_edit(set, &mut pk, e[0], off, e[3], e[4]);
        } else {
            apply_edit(set, &mut sig, e[0], off, e[3], e[4]);
        }
    }
    adjust(&mut pk, b3, pk_new);
    adjust(&mut sig, b3 >> 2, sig_new);

    let pristine = b2 & 0x3F == 0 && nedits == 0 && b3 & 15 == 0 && matches!(ctx_sel, 0 | 6 | 7);

    // M′: Algorithm 2/3 steps 10/5 when |ctx| ≤ 255, otherwise an arbitrary string for Verify_internal.
    let mp: Vec<u8> = if ctx.len() <= 255 { [ctx_prefix(&ctx), msg.clone()].concat() } else { [ctx.clone(), msg.clone()].concat() };
    let split = split_raw % (mp.len() + 1);

    let (up_int, up_ext) = up_verify_both(set, &pk, &sig, &mp, &msg, &ctx);
    let our_int = ours_verify_internal(set, &pk, &mp[..split], &mp[split..], &sig);
    let our_int0 = ours_verify_internal(set, &pk, &[], &mp, &sig);
    assert_eq!(our_int, our_int0, "{set:?}: M′ split changed our verdict (split {split})");
    assert_eq!(our_int, up_int, "{set:?}: verify_internal disagrees: ours={our_int} upstream={up_int}");

    let exact = pk.len() == set.pk_len() && sig.len() == set.sig_len();
    if exact {
        let our_ext = ours_verify(set, &pk, &msg, &ctx, &sig);
        assert_eq!(our_ext, up_ext, "{set:?}: verify disagrees: ours={our_ext} upstream={up_ext} |ctx|={}", ctx.len());
        if ctx.len() <= 255 {
            assert_eq!(our_ext, our_int, "{set:?}: verify vs verify_internal(0‖|ctx|‖ctx‖m)");
            assert_eq!(our_ext, ours_verify_internal_api(set, &pk, &mp, &sig), "{set:?}: api verify_internal");
            assert_eq!(up_ext, up_int, "{set:?}: upstream verify vs verify_internal");
        } else {
            assert!(!our_ext, "{set:?}: accepted |ctx| = {}", ctx.len());
        }
        if pristine {
            assert!(our_ext, "{set:?}: valid signature rejected");
        }
    } else {
        assert!(!our_int, "{set:?}: wrong-length input accepted (pk {} sig {})", pk.len(), sig.len());
    }
});
