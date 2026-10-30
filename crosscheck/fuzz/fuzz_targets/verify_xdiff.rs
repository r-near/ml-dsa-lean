//! verify_xdiff: Verify / Verify_internal of every implementation (ours, RustCrypto ml-dsa, libcrux portable and
//! AVX2, mldsa-native portable and AVX2) on mutated (pk, signature, message, context) tuples. All verdicts must be
//! equal and no implementation may panic. Valid inputs must be accepted.
//!
//! Input format (little endian; missing bytes read as zero):
//!   b0 parameter set (mod 3)   b1 base index (mod pool size)   b2 flags   b3 ctx selector (mod 8)
//!   b4 second base index       b5 edit count (mod 41)           edits: 5 bytes each [region, off lo, off hi, value, mode]
//!   u16 split point of M′ between prefix and message (mod |M′| + 1)
//!   then per flag: pk (pk_len bytes), sig (sig_len bytes), u16-prefixed message, u16-prefixed context.
//! Flags: 0 pk explicit, 1 sig explicit, 2 message explicit, 3 context explicit (overrides the selector),
//! 4 pk from the second base, 5 sig from the second base.
//! Context selector: 0 base, 1 empty, 2 255 bytes, 3 256 bytes, 4 254 bytes, 5 base plus one byte, 6-7 base.
//! Edits: region (see `region_range`; bit 7 targets the message), mode even = xor value (bit flip if value is 0),
//! odd = overwrite with value.
#![no_main]

use libfuzzer_sys::fuzz_target;
use xc::check::eval_tuple;
use xc::oracle;
use xc::Set;
use xfz::*;

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

fuzz_target!(init: oracle::install_panic_hook(true), |data: &[u8]| {
    let mut c = Cur::new(data);
    let set = Set::from_byte(c.u8());
    let pool = pool(set);
    let base = &pool[c.u8() as usize % POOL_SIZE];
    let (flags, ctx_sel, b4, nedits) = (c.u8(), c.u8() & 7, c.u8(), c.u8() % 41);
    let other = &pool[b4 as usize % POOL_SIZE];
    let edits: Vec<[u8; 5]> = (0..nedits).map(|_| [c.u8(), c.u8(), c.u8(), c.u8(), c.u8()]).collect();
    let split_raw = c.u16() as usize;

    let mut pk = if flags & 16 != 0 { other.pk.clone() } else { base.pk.clone() };
    let mut sig = if flags & 32 != 0 { other.sig.clone() } else { base.sig.clone() };
    let mut msg = base.msg.clone();
    let mut ctx = base.ctx.clone();
    if flags & 1 != 0 {
        pk = c.take(set.pk_len());
    }
    if flags & 2 != 0 {
        sig = c.take(set.sig_len());
    }
    if flags & 4 != 0 {
        msg = c.blob(4096);
    }
    match ctx_sel {
        1 => ctx = Vec::new(),
        2 => ctx = pattern(255, 1),
        3 => ctx = pattern(256, 2),
        4 => ctx = pattern(254, 3),
        5 => ctx.push(0x5A),
        _ => {}
    }
    if flags & 8 != 0 {
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
    let pristine = flags & 0x3F == 0 && nedits == 0 && matches!(ctx_sel, 0 | 6 | 7);
    let split = split_raw % (2 + ctx.len().min(255) + msg.len() + 1);

    let t = eval_tuple(set, imps(), &pk, &msg, &ctx, &sig, split);
    if let Some(d) = t.mismatch {
        panic!("{set:?}: verdicts differ (|ctx| = {}, |m| = {}): {d}", ctx.len(), msg.len());
    }
    if pristine {
        assert!(t.verdict && t.verdict_int, "{set:?}: valid signature rejected");
    }
});
