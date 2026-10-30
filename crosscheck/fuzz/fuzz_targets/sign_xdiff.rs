//! sign_xdiff: KeyGen, Sign and Sign_internal of every implementation on a seed, randomness, message and context
//! taken from the input; pk, sk and the signature must be byte-identical everywhere, every implementation must
//! accept the signature (and a few mutations of it must get equal verdicts), and |ctx| > 255 must be refused by all.
//!
//! Input format (little endian; missing bytes read as zero):
//!   b0 parameter set (mod 3)   b1 flags: bit0 deterministic (rnd = 0^32)
//!   b2 ctx selector (mod 8): 0 explicit, 1 empty, 2 255 bytes, 3 256 bytes, 4 254 bytes, 5-7 explicit
//!   32 bytes ξ      32 bytes rnd (always present, ignored when deterministic)      u16 ctx length + ctx
//!   u16 split point of M′      rest = message (at most 16 KiB).
#![no_main]

use libfuzzer_sys::fuzz_target;
use xc::check::{Plan, Stats, run_given};
use xc::cases::{Case, Rng};
use xc::oracle;
use xc::Set;
use xfz::*;

fuzz_target!(init: oracle::install_panic_hook(true), |data: &[u8]| {
    let mut c = Cur::new(data);
    let set = Set::from_byte(c.u8());
    let (flags, ctx_sel) = (c.u8(), c.u8() & 7);
    let xi: [u8; 32] = c.take(32).try_into().unwrap();
    let mut rnd: [u8; 32] = c.take(32).try_into().unwrap();
    let hedged = flags & 1 == 0;
    if !hedged {
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
    let split = split_raw % (2 + ctx.len().min(255) + msg.len() + 1);

    let case = Case { set, idx: 0, xi, rnd, hedged, msg, ctx, split };
    let mut r = Rng::new(u64::from_le_bytes(xi[..8].try_into().unwrap()) ^ split_raw as u64);
    let plan = Plan { sig_flips: 3, pk_flips: 1, exhaustive_cases: 0, keep: 1, light: true };
    let (mut st, mut out) = (Stats::default(), Vec::new());
    run_given(&case, &mut r, imps(), &plan, &mut st, &mut out);
    if st.disagreements > 0 {
        let d = &out[0];
        panic!("{set:?}: {} ({}): {}\n{}", d.kind, d.label, d.detail, d.repro);
    }
});
