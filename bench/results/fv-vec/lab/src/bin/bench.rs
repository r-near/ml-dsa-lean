use fvlab::v;
use std::time::Instant;

type F = fn(&mut [[u64; 4]; 25]);

// Safe wrappers: the lab only runs on AVX2 hardware, checked once in main.
macro_rules! w {
    ($($n:ident),* $(,)?) => {
        vec![$((stringify!($n), (|s: &mut [[u64; 4]; 25]| unsafe { v::$n(s) }) as F)),*]
    };
}

fn main() {
    assert!(std::is_x86_feature_detected!("avx2"));
    let only: Vec<String> = std::env::args().skip(1).collect();
    let mut all: Vec<(&str, F)> = w![shim, avx2, noinl, rotl_x, rotl_noinl, xor_x, xor_noinl, add_x, add_noinl, norot_x, norot_noinl, nod_x, nod_noinl, norho_x, norho_noinl, lv_copy, lv_for, lv2, lv4, lvl1, lvl2, lvl2b, ld1, ld2, ld4, passes];
    all.push(("scalar4", v::scalar4 as F));
    // reference state
    let mut init = [[0u64; 4]; 25];
    let mut x = 0x9E3779B97F4A7C15u64;
    for k in 0..25 {
        for i in 0..4 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            init[k][i] = x;
        }
    }
    let mut refs = init;
    v::scalar4(&mut refs);
    for (name, f) in &all {
        if !only.is_empty() && !only.iter().any(|o| o == name) {
            continue;
        }
        let mut s = init;
        f(&mut s);
        let ok = s == refs || (name.starts_with("norot") || name.starts_with("nod") || name.starts_with("norho"));
        let n = 200_000u32;
        let mut best = f64::MAX;
        for _ in 0..7 {
            let mut s = init;
            let t = Instant::now();
            for _ in 0..n {
                f(std::hint::black_box(&mut s));
            }
            let e = t.elapsed().as_nanos() as f64 / n as f64;
            std::hint::black_box(&s);
            if e < best {
                best = e;
            }
        }
        println!("{name:<14} {} {best:8.1} ns/perm", if ok { "OK  " } else { "BAD " });
    }
}
