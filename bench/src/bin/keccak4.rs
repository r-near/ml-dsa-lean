//! Nanoseconds per 4-way Keccak-f[1600] permutation (`keccak4::keccak_f1600_x4`; AVX2 code only when built with
//! `-C target-feature=+avx2`), next to four scalar permutations. Needs `--features internals`. Run pinned on an idle machine.
use ml_dsa_lean::keccak::keccak_f1600;
use ml_dsa_lean::keccak4::keccak_f1600_x4;
use std::hint::black_box;
use std::time::Instant;

fn median(rounds: usize, n: usize, mut f: impl FnMut()) -> f64 {
    for _ in 0..n {
        f();
    }
    let mut v: Vec<f64> = (0..rounds)
        .map(|_| {
            let t = Instant::now();
            for _ in 0..n {
                f();
            }
            t.elapsed().as_nanos() as f64 / n as f64
        })
        .collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    v[rounds / 2]
}

fn main() {
    let rounds = 101;
    let mut s4 = [[0u64; 4]; 25];
    for (k, l) in s4.iter_mut().enumerate() {
        for (i, x) in l.iter_mut().enumerate() {
            *x = (k as u64 * 0x9e37_79b9_7f4a_7c15) ^ (i as u64 * 0x1234_5678_9abc_def1) ^ 7;
        }
    }
    // Check against the scalar permutation first.
    let mut t = s4;
    keccak_f1600_x4(&mut t);
    for i in 0..4 {
        let mut st = [0u64; 25];
        for k in 0..25 {
            st[k] = s4[k][i];
        }
        keccak_f1600(&mut st);
        for k in 0..25 {
            assert_eq!(st[k], t[k][i], "lane {k} state {i}");
        }
    }
    let x4 = median(rounds, 2000, || {
        keccak_f1600_x4(black_box(&mut s4));
    });
    println!("KECCAK4\tx4\t{x4:.1} ns per 4-way permutation");
    let mut st = [[0u64; 25]; 4];
    let sc = median(rounds, 2000, || {
        for s in st.iter_mut() {
            keccak_f1600(black_box(s));
        }
    });
    println!("KECCAK4\t4x scalar\t{sc:.1} ns");
    println!("KECCAK4\tchecksum\t{:x}", s4[0][0] ^ st[1][2]);
}
