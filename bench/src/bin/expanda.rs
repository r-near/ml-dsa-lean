//! ExpandA micro-benchmark for ML-DSA-65's matrix: the scalar `expand_a` against the 4-way sampler (plain Rust, no lane
//! operations; AVX2 code only when the benchmark is built with `-C target-feature=+avx2`). Needs `--features internals`. Run
//! pinned on an idle machine.
use ml_dsa_lean::sampling::{expand_a, expand_a_into_x4};
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
    let mut rho = [0u8; 32];
    for (i, b) in rho.iter_mut().enumerate() {
        *b = (i * 37 + 11) as u8;
    }
    let want = expand_a::<6, 5>(&rho);
    let mut a = [[[0u32; 256]; 5]; 6];
    expand_a_into_x4::<6, 5>(&rho, &mut a);
    assert!(a == want);
    let s = median(rounds, 200, || {
        black_box(expand_a::<6, 5>(black_box(&rho)));
    });
    println!("EXPANDA65\tscalar\t{:.2} us", s / 1000.0);
    let t = median(rounds, 200, || {
        let mut a = [[[0u32; 256]; 5]; 6];
        expand_a_into_x4::<6, 5>(black_box(&rho), &mut a);
        black_box(&a);
    });
    println!("EXPANDA65\tx4\t{:.2} us", t / 1000.0);
}
