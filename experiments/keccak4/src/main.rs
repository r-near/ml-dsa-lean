//! Usage: keccak4 [label]. Prints ROW<TAB>label<TAB>name<TAB>median_ns<TAB>p10_ns<TAB>min_ns. Run pinned.
//! Times are per call: 4 permutations (scalar4) or one 4-way permutation.
use keccak4::*;
use std::hint::black_box;
use std::time::Instant;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn to_x4(s: &[[u64; 25]; 4]) -> [[u64; 4]; 25] {
    let mut r = [[0u64; 4]; 25];
    for i in 0..25 {
        for l in 0..4 {
            r[i][l] = s[l][i];
        }
    }
    r
}

const NAMES: [&str; 17] = [
    "scalar4", "scalar4_avx2", "x4_v2", "x4_v2_avx2", "x4_v4", "x4_v4_avx2", "x4_v5", "x4_v5_avx2", "x4_v3or", "x4_v6", "x4_v7", "x4_v7_avx2", "x4_intrinsics", "x4_v2a", "x4_v2a_avx2", "x4_v2c", "x4_v2c_avx2",
];

fn run(v: usize, s: &mut [[u64; 25]; 4], x: &mut [[u64; 4]; 25], sc: &mut Scratch) {
    // SAFETY: callers only pass avx2 variants when the CPU has AVX2.
    unsafe {
        match v {
            0 => scalar4(s),
            1 => scalar4_avx2(s),
            2 => x4_v2_default(x),
            3 => x4_v2_avx2(x),
            4 => x4_v4_default(x, sc),
            5 => x4_v4_avx2(x, sc),
            6 => x4_v5_default(x, sc),
            7 => x4_v5_avx2(x, sc),
            8 => x4_v3or_default(x),
            9 => x4_v6_default(x, sc),
            10 => x4_v7_default(x, sc),
            11 => x4_v7_avx2(x, sc),
            12 => intr::keccak_f1600_x4_intrinsics(x),
            13 => x4_v2a_default(x),
            14 => x4_v2a_avx2(x),
            15 => x4_v2c_default(x),
            _ => x4_v2c_avx2(x),
        }
    }
}

fn is_avx2(v: usize) -> bool {
    v == 1 || v == 3 || v == 5 || v == 7 || v == 11 || v == 12 || v == 14 || v == 16
}

fn check(avx2: bool) {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    for _ in 0..2000 {
        let mut s = [[0u64; 25]; 4];
        for l in 0..4 {
            for i in 0..25 {
                s[l][i] = rng.next();
            }
        }
        let x0 = to_x4(&s);
        for l in 0..4 {
            keccak_f1600(&mut s[l]);
        }
        let want = to_x4(&s);
        for v in [2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16] {
            if !avx2 && is_avx2(v) {
                continue;
            }
            let mut x = x0;
            let mut dummy = [[0u64; 25]; 4];
            run(v, &mut dummy, &mut x, &mut Scratch::new());
            assert_eq!(x, want, "{}", NAMES[v]);
        }
    }
    eprintln!("equivalence OK");
}

fn main() {
    let label = std::env::args().nth(1).unwrap_or_else(|| "run".into());
    let avx2 = std::is_x86_feature_detected!("avx2");
    check(avx2);
    let mut rng = Rng(12345);
    let mut s = [[0u64; 25]; 4];
    for l in 0..4 {
        for i in 0..25 {
            s[l][i] = rng.next();
        }
    }
    let mut x = to_x4(&s);
    let mut sc = Scratch::new();
    let reps = 2000;
    let iters = 200;
    let vs: Vec<usize> = (0..17).filter(|v| avx2 || !is_avx2(*v)).collect();
    let mut samples = vec![Vec::new(); 17];
    for _ in 0..reps {
        for &v in &vs {
            let t = Instant::now();
            for _ in 0..iters {
                run(v, black_box(&mut s), black_box(&mut x), black_box(&mut sc));
            }
            samples[v].push(t.elapsed().as_nanos() as f64 / iters as f64);
        }
    }
    black_box((&s, &x));
    for &v in &vs {
        let sm = &mut samples[v];
        sm.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!("ROW\t{}\t{}\t{:.1}\t{:.1}\t{:.1}", label, NAMES[v], sm[sm.len() / 2], sm[sm.len() / 10], sm[0]);
    }
}
