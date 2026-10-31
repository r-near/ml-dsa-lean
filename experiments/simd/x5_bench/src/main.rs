//! Differential tests of the AVX2 shims against the real intrinsics, kernel equivalence checks, and a benchmark of
//! the hand-written kernel against the auto-vectorized variants of x4_ntt. Usage: x5_bench [label]
use std::hint::black_box;
use std::time::Instant;
use x4_ntt::{field, lazy, ntt, shoup};
use x5_shim::{kernel_real, kernel_shim, real, shim};

mod imm_cases;

pub struct Rng(u64);
impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn m256(&mut self) -> [u32; 8] {
        let mut a = [0u32; 8];
        for x in a.iter_mut() {
            // mix of full-range and small values so that sign and carry cases both occur
            *x = if self.next() & 3 == 0 { (self.next() % 64) as u32 } else { self.next() as u32 };
        }
        a
    }
    fn poly(&mut self) -> [u32; 256] {
        let mut p = [0u32; 256];
        for x in p.iter_mut() {
            *x = (self.next() % field::Q as u64) as u32;
        }
        p
    }
}

const N_DIFF: usize = 20_000;
static mut CHECKS: u64 = 0;

fn same(name: &str, want: [u32; 8], got: [u32; 8], inputs: &[[u32; 8]]) {
    // SAFETY: single-threaded counter.
    unsafe { CHECKS += 1 };
    if want != got {
        panic!("shim differs from the real intrinsic: {name}\n inputs {inputs:x?}\n real {want:x?}\n shim {got:x?}");
    }
}

macro_rules! diff2 {
    ($name:literal, $f:ident, $rng:expr) => {
        for _ in 0..N_DIFF {
            let (a, b) = ($rng.m256(), $rng.m256());
            same($name, real::to_lanes(real::$f(real::from_lanes(a), real::from_lanes(b))), shim::$f(a, b), &[a, b]);
        }
    };
}

fn t_shuffle<const M: i32>(r: &mut Rng) {
    for _ in 0..20 {
        let a = r.m256();
        same("shuffle_epi32", real::to_lanes(real::shuffle_epi32::<M>(real::from_lanes(a))), shim::shuffle_epi32::<M>(a), &[a]);
    }
}
fn t_permute4x64<const M: i32>(r: &mut Rng) {
    for _ in 0..20 {
        let a = r.m256();
        same("permute4x64_epi64", real::to_lanes(real::permute4x64_epi64::<M>(real::from_lanes(a))), shim::permute4x64_epi64::<M>(a), &[a]);
    }
}
fn t_blend<const M: i32>(r: &mut Rng) {
    for _ in 0..20 {
        let (a, b) = (r.m256(), r.m256());
        same("blend_epi32", real::to_lanes(real::blend_epi32::<M>(real::from_lanes(a), real::from_lanes(b))), shim::blend_epi32::<M>(a, b), &[a, b]);
    }
}
fn t_srli<const M: i32>(r: &mut Rng) {
    for _ in 0..200 {
        let a = r.m256();
        same("srli_epi64", real::to_lanes(real::srli_epi64::<M>(real::from_lanes(a))), shim::srli_epi64::<M>(a), &[a]);
    }
}
fn t_srai<const M: i32>(r: &mut Rng) {
    for _ in 0..200 {
        let a = r.m256();
        same("srai_epi32", real::to_lanes(real::srai_epi32::<M>(real::from_lanes(a))), shim::srai_epi32::<M>(a), &[a]);
    }
}
fn t_perm2x128<const M: i32>(r: &mut Rng) {
    for _ in 0..20 {
        let (a, b) = (r.m256(), r.m256());
        same("permute2x128_si256", real::to_lanes(real::permute2x128_si256::<M>(real::from_lanes(a), real::from_lanes(b))), shim::permute2x128_si256::<M>(a, b), &[a, b]);
    }
}

fn differential(rng: &mut Rng) {
    diff2!("add_epi32", add_epi32, rng);
    diff2!("sub_epi32", sub_epi32, rng);
    diff2!("mullo_epi32", mullo_epi32, rng);
    diff2!("mul_epi32", mul_epi32, rng);
    diff2!("and_si256", and_si256, rng);
    diff2!("cmpgt_epi32", cmpgt_epi32, rng);
    diff2!("unpacklo_epi64", unpacklo_epi64, rng);
    diff2!("unpackhi_epi64", unpackhi_epi64, rng);
    for _ in 0..N_DIFF {
        let (a, i) = (rng.m256(), rng.m256());
        same("permutevar8x32_epi32", real::to_lanes(real::permutevar8x32_epi32(real::from_lanes(a), real::from_lanes(i))), shim::permutevar8x32_epi32(a, i), &[a, i]);
        let x = rng.next() as u32;
        same("set1_epi32", real::to_lanes(real::set1_epi32(x)), shim::set1_epi32(x), &[[x; 8]]);
        let e: [u32; 8] = rng.m256();
        same(
            "setr_epi32",
            real::to_lanes(real::setr_epi32(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7])),
            shim::setr_epi32(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]),
            &[e],
        );
        let mut mem = [0u32; 256];
        for x in mem.iter_mut() {
            *x = rng.next() as u32;
        }
        let at = (rng.next() % 249) as usize;
        same("loadu_si256", real::to_lanes(real::loadu_si256(&mem, at)), shim::loadu_si256(&mem, at), &[[at as u32; 8]]);
        let (mut m1, mut m2) = (mem, mem);
        let v = rng.m256();
        real::storeu_si256(&mut m1, at, real::from_lanes(v));
        shim::storeu_si256(&mut m2, at, v);
        unsafe { CHECKS += 1 };
        assert_eq!(m1, m2, "storeu_si256 differs");
    }
    imm_cases::run_imm_cases(rng);
}

fn a_from(p: &[u32; 256]) -> [i32; 256] {
    let mut a = [0i32; 256];
    for j in 0..256 {
        a[j] = p[j] as i32;
    }
    a
}

fn kernel_checks(rng: &mut Rng) {
    let mut bad = [0u32; 4];
    let mut n = 0;
    let mut polys: Vec<[u32; 256]> = (0..20_000).map(|_| rng.poly()).collect();
    polys.push([0; 256]);
    polys.push([field::Q - 1; 256]);
    let mut alt = [0u32; 256];
    for (i, x) in alt.iter_mut().enumerate() {
        *x = if i % 2 == 0 { 0 } else { field::Q - 1 };
    }
    polys.push(alt);
    for p in &polys {
        n += 1;
        // scalar lazy reference (x4_ntt): bit-exact on the un-normalized state
        let mut a = a_from(p);
        lazy::ntt_lazy(&mut a);
        let mut s = *p;
        kernel_shim::ntt_lazy_vec(&mut s);
        bad[0] += (s.iter().zip(a.iter()).any(|(&x, &y)| x as i32 != y)) as u32;
        // real intrinsics == shim
        let mut r = *p;
        unsafe { kernel_real::ntt_lazy_vec_avx2(&mut r) };
        bad[1] += (r != s) as u32;
        // canonical wrapper == the crate's ntt
        let want = ntt::ntt(p);
        bad[2] += (kernel_shim::ntt_vec(p) != want) as u32;
        bad[3] += (unsafe { kernel_real::ntt_vec_avx2(p) } != want) as u32;
    }
    println!(
        "CHECK kernel on {n} polys: shim kernel vs scalar lazy (bit-exact, un-normalized) {} mismatches; real kernel vs shim kernel {}; canonical ntt_vec vs crate ntt: shim {}, real {}",
        bad[0], bad[1], bad[2], bad[3]
    );
    assert!(bad.iter().all(|&b| b == 0));
}

struct Suite {
    names: Vec<String>,
    fns: Vec<Box<dyn FnMut(usize)>>,
}
impl Suite {
    fn add(&mut self, name: &str, f: impl FnMut(usize) + 'static) {
        self.names.push(name.to_string());
        self.fns.push(Box::new(f));
    }
    fn run(&mut self, label: &str, rounds: usize, reps: usize) {
        let n = self.fns.len();
        let mut samples = vec![Vec::with_capacity(rounds); n];
        for f in self.fns.iter_mut() {
            f(reps);
        }
        for _ in 0..rounds {
            for (i, f) in self.fns.iter_mut().enumerate() {
                let t = Instant::now();
                f(reps);
                samples[i].push(t.elapsed().as_nanos() as f64 / reps as f64);
            }
        }
        for (i, s) in samples.iter_mut().enumerate() {
            s.sort_by(|a, b| a.partial_cmp(b).unwrap());
            println!("ROW\t{label}\t{}\t{:.1}\t{:.1}\t{:.1}", self.names[i], s[s.len() / 2], s[s.len() / 10], s[0]);
        }
    }
}

fn main() {
    let label = std::env::args().nth(1).unwrap_or_else(|| "run".into());
    if !std::is_x86_feature_detected!("avx2") {
        println!("no AVX2 on this CPU; nothing to test");
        return;
    }
    let mut rng = Rng(0x1234_5678_9ABC_DEF1);
    if std::env::var_os("SIMD_SKIP_CHECK").is_none() {
        differential(&mut rng);
        // SAFETY: single-threaded counter.
        println!("CHECK differential: shim == real intrinsic on {} randomized comparisons covering 19 operations and 904 immediates", unsafe { CHECKS });
        kernel_checks(&mut rng);
    }
    let base = rng.poly();
    let (rounds, reps) = (1001, 200);
    let mut s = Suite { names: vec![], fns: vec![] };
    // SAFETY (closures): AVX2 was detected above.
    macro_rules! full {
        ($name:expr, $f:expr) => {{
            let mut x = base;
            s.add($name, move |reps| {
                for _ in 0..reps {
                    x = black_box($f(black_box(&x)));
                }
            });
        }};
    }
    full!("ntt: crate (Barrett u128), baseline-compiled", ntt::ntt);
    full!("ntt: S shoup (canonical), avx2 clone, autovectorized", |p| unsafe { shoup::ntt_avx2(p) });
    full!("ntt: L lazy + normalize, avx2 clone, autovectorized", |p| unsafe { lazy::ntt_avx2(p) });
    full!("ntt: L lazy + normalize, hand-written AVX2 (8 layers)", |p| unsafe { kernel_real::ntt_vec_avx2(p) });
    {
        let mut w = base;
        s.add("transform only: L lazy, autovectorized, avx2 clone", move |reps| {
            for _ in 0..reps {
                let mut a = black_box(a_from(&base));
                unsafe { lazy::ntt_lazy_avx2(black_box(&mut a)) };
                black_box(&a);
            }
            black_box(&mut w);
        });
        s.add("transform only: L lazy, hand-written AVX2 (8 layers)", move |reps| {
            for _ in 0..reps {
                let mut a = black_box(base);
                unsafe { kernel_real::ntt_lazy_vec_avx2(black_box(&mut a)) };
                black_box(&a);
            }
        });
    }
    // per-layer: hand-written vs the autovectorized lazy layer (the latter is the baseline-compiled generic here, so it
    // is timed through the avx2 clone of the whole transform above; layers are only timed for the hand-written kernel)
    macro_rules! hand_layer {
        ($name:expr, $call:expr) => {{
            let mut w = base;
            s.add($name, move |reps| {
                for _ in 0..reps {
                    unsafe { $call(black_box(&mut w)) };
                }
            });
        }};
    }
    hand_layer!("hand layer LEN=128", kernel_real::layer_wide_avx2::<128, 1, 0>);
    hand_layer!("hand layer LEN=16", kernel_real::layer_wide_avx2::<16, 8, 7>);
    hand_layer!("hand layer LEN=8", kernel_real::layer_wide_avx2::<8, 16, 15>);
    hand_layer!("hand layer LEN=4", kernel_real::layer4_avx2);
    hand_layer!("hand layer LEN=2", kernel_real::layer2_avx2);
    hand_layer!("hand layer LEN=1", kernel_real::layer1_avx2);
    s.run(&label, rounds, reps);
}
