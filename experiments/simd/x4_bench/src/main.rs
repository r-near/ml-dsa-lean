//! Equivalence checks and interleaved micro-benchmarks for the NTT rewrites. Usage: x4_bench [label]
//! Prints `ROW<TAB>label<TAB>name<TAB>median_ns<TAB>p10_ns<TAB>min_ns` lines; run pinned (`taskset -c N`).
//! Rounds are interleaved across all variants (variant 1, 2, ..., n, then again) so that noise from other tenants of
//! the machine hits every variant alike.
use std::hint::black_box;
use std::time::Instant;
use x4_ntt::{field, fold, lazy, mont2, ntt, origl, shoup, tables};

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn poly(&mut self) -> [u32; 256] {
        let mut p = [0u32; 256];
        for x in p.iter_mut() {
            *x = (self.next() % field::Q as u64) as u32;
        }
        p
    }
}

const Q: u64 = field::Q as u64;

fn has_avx2() -> bool {
    std::is_x86_feature_detected!("avx2")
}

fn check_equivalence() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    // fold_reduce == x % q: every x below 2^31, every multiple-of-2^23 boundary, and random x < q^2.
    let mut bad = 0u64;
    for x in 0u64..(1 << 31) {
        if fold::fold_reduce(x) as u64 != x % Q {
            bad += 1;
        }
    }
    let mut k = 0u64;
    while k * (1 << 23) < Q * Q {
        for d in [0u64, 1, 2, 8191, 8192, (1 << 23) - 1] {
            for s in [-1i64, 0, 1] {
                let x = (k * (1 << 23) + d) as i64 + s;
                if x >= 0 && (x as u64) < Q * Q && fold::fold_reduce(x as u64) as u64 != (x as u64) % Q {
                    bad += 1;
                }
            }
        }
        k += 1;
    }
    for x in [Q * Q - 1, Q * Q - 2, Q * Q - Q, (Q - 1) * (Q - 1)] {
        if fold::fold_reduce(x) as u64 != x % Q {
            bad += 1;
        }
    }
    for _ in 0..200_000_000u64 {
        let x = rng.next() % (Q * Q);
        if fold::fold_reduce(x) as u64 != x % Q {
            bad += 1;
        }
    }
    println!("CHECK fold_reduce vs x % q: exhaustive below 2^31, all 2^23 boundaries, 2e8 random below q^2: {bad} mismatches");
    assert_eq!(bad, 0);

    // mul_shoup == x*z % q for every zeta (and its negation) and every canonical x; plus random x < 2^32.
    let mut bad = 0u64;
    for k in 0..256 {
        let (z, zp) = (ntt::ZETAS[k], tables::ZETAS_SHOUP[k]);
        let (zn, znp) = (field::sub(0, ntt::ZETAS[k]), tables::ZETAS_NEG_SHOUP[k]);
        for x in 0..field::Q {
            if shoup::mul_shoup(z, zp, x) as u64 != (x as u64 * z as u64) % Q {
                bad += 1;
            }
            if shoup::mul_shoup(zn, znp, x) as u64 != (x as u64 * zn as u64) % Q {
                bad += 1;
            }
        }
        for _ in 0..200_000 {
            let x = rng.next() as u32;
            if shoup::mul_shoup(z, zp, x) as u64 != (x as u64 * z as u64) % Q {
                bad += 1;
            }
        }
    }
    for x in 0..field::Q {
        if shoup::mul_shoup(8_347_681, tables::F_SHOUP, x) as u64 != (x as u64 * 8_347_681) % Q {
            bad += 1;
        }
    }
    println!("CHECK mul_shoup vs x*z % q: 256 zetas, 256 negated zetas and the scale factor x all x < q, plus 2e5 random x < 2^32 per zeta: {bad} mismatches");
    assert_eq!(bad, 0);

    // mont2::mul == a*b % q: boundary values (all pairs) and 4e8 random pairs.
    let mut bad = 0u64;
    let edge = [0u32, 1, 2, 3, field::Q - 1, field::Q - 2, field::Q / 2, field::Q / 2 + 1, 4_194_304, 8_388_607 % field::Q];
    for &a in &edge {
        for &b in &edge {
            if mont2::mul(a, b) as u64 != (a as u64 * b as u64) % Q {
                bad += 1;
            }
        }
    }
    for _ in 0..400_000_000u64 {
        let (a, b) = (rng.next() % Q, rng.next() % Q);
        if mont2::mul(a as u32, b as u32) as u64 != (a * b) % Q {
            bad += 1;
        }
    }
    println!("CHECK mont2::mul vs a*b % q: all pairs of 10 edge values, 4e8 random pairs: {bad} mismatches");
    assert_eq!(bad, 0);

    // Whole transforms.
    let avx2 = has_avx2();
    let mut polys: Vec<[u32; 256]> = (0..20_000).map(|_| rng.poly()).collect();
    polys.push([0; 256]);
    polys.push([field::Q - 1; 256]);
    polys.push([1; 256]);
    let mut alt = [0u32; 256];
    for (i, x) in alt.iter_mut().enumerate() {
        *x = if i % 2 == 0 { 0 } else { field::Q - 1 };
    }
    polys.push(alt);
    let mut m = [0u32; 14];
    for p in &polys {
        let want = ntt::ntt(p);
        let want_inv = ntt::ntt_inverse(p);
        let want_pw = ntt::multiply_ntt(p, &want);
        m[0] += (fold::ntt(p) != want) as u32;
        m[1] += (shoup::ntt(p) != want) as u32;
        m[2] += (lazy::ntt(p) != want) as u32;
        m[3] += (shoup::ntt_blocks(p) != want) as u32;
        m[4] += (fold::ntt_inverse(p) != want_inv) as u32;
        m[5] += (shoup::ntt_inverse(p) != want_inv) as u32;
        m[6] += (fold::multiply_ntt(p, &want) != want_pw) as u32;
        m[7] += (mont2::multiply_ntt(p, &want) != want_pw) as u32;
        if avx2 {
            // SAFETY: AVX2 was detected at run time.
            unsafe {
                m[8] += (fold::ntt_avx2(p) != want) as u32;
                m[9] += (shoup::ntt_avx2(p) != want) as u32;
                m[10] += (lazy::ntt_avx2(p) != want) as u32;
                m[11] += (shoup::ntt_blocks_avx2(p) != want) as u32;
                m[12] += (shoup::ntt_inverse_avx2(p) != want_inv) as u32;
                m[13] += (mont2::multiply_ntt_avx2(p, &want) != want_pw) as u32;
            }
        }
    }
    println!(
        "CHECK {} polys incl. 0, q-1, 1, alternating, mismatches: ntt[fold {} shoup {} lazy+norm {} shoup-blocks {}] ntt_inverse[fold {} shoup {}] multiply_ntt[fold {} mont2 {}] avx2 clones (ran: {avx2}) [fold {} shoup {} lazy {} shoup-blocks {} shoup-inv {} mont2 {}]",
        polys.len(), m[0], m[1], m[2], m[3], m[4], m[5], m[6], m[7], m[8], m[9], m[10], m[11], m[12], m[13]
    );
    assert!(m.iter().all(|&x| x == 0));

    // Lazy bounds: max |w| / q after each of the 8 layers, over random and extremal canonical inputs.
    let mut worst = [0i64; 8];
    let mut inputs: Vec<[u32; 256]> = polys.iter().take(5000).cloned().collect();
    for _ in 0..5000 {
        let mut p = [0u32; 256];
        for x in p.iter_mut() {
            *x = if rng.next() & 1 == 0 { 0 } else { field::Q - 1 };
        }
        inputs.push(p);
    }
    for p in &inputs {
        let mut a = a_from(p);
        let mut mm = 0;
        macro_rules! step {
            ($len:literal, $it:literal, $l:literal) => {
                lazy::ntt_layer::<$len, $it>(&mut a, &mut mm);
                let mx = a.iter().map(|&v| (v as i64).abs()).max().unwrap();
                if mx > worst[$l] {
                    worst[$l] = mx;
                }
            };
        }
        step!(128, 1, 0);
        step!(64, 2, 1);
        step!(32, 4, 2);
        step!(16, 8, 3);
        step!(8, 16, 4);
        step!(4, 32, 5);
        step!(2, 64, 6);
        step!(1, 128, 7);
    }
    let qf = field::Q as f64;
    let rows: Vec<String> = worst.iter().map(|&v| format!("{:.2}q", v as f64 / qf)).collect();
    println!("CHECK lazy bound: observed max |w| after layers 1..8 over {} inputs = [{}] (analytic bound: q + l*(q/2 + q/64) = [1.52q .. 5.1q])", inputs.len(), rows.join(", "));
}

fn a_from(p: &[u32; 256]) -> [i32; 256] {
    let mut a = [0i32; 256];
    for j in 0..256 {
        a[j] = p[j] as i32;
    }
    a
}

struct Suite {
    names: Vec<String>,
    fns: Vec<Box<dyn FnMut(usize)>>,
}
impl Suite {
    fn new() -> Self {
        Suite { names: vec![], fns: vec![] }
    }
    fn add(&mut self, name: &str, f: impl FnMut(usize) + 'static) {
        self.names.push(name.to_string());
        self.fns.push(Box::new(f));
    }
    fn run(&mut self, label: &str, rounds: usize, reps: usize) {
        let n = self.fns.len();
        let mut samples = vec![Vec::with_capacity(rounds); n];
        for f in self.fns.iter_mut() {
            f(reps); // warm-up
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
    if std::env::var_os("SIMD_SKIP_CHECK").is_none() {
        check_equivalence();
    }
    let avx2 = has_avx2();
    let mut rng = Rng(12345);
    let base = rng.poly();
    let other = rng.poly();
    let (rounds, reps) = (1001, 200);

    // ---- Group 1: whole transforms, canonical in and out.
    let mut s = Suite::new();
    macro_rules! full {
        ($s:ident, $name:expr, $f:expr) => {{
            let mut x = base;
            $s.add($name, move |reps| {
                for _ in 0..reps {
                    x = black_box($f(black_box(&x)));
                }
            });
        }};
    }
    full!(s, "ntt: crate (Barrett u128)", ntt::ntt);
    full!(s, "ntt: F fold (u64 folding)", fold::ntt);
    full!(s, "ntt: S shoup (canonical)", shoup::ntt);
    full!(s, "ntt: S shoup, narrow layers block-indexed", shoup::ntt_blocks);
    full!(s, "ntt: L lazy i32 + normalize", lazy::ntt);
    {
        let mut a = a_from(&base);
        s.add("ntt: L lazy i32 transform only (reload 1 KiB each call)", move |reps| {
            for _ in 0..reps {
                a = black_box(a_from(&base));
                lazy::ntt_lazy(black_box(&mut a));
            }
        });
    }
    if avx2 {
        // SAFETY (all closures below): AVX2 was detected at run time.
        full!(s, "ntt: crate, inside a target_feature(avx2) wrapper", |p| unsafe { origl::ntt_in_tf_wrapper(p) });
        full!(s, "ntt: F fold, avx2 clone", |p| unsafe { fold::ntt_avx2(p) });
        full!(s, "ntt: S shoup, avx2 clone", |p| unsafe { shoup::ntt_avx2(p) });
        full!(s, "ntt: S shoup block-indexed, avx2 clone", |p| unsafe { shoup::ntt_blocks_avx2(p) });
        full!(s, "ntt: L lazy + normalize, avx2 clone", |p| unsafe { lazy::ntt_avx2(p) });
        full!(s, "ntt: S shoup via dispatch shim (cpuid+xgetbv per call)", x4_ntt::ntt_dispatch);
    }
    s.run(&format!("{label}/ntt"), rounds, reps);

    // ---- Group 2: inverse transform and pointwise product.
    let mut s = Suite::new();
    full!(s, "ntt_inverse: crate", ntt::ntt_inverse);
    full!(s, "ntt_inverse: F fold", fold::ntt_inverse);
    full!(s, "ntt_inverse: S shoup", shoup::ntt_inverse);
    if avx2 {
        full!(s, "ntt_inverse: S shoup, avx2 clone", |p| unsafe { shoup::ntt_inverse_avx2(p) });
    }
    macro_rules! pw {
        ($name:expr, $f:expr) => {{
            let mut x = base;
            s.add($name, move |reps| {
                for _ in 0..reps {
                    x = black_box($f(black_box(&x), black_box(&other)));
                }
            });
        }};
    }
    pw!("multiply_ntt: crate", ntt::multiply_ntt);
    pw!("multiply_ntt: F fold", fold::multiply_ntt);
    pw!("multiply_ntt: M mont2 (two Montgomery reductions)", mont2::multiply_ntt);
    if avx2 {
        pw!("multiply_ntt: F fold, avx2 clone", |a, b| unsafe { fold::multiply_ntt_avx2(a, b) });
        pw!("multiply_ntt: M mont2, avx2 clone", |a, b| unsafe { mont2::multiply_ntt_avx2(a, b) });
    }
    s.run(&format!("{label}/inv+pw"), rounds, reps);

    // ---- Group 3: every forward layer on its own (crate shape), per variant.
    let mut s = Suite::new();
    macro_rules! layers {
        (@one $tag:expr, $m:ident, $init:expr, $len:literal, $it:literal, $m0:literal) => {{
            let mut w = $init;
            s.add(&format!("layer LEN={:<3} {}", $len, $tag), move |reps| {
                for _ in 0..reps {
                    $m::layer::<$len, $it, $m0>(black_box(&mut w));
                }
            });
        }};
        ($tag:expr, $m:ident, $init:expr) => {{
            layers!(@one $tag, $m, $init, 128, 1, 0);
            layers!(@one $tag, $m, $init, 64, 2, 1);
            layers!(@one $tag, $m, $init, 32, 4, 3);
            layers!(@one $tag, $m, $init, 16, 8, 7);
            layers!(@one $tag, $m, $init, 8, 16, 15);
            layers!(@one $tag, $m, $init, 4, 32, 31);
            layers!(@one $tag, $m, $init, 2, 64, 63);
            layers!(@one $tag, $m, $init, 1, 128, 127);
        }};
    }
    layers!("crate", origl, base);
    layers!("F fold", fold, base);
    layers!("S shoup", shoup, base);
    layers!("L lazy (values drift; timing only)", lazy, a_from(&base));
    {
        let mut w = base;
        s.add("layer LEN=4   S shoup block-indexed", move |reps| { for _ in 0..reps { shoup::layer4_blocks(black_box(&mut w)); } });
        let mut w = base;
        s.add("layer LEN=2   S shoup block-indexed", move |reps| { for _ in 0..reps { shoup::layer2_blocks(black_box(&mut w)); } });
        let mut w = base;
        s.add("layer LEN=1   S shoup block-indexed", move |reps| { for _ in 0..reps { shoup::layer1_blocks(black_box(&mut w)); } });
    }
    s.run(&format!("{label}/layers"), rounds, reps * 5);
}
