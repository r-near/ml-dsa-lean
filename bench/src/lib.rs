//! Shared pieces of the benchmark harness: the mldsa-native C entry points, a small PRNG, timing statistics and
//! machine information.
#![allow(unused_extern_crates)]

// Pulls in crosscheck's build script output (the static libraries holding mldsa-native).
extern crate xc;

pub mod cells;

use std::time::Instant;

/// C entry points of crosscheck's two mldsa-native builds (csrc/xc_wrap.inc). Every call takes the level
/// (44, 65 or 87); 0 means success. `signature` and `verify` use the FIPS 204 external interface (ctx);
/// `signature` reads its 32 random bytes from `rnd`.
pub mod mld {
    macro_rules! externs {
        ($m:ident, $kp:ident, $sg:ident, $vf:ident) => {
            pub mod $m {
                use std::os::raw::c_int;
                unsafe extern "C" {
                    pub fn $kp(lvl: c_int, pk: *mut u8, sk: *mut u8, seed: *const u8) -> c_int;
                    pub fn $sg(
                        lvl: c_int,
                        sig: *mut u8,
                        m: *const u8,
                        mlen: usize,
                        ctx: *const u8,
                        ctxlen: usize,
                        rnd: *const u8,
                        sk: *const u8,
                    ) -> c_int;
                    pub fn $vf(
                        lvl: c_int,
                        sig: *const u8,
                        m: *const u8,
                        mlen: usize,
                        ctx: *const u8,
                        ctxlen: usize,
                        pk: *const u8,
                    ) -> c_int;
                }
            }
        };
    }
    externs!(portable, xc_p_keypair_internal, xc_p_signature, xc_p_verify);
    #[cfg(all(target_arch = "x86_64", target_os = "linux"))]
    externs!(avx2, xc_a_keypair_internal, xc_a_signature, xc_a_verify);
}

/// splitmix64: deterministic inputs, identical for every implementation.
pub struct Rng(u64);

impl Rng {
    pub fn new(tag: &str, n: u64) -> Rng {
        let mut h = 0xcbf29ce484222325u64;
        for b in tag.bytes() {
            h = (h ^ b as u64).wrapping_mul(0x100000001b3);
        }
        Rng(h ^ n.wrapping_mul(0x9e3779b97f4a7c15))
    }
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    pub fn fill(&mut self, out: &mut [u8]) {
        for c in out.chunks_mut(8) {
            let v = self.next_u64().to_le_bytes();
            c.copy_from_slice(&v[..c.len()]);
        }
    }
    pub fn bytes<const N: usize>(&mut self) -> [u8; N] {
        let mut a = [0u8; N];
        self.fill(&mut a);
        a
    }
}

/// A cheap fingerprint of an output (first and last 8 bytes), used to check that all implementations agree
/// without hashing inside a timed call.
pub fn tag(x: &[u8]) -> u64 {
    let n = x.len();
    u64::from_le_bytes(x[..8].try_into().unwrap()) ^ u64::from_le_bytes(x[n - 8..].try_into().unwrap())
}

#[derive(Clone, Debug)]
pub struct Stats {
    pub median: f64,
    pub mean: f64,
    pub min: f64,
    pub max: f64,
    pub p10: f64,
    pub p50: f64,
    pub p90: f64,
    pub p99: f64,
    pub rounds: usize,
    pub reps: usize,
}

pub fn quantile(sorted: &[f64], q: f64) -> f64 {
    let pos = q * (sorted.len() - 1) as f64;
    let lo = pos.floor() as usize;
    let hi = pos.ceil() as usize;
    sorted[lo] + (sorted[hi] - sorted[lo]) * (pos - lo as f64)
}

/// Times `call(i)` for i in 0..n.
///
/// 1. One pass records the outputs (returned) and is the first warm-up pass.
/// 2. Warm-up passes continue for at least `warm_secs`.
/// 3. `rounds` rounds: each round is `reps` full passes over the n inputs (reps chosen so a round lasts about
///    `round_secs`); the statistic is nanoseconds per call averaged over the round. Every round does the same
///    work, so the spread across rounds is machine noise, not input variation.
/// 4. `lat_passes` further passes time every call separately (Instant overhead is about 25 ns) for the per-call
///    percentiles. Those percentiles show the spread over inputs (rejection-loop attempts for signing).
pub fn measure(
    n: usize,
    rounds: usize,
    lat_passes: usize,
    warm_secs: f64,
    round_secs: f64,
    call: &mut dyn FnMut(usize) -> u64,
) -> (Stats, Vec<u64>) {
    let mut out = Vec::with_capacity(n);
    let t = Instant::now();
    for i in 0..n {
        out.push(call(i));
    }
    let mut pass_secs = t.elapsed().as_secs_f64();
    let warm = Instant::now();
    let mut passes = 1;
    while warm.elapsed().as_secs_f64() < warm_secs || passes < 2 {
        let t = Instant::now();
        for i in 0..n {
            std::hint::black_box(call(i));
        }
        pass_secs = t.elapsed().as_secs_f64();
        passes += 1;
    }
    let reps = ((round_secs / pass_secs).ceil() as usize).max(1);
    let mut per_call = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let t = Instant::now();
        for _ in 0..reps {
            for i in 0..n {
                std::hint::black_box(call(i));
            }
        }
        per_call.push(t.elapsed().as_secs_f64() * 1e9 / (reps * n) as f64);
    }
    let mut lat = Vec::with_capacity(lat_passes * n);
    for _ in 0..lat_passes {
        for i in 0..n {
            let t = Instant::now();
            std::hint::black_box(call(i));
            lat.push(t.elapsed().as_secs_f64() * 1e9);
        }
    }
    per_call.sort_by(|a, b| a.partial_cmp(b).unwrap());
    lat.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let mean = per_call.iter().sum::<f64>() / per_call.len() as f64;
    let (p10, p50, p90, p99) = if lat.is_empty() {
        (f64::NAN, f64::NAN, f64::NAN, f64::NAN)
    } else {
        (quantile(&lat, 0.10), quantile(&lat, 0.50), quantile(&lat, 0.90), quantile(&lat, 0.99))
    };
    (
        Stats {
            median: quantile(&per_call, 0.5),
            mean,
            min: per_call[0],
            max: *per_call.last().unwrap(),
            p10,
            p50,
            p90,
            p99,
            rounds,
            reps,
        },
        out,
    )
}

/// Effective core frequency in GHz: a chain of dependent 1-cycle adds (x86_64 only; 0.0 elsewhere).
pub fn freq_ghz() -> f64 {
    #[cfg(target_arch = "x86_64")]
    {
        let iters: u64 = 200_000_000;
        let mut best = 0.0f64;
        for _ in 0..5 {
            let mut x = 0u64;
            let mut k = iters;
            let t = Instant::now();
            unsafe {
                core::arch::asm!(
                    "2:",
                    "add {x}, 1", "add {x}, 1", "add {x}, 1", "add {x}, 1", "add {x}, 1",
                    "add {x}, 1", "add {x}, 1", "add {x}, 1", "add {x}, 1", "add {x}, 1",
                    "dec {k}",
                    "jnz 2b",
                    x = inout(reg) x,
                    k = inout(reg) k,
                );
            }
            let s = t.elapsed().as_secs_f64();
            std::hint::black_box((x, k));
            best = best.max(iters as f64 * 10.0 / s / 1e9);
        }
        best
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        0.0
    }
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap_or_default()
}

/// (steal jiffies, total jiffies) from /proc/stat.
pub fn steal() -> (u64, u64) {
    let s = read("/proc/stat");
    let line = s.lines().next().unwrap_or("");
    let v: Vec<u64> = line.split_whitespace().skip(1).filter_map(|x| x.parse().ok()).collect();
    (v.get(7).copied().unwrap_or(0), v.iter().sum())
}

/// Machine facts printed at the top of every run.
pub fn sysinfo() -> Vec<String> {
    let mut v = vec![];
    let cpu = read("/proc/cpuinfo");
    let model = cpu.lines().find(|l| l.starts_with("model name")).and_then(|l| l.split(':').nth(1)).unwrap_or("?").trim().to_string();
    let mhz = cpu.lines().find(|l| l.starts_with("cpu MHz")).and_then(|l| l.split(':').nth(1)).unwrap_or("?").trim().to_string();
    v.push(format!("cpu: {model} (reported {mhz} MHz)"));
    let st = read("/proc/self/status");
    let allowed = st.lines().find(|l| l.starts_with("Cpus_allowed_list")).and_then(|l| l.split(':').nth(1)).unwrap_or("?").trim().to_string();
    v.push(format!("cpus_allowed: {allowed}"));
    let stat = read("/proc/self/stat");
    let after = stat.rsplit(')').next().unwrap_or("");
    let proc_cpu = after.split_whitespace().nth(36).unwrap_or("?");
    v.push(format!("running on cpu: {proc_cpu}"));
    v.push(format!("loadavg: {}", read("/proc/loadavg").trim()));
    let (s, t) = steal();
    v.push(format!("steal jiffies: {s} of {t}"));
    v.push(format!("measured core clock: {:.2} GHz (dependent add chain)", freq_ghz()));
    v.push(format!("avx2: {}", cfg!(target_arch = "x86_64") && avx2()));
    v
}

pub fn avx2() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        std::is_x86_feature_detected!("avx2")
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        false
    }
}
