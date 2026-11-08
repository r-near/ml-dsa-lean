//! One cell of the stack-offset scan (`bench/stackscan.sh`): the median time of ONE ML-DSA-`set` operation in a process
//! whose environment the driver has padded, so that the stack starts at a different offset. Prints one line:
//!   `SCAN <set> <op> <median_ns> <min_ns> <max_ns> <sp_mod_4096>`
//! where `sp_mod_4096` is the address of a local of `main` modulo 4096 (with ASLR off it is a function of the padding).
//! Options: --set 44|65|87  --op verify|vk|prepared  --rounds N (default 9)  --calls N (calls per round, default 200)
use ml_dsa_bench::Rng;
use ml_dsa_lean::api;
use std::time::Instant;

macro_rules! run {
    ($kg:ident, $sg:ident, $vf:ident, $vkf:ident, $vpf:ident, $pk:literal, $sig:literal, $op:expr, $rounds:expr, $calls:expr) => {{
        let mut r = Rng::new("inputs", 7);
        let seed: [u8; 32] = r.bytes();
        let (pk, sk) = api::$kg(&seed);
        let msgs: Vec<[u8; 64]> = (0..8).map(|_| r.bytes::<64>()).collect();
        let sigs: Vec<[u8; $sig]> = msgs.iter().map(|m| api::$sg(&sk, m, b"", &[0u8; 32]).unwrap()).collect();
        let vk = Box::new(api::$vkf(&pk));
        let mut acc = 0u64;
        let mut times = Vec::new();
        for round in 0..($rounds + 2) {
            let t = Instant::now();
            for i in 0..$calls {
                let j = i & 7;
                match $op {
                    "verify" => acc ^= api::$vf(std::hint::black_box(&pk), &msgs[j], b"", &sigs[j]) as u64,
                    "vk" => { std::hint::black_box(api::$vkf(std::hint::black_box(&pk))); acc ^= 1 },
                    _ => acc ^= api::$vpf(&vk, &msgs[j], b"", &sigs[j]) as u64,
                }
            }
            let ns = t.elapsed().as_secs_f64() * 1e9 / $calls as f64;
            if round >= 2 {
                times.push(ns);
            }
        }
        std::hint::black_box(acc);
        times
    }};
}

/// Part of the diagnosis (needs `internals` and `avx2`): the 4-way permutation alone, 100 per call, on a state at byte
/// offset `off` of an 8 KiB-aligned heap buffer (`k4`); the 4-way ExpandA of the set (`expanda`); and `tr = H(pk, 64)`
/// as `verify::hash_pk` computes it, with the set's public key length (`hashpk`; it needs no AVX2).
#[cfg(all(feature = "internals", feature = "avx2"))]
fn diag(op: &str, set: u32, off: usize, rounds: usize, calls: usize) -> Vec<f64> {
    use ml_dsa_lean::fast_verify::expand_a_x4_avx2_or_none;
    use ml_dsa_lean::keccak4::avx2_checked;
    // 8 KiB-aligned heap buffer, allocated directly (a `Box<Buf>` with `repr(align(8192))` is built on the stack first, which
    // realigns main's frame and freezes the stack offset this scan is varying).
    let layout = std::alloc::Layout::from_size_align(8192, 8192).unwrap();
    let base = unsafe { std::alloc::alloc(layout) };
    for i in 0..8192 {
        unsafe { base.add(i).write((i * 31) as u8) };
    }
    let rho = [7u8; 32];
    let mut times = Vec::new();
    for round in 0..(rounds + 2) {
        let t = Instant::now();
        for _ in 0..calls {
            match op {
                "hashpk" => {
                    let n = match set { 44 => 1312, 65 => 1952, _ => 2592 };
                    let pkb = [0x5au8; 2592];
                    let mut tr = [0u8; 64];
                    let mut h = ml_dsa_lean::keccak::Shake::shake256();
                    h.absorb(std::hint::black_box(&pkb[..n]));
                    h.finalize();
                    h.squeeze(&mut tr);
                    std::hint::black_box(tr);
                }
                "k4" => {
                    let s: &mut [[u64; 4]; 25] = unsafe { &mut *(base.add(off) as *mut [[u64; 4]; 25]) };
                    for _ in 0..100 {
                        assert!(avx2_checked::keccak_f1600_x4(s));
                    }
                }
                _ => match set {
                    44 => drop(std::hint::black_box(expand_a_x4_avx2_or_none::<4, 4>(std::hint::black_box(&rho)))),
                    65 => drop(std::hint::black_box(expand_a_x4_avx2_or_none::<6, 5>(std::hint::black_box(&rho)))),
                    _ => drop(std::hint::black_box(expand_a_x4_avx2_or_none::<8, 7>(std::hint::black_box(&rho)))),
                },
            }
        }
        let ns = t.elapsed().as_secs_f64() * 1e9 / calls as f64;
        if round >= 2 {
            times.push(ns);
        }
    }
    times
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let opt = |n: &str| args.iter().position(|a| a == n).and_then(|i| args.get(i + 1)).cloned();
    let set: u32 = opt("--set").map(|s| s.parse().unwrap()).unwrap_or(65);
    let op = opt("--op").unwrap_or_else(|| "verify".into());
    let rounds: usize = opt("--rounds").map(|s| s.parse().unwrap()).unwrap_or(9);
    let calls: usize = opt("--calls").map(|s| s.parse().unwrap()).unwrap_or(200);
    #[cfg_attr(not(all(feature = "internals", feature = "avx2")), allow(unused_variables))]
    let off: usize = opt("--off").map(|s| s.parse().unwrap()).unwrap_or(0);
    let marker = 0u8;
    let sp = (std::hint::black_box(&marker) as *const u8 as usize) & 0xfff;
    let op_s: &str = &op;
    #[cfg(all(feature = "internals", feature = "avx2"))]
    if op == "k4" || op == "expanda" || op == "hashpk" {
        let mut times = diag(&op, set, off, rounds, calls);
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        println!("SCAN {set} {op} {:.0} {:.0} {:.0} {sp}", times[times.len() / 2], times[0], times[times.len() - 1]);
        return;
    }
    let mut times = match set {
        44 => run!(keygen_44, sign_44, verify_44, verifying_key_44, verify_prepared_44, 1312, 2420, op_s, rounds, calls),
        65 => run!(keygen_65, sign_65, verify_65, verifying_key_65, verify_prepared_65, 1952, 3309, op_s, rounds, calls),
        _ => run!(keygen_87, sign_87, verify_87, verifying_key_87, verify_prepared_87, 2592, 4627, op_s, rounds, calls),
    };
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("SCAN {set} {op} {:.0} {:.0} {:.0} {sp}", times[times.len() / 2], times[0], times[times.len() - 1]);
}
