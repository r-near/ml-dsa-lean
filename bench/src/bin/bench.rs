//! Timing of keygen, sign (deterministic and hedged) and verify for ML-DSA-44/65/87:
//! this crate (public `api` only), RustCrypto `ml-dsa`, libcrux-ml-dsa (portable, AVX2) and mldsa-native
//! (C portable, AVX2). Run it pinned (`taskset -c N`) on an otherwise idle machine; see docs/performance-baseline.md.
//!
//! Every implementation gets the same inputs. The crosscheck harness has shown that all of them produce
//! byte-identical keys and signatures, so the rejection loop runs the same number of attempts everywhere and
//! signing differences are implementation speed. The first pass over each cell checks that outputs agree.
//!
//! Options: --rounds N (default 15) --lat N (per-call latency passes, default 3) --sets 44,65,87 --only SUBSTR
//!          --label TEXT

use ml_dsa_bench::cells::*;
use ml_dsa_bench::*;
use std::collections::HashMap;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let opt = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned();
    let rounds: usize = opt("--rounds").map(|s| s.parse().unwrap()).unwrap_or(15);
    let lat: usize = opt("--lat").map(|s| s.parse().unwrap()).unwrap_or(3);
    let sets: Vec<u32> = opt("--sets").map(|s| s.split(',').map(|x| x.parse().unwrap()).collect()).unwrap_or(vec![44, 65, 87]);
    let only = opt("--only");
    let label = opt("--label").unwrap_or_default();

    println!("# bench label: {label}");
    println!("# build: opt-level={} debug_assertions={} target_cpu_native_flag={}", env!("BENCH_OPT"), cfg!(debug_assertions), env!("BENCH_RUSTFLAGS"));
    for l in sysinfo() {
        println!("# {l}");
    }
    println!("# inputs: {NMSG} messages of {MSG_LEN} bytes, empty ctx, {NSEED} keygen seeds, one key pair per set; rounds={rounds} lat_passes={lat}");
    println!("ROW\tlabel\tset\top\timpl\tmedian_ns\tmean_ns\tmin_ns\tmax_ns\tcall_p10\tcall_p50\tcall_p90\tcall_p99\trounds\treps\tn");

    let (steal0, tot0) = steal();
    for &set in &sets {
        let d = build_set(set);
        let mut cells = cells_for(set, &d);
        let mut expect: HashMap<&'static str, (String, Vec<u64>)> = HashMap::new();
        for c in cells.iter_mut() {
            let name = format!("{} {}", c.imp, c.group);
            if let Some(o) = &only {
                if !name.contains(o.as_str()) {
                    continue;
                }
            }
            let (st, out) = measure(c.n, rounds, lat, 0.3, 0.12, &mut *c.f);
            match expect.get(c.group) {
                None => {
                    expect.insert(c.group, (c.imp.clone(), out));
                }
                Some((first, e)) => {
                    // rustcrypto's keygen returns the same bytes; every group must agree entry for entry
                    assert!(*e == out, "ML-DSA-{set} {}: {} disagrees with {first}", c.group, c.imp);
                }
            }
            println!(
                "ROW\t{label}\t{set}\t{}\t{}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{:.1}\t{}\t{}\t{}",
                c.group, c.imp, st.median, st.mean, st.min, st.max, st.p10, st.p50, st.p90, st.p99, st.rounds, st.reps, c.n
            );
            eprintln!("ML-DSA-{set} {name}: {:.1} us", st.median / 1e3);
        }
    }
    let (steal1, tot1) = steal();
    println!("# steal jiffies during run: {} of {}", steal1 - steal0, tot1 - tot0);
    println!("# loadavg at end: {}", std::fs::read_to_string("/proc/loadavg").unwrap_or_default().trim());
    println!("# measured core clock at end: {:.2} GHz", freq_ghz());
}
