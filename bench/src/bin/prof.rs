//! Sampling profile of the public APIs with pprof's SIGPROF sampler (perf is not usable in the measured environment: unprivileged
//! users get perf_event_paranoid=4). Writes one folded-stack file per workload (`root;...;leaf count`, inlined
//! frames expanded from the DWARF line tables), which bench/categorize.py turns into a breakdown.
//!
//! Usage: prof OUTDIR [--secs N] [--impl a,b] [--sets 44,65,87] [--ops sign-det,verify,keygen]
//! Implementation names are those of the bench output: ours, rustcrypto, libcrux-portable, libcrux-avx2,
//! mldsa-native-portable, mldsa-native-avx2. Build with `--profile profiling --features prof` so symbols exist.
use ml_dsa_bench::cells::*;
use ml_dsa_bench::*;
use std::io::Write;
use std::time::{Duration, Instant};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out = args.get(1).expect("usage: prof OUTDIR [options]").clone();
    let opt = |name: &str| args.iter().position(|a| a == name).and_then(|i| args.get(i + 1)).cloned();
    let secs: f64 = opt("--secs").map(|s| s.parse().unwrap()).unwrap_or(20.0);
    let list = |name: &str, default: &str| -> Vec<String> { opt(name).unwrap_or(default.to_string()).split(',').map(String::from).collect() };
    let imps = list("--impl", "ours,libcrux-portable");
    let sets: Vec<u32> = list("--sets", "44,65,87").iter().map(|s| s.parse().unwrap()).collect();
    let ops = list("--ops", "sign-det,verify,keygen");
    let freq: i32 = opt("--freq").map(|s| s.parse().unwrap()).unwrap_or(1000);
    std::fs::create_dir_all(&out).unwrap();

    println!("# prof: secs={secs} freq={freq}");
    for l in sysinfo() {
        println!("# {l}");
    }
    for &set in &sets {
        let d = build_set(set);
        let mut cells = cells_for(set, &d);
        for c in cells.iter_mut() {
            if !imps.contains(&c.imp) || !ops.iter().any(|o| o == c.group) {
                continue;
            }
            // warm up, then profile for `secs`
            for i in 0..c.n {
                std::hint::black_box((c.f)(i));
            }
            let guard = pprof::ProfilerGuardBuilder::default()
                .frequency(freq)
                .blocklist(&["libgcc", "pthread", "vdso"])
                .build()
                .unwrap();
            let t = Instant::now();
            let mut calls = 0u64;
            while t.elapsed() < Duration::from_secs_f64(secs) {
                for i in 0..c.n {
                    std::hint::black_box((c.f)(i));
                    calls += 1;
                }
            }
            let wall = t.elapsed().as_secs_f64();
            let report = guard.report().build().unwrap();
            drop(guard);
            let path = format!("{out}/{}.{}.{}.folded", c.imp, set, c.group);
            let mut f = std::fs::File::create(&path).unwrap();
            let mut total = 0isize;
            for (frames, count) in report.data.iter() {
                // frames.frames: leaf first, each frame expands to its inlined symbols (innermost first)
                let mut names: Vec<String> = vec![];
                for fr in &frames.frames {
                    for s in fr {
                        names.push(s.name());
                    }
                }
                names.reverse();
                writeln!(f, "{} {}", names.join(";"), count).unwrap();
                total += count;
            }
            println!("PROF\t{set}\t{}\t{}\t{total} samples\t{calls} calls\t{:.1} us/call\t{path}", c.imp, c.group, wall * 1e6 / calls as f64);
        }
    }
}
