//! Deterministic cross-implementation driver.
//!
//! For each parameter set, N seeded random cases (ξ, rnd, message 0-2 KB, ctx lengths 0/1/255/256 and others,
//! deterministic and hedged signing) go through KeyGen, Sign and Sign_internal on every implementation (byte-for-
//! byte equality of pk, sk and σ) and through Verify and Verify_internal on the honest signature and on many mutated
//! inputs (verdicts must be equal). Then the malformed-key behavior table (informational) is produced.
//!
//! Exit status: 0 if there were no disagreements, 1 otherwise.
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;
use xc::check::{self, Disagreement, Plan, Stats};
use xc::oracle::{self, Imp};
use xc::set::ALL_SETS;
use xc::{undefined, Set};

struct Args {
    seed: u64,
    cases: u64,
    threads: usize,
    exhaustive: u64,
    sets: Vec<Set>,
    out: String,
    sig_flips: usize,
    pk_flips: usize,
    skip_sk: bool,
    only_sk: bool,
    only_wl: bool,
    sk_trials: usize,
    replay: Option<(Set, u64)>,
}

fn usage() -> ! {
    eprintln!(
        "usage: xcheck [--seed N] [--cases N] [--threads N] [--exhaustive N] [--sets 44,65,87] [--out DIR]\n\
         \x20             [--sig-flips N] [--pk-flips N] [--skip-sk] [--only-sk] [--only-wl] [--sk-trials N] [--replay SET IDX]\n\
         cases are per parameter set; --exhaustive N flips every bit of sigma and pk for the first N cases per set.\n\
         env: XC_NO_AVX2=1 drops the AVX2 backends."
    );
    std::process::exit(2)
}

fn parse() -> Args {
    let mut a = Args {
        seed: 0x5EED_0204,
        cases: 1000,
        threads: std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1),
        exhaustive: 0,
        sets: ALL_SETS.to_vec(),
        out: "xc-out".into(),
        sig_flips: 12,
        pk_flips: 4,
        skip_sk: false,
        only_sk: false,
        only_wl: false,
        sk_trials: 4,
        replay: None,
    };
    let mut it = std::env::args().skip(1);
    let num = |s: Option<String>| -> u64 { s.and_then(|x| x.parse().ok()).unwrap_or_else(|| usage()) };
    while let Some(arg) = it.next() {
        match arg.as_str() {
            "--seed" => a.seed = num(it.next()),
            "--cases" => a.cases = num(it.next()),
            "--threads" => a.threads = num(it.next()) as usize,
            "--exhaustive" => a.exhaustive = num(it.next()),
            "--sig-flips" => a.sig_flips = num(it.next()) as usize,
            "--pk-flips" => a.pk_flips = num(it.next()) as usize,
            "--sk-trials" => a.sk_trials = num(it.next()) as usize,
            "--skip-sk" => a.skip_sk = true,
            "--only-sk" => a.only_sk = true,
            "--only-wl" => a.only_wl = true,
            "--out" => a.out = it.next().unwrap_or_else(|| usage()),
            "--sets" => {
                a.sets = it
                    .next()
                    .unwrap_or_else(|| usage())
                    .split(',')
                    .map(|s| Set::from_level(s.trim().parse().unwrap_or(0)).unwrap_or_else(|| usage()))
                    .collect()
            }
            "--replay" => {
                let s = Set::from_level(num(it.next()) as u32).unwrap_or_else(|| usage());
                a.replay = Some((s, num(it.next())));
            }
            _ => usage(),
        }
    }
    a
}

fn report(d: &Disagreement, out_dir: &str, n: usize) {
    if n >= 200 {
        return;
    }
    let set = d.set.map(|s| s.name()).unwrap_or("?");
    if n < 12 {
        println!("DISAGREEMENT [{set}] case {} kind {} ({})\n  {}\n  {}", d.case_idx, d.kind, d.label, d.detail, d.repro);
    }
    let _ = std::fs::create_dir_all(out_dir);
    let path = format!("{out_dir}/disagree-{}-{}-{n}.txt", set, d.case_idx);
    let _ = std::fs::write(path, format!("{}\n{}\n{}\n{}\n{}\n", d.kind, d.label, d.detail, d.repro, d.dump));
}

/// Wrong-length pk / signature inputs, where an oracle API takes slices (only RustCrypto does): must be rejected.
/// Returns (checks, failures).
fn wrong_length(seed: u64, sets: &[Set]) -> (u64, u64) {
    let (mut n, mut bad) = (0u64, 0u64);
    for &set in sets {
        for idx in 0..100u64 {
            let case = xc::cases::make_case(seed, set, idx);
            let (pk, sk) = Imp::Ours.keygen(set, &case.xi);
            let Some(sig) = Imp::Ours.sign(set, &sk, &case.msg, &case.ctx[..case.ctx.len().min(255)], &case.rnd).sig().cloned() else { continue };
            let ctx = &case.ctx[..case.ctx.len().min(255)];
            let mut variants: Vec<(&str, Vec<u8>, Vec<u8>)> = vec![
                ("pk-1", pk[..pk.len() - 1].to_vec(), sig.clone()),
                ("pk+1", [&pk[..], &[0u8][..]].concat(), sig.clone()),
                ("pk empty", Vec::new(), sig.clone()),
                ("pk half", pk[..pk.len() / 2].to_vec(), sig.clone()),
                ("sig-1", pk.clone(), sig[..sig.len() - 1].to_vec()),
                ("sig+1", pk.clone(), [&sig[..], &[0u8][..]].concat()),
                ("sig empty", pk.clone(), Vec::new()),
                ("sig half", pk.clone(), sig[..sig.len() / 2].to_vec()),
            ];
            for other in ALL_SETS {
                if other != set {
                    variants.push(("pk of another level", xc::oracle::Imp::Ours.keygen(other, &case.xi).0, sig.clone()));
                    variants.push(("sig of another level length", pk.clone(), vec![0u8; other.sig_len()]));
                }
            }
            for (label, p, s) in variants {
                n += 1;
                if oracle::rc_verify_any_len(set, &p, &case.msg, ctx, &s) != Ok(false) {
                    bad += 1;
                    println!("WRONG-LENGTH DISAGREEMENT [{}] case {idx}: {label}: rustcrypto did not return reject", set.name());
                }
            }
        }
    }
    (n, bad)
}

fn main() {
    oracle::install_panic_hook(false);
    let a = parse();
    let imps = oracle::available();
    println!("implementations: {}", imps.iter().map(|i| i.name()).collect::<Vec<_>>().join(", "));
    if !imps.contains(&Imp::LibcruxAvx2) {
        println!("note: AVX2 backends not run (no AVX2 here or XC_NO_AVX2 set)");
    }

    if let Some((set, idx)) = a.replay {
        let plan = Plan { sig_flips: a.sig_flips, pk_flips: a.pk_flips, exhaustive_cases: a.exhaustive, keep: 100, light: false };
        let (mut st, mut out) = (Stats::default(), Vec::new());
        check::run_case(a.seed, set, idx, &imps, &plan, &mut st, &mut out);
        println!("replay {} case {idx}: {} verify cases, {} disagreements", set.name(), st.verify_cases, st.disagreements);
        for (n, d) in out.iter().enumerate() {
            report(d, &a.out, n);
        }
        std::process::exit(if st.disagreements == 0 { 0 } else { 1 });
    }

    let mut total = Stats::default();
    if a.only_wl {
        let (n, bad) = wrong_length(a.seed, &a.sets);
        println!("wrong-length inputs (rustcrypto, the only slice-taking oracle): {n} checks, {bad} failures");
        std::process::exit(if bad == 0 { 0 } else { 1 });
    }
    let mut all_dis: Vec<Disagreement> = Vec::new();
    if !a.only_sk {
        let t0 = Instant::now();
        for &set in &a.sets {
            let plan = Plan { sig_flips: a.sig_flips, pk_flips: a.pk_flips, exhaustive_cases: a.exhaustive, keep: 8, light: false };
            let next = AtomicU64::new(0);
            let done = AtomicU64::new(0);
            let merged = Mutex::new((Stats::default(), Vec::<Disagreement>::new()));
            let ts = Instant::now();
            std::thread::scope(|s| {
                for _ in 0..a.threads {
                    s.spawn(|| {
                        let (mut st, mut dis) = (Stats::default(), Vec::new());
                        loop {
                            let start = next.fetch_add(16, Ordering::Relaxed);
                            if start >= a.cases {
                                break;
                            }
                            for idx in start..(start + 16).min(a.cases) {
                                check::run_case(a.seed, set, idx, &imps, &plan, &mut st, &mut dis);
                                done.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                        let mut g = merged.lock().unwrap();
                        g.0.merge(&st);
                        g.1.extend(dis);
                    });
                }
                s.spawn(|| {
                    let mut last = Instant::now();
                    loop {
                        std::thread::sleep(std::time::Duration::from_millis(200));
                        let d = done.load(Ordering::Relaxed);
                        if d >= a.cases {
                            break;
                        }
                        if last.elapsed().as_secs() >= 30 {
                            last = Instant::now();
                            println!("  [{}] {d}/{} cases, {:.0}s", set.name(), a.cases, ts.elapsed().as_secs_f64());
                        }
                    }
                });
            });
            let (st, dis) = merged.into_inner().unwrap();
            println!(
                "{}: {} cases in {:.1}s: keygen results compared {} | signatures compared {} (sign calls {}, ctx>255 refusals {}) | verify cases {} (honest {}, calls {}, mutants accepted by all {}) | disagreements {}",
                set.name(), st.cases, ts.elapsed().as_secs_f64(), st.keygen_compared, st.sign_compared, st.sign_calls, st.ctx_refusals,
                st.verify_cases, st.honest_verify, st.verify_calls, st.mutants_accepted, st.disagreements
            );
            total.merge(&st);
            all_dis.extend(dis);
        }
        println!("\n== totals ({:.1}s) ==", t0.elapsed().as_secs_f64());
        println!(
            "sign cases {} | keygen results compared {} | signatures compared byte for byte {} | sign calls {} | verify cases {} (honest {}) | verify/verify_internal calls {} | mutants accepted by all implementations {} | disagreements {}",
            total.cases, total.keygen_compared, total.sign_compared, total.sign_calls, total.verify_cases, total.honest_verify, total.verify_calls, total.mutants_accepted, total.disagreements
        );
        println!("\n== verify cases per mutation class (tuples, accepted by every implementation, disagreements) ==");
        for (k, (n, acc, dis)) in &total.classes {
            println!("  {k}: {n}, accepted {acc}, disagreements {dis}");
        }
        for (n, d) in all_dis.iter().enumerate() {
            report(d, &a.out, n);
        }
    }

    if !a.only_sk {
        let (n, bad) = wrong_length(a.seed, &a.sets);
        println!("\nwrong-length inputs (rustcrypto, the only slice-taking oracle): {n} checks, {bad} failures");
        total.disagreements += bad;
    }

    if !a.skip_sk {
        println!("\n== malformed secret keys (informational; FIPS 204 leaves Sign undefined here) ==");
        for &set in &a.sets {
            println!("\n{} ({} trials per variant; deterministic Sign, empty ctx; outcome vs ours)", set.name(), a.sk_trials);
            let rows = undefined::run(set, &imps, a.sk_trials, a.seed, 120);
            println!("| variant | ours sk_is_well_formed | mldsa-native pk_from_sk | ours pk_from_sk | {} |", imps.iter().map(|i| i.name()).collect::<Vec<_>>().join(" | "));
            println!("|---|---|---|---|{}", "---|".repeat(imps.len()));
            let mut panics: std::collections::BTreeSet<String> = Default::default();
            for r in &rows {
                for (ii, o) in r.outcomes.iter().enumerate() {
                    for x in o {
                        if let undefined::Outcome::Panic(m) = x {
                            panics.insert(format!("{}: {}", imps[ii].name(), m.chars().take(160).collect::<String>()));
                        }
                    }
                }
                println!(
                    "| {} | {} | {} | {} | {} |",
                    r.variant,
                    r.ours_well_formed,
                    r.mldsa_validate,
                    r.ours_pk_from_sk,
                    r.outcomes.iter().map(|o| undefined::summarize(o)).collect::<Vec<_>>().join(" | ")
                );
            }
            for p in &panics {
                println!("  panic message, {p}");
            }
            let bad: Vec<&str> = rows.iter().filter(|r| !r.pk_from_sk_agrees).map(|r| r.variant.as_str()).collect();
            println!("  pk_from_sk vs mldsa-native: {} of {} variants agree{}", rows.len() - bad.len(), rows.len(),
                if bad.is_empty() { String::new() } else { format!(" (DISAGREE: {})", bad.join(", ")) });
        }
    }

    if !a.only_sk {
        println!("\nRESULT: {} disagreements", total.disagreements);
        std::process::exit(if total.disagreements == 0 { 0 } else { 1 });
    }
}
