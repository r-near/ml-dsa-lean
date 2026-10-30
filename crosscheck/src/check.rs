//! Running cases through every implementation and collecting disagreements.
//!
//! A *verify case* is one tuple (pk, m, ctx, sig) evaluated by every implementation through Verify and, when
//! |ctx| <= 255, Verify_internal on M′; all verdicts must be equal. A *sign check* compares KeyGen, Sign and
//! Sign_internal output byte for byte.
use crate::cases::{self, Case, Mutant, Rng};
use crate::oracle::{Imp, SignRes, Verdict, build_mp};
use crate::Set;
use std::collections::BTreeMap;
use std::fmt::Write as _;

pub fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        let _ = write!(s, "{x:02x}");
    }
    s
}

// ---------------------------------------------------------------------------------------------
// Statistics
// ---------------------------------------------------------------------------------------------

#[derive(Default, Clone, Debug)]
pub struct Stats {
    /// Sign cases (one ξ, message, ctx, rnd).
    pub cases: u64,
    /// Per-implementation keygen results compared with ours (pk and sk each), incl. mldsa-native `keypair`.
    pub keygen_compared: u64,
    /// Signatures compared byte for byte with ours: Sign and Sign_internal, per implementation.
    pub sign_compared: u64,
    /// Sign calls made in total (all implementations, both entry points).
    pub sign_calls: u64,
    /// Cases in which the oracles refused to sign because |ctx| > 255 (all had to refuse).
    pub ctx_refusals: u64,
    /// Verify tuples (each evaluated by every implementation).
    pub verify_cases: u64,
    /// Honest tuples among them (must be accepted everywhere).
    pub honest_verify: u64,
    /// Individual Verify / Verify_internal calls made.
    pub verify_calls: u64,
    /// Tuples on which all implementations agreed to accept although the input was mutated.
    pub mutants_accepted: u64,
    /// Per mutation class: (tuples, accepted-by-all, disagreements).
    pub classes: BTreeMap<String, (u64, u64, u64)>,
    pub disagreements: u64,
}

impl Stats {
    pub fn merge(&mut self, o: &Stats) {
        self.cases += o.cases;
        self.keygen_compared += o.keygen_compared;
        self.sign_compared += o.sign_compared;
        self.sign_calls += o.sign_calls;
        self.ctx_refusals += o.ctx_refusals;
        self.verify_cases += o.verify_cases;
        self.honest_verify += o.honest_verify;
        self.verify_calls += o.verify_calls;
        self.mutants_accepted += o.mutants_accepted;
        self.disagreements += o.disagreements;
        for (k, v) in &o.classes {
            let e = self.classes.entry(k.clone()).or_default();
            e.0 += v.0;
            e.1 += v.1;
            e.2 += v.2;
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Disagreements
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug, Default)]
pub struct Disagreement {
    pub set: Option<Set>,
    pub case_idx: u64,
    /// "keygen", "sign", "sign_internal", "verify", "honest-verify"
    pub kind: String,
    pub label: String,
    pub detail: String,
    /// Minimized reproduction, short: byte edits relative to the honest values, lengths.
    pub repro: String,
    /// The same inputs in full as hex (goes to the output file, not the console).
    pub dump: String,
}

fn fmt_verdicts(rows: &[(Imp, &'static str, Verdict)]) -> String {
    rows.iter().map(|(i, k, v)| format!("{}.{}={}{}", i.name(), k, v.ok, if v.why.is_empty() { String::new() } else { format!("({})", v.why) })).collect::<Vec<_>>().join(" ")
}

// ---------------------------------------------------------------------------------------------
// Verify tuples
// ---------------------------------------------------------------------------------------------

/// Result of evaluating one tuple everywhere.
pub struct TupleOut {
    /// None: all agree. Some(description): disagreement.
    pub mismatch: Option<String>,
    /// Ours (Verify) and ours (Verify_internal), valid when no mismatch.
    pub verdict: bool,
    pub verdict_int: bool,
    pub calls: u64,
}

/// Evaluates (pk, m, ctx, sig) with every implementation. Verify verdicts must all be equal; Verify_internal verdicts
/// (on M′ = 0‖|ctx|‖ctx‖m, or ctx‖m when |ctx| > 255) must all be equal; for |ctx| <= 255 the two must coincide.
/// For |ctx| > 255 Verify must reject everywhere.
pub fn eval_tuple(set: Set, imps: &[Imp], pk: &[u8], m: &[u8], ctx: &[u8], sig: &[u8], split: usize) -> TupleOut {
    let mp = build_mp(ctx, m).unwrap_or_else(|| [ctx, m].concat());
    let mut rows: Vec<(Imp, &'static str, Verdict)> = Vec::with_capacity(imps.len() * 2);
    for &i in imps {
        rows.push((i, "verify", i.verify(set, pk, m, ctx, sig)));
        rows.push((i, "internal", i.verify_internal(set, pk, &mp, split, sig)));
    }
    let calls = rows.len() as u64;
    let ours_ext = rows[0].2.ok;
    let ours_int = rows[1].2.ok;
    let ext_ok = rows.iter().filter(|r| r.1 == "verify").all(|r| r.2.ok == ours_ext);
    let int_ok = rows.iter().filter(|r| r.1 == "internal").all(|r| r.2.ok == ours_int);
    let link_ok = if ctx.len() <= 255 { ours_ext == ours_int } else { !ours_ext };
    let panicked = rows.iter().any(|r| r.2.why == "PANIC");
    let mismatch = if ext_ok && int_ok && link_ok && !panicked { None } else { Some(fmt_verdicts(&rows)) };
    TupleOut { mismatch, verdict: ours_ext, verdict_int: ours_int, calls }
}

fn class_of(label: &str) -> String {
    let l = label.split(" byte").next().unwrap_or(label);
    l.to_string()
}

// ---------------------------------------------------------------------------------------------
// Minimization
// ---------------------------------------------------------------------------------------------

/// Shrinks a verify mutant while the implementations keep disagreeing: first the message and context, then the
/// edits relative to the honest signature and key, one byte at a time.
pub fn minimize_verify(set: Set, imps: &[Imp], honest_pk: &[u8], honest_sig: &[u8], mut m: Mutant, split: usize) -> Mutant {
    let dis = |x: &Mutant| eval_tuple(set, imps, &x.pk, &x.msg, &x.ctx, &x.sig, split).mismatch.is_some();
    if !dis(&m) {
        return m;
    }
    for (msg, ctx) in [(Vec::new(), Vec::new()), (Vec::new(), m.ctx.clone()), (m.msg.clone(), Vec::new())] {
        let t = Mutant { msg, ctx, ..m.clone() };
        if dis(&t) {
            m = t;
            break;
        }
    }
    for i in 0..m.sig.len() {
        if m.sig[i] != honest_sig[i] {
            let t = Mutant { sig: { let mut s = m.sig.clone(); s[i] = honest_sig[i]; s }, ..m.clone() };
            if dis(&t) {
                m = t;
            }
        }
    }
    for i in 0..m.pk.len() {
        if m.pk[i] != honest_pk[i] {
            let t = Mutant { pk: { let mut p = m.pk.clone(); p[i] = honest_pk[i]; p }, ..m.clone() };
            if dis(&t) {
                m = t;
            }
        }
    }
    m
}

fn edits(honest: &[u8], x: &[u8]) -> String {
    let d: Vec<String> = honest.iter().zip(x).enumerate().filter(|(_, (a, b))| a != b).map(|(i, (a, b))| format!("{i}:{a:02x}->{b:02x}")).collect();
    if d.is_empty() { "none".into() } else { d.join(",") }
}

fn verify_repro(case_idx: u64, honest_pk: &[u8], honest_sig: &[u8], min: &Mutant, split: usize) -> (String, String) {
    (
        format!(
            "case {case_idx}; minimized: sig edits vs honest signature [{}], pk edits vs honest pk [{}], |msg|={}, |ctx|={}, split={split}",
            edits(honest_sig, &min.sig),
            edits(honest_pk, &min.pk),
            min.msg.len(),
            min.ctx.len(),
        ),
        format!("pk  = {}\nsig = {}\nmsg = {}\nctx = {}", hex(&min.pk), hex(&min.sig), hex(&min.msg), hex(&min.ctx)),
    )
}

// ---------------------------------------------------------------------------------------------
// Sign checks
// ---------------------------------------------------------------------------------------------

/// What a case produced for the verify stage.
pub struct SignOut {
    pub pk: Vec<u8>,
    pub sk: Vec<u8>,
    /// Honest signature (Sign_internal on M′; equals Sign's for |ctx| <= 255). None if ours refused.
    pub sig: Option<Vec<u8>>,
    pub mismatches: Vec<(String, String)>,
}

/// KeyGen, Sign and Sign_internal on `case` with every implementation; mismatches against ours.
pub fn sign_checks(case: &Case, imps: &[Imp], stats: &mut Stats) -> SignOut {
    let set = case.set;
    let mut mism: Vec<(String, String)> = Vec::new();
    let (pk, sk) = Imp::Ours.keygen(set, &case.xi);
    for &i in &imps[1..] {
        let (p, s) = i.keygen(set, &case.xi);
        stats.keygen_compared += 1;
        if p != pk {
            mism.push(("keygen".into(), format!("{}: pk differs from ours", i.name())));
        }
        if s != sk {
            mism.push(("keygen".into(), format!("{}: sk differs from ours", i.name())));
        }
        if let Some((p, s)) = i.keygen_alt(set, &case.xi) {
            stats.keygen_compared += 1;
            if p != pk || s != sk {
                mism.push(("keygen".into(), format!("{}: randomized keypair() differs from ours", i.name())));
            }
        }
    }
    let mp = build_mp(&case.ctx, &case.msg).unwrap_or_else(|| [&case.ctx[..], &case.msg[..]].concat());
    // Sign_internal on M′.
    let ours_int = Imp::Ours.sign_internal(set, &sk, &mp, case.split, &case.rnd);
    stats.sign_calls += 1;
    for &i in &imps[1..] {
        let r = i.sign_internal(set, &sk, &mp, case.split, &case.rnd);
        stats.sign_calls += 1;
        stats.sign_compared += 1;
        if !r.same(&ours_int) || matches!(r, SignRes::Panic(_)) {
            mism.push(("sign_internal".into(), format!("{}: {} vs ours {}", i.name(), describe(&r), describe(&ours_int))));
        }
    }
    // Sign with ctx.
    let ours_ext = Imp::Ours.sign(set, &sk, &case.msg, &case.ctx, &case.rnd);
    stats.sign_calls += 1;
    if case.ctx.len() > 255 {
        stats.ctx_refusals += 1;
        if !matches!(ours_ext, SignRes::NoSig(_)) {
            mism.push(("sign".into(), format!("ours signed with |ctx| = {}", case.ctx.len())));
        }
    } else if !ours_ext.same(&ours_int) {
        mism.push(("sign".into(), "ours: Sign differs from Sign_internal on M'".into()));
    }
    for &i in &imps[1..] {
        let r = i.sign(set, &sk, &case.msg, &case.ctx, &case.rnd);
        stats.sign_calls += 1;
        stats.sign_compared += 1;
        if !r.same(&ours_ext) || matches!(r, SignRes::Panic(_)) {
            mism.push(("sign".into(), format!("{}: {} vs ours {}", i.name(), describe(&r), describe(&ours_ext))));
        }
    }
    let sig = ours_int.sig().cloned();
    if sig.is_none() {
        mism.push(("sign_internal".into(), format!("ours did not sign: {}", describe(&ours_int))));
    }
    SignOut { pk, sk, sig, mismatches: mism }
}

fn describe(r: &SignRes) -> String {
    match r {
        SignRes::Sig(s) => format!("sig({} bytes, {})", s.len(), &hex(&s[..8.min(s.len())])),
        SignRes::NoSig(e) => format!("error({e})"),
        SignRes::Panic(e) => format!("PANIC({e})"),
    }
}

/// Shrinks a sign-side disagreement: message and context to the shortest that still disagrees.
pub fn minimize_case(case: &Case, imps: &[Imp]) -> Case {
    let dis = |c: &Case| {
        let mut st = Stats::default();
        !sign_checks(c, imps, &mut st).mismatches.is_empty()
    };
    let mut best = Case { set: case.set, idx: case.idx, xi: case.xi, rnd: case.rnd, hedged: case.hedged, msg: case.msg.clone(), ctx: case.ctx.clone(), split: case.split };
    for ctx in [Vec::new(), best.ctx.clone()] {
        let t = Case { ctx, msg: best.msg.clone(), split: 0, ..clone_head(&best) };
        if dis(&t) {
            best = t;
            break;
        }
    }
    loop {
        let n = best.msg.len();
        if n == 0 {
            break;
        }
        let mut progressed = false;
        for len in [0, n / 2, n - 1] {
            if len >= n {
                continue;
            }
            let t = Case { msg: best.msg[..len].to_vec(), ctx: best.ctx.clone(), split: 0, ..clone_head(&best) };
            if dis(&t) {
                best = t;
                progressed = true;
                break;
            }
        }
        if !progressed {
            break;
        }
    }
    best
}

fn clone_head(c: &Case) -> Case {
    Case { set: c.set, idx: c.idx, xi: c.xi, rnd: c.rnd, hedged: c.hedged, msg: Vec::new(), ctx: Vec::new(), split: c.split }
}

// ---------------------------------------------------------------------------------------------
// One case, end to end
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Plan {
    /// Random signature bit flips per case, spread over c̃, z, hint positions, hint counts, anywhere.
    pub sig_flips: usize,
    /// Random public-key bit flips per case.
    pub pk_flips: usize,
    /// Run every single-bit flip of σ and pk for cases with idx < this.
    pub exhaustive_cases: u64,
    /// Max disagreements to minimize and keep per call.
    pub keep: usize,
    /// Fewer mutants per case (fuzz targets, where executions per second matter).
    pub light: bool,
}

impl Default for Plan {
    fn default() -> Plan {
        Plan { sig_flips: 12, pk_flips: 4, exhaustive_cases: 0, keep: 8, light: false }
    }
}

pub fn run_case(master: u64, set: Set, idx: u64, imps: &[Imp], plan: &Plan, stats: &mut Stats, out: &mut Vec<Disagreement>) {
    let case = cases::make_case(master, set, idx);
    let mut r = Rng::for_case(master ^ 0x5151_5151, set, idx);
    run_given(&case, &mut r, imps, plan, stats, out);
}

/// Runs an explicit case (fuzz targets build theirs from the input bytes); `r` drives the mutations.
pub fn run_given(case: &Case, r: &mut Rng, imps: &[Imp], plan: &Plan, stats: &mut Stats, out: &mut Vec<Disagreement>) {
    let (set, idx) = (case.set, case.idx);
    stats.cases += 1;
    let so = sign_checks(case, imps, stats);
    if !so.mismatches.is_empty() {
        stats.disagreements += so.mismatches.len() as u64;
        if out.len() < plan.keep {
            let min = minimize_case(case, imps);
            for (kind, detail) in &so.mismatches {
                out.push(Disagreement {
                    set: Some(set),
                    case_idx: idx,
                    kind: kind.clone(),
                    label: "sign case".into(),
                    detail: detail.clone(),
                    repro: format!(
                        "xi={} rnd={} hedged={} |msg|={} (minimized {}) |ctx|={} (minimized {}) split={}",
                        hex(&case.xi), hex(&case.rnd), case.hedged, case.msg.len(), min.msg.len(), case.ctx.len(), min.ctx.len(), case.split
                    ),
                    dump: format!("msg(min) = {}\nctx(min) = {}", hex(&min.msg), hex(&min.ctx)),
                });
            }
        }
    }
    let Some(sig) = so.sig else { return };

    let tuple = |m: &Mutant, honest: bool, stats: &mut Stats, out: &mut Vec<Disagreement>| {
        let t = eval_tuple(set, imps, &m.pk, &m.msg, &m.ctx, &m.sig, case.split);
        stats.verify_cases += 1;
        stats.verify_calls += t.calls;
        let cl = class_of(&m.label);
        let e = stats.classes.entry(cl).or_default();
        e.0 += 1;
        let bad_honest = honest && t.mismatch.is_none() && !(t.verdict_int && (t.verdict || case.ctx.len() > 255));
        if honest {
            stats.honest_verify += 1;
        }
        if let Some(d) = &t.mismatch {
            stats.disagreements += 1;
            stats.classes.get_mut(&class_of(&m.label)).unwrap().2 += 1;
            if out.len() < plan.keep {
                let min = minimize_verify(set, imps, &so.pk, &sig, m.clone(), case.split);
                let (repro, dump) = verify_repro(idx, &so.pk, &sig, &min, case.split);
                out.push(Disagreement {
                    set: Some(set),
                    case_idx: idx,
                    kind: if honest { "honest-verify".into() } else { "verify".into() },
                    label: m.label.clone(),
                    detail: d.clone(),
                    repro,
                    dump,
                });
            }
        } else if bad_honest {
            stats.disagreements += 1;
            out.push(Disagreement { set: Some(set), case_idx: idx, kind: "honest-verify".into(), label: m.label.clone(), detail: "all implementations reject an honest signature".into(), repro: String::new(), dump: String::new() });
        } else if !honest && (t.verdict || t.verdict_int) {
            // Every implementation accepts a mutated input: not a disagreement, but it is counted and reported.
            stats.mutants_accepted += 1;
            stats.classes.get_mut(&class_of(&m.label)).unwrap().1 += 1;
        }
    };

    let honest = Mutant { label: "honest".into(), pk: so.pk.clone(), sig: sig.clone(), msg: case.msg.clone(), ctx: case.ctx.clone() };
    tuple(&honest, true, stats, out);

    for m in cases::mutants(set, &so.pk, &sig, &case.msg, &case.ctx, r, plan.sig_flips, plan.pk_flips, plan.light) {
        tuple(&m, false, stats, out);
    }
    if idx < plan.exhaustive_cases {
        for m in cases::exhaustive_flips(set, &so.pk, &sig, &case.msg, &case.ctx) {
            tuple(&m, false, stats, out);
        }
    }
}
