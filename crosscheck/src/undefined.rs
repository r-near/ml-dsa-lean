//! Behavior that FIPS 204 leaves undefined: signing with a secret key that skDecode (Algorithm 25) can decode
//! but that is not a key KeyGen could have produced (s1 or s2 outside [−η, η], t0 or tr inconsistent, garbage).
//! Informational only: nothing here is a disagreement. The table records what each implementation does.
use crate::cases::Rng;
use crate::oracle::{self, Imp, SignRes};
use crate::Set;
use std::sync::mpsc;
use std::time::Duration;

/// Packed width of an s1/s2 coefficient field in bits and the out-of-range code used (all ones).
fn field_bits(set: Set) -> usize {
    if set.eta() == 2 { 3 } else { 4 }
}

/// Overwrites coefficient field `c` (0..256) of the polynomial starting at byte `poly_start` with the all-ones
/// code, which decodes to η − code < −η.
fn set_field_oob(sk: &mut [u8], set: Set, poly_start: usize, c: usize) {
    let bits = field_bits(set);
    let bit0 = c * bits;
    for b in 0..bits {
        let pos = bit0 + b;
        sk[poly_start + pos / 8] |= 1 << (pos % 8);
    }
}

pub fn variants(set: Set, sk: &[u8], r: &mut Rng) -> Vec<(String, Vec<u8>)> {
    let ep = set.eta_poly_bytes();
    let (s1, s2, t0) = (set.sk_s1_start(), set.sk_s2_start(), set.sk_t0_start());
    let mut v: Vec<(String, Vec<u8>)> = Vec::new();
    let mut add = |name: &str, f: &dyn Fn(&mut Vec<u8>)| {
        let mut k = sk.to_vec();
        f(&mut k);
        v.push((name.to_string(), k));
    };
    add("baseline (valid key)", &|_| {});
    add("s1[0][0] out of range", &|k| set_field_oob(k, set, s1, 0));
    add("s1[L-1][255] out of range", &|k| set_field_oob(k, set, s1 + (set.l() - 1) * ep, 255));
    add("s2[0][0] out of range", &|k| set_field_oob(k, set, s2, 0));
    add("s2[K-1][255] out of range", &|k| set_field_oob(k, set, s2 + (set.k() - 1) * ep, 255));
    add("s1 all fields out of range", &|k| {
        for b in &mut k[s1..s2] {
            *b = 0xFF;
        }
    });
    add("s2 all fields out of range", &|k| {
        for b in &mut k[s2..t0] {
            *b = 0xFF;
        }
    });
    let junk = r.bytes(set.l() * ep);
    add("s1 random bytes", &|k| k[s1..s1 + junk.len()].copy_from_slice(&junk));
    let (tpos, tbit) = (t0 + r.below(set.sk_len() - t0), r.below(8));
    add("t0 one bit flipped (in range, inconsistent)", &|k| k[tpos] ^= 1 << tbit);
    let (trpos, trbit) = (64 + r.below(64), r.below(8));
    add("tr one bit flipped", &|k| k[trpos] ^= 1 << trbit);
    let (rpos, rbit) = (r.below(32), r.below(8));
    add("rho one bit flipped", &|k| k[rpos] ^= 1 << rbit);
    let (kpos, kbit) = (32 + r.below(32), r.below(8));
    add("K one bit flipped (still a plausible key)", &|k| k[kpos] ^= 1 << kbit);
    add("sk all 0x00", &|k| k.iter_mut().for_each(|b| *b = 0));
    add("sk all 0xFF", &|k| k.iter_mut().for_each(|b| *b = 0xFF));
    v
}

/// One implementation's reaction to one malformed key.
#[derive(Clone, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum Outcome {
    /// The same signature as ours; whether it verifies under the original public key.
    SameAsOurs { verifies: bool },
    /// A different signature; whether our Verify accepts it under the original public key.
    Differs { verifies: bool },
    Error(String),
    Panic(String),
    Hang,
}

impl Outcome {
    pub fn label(&self) -> String {
        match self {
            Outcome::SameAsOurs { verifies: true } => "same sig (valid)".into(),
            Outcome::SameAsOurs { verifies: false } => "same sig (invalid)".into(),
            Outcome::Differs { verifies: true } => "other sig (valid)".into(),
            Outcome::Differs { verifies: false } => "other sig (invalid)".into(),
            Outcome::Error(e) => format!("error: {e}"),
            Outcome::Panic(_) => "PANIC".into(),
            Outcome::Hang => "HANG".into(),
        }
    }
}

/// Signs (deterministic variant, ctx empty) with `imp`, in a helper thread with a timeout.
fn sign_with_timeout(imp: Imp, set: Set, sk: Vec<u8>, msg: Vec<u8>, secs: u64) -> Option<SignRes> {
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(move || {
            let _ = tx.send(imp.sign(set, &sk, &msg, &[], &[0u8; 32]));
        })
        .unwrap();
    rx.recv_timeout(Duration::from_secs(secs)).ok()
}

pub struct Row {
    pub variant: String,
    /// Our `sk_is_well_formed_NN`.
    pub ours_well_formed: bool,
    /// mldsa-native `pk_from_sk`: "ok", "ok (different pk)" or the error name.
    pub mldsa_validate: String,
    /// Our `pk_from_sk_NN`: "ok", "ok (different pk)" or "rejected"; "mixed" if the trials differ.
    pub ours_pk_from_sk: String,
    /// True iff our `pk_from_sk_NN` accepted and rejected exactly the keys mldsa-native's `pk_from_sk` did.
    pub pk_from_sk_agrees: bool,
    /// Per implementation (in `imps` order), outcomes over the trials.
    pub outcomes: Vec<Vec<Outcome>>,
}

/// Runs every variant over `trials` freshly derived keys.
pub fn run(set: Set, imps: &[Imp], trials: usize, seed: u64, timeout_secs: u64) -> Vec<Row> {
    let mut rng = Rng::new(seed ^ set.level() as u64);
    let keys: Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> = (0..trials)
        .map(|_| {
            let xi = rng.array32();
            let (pk, sk) = Imp::Ours.keygen(set, &xi);
            let n = rng.range(0, 64);
            let msg = rng.bytes(n);
            (pk, sk, msg)
        })
        .collect();
    let names: Vec<String> = variants(set, &keys[0].1, &mut Rng::new(1)).into_iter().map(|(n, _)| n).collect();
    let mut rows: Vec<Row> = names
        .iter()
        .map(|n| Row { variant: n.clone(), ours_well_formed: true, mldsa_validate: String::new(), ours_pk_from_sk: String::new(), pk_from_sk_agrees: true, outcomes: vec![Vec::new(); imps.len()] })
        .collect();
    for (pk, sk, msg) in &keys {
        let vs = variants(set, sk, &mut Rng::new(seed.wrapping_add(7)));
        for (vi, (_, k)) in vs.iter().enumerate() {
            let row = &mut rows[vi];
            row.ours_well_formed = row.ours_well_formed && oracle::ours_sk_is_well_formed(set, k);
            let mv = imps.iter().find_map(|i| i.validate_sk(set, k));
            let s = match mv.clone() {
                None => "n/a".to_string(),
                Some(Ok(p)) if &p == pk => "ok".to_string(),
                Some(Ok(_)) => "ok (different pk)".to_string(),
                Some(Err(rc)) => crate::mldsa_native::err_name(rc),
            };
            if row.mldsa_validate.is_empty() {
                row.mldsa_validate = s;
            } else if row.mldsa_validate != s {
                row.mldsa_validate = "mixed".into();
            }
            let ours_pk = oracle::ours_pk_from_sk(set, k);
            let os = match &ours_pk {
                None => "rejected".to_string(),
                Some(p) if p == pk => "ok".to_string(),
                Some(_) => "ok (different pk)".to_string(),
            };
            if row.ours_pk_from_sk.is_empty() {
                row.ours_pk_from_sk = os;
            } else if row.ours_pk_from_sk != os {
                row.ours_pk_from_sk = "mixed".into();
            }
            // mldsa-native: an error code is a rejection; a returned pk must be ours.
            row.pk_from_sk_agrees = row.pk_from_sk_agrees
                && match (&mv, &ours_pk) {
                    (None, _) => true,
                    (Some(Ok(a)), Some(b)) => a == b,
                    (Some(Err(_)), None) => true,
                    _ => false,
                };
            let results: Vec<Option<SignRes>> = imps.iter().map(|&i| sign_with_timeout(i, set, k.clone(), msg.clone(), timeout_secs)).collect();
            let ours = results[0].clone();
            for (ii, res) in results.iter().enumerate() {
                let o = match res {
                    None => Outcome::Hang,
                    Some(SignRes::Panic(m)) => Outcome::Panic(m.clone()),
                    Some(SignRes::NoSig(e)) => Outcome::Error(e.split('(').next().unwrap_or(e).trim().to_string()),
                    Some(SignRes::Sig(s)) => match &ours {
                        Some(SignRes::Sig(os)) if os == s => Outcome::SameAsOurs { verifies: Imp::Ours.verify(set, pk, msg, &[], s).ok },
                        _ => Outcome::Differs { verifies: Imp::Ours.verify(set, pk, msg, &[], s).ok },
                    },
                };
                row.outcomes[ii].push(o);
            }
        }
    }
    rows
}

/// "same sig" or "4x same sig" style summary of the trial outcomes.
pub fn summarize(outs: &[Outcome]) -> String {
    let mut sorted = outs.to_vec();
    sorted.sort();
    let mut parts: Vec<String> = Vec::new();
    let mut i = 0;
    while i < sorted.len() {
        let mut j = i;
        while j < sorted.len() && sorted[j] == sorted[i] {
            j += 1;
        }
        parts.push(if sorted.len() == j - i { sorted[i].label() } else { format!("{}x {}", j - i, sorted[i].label()) });
        i = j;
    }
    parts.join("; ")
}
