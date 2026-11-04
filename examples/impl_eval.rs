//! Native side of the differential evaluation of the extracted code (see scripts/impl-eval.sh).
//!
//! `impl_eval INPUTS OUTPUTS` runs the crate on every line of INPUTS (`op arg arg ...`, produced by
//! scripts/gen-impl-eval-inputs.py) and writes one canonical output line per input line, in the same format as
//! `lean/SpecTests/ImplEval.lean`: `N` for `None`, `FAIL` when the function panics (the extracted function returns
//! `fail`), `BADIN` for a malformed line. Build with overflow checks on (the script sets
//! `CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`) so that arithmetic overflow panics as it does in the extraction.
use ml_dsa_lean::api::*;
use ml_dsa_lean::encode::*;
use ml_dsa_lean::field;
use ml_dsa_lean::keccak::{Shake, keccak_f1600};
use ml_dsa_lean::ntt;
use ml_dsa_lean::params::*;
use ml_dsa_lean::rounding::*;
use ml_dsa_lean::sampling::*;
use std::fmt::Write as _;
use std::io::{BufRead, BufWriter, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};

type Poly = [u32; 256];

fn unhex(s: &str) -> Option<Vec<u8>> {
    if s == "-" {
        return Some(Vec::new());
    }
    if s.len() % 2 != 0 {
        return None;
    }
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).ok()).collect()
}
fn hex_bytes(b: &[u8]) -> String {
    if b.is_empty() {
        return "-".into();
    }
    let mut s = String::with_capacity(2 * b.len());
    for x in b {
        write!(s, "{x:02x}").unwrap();
    }
    s
}
fn poly(s: &str) -> Option<Poly> {
    if s.len() != 2048 {
        return None;
    }
    let mut p = [0u32; 256];
    for (i, c) in p.iter_mut().enumerate() {
        *c = u32::from_str_radix(&s[8 * i..8 * i + 8], 16).ok()?;
    }
    Some(p)
}
fn polys<const N: usize>(s: &str) -> Option<[Poly; N]> {
    if s.len() != 2048 * N {
        return None;
    }
    let mut v = [[0u32; 256]; N];
    for (i, p) in v.iter_mut().enumerate() {
        *p = poly(&s[2048 * i..2048 * (i + 1)])?;
    }
    Some(v)
}
fn matrix<const K: usize, const L: usize>(s: &str) -> Option<[[Poly; L]; K]> {
    if s.len() != 2048 * K * L {
        return None;
    }
    let mut m = [[[0u32; 256]; L]; K];
    for i in 0..K {
        for j in 0..L {
            let o = 2048 * (i * L + j);
            m[i][j] = poly(&s[o..o + 2048])?;
        }
    }
    Some(m)
}
fn bpolys<const N: usize>(s: &str) -> Option<[[bool; 256]; N]> {
    if s.len() != 256 * N {
        return None;
    }
    let b = s.as_bytes();
    let mut v = [[false; 256]; N];
    for i in 0..N {
        for j in 0..256 {
            v[i][j] = b[256 * i + j] == b'1';
        }
    }
    Some(v)
}
fn hex_poly(p: &Poly) -> String {
    let mut s = String::with_capacity(2048);
    for c in p {
        write!(s, "{c:08x}").unwrap();
    }
    s
}
fn hex_polys(v: &[Poly]) -> String {
    v.iter().map(hex_poly).collect()
}
fn hex_bpolys(v: &[[bool; 256]]) -> String {
    v.iter().flat_map(|p| p.iter().map(|&b| if b { '1' } else { '0' })).collect()
}
fn bit(b: bool) -> String {
    (b as u8).to_string()
}
fn opt(o: Option<u32>) -> String {
    o.map_or("N".into(), |x| x.to_string())
}
fn n(s: &str) -> Option<u64> {
    s.parse().ok()
}
fn arr<const M: usize>(s: &str) -> Option<[u8; M]> {
    unhex(s)?.try_into().ok()
}

fn params_of(sn: &str) -> &'static Params {
    match sn {
        "44" => &ML_DSA_44,
        "65" => &ML_DSA_65,
        _ => &ML_DSA_87,
    }
}

fn shake_run(is128: bool, msg: &[u8], outlen: usize, chunk: usize) -> Vec<u8> {
    let mut sh = if is128 { Shake::shake128() } else { Shake::shake256() };
    for c in msg.chunks(chunk) {
        sh.absorb(c);
    }
    sh.finalize();
    let mut out = Vec::new();
    let mut rem = outlen;
    while rem > 0 {
        let k = chunk.min(rem);
        let mut buf = vec![0u8; k];
        sh.squeeze(&mut buf);
        out.extend_from_slice(&buf);
        rem -= k;
    }
    out
}

fn plain_op(op: &str, a: &[&str]) -> Option<String> {
    Some(match op {
        "f_add" => field::add(n(a[0])? as u32, n(a[1])? as u32).to_string(),
        "f_sub" => field::sub(n(a[0])? as u32, n(a[1])? as u32).to_string(),
        "f_mul" => field::mul(n(a[0])? as u32, n(a[1])? as u32).to_string(),
        "f_neg" => field::neg(n(a[0])? as u32).to_string(),
        "f_small_reduce" => field::small_reduce(n(a[0])? as u32).to_string(),
        "f_barrett_reduce" => field::barrett_reduce(n(a[0])?).to_string(),
        "f_ct_lt_mask" => field::ct_lt_mask(n(a[0])?, n(a[1])?).to_string(),
        "f_ct_select" => field::ct_select(n(a[0])? as u32, n(a[1])? as u32, n(a[2])? as u32).to_string(),
        "ntt" => hex_poly(&ntt::ntt(&poly(a[0])?)),
        "ntt_inverse" => hex_poly(&ntt::ntt_inverse(&poly(a[0])?)),
        "multiply_ntt" => hex_poly(&ntt::multiply_ntt(&poly(a[0])?, &poly(a[1])?)),
        "add_poly" => hex_poly(&ntt::add_poly(&poly(a[0])?, &poly(a[1])?)),
        "sub_poly" => hex_poly(&ntt::sub_poly(&poly(a[0])?, &poly(a[1])?)),
        "power2round" => {
            let (r1, r0) = power2round(n(a[0])? as u32);
            format!("{r1} {r0}")
        }
        "infinity_norm" => infinity_norm(n(a[0])? as u32).to_string(),
        "poly_power2round" => {
            let (t1, t0) = poly_power2round(&poly(a[0])?);
            format!("{} {}", hex_poly(&t1), hex_poly(&t0))
        }
        "rej_ntt_poly" => hex_poly(&rej_ntt_poly(&arr::<34>(a[0])?)),
        "coeff_from_three_bytes" => opt(coeff_from_three_bytes(n(a[0])? as u8, n(a[1])? as u8, n(a[2])? as u8)),
        "bit_pack" => {
            let c = n(a[1])? as usize;
            let mut out = vec![0u8; 32 * c];
            bit_pack(&poly(a[0])?, c, &mut out);
            hex_bytes(&out)
        }
        "bit_unpack" => {
            let c = n(a[1])? as usize;
            let v = unhex(a[0])?;
            if v.len() != 32 * c {
                return None;
            }
            hex_poly(&bit_unpack(&v, c))
        }
        "keccak_f1600" => {
            let bs = unhex(a[0])?;
            if bs.len() != 200 {
                return None;
            }
            let mut st = [0u64; 25];
            for (i, w) in st.iter_mut().enumerate() {
                *w = u64::from_le_bytes(bs[8 * i..8 * i + 8].try_into().unwrap());
            }
            keccak_f1600(&mut st);
            hex_bytes(&st.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>())
        }
        "shake128" | "shake256" => {
            let chunk = n(a[2])? as usize;
            if chunk == 0 {
                return None;
            }
            hex_bytes(&shake_run(op == "shake128", &unhex(a[0])?, n(a[1])? as usize, chunk))
        }
        _ => return None,
    })
}

fn set_op<const K: usize, const L: usize>(sn: &str, base: &str, a: &[&str]) -> Option<String> {
    let p = params_of(sn);
    Some(match base {
        "matrix_vector_ntt" => hex_polys(&ntt::matrix_vector_ntt::<K, L>(&matrix::<K, L>(a[0])?, &polys::<L>(a[1])?)),
        "vec_infinity_norm" => vec_infinity_norm::<K>(&polys::<K>(a[0])?).to_string(),
        "decompose" => {
            let (r1, r0) = decompose(p, n(a[0])? as u32);
            format!("{r1} {r0}")
        }
        "high_bits" => high_bits(p, n(a[0])? as u32).to_string(),
        "low_bits" => low_bits(p, n(a[0])? as u32).to_string(),
        "make_hint" => bit(make_hint(p, n(a[0])? as u32, n(a[1])? as u32)),
        "use_hint" => use_hint(p, n(a[0])? != 0, n(a[1])? as u32).to_string(),
        "poly_high_bits" => hex_poly(&poly_high_bits(p, &poly(a[0])?)),
        "poly_low_bits" => hex_poly(&poly_low_bits(p, &poly(a[0])?)),
        "poly_use_hint" => hex_poly(&poly_use_hint(p, &bpolys::<1>(a[0])?[0], &poly(a[1])?)),
        "coeff_from_half_byte" => opt(coeff_from_half_byte(p, n(a[0])? as u8)),
        "rej_bounded_poly" => hex_poly(&rej_bounded_poly(p, &arr::<66>(a[0])?)),
        "expand_a" => {
            let m = expand_a::<K, L>(&arr::<32>(a[0])?);
            m.iter().map(|row| hex_polys(row)).collect()
        }
        "expand_s" => {
            let (s1, s2) = expand_s::<K, L>(p, &arr::<64>(a[0])?);
            format!("{} {}", hex_polys(&s1), hex_polys(&s2))
        }
        "expand_mask" => hex_polys(&expand_mask::<L>(p, &arr::<64>(a[0])?, n(a[1])? as u16)),
        "sample_in_ball" => hex_poly(&sample_in_ball(p, &unhex(a[0])?)),
        "pk_encode" => {
            let mut out = vec![0u8; 32 + 320 * K];
            pk_encode::<K>(&arr::<32>(a[0])?, &polys::<K>(a[1])?, &mut out);
            hex_bytes(&out)
        }
        "pk_decode" => {
            let (rho, t1) = pk_decode::<K>(&unhex(a[0])?);
            format!("{} {}", hex_bytes(&rho), hex_polys(&t1))
        }
        "sk_encode" => {
            let mut out = vec![0u8; sk_len(p)];
            sk_encode::<K, L>(
                p,
                &arr::<32>(a[0])?,
                &arr::<32>(a[1])?,
                &arr::<64>(a[2])?,
                &polys::<L>(a[3])?,
                &polys::<K>(a[4])?,
                &polys::<K>(a[5])?,
                &mut out,
            );
            hex_bytes(&out)
        }
        "sk_decode" => {
            let sk = sk_decode::<K, L>(p, &unhex(a[0])?);
            format!(
                "{} {} {} {} {} {}",
                hex_bytes(&sk.rho),
                hex_bytes(&sk.key),
                hex_bytes(&sk.tr),
                hex_polys(&sk.s1),
                hex_polys(&sk.s2),
                hex_polys(&sk.t0)
            )
        }
        "sig_encode" => {
            let mut out = vec![0u8; sig_len(p)];
            sig_encode::<K, L>(p, &unhex(a[0])?, &polys::<L>(a[1])?, &bpolys::<K>(a[2])?, &mut out);
            hex_bytes(&out)
        }
        "sig_decode" => match sig_decode::<K, L>(p, &unhex(a[0])?) {
            None => "N".into(),
            Some((ct, z, h)) => format!("{} {} {}", hex_bytes(&ct), hex_polys(&z), hex_bpolys(&h)),
        },
        "w1_encode" => {
            let mut out = vec![0u8; K * 32 * p.w1_bits];
            w1_encode::<K>(p, &polys::<K>(a[0])?, &mut out);
            hex_bytes(&out)
        }
        "hint_bit_pack" => {
            let mut out = vec![0u8; p.omega + K];
            hint_bit_pack::<K>(p, &bpolys::<K>(a[0])?, &mut out);
            hex_bytes(&out)
        }
        "hint_bit_unpack" => match hint_bit_unpack::<K>(p, &unhex(a[0])?) {
            None => "N".into(),
            Some(h) => hex_bpolys(&h),
        },
        _ => return None,
    })
}

macro_rules! api_op {
    ($base:expr, $a:expr, $kg:ident, $sg:ident, $si:ident, $vf:ident, $vi:ident, $pk:literal, $sk:literal, $sig:literal) => {{
        let a = $a;
        match $base {
            "keygen" => {
                let (pk, sk) = $kg(&arr::<32>(a[0])?);
                format!("{} {}", hex_bytes(&pk), hex_bytes(&sk))
            }
            "sign" => match $sg(&arr::<$sk>(a[0])?, &unhex(a[1])?, &unhex(a[2])?, &arr::<32>(a[3])?) {
                None => "N".into(),
                Some(s) => hex_bytes(&s),
            },
            "sign_internal" => match $si(&arr::<$sk>(a[0])?, &unhex(a[1])?, &arr::<32>(a[2])?) {
                None => "N".into(),
                Some(s) => hex_bytes(&s),
            },
            "verify" => bit($vf(&arr::<$pk>(a[0])?, &unhex(a[1])?, &unhex(a[2])?, &arr::<$sig>(a[3])?)),
            "verify_internal" => bit($vi(&arr::<$pk>(a[0])?, &unhex(a[1])?, &arr::<$sig>(a[2])?)),
            _ => return None,
        }
    }};
}

fn api_op(sn: &str, base: &str, a: &[&str]) -> Option<String> {
    Some(match sn {
        "44" => api_op!(base, a, keygen_44, sign_44, sign_internal_44, verify_44, verify_internal_44, 1312, 2560, 2420),
        "65" => api_op!(base, a, keygen_65, sign_65, sign_internal_65, verify_65, verify_internal_65, 1952, 4032, 3309),
        _ => api_op!(base, a, keygen_87, sign_87, sign_internal_87, verify_87, verify_internal_87, 2592, 4896, 4627),
    })
}

fn eval_line(line: &str) -> String {
    let parts: Vec<&str> = line.split(' ').collect();
    let op = parts[0];
    let a = &parts[1..];
    // Reading a[i] past the end is a malformed line, not a panic of the function under test.
    let need = |k: usize| a.len() >= k;
    let sn = if op.len() > 2 { &op[op.len() - 2..] } else { "" };
    let r = if sn == "44" || sn == "65" || sn == "87" {
        let base = &op[..op.len() - 2];
        let args_ok = need(1);
        if !args_ok {
            None
        } else {
            let a4: Vec<&str> = a.iter().copied().chain(std::iter::repeat("")).take(a.len().max(6)).collect();
            api_op_guarded(sn, base, &a4).or_else(|| match sn {
                "44" => set_op::<4, 4>(sn, base, &a4),
                "65" => set_op::<6, 5>(sn, base, &a4),
                _ => set_op::<8, 7>(sn, base, &a4),
            })
        }
    } else if need(1) {
        let a4: Vec<&str> = a.iter().copied().chain(std::iter::repeat("")).take(a.len().max(6)).collect();
        plain_op(op, &a4)
    } else {
        None
    };
    r.unwrap_or_else(|| "BADIN".into())
}

fn api_op_guarded(sn: &str, base: &str, a: &[&str]) -> Option<String> {
    if matches!(base, "keygen" | "sign" | "sign_internal" | "verify" | "verify_internal") {
        api_op(sn, base, a)
    } else {
        None
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: impl_eval INPUTS OUTPUTS");
        std::process::exit(2);
    }
    std::panic::set_hook(Box::new(|_| {}));
    let input = std::io::BufReader::new(std::fs::File::open(&args[1]).unwrap());
    let mut out = BufWriter::new(std::fs::File::create(&args[2]).unwrap());
    let t0 = std::time::Instant::now();
    let mut count = 0usize;
    for line in input.lines() {
        let line = line.unwrap();
        let res = catch_unwind(AssertUnwindSafe(|| eval_line(&line))).unwrap_or_else(|_| "FAIL".into());
        writeln!(out, "{res}").unwrap();
        count += 1;
    }
    out.flush().unwrap();
    eprintln!("impl_eval: {count} cases in {:?}", t0.elapsed());
}
