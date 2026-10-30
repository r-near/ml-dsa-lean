//! Writes the seed corpus for the three fuzz targets from the vendored ACVP vectors (tests/data/acvp) plus a few
//! hand-built pool seeds: `gen_seeds <acvp dir> <corpus dir>` creates <corpus dir>/{verify_diff,sign_diff,decode_roundtrip}/.
//! Only the pure (non-preHash, non-externalMu) interface is used. Internal-interface vectors are used when M′ has the form
//! 0 ‖ |ctx| ‖ ctx ‖ m, which is the only M′ shape the context-based targets can express.
use fz::*;
use serde::Deserialize;
use std::io::Read;
use std::path::Path;

#[derive(Deserialize)]
struct File {
    #[serde(rename = "testGroups")]
    groups: Vec<Group>,
}
#[derive(Deserialize)]
struct Group {
    #[serde(rename = "parameterSet")]
    parameter_set: String,
    #[serde(rename = "preHash", default)]
    pre_hash: Option<String>,
    #[serde(rename = "externalMu", default)]
    external_mu: bool,
    #[serde(rename = "signatureInterface", default)]
    interface: Option<String>,
    tests: Vec<Case>,
}
#[derive(Deserialize)]
struct Case {
    seed: Option<String>,
    pk: Option<String>,
    sk: Option<String>,
    message: Option<String>,
    context: Option<String>,
    rnd: Option<String>,
    signature: Option<String>,
}

fn load(dir: &Path, name: &str) -> File {
    let bytes = std::fs::read(dir.join(format!("{name}.json.gz"))).expect("read acvp file");
    let mut json = String::new();
    flate2::read::GzDecoder::new(&bytes[..]).read_to_string(&mut json).unwrap();
    serde_json::from_str(&json).unwrap()
}

fn unhex(s: &str) -> Vec<u8> {
    let v = |c: u8| match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        b'A'..=b'F' => c - b'A' + 10,
        _ => panic!("bad hex"),
    };
    s.as_bytes().chunks(2).map(|c| v(c[0]) << 4 | v(c[1])).collect()
}

fn hex(f: &Option<String>) -> Vec<u8> {
    f.as_deref().map(unhex).unwrap_or_default()
}

/// (ctx, m) such that M′ = 0 ‖ |ctx| ‖ ctx ‖ m, for the pure interface; `None` if the vector cannot be expressed.
fn split_case(g: &Group, c: &Case) -> Option<(Vec<u8>, Vec<u8>)> {
    if g.pre_hash.as_deref() == Some("preHash") || g.external_mu {
        return None;
    }
    let msg = hex(&c.message);
    match g.interface.as_deref() {
        Some("external") => Some((hex(&c.context), msg)),
        _ => {
            let n = *msg.get(1)? as usize;
            (msg[0] == 0 && msg.len() >= 2 + n).then(|| (msg[2..2 + n].to_vec(), msg[2 + n..].to_vec()))
        }
    }
}

struct Out {
    dir: std::path::PathBuf,
    n: usize,
}
impl Out {
    fn new(root: &Path, target: &str) -> Out {
        let dir = root.join(target);
        std::fs::create_dir_all(&dir).unwrap();
        Out { dir, n: 0 }
    }
    fn put(&mut self, data: &[u8]) {
        std::fs::write(self.dir.join(format!("acvp-{:04}", self.n)), data).unwrap();
        self.n += 1;
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (acvp, root) = (Path::new(&args[1]), Path::new(&args[2]));
    let mut verify = Out::new(root, "verify_diff");
    let mut sign = Out::new(root, "sign_diff");
    let mut decode = Out::new(root, "decode_roundtrip");

    // verify_diff: sigVer vectors, all fields explicit (flags 1|2|4|8), no edits.
    for g in load(acvp, "sigVer").groups {
        let set = Set::from_name(&g.parameter_set).unwrap();
        for c in &g.tests {
            let Some((ctx, msg)) = split_case(&g, c) else { continue };
            let (pk, sig) = (hex(&c.pk), hex(&c.signature));
            if pk.len() != set.pk_len() || sig.len() != set.sig_len() || ctx.len() > 1024 || msg.len() > 8192 {
                continue;
            }
            let mut e = Enc::default();
            e.u8(set.to_byte()).u8(0).u8(15).u8(0).u8(0).u8(0).u8(0);
            e.raw(&[0, 0, 0, 0, 0, 0]); // split, pk length, sig length
            e.raw(&pk).raw(&sig).blob(&msg).blob(&ctx);
            verify.put(&e.0);
        }
    }
    // verify_diff: pool seeds without edits (all bases, ctx selectors) and with one edit per region.
    for set in [Set::S44, Set::S65, Set::S87] {
        for base in 0..POOL_SIZE as u8 {
            for ctx_sel in [0u8, 1, 2, 3] {
                let mut e = Enc::default();
                e.u8(set.to_byte()).u8(base).u8(0).u8(0).u8(ctx_sel).u8(0).u8(0).raw(&[0; 6]);
                verify.put(&e.0);
            }
            for region in 0..8u8 {
                let mut e = Enc::default();
                e.u8(set.to_byte()).u8(base).u8(0).u8(0).u8(0).u8(0).u8(1);
                e.raw(&[region, base, 0, 0, 0]).raw(&[0; 6]);
                verify.put(&e.0);
            }
            // pk from another base, hint counts rewritten
            let mut e = Enc::default();
            e.u8(set.to_byte()).u8(base).u8(16).u8(0).u8(0).u8(base.wrapping_add(1)).u8(0).raw(&[0; 6]);
            verify.put(&e.0);
        }
    }

    // sign_diff: keyGen seeds paired with sigGen message/context/rnd; decode_roundtrip: sigGen sk + message/context/rnd.
    let keygen = load(acvp, "keyGen");
    let mut seeds: Vec<(Set, Vec<u8>, Vec<u8>)> = Vec::new(); // (set, xi, sk)
    for g in &keygen.groups {
        let set = Set::from_name(&g.parameter_set).unwrap();
        for c in &g.tests {
            seeds.push((set, hex(&c.seed), hex(&c.sk)));
        }
    }
    let mut k = 0;
    for g in load(acvp, "sigGen").groups {
        let set = Set::from_name(&g.parameter_set).unwrap();
        for c in &g.tests {
            let Some((ctx, msg)) = split_case(&g, c) else { continue };
            if ctx.len() > 1024 || msg.len() > 8192 {
                continue;
            }
            let det = c.rnd.is_none();
            let rnd = if det { vec![0u8; 32] } else { hex(&c.rnd) };
            // decode_roundtrip: the expanded sk from the vector.
            let sk = hex(&c.sk);
            if sk.len() == set.sk_len() {
                let mut e = Enc::default();
                e.u8(set.to_byte()).u8(det as u8).u8(0).raw(&sk).raw(&rnd).blob(&ctx).raw(&msg);
                decode.put(&e.0);
            }
            // sign_diff: a keyGen seed of the same parameter set.
            let same: Vec<_> = seeds.iter().filter(|s| s.0 == set).collect();
            let (_, xi, _) = same[k % same.len()];
            k += 1;
            let mut e = Enc::default();
            e.u8(set.to_byte()).u8(det as u8).u8(0).raw(xi).raw(&rnd).blob(&ctx).u8(0).u8(0).raw(&msg);
            sign.put(&e.0);
        }
    }
    // decode_roundtrip: keygen sk with no edits (flag 2), one per keyGen seed of each set.
    for (set, xi, _) in seeds.iter().step_by(5) {
        let mut e = Enc::default();
        e.u8(set.to_byte()).u8(2).u8(0).raw(xi).u8(0).raw(&[7; 32]).blob(b"ctx").raw(b"hello");
        decode.put(&e.0);
    }
    println!("seeds: verify_diff {}, sign_diff {}, decode_roundtrip {}", verify.n, sign.n, decode.n);
}
