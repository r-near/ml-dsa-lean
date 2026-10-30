//! Seeded PRNG, case generation and signature/key mutations.
//!
//! Case `idx` of parameter set `set` under master seed `seed` is a pure function of (seed, set, idx), so any
//! disagreement can be replayed with `xcheck --replay <set> <idx>` regardless of thread count.
use crate::Set;

/// xoshiro256** seeded through SplitMix64.
#[derive(Clone)]
pub struct Rng {
    s: [u64; 4],
}

fn splitmix(x: &mut u64) -> u64 {
    *x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *x;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

impl Rng {
    pub fn new(seed: u64) -> Rng {
        let mut x = seed;
        Rng { s: [splitmix(&mut x), splitmix(&mut x), splitmix(&mut x), splitmix(&mut x)] }
    }
    /// The generator for case `idx` of `set` under `master`.
    pub fn for_case(master: u64, set: Set, idx: u64) -> Rng {
        let mut x = master ^ 0xA076_1D64_78BD_642F;
        let a = splitmix(&mut x) ^ (set.level() as u64).wrapping_mul(0xE703_7ED1_A0B4_28DB);
        let mut y = a ^ idx.wrapping_mul(0x8EBC_6AF0_9C88_C6E3);
        Rng::new(splitmix(&mut y))
    }
    pub fn u64(&mut self) -> u64 {
        let r = self.s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = self.s[1] << 17;
        self.s[2] ^= self.s[0];
        self.s[3] ^= self.s[1];
        self.s[1] ^= self.s[2];
        self.s[0] ^= self.s[3];
        self.s[2] ^= t;
        self.s[3] = self.s[3].rotate_left(45);
        r
    }
    /// Uniform in 0..n (n > 0); modulo bias is irrelevant here.
    pub fn below(&mut self, n: usize) -> usize {
        (self.u64() % n as u64) as usize
    }
    pub fn range(&mut self, lo: usize, hi_inclusive: usize) -> usize {
        lo + self.below(hi_inclusive - lo + 1)
    }
    pub fn u8(&mut self) -> u8 {
        self.u64() as u8
    }
    pub fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }
    pub fn bytes(&mut self, n: usize) -> Vec<u8> {
        let mut v = vec![0u8; n];
        for c in v.chunks_mut(8) {
            let w = self.u64().to_le_bytes();
            c.copy_from_slice(&w[..c.len()]);
        }
        v
    }
    pub fn array32(&mut self) -> [u8; 32] {
        self.bytes(32).try_into().unwrap()
    }
}

// ---------------------------------------------------------------------------------------------
// Sign cases
// ---------------------------------------------------------------------------------------------

pub struct Case {
    pub set: Set,
    pub idx: u64,
    pub xi: [u8; 32],
    pub rnd: [u8; 32],
    pub hedged: bool,
    pub msg: Vec<u8>,
    pub ctx: Vec<u8>,
    /// Where M′ is cut into prefix and message for the oracles that take both (mldsa-native internal API).
    pub split: usize,
}

/// Message lengths 0..=2048, weighted toward the SHAKE-256 rate boundary (136) and the extremes.
fn msg_len(r: &mut Rng) -> usize {
    match r.below(10) {
        0 => [0, 1, 2, 3][r.below(4)],
        1 => [135, 136, 137, 271, 272, 273, 2047, 2048][r.below(8)],
        _ => r.range(0, 2048),
    }
}

/// Context lengths: 0, 1, 255 and 256 each get a fixed share (256 is out of range and must be refused).
fn ctx_len(r: &mut Rng) -> usize {
    match r.below(100) {
        0..=17 => 0,
        18..=35 => 1,
        36..=51 => 255,
        52..=61 => 256,
        _ => r.range(2, 254),
    }
}

pub fn make_case(master: u64, set: Set, idx: u64) -> Case {
    let mut r = Rng::for_case(master, set, idx);
    let xi = r.array32();
    let hedged = r.chance(50);
    let rnd = if hedged { r.array32() } else { [0u8; 32] };
    let n = msg_len(&mut r);
    let msg = r.bytes(n);
    let c = ctx_len(&mut r);
    let ctx = r.bytes(c);
    let split_raw = r.below(1 << 16);
    let split = split_raw % (2 + ctx.len().min(255) + msg.len() + 1);
    Case { set, idx, xi, rnd, hedged, msg, ctx, split }
}

// ---------------------------------------------------------------------------------------------
// Mutations of a valid (pk, sig)
// ---------------------------------------------------------------------------------------------

/// Which part of a signature a flip targets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Region {
    CTilde,
    Z,
    HintPositions,
    HintCounts,
    Anywhere,
}

pub fn region_range(set: Set, r: Region) -> (usize, usize) {
    match r {
        Region::CTilde => (0, set.c_tilde_len()),
        Region::Z => (set.c_tilde_len(), set.hint_start()),
        Region::HintPositions => (set.hint_start(), set.counts_start()),
        Region::HintCounts => (set.counts_start(), set.sig_len()),
        Region::Anywhere => (0, set.sig_len()),
    }
}

const REGIONS: [Region; 5] = [Region::CTilde, Region::Z, Region::HintPositions, Region::HintCounts, Region::Anywhere];

/// A description of one mutated verification input, replayable from the honest values.
#[derive(Clone, Debug)]
pub struct Mutant {
    pub label: String,
    pub pk: Vec<u8>,
    pub sig: Vec<u8>,
    pub msg: Vec<u8>,
    pub ctx: Vec<u8>,
}

fn flip(buf: &mut [u8], pos: usize, bit: u32) {
    buf[pos] ^= 1 << bit;
}

/// Hint decoded from an honest signature: per polynomial, the positions.
fn parse_hint(set: Set, sig: &[u8]) -> Vec<Vec<u8>> {
    let (hs, cs) = (set.hint_start(), set.counts_start());
    let mut out = Vec::new();
    let mut prev = 0usize;
    for i in 0..set.k() {
        let c = sig[cs + i] as usize;
        let c = c.min(set.omega());
        out.push(sig[hs + prev.min(c)..hs + c].to_vec());
        prev = c;
    }
    out
}

/// Writes `hint` back as an encoding (positions in order, zero padding, cumulative counts), without
/// validating it: callers deliberately pass malformed hints.
fn write_hint(set: Set, sig: &mut [u8], hint: &[Vec<u8>], counts_override: Option<&[u8]>) {
    let (hs, cs) = (set.hint_start(), set.counts_start());
    for b in &mut sig[hs..] {
        *b = 0;
    }
    let mut idx = 0usize;
    for (i, h) in hint.iter().enumerate() {
        for &p in h {
            if idx < set.omega() {
                sig[hs + idx] = p;
            }
            idx += 1;
        }
        sig[cs + i] = idx.min(255) as u8;
    }
    if let Some(c) = counts_override {
        sig[cs..cs + set.k()].copy_from_slice(c);
    }
}

/// Malformed (or merely unusual) hint encodings, all derived from an honest signature. Each is labelled.
pub fn hint_mutants(set: Set, sig: &[u8], r: &mut Rng) -> Vec<(String, Vec<u8>)> {
    let (hs, cs, k, w) = (set.hint_start(), set.counts_start(), set.k(), set.omega());
    let hint = parse_hint(set, sig);
    let total: usize = hint.iter().map(|h| h.len()).sum();
    let mut out: Vec<(String, Vec<u8>)> = Vec::new();
    let mut s;

    // Nonzero padding after the last used position (the byte just after the used region, and a random later one).
    if total < w {
        s = sig.to_vec();
        s[hs + total] = 1 + r.u8() % 255;
        out.push(("hint: nonzero padding right after last position".into(), s));
        s = sig.to_vec();
        let p = hs + r.range(total, w - 1);
        s[p] = 1 + r.u8() % 255;
        out.push(("hint: nonzero padding at random unused slot".into(), s));
        s = sig.to_vec();
        s[hs + w - 1] = 1 + r.u8() % 255;
        out.push(("hint: nonzero padding in last slot".into(), s));
    }
    // A count above ω.
    s = sig.to_vec();
    s[cs + r.below(k)] = (w + 1 + r.below(255 - w)) as u8;
    out.push(("hint: count > omega".into(), s));
    s = sig.to_vec();
    s[cs + k - 1] = 255;
    out.push(("hint: final count 255".into(), s));
    // Non-monotone counts: lower a count below its predecessor.
    {
        s = sig.to_vec();
        let i = r.range(1, k - 1);
        let prev = s[cs + i - 1];
        if prev > 0 {
            s[cs + i] = prev - 1 - (r.u8() % prev);
            out.push(("hint: counts decrease".into(), s));
        }
    }
    // Final count below an earlier count.
    if total > 0 {
        s = sig.to_vec();
        s[cs + k - 1] = (total as u8).saturating_sub(1);
        out.push(("hint: final count below total".into(), s));
    }
    // Final count above the used positions but within omega (extra positions read as zeros: duplicates of 0).
    if total < w {
        s = sig.to_vec();
        for i in 0..k {
            if s[cs + i] as usize >= total {
                s[cs + i] = (total + 1) as u8;
            }
        }
        out.push(("hint: counts claim one extra (zero) position".into(), s));
    }
    // Non-increasing positions inside a polynomial: duplicate / swap where a polynomial has at least two hints,
    // otherwise invent them (a repeated and a decreasing pair in the first polynomial).
    {
        match (0..k).find(|&i| hint[i].len() >= 2) {
            Some(i) => {
                let mut hd = hint.clone();
                hd[i][1] = hd[i][0];
                s = sig.to_vec();
                write_hint(set, &mut s, &hd, None);
                out.push(("hint: duplicate position".into(), s));
                let mut hw = hint.clone();
                hw[i].swap(0, 1);
                s = sig.to_vec();
                write_hint(set, &mut s, &hw, None);
                out.push(("hint: swapped (decreasing) positions".into(), s));
            }
            None => {
                for (label, pair) in [("hint: invented duplicate position", [5u8, 5u8]), ("hint: invented decreasing positions", [9u8, 3u8])] {
                    let mut hh = vec![pair.to_vec()];
                    hh.extend(hint[1..].iter().cloned());
                    s = sig.to_vec();
                    write_hint(set, &mut s, &hh, None);
                    out.push((label.into(), s));
                }
            }
        }
    }
    // A well-formed extra hint (valid encoding, wrong h): exercises UseHint, all must reject identically.
    if total < w {
        let mut h = hint.clone();
        let i = r.below(k);
        let mut p = r.u8();
        while h[i].contains(&p) {
            p = r.u8();
        }
        h[i].push(p);
        h[i].sort_unstable();
        s = sig.to_vec();
        write_hint(set, &mut s, &h, None);
        out.push(("hint: valid extra hint".into(), s));
    }
    // The maximal valid hint: omega strictly increasing positions in the first polynomial(s).
    {
        let mut h = vec![Vec::new(); k];
        for (j, slot) in (0..w).enumerate() {
            h[(j * k) / w].push((slot % 256) as u8);
        }
        for p in &mut h {
            p.sort_unstable();
            p.dedup();
        }
        s = sig.to_vec();
        write_hint(set, &mut s, &h, None);
        out.push(("hint: dense valid hint".into(), s));
    }
    // All counts omega with strictly increasing positions in the first slot run (rest empty).
    {
        s = sig.to_vec();
        for i in 0..w {
            s[hs + i] = (i * 3 % 256) as u8;
        }
        for i in 0..k {
            s[cs + i] = w as u8;
        }
        out.push(("hint: first poly takes all omega".into(), s));
    }
    // Empty hint with stale positions left in place (positions nonzero but counts zero => padding nonzero).
    {
        s = sig.to_vec();
        for i in 0..k {
            s[cs + i] = 0;
        }
        out.push(("hint: counts zeroed, positions left".into(), s));
    }
    // Completely random hint region.
    {
        s = sig.to_vec();
        for b in &mut s[hs..] {
            *b = r.u8();
        }
        out.push(("hint: random hint region".into(), s));
    }
    // Random hint region with sane counts: strictly increasing random positions, random split.
    {
        s = sig.to_vec();
        let n = r.range(0, w);
        let mut pos: Vec<u8> = (0..n).map(|_| r.u8()).collect();
        pos.sort_unstable();
        pos.dedup();
        for b in &mut s[hs..] {
            *b = 0;
        }
        for (i, p) in pos.iter().enumerate() {
            s[hs + i] = *p;
        }
        let mut cuts: Vec<usize> = (0..k - 1).map(|_| r.range(0, pos.len())).collect();
        cuts.sort_unstable();
        for (i, c) in cuts.iter().enumerate() {
            s[cs + i] = *c as u8;
        }
        s[cs + k - 1] = pos.len() as u8;
        out.push(("hint: random increasing positions".into(), s));
    }
    out
}

/// A random mix of mutations of a valid (pk, msg, ctx, sig). `nflips` signature bit flips spread over the regions,
/// `npk` public-key bit flips, all hint classes, saturated blocks and message/context tweaks.
pub fn mutants(set: Set, pk: &[u8], sig: &[u8], msg: &[u8], ctx: &[u8], r: &mut Rng, nflips: usize, npk: usize, light: bool) -> Vec<Mutant> {
    let mut out = Vec::new();
    let mk = |label: String, pk: Vec<u8>, sig: Vec<u8>, msg: Vec<u8>, ctx: Vec<u8>| Mutant { label, pk, sig, msg, ctx };

    for j in 0..nflips {
        let reg = REGIONS[j % REGIONS.len()];
        let (lo, hi) = region_range(set, reg);
        let pos = lo + r.below(hi - lo);
        let bit = r.below(8) as u32;
        let mut s = sig.to_vec();
        flip(&mut s, pos, bit);
        out.push(mk(format!("sig bit flip {reg:?} byte {pos} bit {bit}"), pk.to_vec(), s, msg.to_vec(), ctx.to_vec()));
    }
    // Always include the first and last byte of each signature region.
    for &reg in if light { &[][..] } else { &[Region::CTilde, Region::Z, Region::HintPositions, Region::HintCounts][..] } {
        let (lo, hi) = region_range(set, reg);
        for pos in [lo, hi - 1] {
            let mut s = sig.to_vec();
            flip(&mut s, pos, r.below(8) as u32);
            out.push(mk(format!("sig bit flip edge {reg:?} byte {pos}"), pk.to_vec(), s, msg.to_vec(), ctx.to_vec()));
        }
    }
    for j in 0..npk {
        let (lo, hi) = if j % 2 == 0 { (0, 32) } else { (32, set.pk_len()) };
        let pos = lo + r.below(hi - lo);
        let bit = r.below(8) as u32;
        let mut p = pk.to_vec();
        flip(&mut p, pos, bit);
        out.push(mk(format!("pk bit flip byte {pos} bit {bit}"), p, sig.to_vec(), msg.to_vec(), ctx.to_vec()));
    }
    let mut hints = hint_mutants(set, sig, r);
    if light {
        let i = r.below(hints.len());
        hints = vec![hints.swap_remove(i)];
    }
    for (label, s) in hints {
        out.push(mk(label, pk.to_vec(), s, msg.to_vec(), ctx.to_vec()));
    }
    // Saturated / zeroed blocks.
    let (zlo, zhi) = region_range(set, Region::Z);
    let blocks: &[(&str, u8, usize, usize)] = if light { &[] } else { &[
        ("sig: z all 0xFF", 0xFFu8, zlo, zhi),
        ("sig: z all 0x00", 0x00, zlo, zhi),
        ("sig: c-tilde all 0x00", 0x00, 0, set.c_tilde_len()),
        ("sig: all 0x00", 0x00, 0, set.sig_len()),
        ("sig: all 0xFF", 0xFF, 0, set.sig_len()),
    ] };
    for &(label, byte, lo, hi) in blocks {
        let mut s = sig.to_vec();
        for b in &mut s[lo..hi] {
            *b = byte;
        }
        out.push(mk(label.into(), pk.to_vec(), s, msg.to_vec(), ctx.to_vec()));
    }
    if !light {
        let mut p = pk.to_vec();
        for b in &mut p[32..] {
            *b = 0xFF;
        }
        out.push(mk("pk: t1 all 0xFF".into(), p, sig.to_vec(), msg.to_vec(), ctx.to_vec()));
        let mut p = pk.to_vec();
        for b in &mut p[32..] {
            *b = 0;
        }
        out.push(mk("pk: t1 all 0x00".into(), p, sig.to_vec(), msg.to_vec(), ctx.to_vec()));
    }
    // Message and context tweaks (verdict must be reject for every implementation).
    {
        let mut m = msg.to_vec();
        if m.is_empty() {
            m.push(r.u8());
        } else {
            let pos = r.below(m.len());
            flip(&mut m, pos, r.below(8) as u32);
        }
        out.push(mk("msg tweak".into(), pk.to_vec(), sig.to_vec(), m, ctx.to_vec()));
        let mut c = ctx.to_vec();
        if c.is_empty() || (c.len() <= 255 && r.chance(50)) {
            c.push(r.u8());
        } else {
            let pos = r.below(c.len());
            flip(&mut c, pos, r.below(8) as u32);
        }
        out.push(mk("ctx tweak".into(), pk.to_vec(), sig.to_vec(), msg.to_vec(), c));
        // Context of 256 bytes: out of range, all must refuse.
        let mut c = ctx.to_vec();
        c.resize(256.max(ctx.len() + 1), 0x42);
        out.push(mk("ctx extended to 256 bytes".into(), pk.to_vec(), sig.to_vec(), msg.to_vec(), c));
    }
    out
}

/// Every single-bit flip of the signature and of the public key (the exhaustive pass).
pub fn exhaustive_flips(set: Set, pk: &[u8], sig: &[u8], msg: &[u8], ctx: &[u8]) -> impl Iterator<Item = Mutant> {
    let sig_n = sig.len() * 8;
    let pk_n = pk.len() * 8;
    let (pk, sig, msg, ctx) = (pk.to_vec(), sig.to_vec(), msg.to_vec(), ctx.to_vec());
    let _ = set;
    (0..sig_n + pk_n).map(move |i| {
        if i < sig_n {
            let mut s = sig.clone();
            flip(&mut s, i / 8, (i % 8) as u32);
            Mutant { label: format!("exhaustive sig byte {} bit {}", i / 8, i % 8), pk: pk.clone(), sig: s, msg: msg.clone(), ctx: ctx.clone() }
        } else {
            let j = i - sig_n;
            let mut p = pk.clone();
            flip(&mut p, j / 8, (j % 8) as u32);
            Mutant { label: format!("exhaustive pk byte {} bit {}", j / 8, j % 8), pk: p, sig: sig.clone(), msg: msg.clone(), ctx: ctx.clone() }
        }
    })
}
