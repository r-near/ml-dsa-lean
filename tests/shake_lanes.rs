//! `keccak::Shake` moves whole 8-byte lanes when it can and single bytes otherwise. This compares it with a plain
//! byte-at-a-time sponge (the same permutation, no lane code) for every split of the input across `absorb` calls and
//! every chunking of the output across `squeeze` calls that the lane/byte boundary cases need: lane-aligned and
//! unaligned starts, calls shorter than a lane, and runs that cross the rate boundary.

use ml_dsa_lean::keccak::{Shake, keccak_f1600};

/// Byte-at-a-time reference SHAKE (FIPS 202 sponge on bytes, little-endian lanes).
fn reference(rate: usize, msg: &[u8], out_len: usize) -> Vec<u8> {
    let mut st = [0u64; 25];
    let xor = |st: &mut [u64; 25], i: usize, b: u8| st[i / 8] ^= (b as u64) << (8 * (i % 8));
    let mut pos = 0;
    for &b in msg {
        xor(&mut st, pos, b);
        pos += 1;
        if pos == rate {
            keccak_f1600(&mut st);
            pos = 0;
        }
    }
    xor(&mut st, pos, 0x1F);
    xor(&mut st, rate - 1, 0x80);
    keccak_f1600(&mut st);
    let mut out = Vec::with_capacity(out_len);
    let mut pos = 0;
    while out.len() < out_len {
        if pos == rate {
            keccak_f1600(&mut st);
            pos = 0;
        }
        out.push((st[pos / 8] >> (8 * (pos % 8))) as u8);
        pos += 1;
    }
    out
}

/// Small deterministic generator (no dependencies).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn run(make: fn() -> Shake, rate: usize, rng: &mut Lcg, msg_len: usize, out_len: usize) {
    let msg: Vec<u8> = (0..msg_len).map(|_| rng.next() as u8).collect();
    let want = reference(rate, &msg, out_len);

    let mut sh = make();
    let mut at = 0;
    while at < msg_len {
        // Mix tiny pieces (a few bytes), lane-sized pieces and long pieces.
        let n = match rng.below(4) {
            0 => 1 + rng.below(7),
            1 => 8,
            2 => 1 + rng.below(40),
            _ => 1 + rng.below(2 * rate),
        };
        let n = n.min(msg_len - at);
        sh.absorb(&msg[at..at + n]);
        at += n;
        if rng.below(5) == 0 {
            sh.absorb(&[]);
        }
    }
    sh.finalize();
    let mut got = vec![0u8; out_len];
    let mut at = 0;
    while at < out_len {
        let n = match rng.below(5) {
            0 => 1 + rng.below(7),
            1 => 8,
            2 => 3,
            3 => 1 + rng.below(40),
            _ => 1 + rng.below(2 * rate),
        };
        let n = n.min(out_len - at);
        sh.squeeze(&mut got[at..at + n]);
        at += n;
        if rng.below(5) == 0 {
            sh.squeeze(&mut []);
        }
    }
    assert_eq!(got, want, "rate {rate}, message {msg_len} bytes, output {out_len} bytes");
}

#[test]
fn lane_sponge_matches_byte_reference() {
    let mut rng = Lcg(0x5EED);
    for (make, rate) in [(Shake::shake128 as fn() -> Shake, 168), (Shake::shake256 as fn() -> Shake, 136)] {
        for msg_len in (0..=3 * rate + 9).chain([5 * rate, 5 * rate + 1, 10 * rate - 1]) {
            for _ in 0..6 {
                let out_len = 1 + rng.below(3 * rate + 16);
                run(make, rate, &mut rng, msg_len, out_len);
            }
        }
        // Long outputs through the rate boundary, in one call and in pieces.
        for out_len in [rate - 1, rate, rate + 1, 2 * rate, 5 * rate + 3] {
            run(make, rate, &mut rng, 34, out_len);
            let msg = vec![0x5Au8; 34];
            let mut sh = make();
            sh.absorb(&msg);
            sh.finalize();
            let mut one = vec![0u8; out_len];
            sh.squeeze(&mut one);
            assert_eq!(one, reference(rate, &msg, out_len));
        }
    }
}
