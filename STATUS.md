# Status

What is proved, under which premises, and what is trusted. Updated as work lands.

**Proved so far** (standard axioms only; `scripts/check-axioms.sh` checks every extracted def and every name in
`lean/headline-theorems.txt`, 399 declarations). Each is a `@[step]` refinement spec of an extracted function
against its `lean/Spec` algorithm, under representation relations from `Proofs/Repr.lean`.

Done-gate: a module counts as proved only after `scripts/lean-check.sh` passes: a pipefail-safe `lake build` exits 0,
the full log has no `error:` or `sorry` warning, and the axiom gate passes. Earlier rx jobs could report success on
failed builds (ISSUES T-6). Every row below was re-verified on 2026-10-30 by a cold rebuild of ffc445c (job
`verify-head`).

| Module | What is proved | Extra hypotheses (all satisfiable; witnesses in the files) |
|---|---|---|
| `Proofs/Field.lean`, `Repr.lean` | field ops, masks, infinity norm vs ‖·‖∞, `Params.Valid` for 44/65/87 | canonical inputs |
| `Proofs/NTT*.lean` | NTT, NTT⁻¹ (Alg 41/42); zeta table by `decide +kernel` | canonical inputs |
| `Proofs/NTTOps.lean`, `Coeff.lean` | Alg 44–48, vector NTT, CoeffFromThreeBytes/HalfByte (Alg 14/15) | η ∈ {2, 4} |
| `Proofs/Rounding*.lean` | Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint (Alg 35–40) and polynomial maps | γ2 ∈ {95232, 261888} |
| `Proofs/Encode*.lean` | bit accumulator = SimpleBitPack/BitPack and unpack (Alg 16–19), w1Encode, pk/sk encode/decode (Alg 22–25); decoders for every byte string of the right length | coefficient ranges for the encoders |
| `Proofs/Hint.lean` | HintBitUnpack for every byte string incl. all ⊥ cases; HintBitPack (Alg 20/21) | weight ≤ ω for packing |
| `Proofs/Keccak*.lean` | Keccak-f[1600]; SHAKE128/256 absorb, finalize, squeeze vs `Spec.SHAKE*`; absorbing a then b = absorbing a ‖ b | none |

| `Proofs/SampleA.lean` | RejNTTPoly, ExpandA (Alg 30/32): spec `some` at fuel F ⇒ Rust terminates and agrees | `RejTerm`; witness: RejNTTPoly on a zero seed by `decide +kernel` (ExpandA: `Witnesses.lean`) |
| `Proofs/SampleS.lean` | RejBoundedPoly, ExpandS (Alg 31/33), coefficients within ±η | `RejTerm`; η ∈ {2, 4}; k + ℓ < 256; witnesses by `decide +kernel` |
| `Proofs/SampleBall.lean` | SampleInBall (Alg 29) for every c̃ on which the spec returns `some`, coefficients in {−1, 0, 1} | `RejTerm`; τ ≤ 64; witness: zero c̃ by `decide +kernel` (`SampleBallWitness.lean`) |
| `Proofs/ExpandMask.lean` | ExpandMask (Alg 34) and the range −γ1 < y ≤ γ1 | κ + ℓ ≤ 2¹⁶ (the κ budget); γ1 ∈ {2¹⁷, 2¹⁹} |
| `Proofs/SigCodec.lean` | sigDecode for every byte string of length sigLen; sigEncode, incl. the z mod± q form Sign uses | γ1 ∈ {2¹⁷, 2¹⁹}, λ/4 ≤ 64; weight ≤ ω and z ranges for encoding |
| `Proofs/Steps.lean` | Sign steps 18–21 and 25–26, KeyGen t and Power2Round, Verify t1·2^d and c̃ compare, API ctx prefix | γ2 ∈ {95232, 261888}; d = 13; k ≤ 2²⁰ |

| `Proofs/Bridge.lean` | Z_q infinity norm of a `ReprVec`, ‖LowBits‖∞ ≤ γ2, t1 ∈ [0, 1024) after pkDecode | γ2 ∈ {95232, 261888}; d = 13 |
| `Proofs/Witnesses.lean`, `SampleBallWitness.lean` | kernel witnesses: ExpandA (44, zero seed), ExpandS (65, bundled with `Params.Std`), SampleInBall (44, zero c̃) | none (~16 min of kernel evaluation on a cold build) |
| `Proofs/KeyGen.lean` | **KeyGen_internal (Alg 6)**: Rust pk and sk bytes = spec's, for every ξ on which the spec returns `some` | `Params.Std`; buffer lengths; `RejTerm` (= ExpandA and ExpandS return `some` on the derived seeds, `keygen_isSome_iff`) |

Not yet proved: Sign_internal, Verify_internal (in progress), API. The per-module premises (η, γ1, γ2, τ, d and size
bounds) will be folded into one parameter predicate, proved for 44/65/87, before the top theorems. Wave-4b proofs are
not yet independently reviewed.

## Target

One end-to-end Lean proof, readable top-down:

- `keygen_correct`: `Impl.api.keygen_*` = FIPS 204 Algorithm 1 / 6.
- `sign_correct`: `Impl.api.sign_*` = Algorithm 2 / 7 (bounded κ budget, `none` on exhaustion).
- `verify_correct`: `Impl.api.verify_*` = Algorithm 3 / 8, for **all** byte strings pk, σ of the encoded lengths. The
  core `verify_internal` takes slices and needs `pk.len = pk_len p` and `σ.len = sig_len p` as explicit hypotheses
  (it indexes them directly); the API's fixed-size arrays discharge them. The one other premise is `RejTerm` on attacker-chosen seeds:
  the spec's ExpandA(ρ) (ρ from pk) and SampleInBall(c̃) (c̃ from σ) return `some` at the stated fuel. Finding a seed
  that exhausts the fuel is believed infeasible (SHAKE output would have to reject hundreds of times in a row), but
  the proof does not show it, so this is an assumption about SHAKE, not about honest randomness (ISSUES E-3).
- Stretch: `Verify(pk, M, Sign(sk, M)) = true` for `(pk, sk) = KeyGen(ξ)`.

Named premises (the only ones allowed; each needs a satisfiability witness):

- `RejTerm`: the rejection samplers (RejNTTPoly in ExpandA, RejBoundedPoly in ExpandS, SampleInBall's draw) receive
  enough accepted samples from SHAKE. Probabilistic, not provable. Concretely: the spec samplers are fuel-bounded and
  return `Option`; theorems take "the spec returns `some` at fuel F" as the hypothesis. The Rust loops are unbounded
  (Aeneas `loop`), so without it they can diverge, and no theorem can claim totality for every seed.
- κ budget: Sign is compared with `Sign_internal_bounded B`, B = ⌊(2¹⁶ − ℓ)/ℓ⌋ + 1.

Trusted base: spec fidelity of `lean/Spec` (one independent review plus ACVP cross-check), Charon/Aeneas translation
(pins below), rustc/LLVM, the Lean kernel with `propext`, `Classical.choice`, `Quot.sound`. Zeroize and anything above
`api` are outside the proof.

## Decisions

| Decision | Choice | Why |
|---|---|---|
| Crate | `ml-dsa-verified` (`ml_dsa_verified`), `no_std`, no core dependencies | extraction closure = this crate + core |
| Lean layout | lake package `MlDsaVerified` in `lean/`; extracted code in `lean/Impl/` (Aeneas namespace `Impl`), spec in `lean/Spec/`, proofs in `lean/Proofs/` | names are fixed now so proofs don't churn |
| M′ | `sign_internal(p, sk, m_prefix, m, rnd, sig)` and `verify_internal(p, pk, m_prefix, m, sig)`, with M′ = `m_prefix ‖ m` absorbed in two calls | the external API builds 0 ‖ \|ctx\| ‖ ctx (≤ 257 bytes) on the stack, no alloc; the proof needs one sponge lemma: absorbing two slices = absorbing their concatenation |
| Charon | generic (no `--monomorphize`) | 0 external axioms vs 9 (SURVEY B-X3) |
| Toolchain pins | Charon nightly-2026.09.02, Aeneas build-183e4f0, Rust nightly-2026-08-18 (extraction), Lean v4.31.0 | campaign pins (docs/SURVEY.md) |
| Extraction gate | Aeneas exit 0, no `[Error]`/`[Warning]`, no local opaque function, no referenced external axiom, every extracted def on standard axioms only | any failure is fixed in the Rust code, not worked around |

## Phase plan

Order is fixed: working code before proofs.

### Phase 1: finish the code

- **Wave 1** (parallel, disjoint files)
  - A. In-repo extraction pipeline (`scripts/`, `lean/` lake project, `lean/Impl/`); reproduce the skeleton baseline.
  - B. Leaf algorithms in `src/{sampling,encode,rounding}.rs`: CoeffFromHalfByte (15), RejBoundedPoly (31), ExpandS
    (33), pkEncode/pkDecode (22/23), skEncode (24), sigDecode (27), HintBitUnpack (21), UseHint (40), vector
    Power2Round. Tests in `tests/leaf.rs`.
  - C. ACVP vectors (vendored, gzipped subset) and harness `tests/acvp.rs`; sigGen now, keyGen/sigVer after wave 2.
  - D. `docs/PORTING-MAP.md`: which campaign Lean lemmas port, from where, and what changes.
- **Wave 2**: `keygen::keygen_internal` (Alg 6) and `verify::verify_internal` (Alg 8) in parallel; NTT refinement
  prototype in Lean as soon as the lake project exists (main proof-performance risk).
- **Wave 3**: `api` (Alg 1/2/3, ctx ≤ 255; HashML-DSA Alg 4/5 if cheap), key-cache structs, zeroize (optional
  feature, off during extraction), checkct probes. Re-extract after each module.

Done when: all of the above extract under the gate, and phase-2 tests pass.

### Phase 2: test

Differential tests against RustCrypto `ml-dsa` a3690c4 on randomized inputs (keygen, sign, verify accept/reject,
mutated σ, malformed hints, |ctx| = 256), ACVP keyGen/sigGen/sigVer, random-σ-bytes robustness for Verify (no panics),
checkct/BINSEC if practical, benchmarks vs upstream.

### Phase 3: Lean spec

`lean/Spec/`: FIPS 204 Algorithms 1–3 and 6–48 (+ FIPS 202 Keccak/SHAKE), one `def` per algorithm with step-number
comments. `Sign_internal_bounded`. Evaluated on ACVP vectors in Lean as a fidelity check. Independent review.

### Phase 4: refinement proofs

Bottom-up: field/rounding/hint, NTT, Keccak/sponge, encodings, samplers, ExpandA/S/Mask, KeyGen_internal, Sign
attempt and loop, Verify_internal, then API corollaries. `#print axioms` on every headline theorem, scripted.

### Phase 5 (stretch): correctness

Spec-level `Verify(pk, M, Sign(sk, M)) = true`, transferred through the three top theorems.

## Progress

| Item | State | Evidence |
|---|---|---|
| Sign_internal (Alg 7) 44/65/87 | matches upstream, 25 cases per set; ACVP sigGen pure internal + external, deterministic + hedged: 60/60 | `tests/diff.rs`, `tests/acvp.rs` |
| KeyGen_internal (Alg 6) | pk and sk match upstream on 30 seeds per set; ACVP keyGen 75/75 | `tests/keygen.rs`, `tests/acvp.rs` |
| Verify_internal (Alg 8) | agrees with upstream on 1,260 cases per set (valid, bit flips in c̃/z/h, wrong M, wrong pk); no panic on random pk/σ (debug build); ACVP sigVer pure 30/30 | `tests/verify.rs`, `tests/acvp.rs` |
| Leaf algorithms (15, 21–24, 27, 31, 33, 40) | round trips on upstream bytes, naive references, every HintBitUnpack ⊥ case; reviewed (no bugs; test gaps queued for wave 3) | `tests/leaf.rs` |
| Extraction | 257 defs, Aeneas 0 errors / 0 warnings, no local opaque, no external axioms, standard axioms on all defs | `lean/Impl/extract-report.json` |
| NTT refinement prototype | both directions proved; ~10 s per proof file in `lake build`, ~3 GB, default heartbeats; Rust NTT shape unchanged. Main performance risk retired | `lean/Proofs/NTT*.lean` |
| Public API (Alg 1/2/3) | stateless fixed-array functions per set; ctx prefix on the stack; matches upstream's external interface (72 cases incl. \|ctx\| = 0, 255, 256) | `tests/api.rs` |
| Randomized differential | 200 keygen + 200 sign/verify (M′ up to 10 kB, random prefix split) + 2,000 sign per set; hint-region differential 30k per set | `tests/random_diff.rs`, `tests/leaf.rs` |
| zeroize | optional, off by default and during extraction; wipes sign/keygen secrets | `src/{sign,keygen}.rs` |
| Extraction (current) | 274 defs, gate clean, 278 declarations on standard axioms | `lean/Impl/extract-report.json` |
| Constant time (BINSEC) | 39 probes × 3 targets, signing steps on production code: x86_64 and thumbv7em all secure; riscv32imac 32 secure, 6 unknown (signing-step timeouts), 1 probe artifact; mask-select leak fixed with a RISC-V-only barrier (ISSUES CT-1) | `checkct/` |
| Bench (box, release) | keygen 0.57–0.62×, sign 1.10–1.21×, verify 2.2–2.9× upstream. Verify re-runs ExpandA per call; upstream's `VerifyingKey` caches Â | `examples/bench.rs` |
| Lean spec (phase 3) | `lean/Spec/`: FIPS 202 SHAKE and FIPS 204 Alg 1–3, 6–48, ~1,200 lines; evaluates: `spec-acvp` 63/63 ACVP cases, 38 SHAKE KATs shared with the Rust tests; two independent fidelity reviews: no spec bugs (comment overclaims fixed) | `lean/Spec/`, `lean/SpecTests/` |

Out of scope, by decision: HashML-DSA (Alg 4/5) and external μ. Upstream does not implement them, and ACVP preHash
cases need SHA-2/SHA-3 variants beyond SHAKE, so partial coverage buys little. ACVP preHash and externalMu groups are
skipped and counted in the test output.
