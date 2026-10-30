# Status

What is proved, under which premises, and what is trusted. Updated as work lands.

**Proved so far** (standard axioms only, checked by `scripts/check-axioms.sh`):

| Theorem | Statement | Premises |
|---|---|---|
| `Proofs.ntt_correct` | `∃ r, Impl.ntt.ntt w = ok r ∧ Canonical r ∧ toZq r = Spec.NTT (toZq w)` (FIPS 204 Alg 41) | `Canonical w` (all coefficients < q) |
| `Proofs.ntt_inverse_correct` | same for `Impl.ntt.ntt_inverse` and `Spec.NTTInv` (Alg 42) | `Canonical w` |

Not yet independently reviewed. Field-op lemmas (`Proofs/Field.lean`) back them.

## Target

One end-to-end Lean proof, readable top-down:

- `keygen_correct`: `Impl.api.keygen_*` = FIPS 204 Algorithm 1 / 6.
- `sign_correct`: `Impl.api.sign_*` = Algorithm 2 / 7 (bounded κ budget, `none` on exhaustion).
- `verify_correct`: `Impl.api.verify_*` = Algorithm 3 / 8, for **all** byte strings pk, σ of the encoded lengths. The
  core `verify_internal` takes slices and needs `pk.len = pk_len p` and `σ.len = sig_len p` as explicit hypotheses
  (it indexes them directly); the API's fixed-size arrays discharge them. No other premise on pk or σ.
- Stretch: `Verify(pk, M, Sign(sk, M)) = true` for `(pk, sk) = KeyGen(ξ)`.

Named premises (the only ones allowed; each needs a satisfiability witness):

- `RejTerm`: the rejection samplers (RejNTTPoly in ExpandA, RejBoundedPoly in ExpandS, SampleInBall's draw) receive
  enough accepted samples from SHAKE. Probabilistic, not provable.
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
| Wave 3 in progress | API (Alg 1/2/3), zeroize feature, checkct, tests, bench; Lean spec started in parallel | |

Out of scope, by decision: HashML-DSA (Alg 4/5) and external μ. Upstream does not implement them, and ACVP preHash
cases need SHA-2/SHA-3 variants beyond SHAKE, so partial coverage buys little. ACVP preHash and externalMu groups are
skipped and counted in the test output.
