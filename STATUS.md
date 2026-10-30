# Status

What is proved, under which premises, and what is trusted. Updated as work lands.

**Proved so far: nothing.** The Rust skeleton covers Sign_internal and matches upstream; no Lean theorem about it exists yet.

## Target

One end-to-end Lean proof, readable top-down:

- `keygen_correct`: `Impl.api.keygen_*` = FIPS 204 Algorithm 1 / 6.
- `sign_correct`: `Impl.api.sign_*` = Algorithm 2 / 7 (bounded κ budget, `none` on exhaustion).
- `verify_correct`: `Impl.api.verify_*` = Algorithm 3 / 8, for **all** byte strings pk, σ.
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
| Skeleton Sign_internal 44/65/87 | matches upstream, 25 cases per set | `tests/diff.rs` |
| Skeleton extraction | 180 defs, standard axioms (campaign run; to be reproduced in-repo by wave 1 A) | `extracted-lean/` |
