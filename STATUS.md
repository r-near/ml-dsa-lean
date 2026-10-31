# Status

What is proved, under which premises, and what is trusted. Updated as work lands.

**Proved so far** (standard axioms only; `scripts/check-axioms.sh` checks every extracted def and every name in
`lean/headline-theorems.txt`, 632 declarations at 87b4219). Each is a `@[step]` refinement spec of an extracted function
against its `lean/Spec` algorithm, under representation relations from `Proofs/Repr.lean`.

Done-gate: a module counts as proved only after `scripts/lean-check.sh` passes: a pipefail-safe `lake build` exits 0,
the full log has no `error:` or `sorry` warning, and the axiom gate passes. Each agent reuses one stable `rx submit` name for its gates, which keeps
that name's `.lake/build` warm (ISSUES T-7). Earlier rx jobs could report success on
failed builds (ISSUES T-6). Every row below passed this gate at 87b4219 (job `gate-main`, `LEAN CHECK OK`, 632 declarations).
The phase 1–4a rows were also re-verified by a cold rebuild of ffc445c (job `verify-head`).

| Module | What is proved | Extra hypotheses (parameter facts witnessed for 44/65/87; sampler premises: leaf witnesses, see below) |
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
| `Proofs/KeyGen.lean` | **KeyGen_internal (Alg 6)**: Rust pk and sk bytes = spec's, for every ξ on which the spec returns `some` | `Params.Std`; buffer lengths; `RejTerm` (= ExpandA and ExpandS return `some` on the derived seeds, `keygen_isSome_iff`); unconditional version without `RejTerm`: `PartialKeyGen.lean` |

| `Proofs/Verify.lean` | **Verify_internal (Alg 8)**: Rust verdict = spec's, for every pk and σ (any length: a wrong length returns false on both sides) and every M′ = m_prefix ‖ m | `Params.Std`; `RejTerm` (`verify_isSome_iff`: if sigDecode succeeds, ExpandA(ρ) and SampleInBall(c̃) return `some`; malformed hints and wrong lengths always give `some false`) |
| `Proofs/Sign.lean` | **Sign_internal (Alg 7, bounded)**: spec `some σ` (any budget B) ⇒ Rust returns true and writes σ; all `kappaBudget` attempts rejected with enough sampler fuel (`Exhausted`) ⇒ Rust returns false and leaves the output buffer untouched (`r.2 = sig`). For every sk byte string of length skLen | `Params.Std`; buffer lengths; `RejTerm` (`sign_isSome_iff`, `sign_none_cases`: the spec's `none` splits into fuel failure vs budget exhaustion); unconditional version without `RejTerm`: `PartialSign.lean` |

`Params.Std` = `Params.Valid` ∧ `StdParams`; `StdParams` (d = 13, γ1/γ2/η of the standard sets, τ ≤ 64, k + ℓ < 256,
k ≤ 8, ℓ ≥ 1, ω ≤ 255, …) holds for ML-DSA-44/65/87 (`ML_DSA_NN_std`).

| `Proofs/API.lean` | **Public API (Alg 1/2/3)** for 44/65/87: `keygen_NN`, `verify_NN` (incl. \|ctx\| > 255 → false), `sign_NN` (σ on success; `none` for \|ctx\| > 255 and on exhaustion); M′ = 0 ‖ \|ctx\| ‖ ctx ‖ M matches the spec | the spec returns `some` (or `Exhausted`); nothing on the contents of pk, sk, σ, M, ctx |
| `Proofs/APIInternal.lean` | **Internal API (Alg 7/8 without ctx)** for 44/65/87: `sign_internal_NN` (σ on success, `none` on exhaustion), `verify_internal_NN`; and the "only if" for `none`: `sign_NN`/`sign_internal_NN` return `none` only when the spec fails at every fuel, with the cases spelled out (\|ctx\| > 255, pre-loop failure, loop failure or exhaustion) | as for `API.lean` |
| `Proofs/SkWellFormed.lean` | **Optional key check (not a FIPS step)**: `api.sk_is_well_formed_NN sk` returns `skWellFormed`, i.e. every s1/s2 coefficient skDecode yields lies in [−η, η] (t0 is always in range); keys from KeyGen are well-formed (`skWellFormed_keygen`); kernel witnesses for both outcomes. Sign does not call it (E-4) | none for the per-set theorems; KeyGen returns `some` for `skWellFormed_keygen` |
| `Proofs/PkFromSk.lean` | **Optional key-consistency check (not a FIPS step)**: `api.pk_from_sk_NN sk` returns `Some pk` iff s1/s2 are in [−η, η] and recomputing KeyGen steps 5–9 from (ρ, s1, s2) reproduces the stored t0 and tr (K is a free seed, unchecked); never panics, agrees exactly with `skConsistentR` at any fuel; keys from KeyGen pass (`skConsistent_keygen`); acceptance implies the stored t0 and tr match (`skConsistent_sound`). Agrees with mldsa-native's `pk_from_sk` on 14 variants per set. Constant time: its steps are BINSEC-probed individually and its comparisons accumulate without early exit; the function as a whole has no probe | none for the API theorems |
| `Proofs/Divergence.lean` | For every API function: the Rust diverges iff the spec returns no result at every fuel (Sign: and \|ctx\| ≤ 255 and no `Exhausted` at any fuel) | none |
| `Proofs/Corr*.lean`, `Correctness.lean` | **Correctness (phase 5)**: for honest keys, Verify accepts Sign's output. Spec level, internal (`correct_internal`) and external with ctx (`correct_external`); Rust: `api.keygen_NN` → `api.sign_NN` → `api.verify_NN` returns true (`correct_44/65/87`). Building blocks: NTT algebra and convolution, ‖c·s‖∞ ≤ β, Power2Round/HighBits/UseHint lemmas, codec round trips, SampleInBall weight = τ | `StdParams`; KeyGen and Sign return `some` (RejTerm, κ budget), same fuel for all three |

Reviews: the leaf proofs (phase 4a/4b) and the three internal top theorems were independently reviewed, and so were
the API theorems, the `verify_internal` length guard (7bb0dbe) and the Sign exhaustion change (4d86309); no
blockers, findings folded into the sections below. A fourth review covered `APIInternal`, `SkWellFormed`, the
api-only visibility change and the new tests (12 more mutants, all killed); no soundness defects, doc fixes in 4adba1e.
The test harnesses (ACVP, Wycheproof, the three differentials, the fuzz targets) were not themselves reviewed; their
sensitivity was checked by planting bugs instead.

## Target

One end-to-end Lean proof, readable top-down:

- `keygen_correct`: `Impl.api.keygen_*` = FIPS 204 Algorithm 1 / 6.
- `sign_correct`: `Impl.api.sign_*` = Algorithm 2 / 7 (bounded κ budget, `none` on exhaustion).
- `verify_correct`: `Impl.api.verify_*` = Algorithm 3 / 8, for **all** byte strings pk, σ. The core
  `verify_internal` takes slices and starts with a length guard (`pk.len != pk_len p` or `σ.len != sig_len p` returns
  false; input validation consistent with FIPS 204), so `verify_internal_spec` has no length hypotheses.
  **No premises at all since c9f6663** (`Proofs/PartialAPI.lean`, `verify_NN_exact`, `verify_internal_NN_exact`):
  for every `pk`, `m`, `ctx`, `σ` of the API types, (a) the extracted Rust never returns `fail` (no panic, overflow
  or out-of-bounds in the Aeneas model); (b) if it returns `ok b`, then `Spec.Verify … F = some b` for some fuel `F`;
  and (c) if `Spec.Verify … F = some b` for any `F`, it returns `ok b`. Hence `b` is unique across fuels, and the
  Rust diverges exactly when the spec returns `none` at every fuel, i.e. when FIPS 204's unbounded ExpandA or
  SampleInBall would never terminate (`Proofs/Divergence.lean`). The proof uses
  generic loop lemmas proved by fixpoint induction (`Proofs/Partial.lean`) and fuel monotonicity of the samplers.
  Not modeled: stack exhaustion and out-of-memory.
- `keygen_correct`, **no premises since 1be1625** (`Proofs/PartialKeyGen.lean`, `keygen_NN_exact`): for every seed
  ξ, (a) the extracted Rust never returns `fail`; (b) if `api.keygen_NN ξ = ok (pk, sk)` then `Spec.KeyGen … F =
  some (pk, sk)` for some fuel `F`; (c) if `Spec.KeyGen … F = some (pk, sk)` at any `F`, it returns `ok` of arrays
  holding that pair. So the pair is unique across fuels, and the Rust diverges exactly when the spec returns `none`
  at every fuel (`Proofs/Divergence.lean`).
- `sign_correct`, **no premises since 0074e0c** (`Proofs/PartialSign.lean`, `sign_NN_exact`,
  `sign_internal_NN_exact`): for every `sk`, `m`, `ctx`, `rnd` of the API types, (a) never `fail`; (b) if the Rust
  returns `some σ` then `Spec.Sign … F = some σ` for some `F`; (c) if `Spec.Sign … F = some σ` at any `F`, the Rust
  returns `some σ`; (d) it returns `none` iff |ctx| > 255 or `Exhausted` holds at some fuel for M′ = 0 ‖ |ctx| ‖ ctx
  ‖ m: ExpandA and all `kappaBudget` SampleInBall calls finished within the fuel and every attempt was rejected. The
  Rust's cap κ + ℓ ≤ 2¹⁶ is the same as `kappaBudget`; it is an implementation bound FIPS 204 allows (κ is encoded
  in 16 bits by ExpandMask), not a divergence from FIPS. Divergence happens only when no fuel lets ExpandA and the
  SampleInBall calls of the attempts that run terminate (`Proofs/Divergence.lean`).
- Prepared keys (`Proofs/PreparedVerify.lean`, `PreparedSign.lean`): `verifying_key_NN` / `signing_key_NN` never
  `fail` (they diverge only where ExpandA does), and for every key they return, `verify_prepared_NN vk … =
  verify_NN pk …` and `sign_prepared_NN ssk … = sign_NN sk …` as computations (including `fail` and divergence),
  with `*_exact` theorems against `Spec.Verify` / `Spec.Sign` in the same shape as above. The structs have private
  fields and are only built by those functions, so the premise `verifying_key_NN pk = ok vk` holds for every value a
  caller can hold.
- These partial theorems restrict what the Rust may return; they give no positive guarantee for a concrete input.
  That the spec returns `some` for a given input still has no kernel witness at the top level (see below).
- Stretch: `Verify(pk, M, Sign(sk, M)) = true` for `(pk, sk) = KeyGen(ξ)`. **Done** (`Proofs/Correctness.lean`).

Named premises (the only ones allowed; each needs a satisfiability witness):

- `RejTerm`: the rejection samplers (RejNTTPoly in ExpandA, RejBoundedPoly in ExpandS, SampleInBall's draw) receive
  enough accepted samples from SHAKE. Probabilistic, not provable. Concretely: the spec samplers are fuel-bounded and
  return `Option`; theorems take "the spec returns `some` at fuel F" as the hypothesis. The Rust loops are unbounded
  (Aeneas `loop`). The unconditional `*_exact` theorems for KeyGen, Sign and Verify (above) do not carry it; the
  older premised theorems (`keygen_internal_spec`, `sign_internal_spec_some`, …) still do.
- κ budget: Sign is compared with `Sign_internal_bounded B`, B = ⌊(2¹⁶ − ℓ)/ℓ⌋ + 1.

Witness status of the premises:

- Parameter premises (`Params.Std`): kernel-checked for 44/65/87.
- Sampler premises at the leaves: kernel witnesses on zero seeds (RejNTTPoly, ExpandA for 44, RejBoundedPoly and
  ExpandS for 44 and 65, SampleInBall for 44).
- Top-level `some` premises of KeyGen/Sign/Verify: **no kernel witness** for any concrete input (the derived seeds
  would need SHAKE on ξ/pk/σ plus the full samplers). The `*_isSome_iff` lemmas reduce them to sampler facts; the
  evidence they hold is the spec's ACVP run (`spec-acvp`, 63/63), which is outside the kernel.
- `Exhausted` (Sign's `false` case, all κ attempts rejected): satisfiable only by a counting argument; no witness,
  probability about 2^-thousands per input, untestable in practice.

Not covered by any theorem:

- Positive existence: that the spec returns `some` for a concrete input has no kernel witness at the top level
  (KeyGen/Sign/Verify); the sampler leaves have witnesses. Every input is covered by the unconditional theorems
  above, which say the Rust never panics and agrees with the spec whenever either returns.
- The crate-private internals, public only under the `internals` feature (tests, fuzzing): `verify_internal` with a
  `Params` inconsistent with its `K`/`L` (the decoders index by `K`/`L`, so it can panic), and `sign_internal` /
  `keygen_internal` with wrong-length slices (E-1). Without the feature the public surface is `api` only, and every
  `api` function has a theorem; they pass fixed-size arrays and consistent parameters.
- The opt-in `avx2` feature (x86_64): a runtime CPUID check picks between two compilations of the same proved NTT
  bodies (portable and `#[target_feature(enable = "avx2")]`). The shim is the crate's only `unsafe`
  (`forbid(unsafe_code)` without the feature, `deny` plus one `allow` on the shim with it); BINSEC 0.11.3 cannot lift
  the AVX2 copy, which is covered by a static scan and `tests/dispatch.rs` only (`docs/object-code-assurance.md`
  §3.5). Off by default. `-C target-cpu=x86-64-v3` is 4–9% faster again with no `unsafe` and no dispatch, but the
  binary then requires AVX2 and BINSEC cannot lift its vector code either.
- The `zeroize` build (the proved code is extracted with it off; the wipes come after the outputs are written) and
  stack use. Measured worst case (`tools/stack/`, release, statically and by stack painting): Sign 115/167/239 KB,
  Verify 59/87/131 KB, KeyGen 58/90/134 KB for 44/65/87 on x86_64; other targets within 4%. The earlier "60 KB" was wrong.

Trusted base: spec fidelity of `lean/Spec` (three independent reviews, ACVP and Wycheproof cross-checks, a component
differential against VCVio's independent formalization, and equivalence proofs against ocaml-pq's independent Lean transcription
of every algorithm from the arithmetic leaves up to KeyGen, Sign and Verify, with our SHAKE in both; see Progress), Charon/Aeneas translation
(pins below; differentially tested, see Progress), rustc/LLVM, the Lean kernel with `propext`, `Classical.choice`, `Quot.sound`. Zeroize, the opt-in AVX2 dispatch shim and anything above
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
| Extraction (current) | 342 defs, gate clean, standard axioms on all defs | `lean/Impl/extract-report.json` |
| Constant time (BINSEC) | 74 probes per target, release builds: every function that touches secret data in KeyGen and Sign, including `sk_is_well_formed`, ExpandS, NTT of s1, t, Power2Round, skEncode/Decode, the Sign steps, plus a whole-`sign_internal` census and a positive control (insecure everywhere, as it should be). "Secure" means BINSEC explored the compiled probe to completion and found no secret-dependent branch, memory address or division operand, for all secret values; the lifter and constant instruction latency are trusted. Results at 069b439 (before batch 1; a full sweep of the merged tree is pending): x86_64 64 secure / 3 insecure / 4 unknown, thumbv7em 69/2/0, riscv32imac 66/3/2; the expected insecure ones are RejBoundedPoly (branches on its public accept pattern) and the standalone riscv `ct_lt_mask`. **One real leak, fixed: CT-2** (Decompose edge select on x86_64, 069b439); after the fix every x86_64 signing-step probe is secure in the default and nearcore-like profiles. AArch64 (own script, BINSEC 0.11.3): scalar build all secure; the NEON build's vectorized probes can't be lifted (`umax`/`umin`). The whole-Sign census never completes (it reaches public sampler branches) | `checkct/` |
| Bench (box, nearcore profile, 2026-10-31) | ML-DSA-87, µs, default / `avx2` feature / x86-64-v3: keygen 229 / 193 / 180, sign-det 714 / 466 / 429 (prepared key 543 / 312 / 285), verify 235 / 189 / 175 (prepared key 82 / 39 / 35). Baseline before batch 1: 233 / 798 / 242 µs. Prepared-key verify with AVX2 (39 µs) is below the uncached AVX2 verify of mldsa-native (55 µs) and libcrux (109 µs), a different operation (no pk decode, ExpandA or NTT(t1) per call); uncached sign/verify are 1.7–3.8× behind them | `docs/performance-baseline.md` §7, `bench/` |
| Aeneas translation (differential) | the extracted `Impl` compiled and run against the native Rust on the same inputs: 345,360 cases, 100% agreement (Keccak, field, NTT, rounding, samplers, codecs, and the full public API incl. 225 ACVP-derived cases); 4 injected bugs all detected | `scripts/impl-eval.sh`, `lean/SpecTests/ImplEval.lean`, `examples/impl_eval.rs` |
| Wycheproof (C2SP, d17cc89) | Rust: 1063 vectors pass, 0 fail, 6 known (E-4: out-of-range secret keys), 69 skipped (external-μ only, out of scope); Lean spec: 928/928 agree (631 verify, 236 sign, 61 keygen) | `tests/wycheproof.rs`, `lean/SpecTests/Wycheproof.lean` |
| Third spec review (FIPS 204/202 PDFs) | every `lean/Spec` def checked step by step against the PDFs and NIST's potential-updates list; whole-domain rounding check against a FIPS-literal Python reference; SHAKE vs hashlib around the rate; no transcription errors | review notes (not committed) |
| VCVio component differential (aae1c9c) | `lean/Spec` vs VCVio's independent `MLDSA.Concrete`, both compiled: 1,345,635 in-precondition cases agree, 0 mismatches (Power2Round, Decompose/HighBits/LowBits, UseHint exhaustive over Z_q for each set; MakeHint, NTT/NTTInv/MultiplyNTT, all bit packers and key/sig codecs, HintBitPack/Unpack sampled with edges); both also match a FIPS-literal Python reference. Only difference: HintBitPack with more than ω ones (outside Alg 20's precondition; the two sides handle overflow differently). VCVio's compiled NTT runs its loop kernels; those were checked against its structural definitions on 600 vectors | `scripts/diff-vcvio/`, `lean/SpecTests/DiffVCVio.lean` |
| ocaml-pq spec cross-check (ceeb278, ISC) | **Proved equal** to ocaml-pq's independent Lean transcription, in a separate Lean v4.34 project that vendors `lean/Spec` byte-identically (91 theorems, standard axioms only; `xspec/headline-theorems.txt` separates top-level equivalences from supporting lemmas). Leaves: ModPM, Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint, CoeffFromHalfByte/ThreeBytes, NTT, NTT⁻¹, MultiplyNTT, AddNTT, the bit/byte conversions, all packing and encodings, ExpandMask; skDecode characterized exactly. Samplers, both directions: RejNTTPoly, RejBoundedPoly, SampleInBall, ExpandA, ExpandS. **Top level, both directions, all three parameter sets:** KeyGen; Verify (the Bool verdict, so accept and reject; right-length pk and σ); Sign_internal and Sign on the key our skDecode produces, composed with their decodeSk where it accepts. Documented differences: their Sign loop stops after 821 attempts (a probability argument, not a proved bound), ours after κ budget; if ours returns σ at attempt a, theirs returns the same σ iff a < 821 and none otherwise; their key import also rejects keys with inconsistent tr/t0, which FIPS and ours accept. The theirs-to-ours directions assume their rejection samplers terminate on the given input (their samplers return a default otherwise); the ours-to-theirs theorems derive those premises whenever ours returns. Not compared: Keccak (both sides use our SHAKE), and the default fuel when ours returns none. **Differential** (1.36M compiled lines, both sides also checked against ACVP answers) remains as an executable check; sensitivity: an injected UseHint bug gave 8,129 differing lines | `xspec/`, `scripts/xspec/` |
| Proof mutation testing | 29 semantic mutants of `src` (rounding edge cases, hint checks, norm bounds, NTT⁻¹ layers and scale, sampler indices, seeds and hash inputs, κ budget, ctx and length guards, parameter constants): every one breaks the Lean build at the spec theorem of the mutated function. `cargo test` missed 5 (λ/4-byte c̃ compare, `infinity_norm` threshold, HintBitUnpack's count > ω check, Verify's ‖z‖∞ `<`, κ budget). About a third fail as unprovable goals, the rest as script-shape breaks. Regression tests now kill four of the five (`tests/mutants.rs` for the norm threshold, hint count and ‖z‖∞; the `prefix_eq` unit test in `src/verify.rs` for the c̃ compare, which no end-to-end test can reach); the κ budget stays proof-only | harness not committed (throwaway) |
| Differential fuzzing vs upstream `ml-dsa` (a3690c4) | about 50 minutes per target on the box, 0 crashes, 0 disagreements: `verify_diff` 12.1M execs (mutated c̃/z/hints/pk, ctx 0–256, wrong lengths; 96.7% region coverage of `src`), `sign_diff` 787k (keygen, `sign_internal`, hedged and deterministic `sign` byte-identical; 98.2%), `decode_roundtrip` 1.1M (Sign on arbitrary sk bytes never panics; matches upstream wherever upstream accepts the key). Upstream panics on s1/s2 coefficients outside [−η, η], which FIPS 204 Alg 25 leaves undefined (E-4); the κ-exhaustion path was never reached. Sensitivity: with the hint zero-padding check removed, `verify_diff` reported ours=true, upstream=false after about 3,800 runs (9 s); a removed `count > ω` check was not found in 180 s (it rarely changes the verdict) | `fuzz/` |
| Cross-implementation differential (libcrux-ml-dsa 0.0.11 portable + AVX2, mldsa-native v2.0.0 C + AVX2, RustCrypto a3690c4) | 0 disagreements, 0 crashes: 1.05M keygens and 1.5M signatures byte-identical; 15.4M verify cases (every single-bit flip of σ and pk for 60 cases per set, plus mutation classes covering c̃, z, hint encodings, pk; about 185M verify calls), all 150k honest signatures accepted by all; fuzzing 3.66M `verify_xdiff` and 195k `sign_xdiff` executions. Sensitivity: with the hint zero-padding check removed, 4,012 disagreements (ours accepted, all others rejected). Malformed sk (FIPS-undefined): ours, libcrux and mldsa-native sign identically; RustCrypto panics; mldsa-native's `pk_from_sk` also rejects inconsistent t0/tr/ρ | `crosscheck/` |
| Lean spec (phase 3) | `lean/Spec/`: FIPS 202 SHAKE and FIPS 204 Alg 1–3, 6–48, ~1,200 lines; evaluates: `spec-acvp` 63/63 ACVP cases, 38 SHAKE KATs shared with the Rust tests; two independent fidelity reviews: no spec bugs (comment overclaims fixed) | `lean/Spec/`, `lean/SpecTests/` |

Out of scope, by decision: HashML-DSA (Alg 4/5) and external μ. HashML-DSA: upstream does not implement it (no
differential oracle), and ACVP preHash cases need SHA-2/SHA-3 hash functions beyond SHAKE, each another primitive to
implement and prove. External μ: upstream does implement it (`sign_mu_*`, `verify_mu`), so it is cheaper, but FIPS
204 describes it only as an allowed variant of Alg 7/8, so it would need its own spec entry and theorems; it was
deferred, not ruled out. ACVP preHash/externalMu groups and Wycheproof μ-only vectors are skipped and counted.