# Assurance case for reviewers

What `ml-dsa-verified` establishes about its public `api`, under which assumptions, what it does not cover, and how to
reproduce each piece of evidence. Every statement cites `STATUS.md`, a Lean source, or a script; where this document
and `STATUS.md` differ, `STATUS.md` wins (it is updated as work lands). Line numbers are for the tree this file was
written on. Nothing here is a FIPS validation or certification: ACVP vectors are test vectors, not a CMVP validation,
and the crate has neither.

**Vocabulary.** "Proved" means a Lean theorem that passes the axiom gate (`scripts/check-axioms.sh`: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`). "Checked" means a tool or test run found no counterexample on the
inputs it covered. "Spec" is `lean/Spec`, our transcription of FIPS 204 (Algorithms 1–3 and 6–48) and FIPS 202
(SHAKE). "Rust" is the code extracted by Charon/Aeneas into `lean/Impl` and modeled there (`RustM` = `ok`, `fail` or
`div`).

## 1. What is proved

The last full done-gate recorded in `STATUS.md` is at 87b4219 (`scripts/lean-check.sh`: pipefail `lake build`, no
`error:` or `sorry`, axiom gate over 632 declarations; STATUS.md lines 5–12). Pin a commit and rerun it (section 6).

### 1.1 The `*_exact` theorems: the API against the unbounded FIPS 204 algorithms, no premises

For each parameter set NN ∈ {44, 65, 87} and every value of the API argument types:

| Rust function | Theorem (Lean file) |
|---|---|
| `api.verify_NN`, `api.verify_internal_NN` | `verify_NN_exact`, `verify_internal_NN_exact` (`Proofs/PartialAPI.lean`, from line 173) |
| `api.keygen_NN` | `keygen_NN_exact` (`Proofs/PartialKeyGen.lean`, e.g. line 305) |
| `api.sign_NN`, `api.sign_internal_NN` | `sign_NN_exact`, `sign_internal_NN_exact` (`Proofs/PartialSign.lean`, e.g. line 999) |
| `api.pk_from_sk_NN` | `pk_from_sk_NN_exact` (`Proofs/PkFromSk.lean`, e.g. line 731) |

In words, for Verify: (a) the Rust never returns `fail`, i.e. no panic, arithmetic overflow or out-of-bounds access in
the Aeneas model; (b) if it returns `ok b`, then `Spec.Verify … F = some b` for some fuel `F`; (c) if `Spec.Verify … F =
some b` at any fuel, it returns `ok b`. The verdict is therefore unique across fuels. KeyGen has the same shape with
`(pk, sk)`. For Sign, (b) and (c) hold with `some σ`, and `api.sign_NN … = ok none` exactly when |ctx| > 255 or the
spec's `Exhausted` holds at some fuel (all `kappaBudget` attempts rejected). The premises that earlier theorems carried
(`RejTerm`, `Params.Std`, buffer lengths) are not in these statements (STATUS.md lines 65–85).

"Fuel" is how the spec makes the FIPS rejection-sampling loops (ExpandA, ExpandS, SampleInBall) total: the spec
returns `none` if a loop runs out of fuel; the Rust loops are unbounded.

### 1.2 `Divergence.lean`: when the Rust does not terminate

`Proofs/Divergence.lean` (`rustM_div_iff`, `verify_NN_div_iff`, `keygen_NN_div_iff`, `sign_NN_div_iff`,
`pk_from_sk_NN_div_iff`, and the prepared-key analogues): the Rust returns `div` exactly when the spec returns no
result at any fuel, i.e. when FIPS 204's unbounded ExpandA or SampleInBall would never terminate on that input. This
is not a termination proof; termination is probabilistic (STATUS.md line 106, ISSUES E-3). Sign's κ loop is bounded,
so Sign diverges only through a sampler (STATUS.md lines 82–85).

### 1.3 Correctness for honest keys

`Proofs/Correctness.lean`: `correct_internal` and `correct_external` at spec level, and `correct_44`, `correct_65`,
`correct_87` for the Rust: `api.keygen_NN` then `api.sign_NN` then `api.verify_NN` returns true. Premises: `StdParams`,
and that KeyGen and Sign return `some` at the same fuel (STATUS.md line 47).

### 1.4 Prepared keys

`Proofs/PreparedVerify.lean` and `PreparedSign.lean`: `verify_prepared_NN_eq`, `verify_internal_prepared_NN_eq`,
`sign_prepared_NN_eq`, `sign_internal_prepared_NN_eq` say that for a key object returned by `verifying_key_NN pk` or
`signing_key_NN sk`, the prepared call equals the one-shot call as a computation (including `fail` and divergence);
`*_exact` versions against the spec exist too. `verifying_key_NN` and `signing_key_NN` never fail and diverge only where
ExpandA does (`Divergence.lean`, `verifying_key_NN_div_iff`). The key structs have private fields and are only built by
those constructors, so the hypothesis `verifying_key_NN pk = ok vk` covers every key a caller can hold (STATUS.md lines
86–97). The `Drop` wipe of a prepared signing key is not in the model.

### 1.5 `SkWellFormed` and `PkFromSk` (optional checks, not FIPS steps)

`Proofs/SkWellFormed.lean` (`skWellFormedAPI_spec`, `skWellFormed_keygen`): `sk_is_well_formed_NN` returns whether every
s1/s2 coefficient that skDecode yields lies in [−η, η]; keys from KeyGen pass. `Proofs/PkFromSk.lean`
(`pk_from_sk_NN_exact`, `skConsistent_keygen`, `skConsistent_sound`): `pk_from_sk_NN` returns `Some pk` iff the range
check passes and recomputing KeyGen steps 5–9 reproduces the stored t0 and tr (K is a free seed, unchecked). `sign_NN`
follows FIPS 204 Algorithm 25 literally and does not call either (ISSUES E-4; STATUS.md lines 44–45). Whether nearcore
needs them depends on how it loads keys.

### 1.6 Cross-check of the spec: `xspec`

The Rust theorems are only as good as the spec. `xspec/` is a separate Lean v4.34 project that vendors `lean/Spec`
byte-identically and proves it equal to ocaml-pq's independent Lean transcription (91 theorems, standard axioms only,
`xspec/headline-theorems.txt`; gate `scripts/xspec/check-axioms.sh`). Top level, both directions, all three parameter
sets: KeyGen, Verify (the Boolean verdict) and Sign, with the documented differences (their Sign loop stops after 821
attempts, theirs-to-ours directions assume their samplers terminate; their key import rejects inconsistent tr/t0)
in STATUS.md line 221. This is a proof about specs, not about the Rust. Other fidelity evidence: ACVP (`spec-acvp`
63/63 in Lean; the Rust runs ACVP keyGen 75/75, sigGen 60/60, sigVer 30/30), Wycheproof (STATUS.md line 218), a
component differential against VCVio (1,345,635 cases, 0 mismatches), three spec reviews against the FIPS PDFs
(STATUS.md lines 205–225).

## 2. What each result assumes: the trusted base

STATUS.md lines 144–148, with the details a reviewer needs:

1. **Spec fidelity** of `lean/Spec` against FIPS 204/202. Evidence is the list in 1.6; none of it is a proof that the
   spec is the standard.
2. **Charon/Aeneas translation** (pins in STATUS.md "Decisions": Charon nightly-2026.09.02, Aeneas build-183e4f0, Rust
   nightly-2026-08-18, Lean v4.31.0). Extraction runs with `--cfg miri`, so the proved code is the source with the
   `cfg(miri)` variants: `field::opaque_u32` and the RISC-V `black_box` are the identity there, and the AVX2 dispatch
   is absent (ISSUES CT-1, CT-2; `docs/object-code-assurance.md` §3.5). Evidence: 345,360 cases of the extracted
   code run against the native Rust, 100% agreement, 4 injected bugs detected (`scripts/impl-eval.sh`).
3. **rustc/LLVM** compile the source faithfully. The theorems are about source semantics, not object code.
4. **The Lean kernel** with `propext`, `Classical.choice`, `Quot.sound`.

Premises the older, non-`_exact` theorems still carry, and their witnesses: `RejTerm` (samplers get enough accepted
samples; probabilistic), the κ budget, `Params.Std` (kernel-checked for 44/65/87) (STATUS.md lines 102–121).

## 3. What is NOT covered

- **Stack exhaustion and out-of-memory are not modeled** (STATUS.md line 72). Worst-case stack was measured, not
  proved: Sign 116/168/240 KB, Verify 50/76/115 KB, KeyGen 64/98/143 KB for 44/65/87 (`tools/stack/README.md`).
- **No top-level kernel witness** that the spec returns `some` for any concrete KeyGen/Sign/Verify input; the sampler
  leaves have witnesses on zero seeds. The `_exact` theorems still cover every input (STATUS.md lines 116–126).
- **Keccak is not cross-checked against ocaml-pq**: both sides of `xspec` use our SHAKE (STATUS.md line 221). Our
  Keccak is proved against `Spec.SHAKE128/256` (`Proofs/Keccak*.lean`) and runs 38 SHAKE KATs; that is the evidence.
- **The opt-in `avx2` feature** (runtime CPUID dispatch, the crate's only `unsafe`) and **the `zeroize` feature** are
  outside the proof. The AVX2 copy of the NTT is covered by `tests/dispatch.rs`, the KAT suites run with the feature,
  and a static scan, not by BINSEC (STATUS.md lines 131–143; `docs/object-code-assurance.md` §3.5).
- **Crate-private internals** exposed by the `internals` feature (`verify_internal` with an inconsistent `Params`;
  `sign_internal`/`keygen_internal` on wrong-length slices) can panic. Without the feature the public surface is `api`
  only (STATUS.md lines 127–130, ISSUES E-1).
- **Out of scope by decision:** HashML-DSA (Algorithms 4/5) and external μ (STATUS.md line 227).
- **Randomness** is the caller's: `keygen_NN` takes ξ and `sign_NN` takes `rnd` (`src/api.rs` module docs).
- **Test harnesses** (ACVP, Wycheproof, differentials, fuzzers) were not themselves reviewed; their sensitivity was
  checked by planting bugs (STATUS.md lines 53–54).
- **No recorded comparison against aws-lc** (the library nearcore calls today for ML-DSA-65, see
  `docs/nearcore-integration.md`). The cross-implementation differential covers libcrux, mldsa-native and RustCrypto
  (STATUS.md line 224).

## 4. Constant-time evidence and its scope

Constant time is checked on compiled probes with BINSEC (relational symbolic execution), not proved in Lean.
"Secure" means BINSEC explored the compiled probe to completion and found no secret-dependent branch, memory address
or division operand for all secret values; the lifter, the solver and "instructions take operand-independent time" are
trusted (STATUS.md line 215; `docs/object-code-assurance.md` §3.2). Verify handles only public data; the property
matters for KeyGen and Sign.

Full sweep at e9a1c74 (2026-11-01), 87 probes per target, counts secure / expected-insecure / unknown / no verdict
(OOM): x86_64 default 80/7/0/0, `nearcore` profile 74/7/6/0, `avx2` dispatch 80/7/0/0, `nearcore-dispatch` 74/6/6/1,
thumbv7em 81/4/0/2, riscv32imac 78/6/2/1, AArch64 without NEON 73/3/11/0. No unexpected leak. Two real leaks were found
and fixed earlier (ISSUES CT-1, CT-2). Limits:

- **Whole-Sign** has no verdict: the censuses report only the public `sample_in_ball` accept branch, or run out of
  memory on thumbv7em and riscv32imac. Sign is covered by its secret-touching pieces (`response_*`, `hint_step_*`,
  ExpandMask, hashing, `prepare_sk`, `signing_key`).
- **Unknowns** (no leak found, no conclusion): six `sk_is_well_formed*` probes under the `nearcore` profiles (BINSEC
  cannot lift SSE2 `movmskpd`); two on riscv32imac; eleven on AArch64 (one stuck solver query each), partly covered by
  split probes (STATUS.md line 215; `checkct/README.md`, "Split probes"). `sk_is_well_formed` branches on coefficient
  signs by design and is documented as not constant time (`src/api.rs`, doc of `sk_is_well_formed_NN`).
- **The `nearcore` CT profile only approximates nearcore's build.** It lacks `overflow-checks = true`, nearcore's x86_64
  target features, and Rust 1.95.0 (STATUS.md line 215; `checkct/README.md` line 38). A matching profile and re-sweep
  are in progress per STATUS.md; until they land, the `nearcore` rows say nothing about nearcore's exact binary.
- **AVX2 and NEON code:** the AVX2 NTT copy is covered by a static scan only; AArch64 builds with NEON cannot be lifted
  (the production Graviton/Apple build); macOS is not covered.
- **Other builds:** verdicts depend on code shape and hold for the builds measured; `zeroize` builds are not probed.
- Hardware timing (variable-latency instructions, speculation, power) is outside the model.

## 5. Reading the evidence together

- "The extracted Rust never fails and equals the FIPS 204 algorithm on every input" is the content of 1.1, modulo the
  trusted base in section 2. That statement is about a source-level model; the nearcore-profile test run in
  `scripts/ci.sh` (`nearcore-test`, overflow checks on) is an empirical check of the compiled code, not a proof.
- Agreement of Verify verdicts across nodes and builds is a consensus property. 1.1 gives it only for nodes that run
  code with the semantics of the extracted source (trusted base item 3). With the `avx2` feature on, the dispatched
  and portable NTT copies are tested equal (`tests/dispatch.rs`), not proved.

## 6. How to reproduce each piece

All heavy commands run on the build box through `rx` (see the repository's rules); the exact job lines are in each
script's header.

| Evidence | Command |
|---|---|
| `*_exact`, prepared, correctness, SkWellFormed, PkFromSk, Divergence; axiom gate | `scripts/lean-check.sh` (full build, no `error:`/`sorry`, then `scripts/check-axioms.sh` over `lean/headline-theorems.txt`) |
| Extraction is clean and `lean/Impl` is current | `scripts/extract-and-build.sh` (STATUS.md "Extraction gate") |
| Spec against ocaml-pq | `scripts/xspec/check-axioms.sh`; executable differential `scripts/xspec/run-diff.sh all` |
| Spec against VCVio | `scripts/diff-vcvio/run.sh all` |
| Spec against ACVP | `lake build spec-acvp && .lake/build/bin/spec-acvp` in `lean/` |
| Extracted Lean vs native Rust | `scripts/impl-eval.sh lean`, `rs`, then `compare` |
| Rust tests (ACVP, Wycheproof, differentials, leaf, API) and builds on thumbv7em, MSRV, nearcore profile, wasm32, fuzz smoke, `cargo deny` | `scripts/ci.sh` |
| Cross-implementation differential and fuzzing | `crosscheck/README.md` ("How to run") |
| Differential fuzzing vs RustCrypto | `fuzz/` (`cargo fuzz run verify_diff`, `sign_diff`, `decode_roundtrip`) |
| Constant time | `checkct/README.md` (`checkct/run-select.sh`, `aarch64.sh`, `run-prepared.sh`) |
| Stack | `tools/stack/run.sh` (`tools/stack/README.md`) |
| Performance | `bench/compare.sh` (`docs/performance-baseline.md` §9) |

## 7. Wording that stays inside the evidence

Safe: "the extracted Rust for every `api` function is proved, with no premises, to never fail and to agree with the
Lean transcription of FIPS 204 whenever either returns (`*_exact`), with the trusted base in `docs/assurance.md` §2";
"constant time is checked by BINSEC on compiled probes for the builds and targets in §4". Not supported: "formally
verified" without that scope; "constant time" for whole-Sign; any statement about aws-lc equivalence; "FIPS validated"
or "FIPS certified".
