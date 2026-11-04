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

The last full done-gate passed at e917292 (2026-11-03), 765 declarations (`scripts/lean-check.sh`: pipefail `lake build`,
no `error:` or `sorry`, axiom gate over `lean/headline-theorems.txt`; the gate definition is at the top of `STATUS.md`).
Pin a commit and rerun it (section 6).

### 1.1 The `*_exact` theorems: the API against the unbounded FIPS 204 algorithms, no premises

For each parameter set NN ∈ {44, 65, 87} and every value of the API argument types:

| Rust function | Theorem (Lean file) |
|---|---|
| `api.verify_NN`, `api.verify_internal_NN` | `verify_NN_exact`, `verify_internal_NN_exact` (`Proofs/PartialAPI.lean`, from line 173) |
| `api.keygen_NN` | `keygen_NN_exact` (`Proofs/PartialKeyGen.lean`, e.g. line 305) |
| `api.sign_NN`, `api.sign_internal_NN` | `sign_NN_exact`, `sign_internal_NN_exact` (`Proofs/PartialSign.lean`, e.g. line 999) |
| `api.pk_from_sk_NN` | `pk_from_sk_NN_exact` (`Proofs/PkFromSk.lean`, e.g. line 731) |

In words, for Verify: (a) the Rust never returns `fail`, i.e. no panic, arithmetic overflow or out-of-bounds access in
the Aeneas model (stack exhaustion and out-of-memory are not modeled, and the Rust can diverge, `div`, exactly when the
spec returns no result at any fuel, 1.2); (b) if it returns `ok b`, then `Spec.Verify … F = some b` for some fuel `F`; (c) if `Spec.Verify … F =
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
byte-identically and proves it equal to ocaml-pq's independent Lean transcription (standard axioms only; 144 headline
names in `xspec/headline-theorems.txt`, 142 equivalence theorems and 2 kernel known-answer tests; gate
`scripts/xspec/check-axioms.sh`; STATUS.md "ocaml-pq spec cross-check" row). Top level, both directions, all three
parameter sets, with these scope qualifiers from STATUS.md:

- **KeyGen**: equivalence of the public key and secret key.
- **Verify**: the Boolean verdict (accept and reject), for a right-length pk and σ.
- **Sign** (`Sign_internal` and `Sign`): on the key our `skDecode` produces, composed with their `decodeSk` where it
  accepts.
- **Sign loop bound**: their Sign loop stops after 821 attempts (a probability argument, not a proved bound), ours
  after the κ budget. If ours returns σ at attempt a, theirs returns the same σ iff a < 821 and none otherwise.
- **Key import**: their import also rejects keys with inconsistent tr/t0, which FIPS 204 and our spec accept.
- **Samplers**: the theirs-to-ours directions assume their rejection samplers terminate on the given input (they
  return a default otherwise); the ours-to-theirs theorems derive those premises whenever ours returns.
- Not compared: the default fuel when ours returns `none`.

**Keccak** is cross-checked: our Keccak-f[1600] and SHAKE128/256 are proved equal to ocaml-pq's independent FIPS 202
transcription (bit strings, every input and output length, round by round) and to its `Mldsa_keccak` model, and
KeyGen, Verify and Sign are restated on ocaml-pq's own SHAKE (`*_ocaml`). Limits: two reject-case Verify lemmas that
hold for any XOF are not restated, and the `keyGen_*_ocaml` premises still name a seed computed with our H. The check
is only as independent as ocaml-pq's FIPS 202 transcription is of ours; its anchor is their published-digest proofs. The
two kernel known-answer tests (empty message) are tests, not an equivalence.

This is a proof about specs, not about the Rust. Other fidelity evidence: ACVP (`spec-acvp` 63/63 in Lean; the Rust
runs ACVP keyGen 75/75, sigGen 60/60, sigVer 30/30), Wycheproof (STATUS.md "Wycheproof" row), a component differential
against VCVio (1,345,635 cases, 0 mismatches), and three spec reviews against the FIPS PDFs. Those reviews were
internal: reviewer passes run within this project (STATUS.md calls them "independent", meaning independent of the
author of the spec, not third parties), and the notes of the third are not committed. **No third-party audit and no
CMVP or other validation of this crate or its spec exists.**

## 2. What each result assumes: the trusted base

STATUS.md lines 144–148, with the details a reviewer needs:

1. **Spec fidelity** of `lean/Spec` against FIPS 204/202. Evidence is the list in 1.6 (internal reviews, test vectors,
   and equivalence to other transcriptions); none of it is a proof that the spec is the standard, and none of it is a
   third-party audit.
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
- **Top-level kernel witness for one input only.** `correct_44_nonvacuous` (`lean/Proofs/TopWitnessCorrect.lean`,
  checked by `scripts/witness-check.sh`) shows the hypotheses of `correct_44` hold for one ML-DSA-44 input: KeyGen,
  Sign and Verify (`some true`) all evaluated in the kernel, and the Rust keygen → sign → verify chain returns true.
  ML-DSA-65/87 and other inputs have no witness. The `_exact` theorems still cover every input.
- **Keccak is cross-checked with limits**: `xspec` proves our Keccak-f[1600] and SHAKE128/256 equal to ocaml-pq's FIPS 202
  transcription, and restates KeyGen, Verify and Sign on their SHAKE, but two reject-case Verify lemmas are not
  restated, the `keyGen_*_ocaml` premises still name a seed computed with our H, and independence is only that of
  ocaml-pq's transcription (section 1.6). Our Keccak is also proved against `Spec.SHAKE128/256` (`Proofs/Keccak*.lean`)
  and runs 38 SHAKE KATs.
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
- **The aws-lc comparison is a test, not a proof.** `tests/awslc_diff.rs` compares verdicts against aws-lc-rs 1.18.2,
  the library nearcore calls today for ML-DSA-65: 0 differences in about 3.2M verify comparisons (incl. malformed
  hints, wrong lengths, forged boundary signatures) and 610 Wycheproof vectors, byte-identical KeyGen on 15,000
  seeds. Only ctx = "" is compared, signatures are cross-verified rather than compared (aws-lc signs hedged), and a
  dropped "decreasing count" hint check would not be visible at the verdict level (see the STATUS.md aws-lc row).

## 4. Constant-time evidence and its scope

Constant time is checked on compiled probes with BINSEC (relational symbolic execution), not proved in Lean.
"Secure" means BINSEC explored the compiled probe to completion and found no secret-dependent branch, memory address
or division operand for all secret values; the lifter, the solver and "instructions take operand-independent time" are
trusted (STATUS.md line 221; `docs/object-code-assurance.md` §3.2). Verify handles only public data; the property
matters for KeyGen and Sign.

Full sweep at 15b4ce2 (2026-11-04), 113 entrypoints per run plus two whole-Sign censuses. Counts secure / expected-insecure /
unexpected-insecure / unknown / no verdict (OOM) on the 87-probe basis of the previous sweep (e9a1c74, 2026-11-01; then
15b4ce2): x86_64 default 80/7/0/0/0, then 80/6/0/0/1; `nearcore` profile 74/7/0/6/0, then 80/7/0/0/0; `avx2` dispatch
80/7/0/0/0, then 80/6/0/0/1; `nearcore-dispatch` 74/6/0/6/1, then 80/6/0/0/1; thumbv7em 81/4/0/0/2, unchanged; riscv32imac
78/6/0/2/1, unchanged; AArch64 without NEON 73/3/0/11/0, unchanged (`checkct/README.md`, "Full sweep at 15b4ce2"). No
unexpected leak. Three real leaks were found and fixed (ISSUES CT-1, CT-2, CT-3). Limits:

- **Whole-Sign** has no verdict: the censuses report only the public `sample_in_ball` accept branch, run out of memory
  (thumbv7em, riscv32imac, and now the x86_64 default and `dispatch` prepared census at 120 GB), or are cut at the NTT
  under nearcore's exact build. Sign is covered by its secret-touching pieces (`response_*`, `hint_step_*`, ExpandMask,
  hashing, `prepare_sk`, `signing_key`).
- **Unknowns** (no leak found, no conclusion): under nearcore's exact build (`nearcore-exact`, 113 probes: 61 secure, 3
  expected insecure, 49 unknown) the NTT, `compute_t`, `prepare_sk`/`signing_key`, `hint_step`, `response` and the two
  censuses have no verdict, because BINSEC 0.11.3 cannot lift the VEX instructions (`vinsertps`, `vblendvps`, `vblendps`
  on `ymm`) that `+fma` (which implies AVX) lets LLVM emit; one more probe is a solver stall (ISSUES T-9, upstream U-44).
  With the vectorizers off (`nearcore-exact-novec`) all 113 get a verdict: 108 secure, 5 expected insecure. Elsewhere:
  two on riscv32imac plus three new riscv32imac split pieces (a solver stall at one store; the full-size probes they split
  are secure) and eleven on AArch64 (one stuck solver query each), partly covered by split probes (STATUS.md line 221;
  `checkct/README.md`, "Split probes"). `sk_is_well_formed` is branch-free since ae6023c (CT-3) and `secure` on every target
  and profile measured, including `nearcore-exact` (`src/api.rs`, doc of `sk_is_well_formed_NN`).
- **The `nearcore-exact` CT profile is nearcore's exact release build for the crate in isolation** (`overflow-checks =
  true`, nearcore's x86_64 target features, Rust 1.95.0, read from nearcore cd5a94457; the older `nearcore` profile still
  only approximates it). It is not nearcore's binary: callers, allocator, glibc `memcpy` and the prebuilt `core` differ
  (`checkct/README.md`, "What this does and does not show").
- **AVX2 and NEON code:** the AVX2 NTT copy is covered by a static scan only; AArch64 builds with NEON cannot be lifted;
  macOS is not covered.
- **Other builds:** verdicts depend on code shape and hold for the builds measured; `zeroize` builds are not probed.
- Hardware timing (variable-latency instructions, speculation, power) is outside the model.

## 5. Reading the evidence together

- "The extracted Rust never fails and equals the FIPS 204 algorithm on every input" is the content of 1.1, modulo the
  trusted base in section 2, in the Aeneas model: stack exhaustion and out-of-memory are not modeled, and where the spec
  returns no result at any fuel the Rust diverges instead of returning (1.2). That statement is about a source-level
  model; the nearcore-profile test run in `scripts/ci.sh` (`nearcore-test`, overflow checks on) is an empirical check of
  the compiled code, not a proof.
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

Safe: "the extracted Rust for every `api` function is proved, with no premises, to never fail (in the Aeneas model: stack
exhaustion and out-of-memory are not modeled, and the Rust can diverge exactly when the spec returns no result at any
fuel, §1.2) and to agree with the Lean transcription of FIPS 204 whenever either returns (`*_exact`), with the trusted
base in `docs/assurance.md` §2";
"constant time is checked by BINSEC on compiled probes for the builds and targets in §4". Not supported: "formally
verified" without that scope; "constant time" for whole-Sign; any statement about aws-lc equivalence; "FIPS validated"
or "FIPS certified".
