# Assurance case for reviewers

What `ml-dsa-lean` establishes about its public `api`, under which assumptions, what it does not cover, and how to
reproduce each piece of evidence. Every statement cites a Lean source, a script, a test or a checked-in result. Nothing
here is a FIPS validation or certification: ACVP vectors are test vectors, not a CMVP validation, and the crate has
neither. The crate is unaudited by third parties.

**Vocabulary.** "Proved" means a Lean theorem that passes the axiom gate (`scripts/check-axioms.sh`: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`). "Checked" means a tool or test run found no counterexample on the
inputs it covered. "Spec" is `lean/Spec`, our transcription of FIPS 204 (Algorithms 1–3 and 6–48) and FIPS 202
(SHAKE). "Rust" is the code extracted by Charon/Aeneas into `lean/Impl` and modeled there (`RustM` = `ok`, `fail` or
`div`).

## 0. Gates and pins

The gates below passed on the branch `t3/c288d712` (Sign's per-attempt wiping and in-place key decoding; `src/` and
`lean/Impl` changed there, so these results replace the earlier ones). `lean-check.sh` and `witness-check.sh` ran on a tree
whose `lean/` is byte-identical to the final one except `lean/Impl/extract-report.json` (a source hash that the Lean build
does not read); `scripts/ci.sh --lean` ran on the final tree (merge of `main` at e11ff2a, commit 2427004). Every statement
named in `lean/headline-theorems.txt` and `lean/witness-theorems.txt` (553 names) has the same text as at d482a38, and
`lean/Spec` is unchanged; the extracted functions those statements speak about did change (`sk_decode_into`,
`unpack_signed_into`, `scalar_vector_ntt_inverse_into`, `matrix_vector_ntt_into`, `response_into`, `hint_step_into`,
`ntt_inverse_in_place`, `more_attempts`), and their proofs were redone:

| Gate | Result |
|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`, 780 declarations (pipefail `lake build` exits 0, no `error:` or `sorry` in the log, axiom gate over every extracted def and every name in `lean/headline-theorems.txt`; axioms used: `propext`, `Classical.choice`, `Quot.sound`) |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`, 146 names |
| `scripts/ci.sh --lean` | 20 of 20 steps passed (including `extract-hash`, `axiom-gate-selftest`, `lean`) |

The fast verify (1.9) is a later tree: commit c4d522a, on which every gate below was run on the Linux build
box on 2026-11-07 (the README example test too; the commits after c4d522a change the checkct driver (997b2e5, which includes
`src/verify_arith.rs` so that `verify.rs` compiles there), documentation and benchmark result files only, no file under `src/`, `lean/` or `scripts/`):

| Gate | Result on c4d522a |
|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`: `Build completed successfully (3332 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt` (412), 877 checked, then over the 9 names of `lean/keccak4-theorems.txt` and the 51 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound` |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3324 jobs)`, 146 names checked, axioms `propext`, `Classical.choice`, `Quot.sound` |
| `scripts/ci.sh --lean` | `CI SUMMARY: 21 passed, 0 failed, 0 skipped` (run on 13f49e6, which differs from c4d522a only by the checkct driver and documentation; every step, including `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `diff-awslc`, the three fuzz targets, `extract-hash`, `axiom-gate-selftest` and `lean`) |
| `scripts/check-avx2-inlining.sh` | `OK: no out-of-line intrinsic wrappers; verify-only arithmetic fully inlined; 39256 lines of ymm code` |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | every test binary passes: 127 tests in 27 result lines (26 test binaries and the doc-tests), 0 failed |
| `cargo +1.86.0 build --features avx2` | builds (the declared MSRV) |
| README example test (`cargo test --test readme_example`) | 2 passed |
| `scripts/extract_hash.py check` | `extract hash OK`: the 4 files of `lean/Impl` match `extract-report.json` (sha 24d4bacc59c5369680663c0aa996daf0b4532f4fcddbc6b8dfe2f74ef5095822) |
| checkct driver | on 997b2e5 (the driver gains `src/verify_arith.rs`): builds for riscv32imac, thumbv7em and x86_64, with and without `avx2`. The full profile build and the BINSEC smoke run (verdicts match the sweep) were run on 6ccc3e6 and not repeated after the verify-only arithmetic; Sign and KeyGen sources are unchanged since (section 4) |

The prepared-key verify under `avx2` (branch `fv-p5`; a second AVX2 wrapper, 1.9) is a later tree again: commit 5b5252e. It changed
no Lean statement or proof (`lean/Impl` is re-extracted, and only comment line numbers and the extraction digest moved), no name
in `lean/headline-theorems.txt` (412) or `lean/fast-verify-theorems.txt` (51), and nothing Sign or KeyGen calls. Every gate below
ran on the Linux build box on 2026-11-07, on the tree of the commit named in the first column (the checkct driver commit 5b5252e
follows the tree on which `lean-check.sh`, `witness-check.sh` and the tests ran, and changes `checkct/driver/src/main.rs` only; the commit that
adds this table changes documentation only):

| Gate | Result | Run on |
|---|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`: `Build completed successfully (3333 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt`, 877 checked, then over the 9 names of `lean/keccak4-theorems.txt` and the 51 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound` | e8f9821 |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3325 jobs)`, 146 names checked, axioms `propext`, `Classical.choice`, `Quot.sound`; `AXIOM GATE OK` | e8f9821 |
| `scripts/ci.sh --lean` | `CI SUMMARY: 21 passed, 0 failed, 0 skipped` (every step, including `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `diff-awslc`, the three fuzz targets at 60 s, `extract-hash`, `axiom-gate-selftest` and `lean` with `LEAN CHECK OK`) | 5b5252e |
| `scripts/check-avx2-inlining.sh` | `OK: no out-of-line intrinsic wrappers; verify-only arithmetic fully inlined; 53809 lines of ymm code`; the three `verify_prepared_avx2` instantiations hold 4076, 4965 and 5512 lines of ymm code (K = 4, 6, 8) | e8f9821, 5b5252e (ci) |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | 27 result lines (26 test binaries and the doc-tests), 127 tests passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`) | e8f9821 |
| `cargo +1.86.0 build --features avx2` | builds (the declared MSRV) | e8f9821, 5b5252e |
| README example test (`cargo test --test readme_example`) | 2 passed | e8f9821 |
| `scripts/extract_hash.py check` | `extract hash OK`: the 4 files of `lean/Impl` match `extract-report.json` (extraction inputs sha256 52571a1f7c49096884c80c4a8ab1aecbff020f595aee363b2f2c9a0e9062eb39) | 5b5252e |
| checkct driver | builds (release, `-p driver`) for riscv32imac, thumbv7em and x86_64, each with and without `avx2`. The driver needed the third re-export of `fast_verify` (5b5252e). The BINSEC sweep was not rerun: no source Sign or KeyGen calls changed since the last full profile build and smoke run named above (section 4) | 5b5252e |

The stack-offset fix (branch `fv-p6`; 1.9) is a later tree again. It changed no Lean statement or proof, no name in
`lean/headline-theorems.txt` (412) or `lean/fast-verify-theorems.txt` (51), and nothing Sign or KeyGen calls: the changes under
`src/` are `src/fast_verify/dispatch.rs` (a stack-realigning local in each of the six wrappers, and `prepare_vk_avx2` building
the key in place) and a `#[path]` attribute in `src/fast_verify.rs`; `lean/Impl` is re-extracted and only the extraction digest
moved. Every gate below ran on the Linux build box on 2026-11-07 or 2026-11-08, on the tree of the commit named in the last column.
The two standalone Lean gates ran on bd2a963, a bench-only commit whose `src/` and `lean/` are those of 364252a (the last commit that changes either) and of the final tree (the `lean` step of `ci.sh --lean`
repeated the first on 306360d); the other gates ran on 306360d, which differs from bd2a963 by one attribute in
`bench/src/bin/stackscan.rs`; the commit that adds this table changes documentation and benchmark result
files only.

| Gate | Result | Run on |
|---|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`: `Build completed successfully (3333 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt`, 877 checked, then over the 9 names of `lean/keccak4-theorems.txt` and the 51 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound` | bd2a963 |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3325 jobs)`, 146 names checked, `AXIOM GATE OK` | bd2a963 |
| `scripts/ci.sh --lean` | `CI SUMMARY: 21 passed, 0 failed, 0 skipped` (every step, including `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `diff-awslc`, the three fuzz targets at 60 s, `extract-hash`, `axiom-gate-selftest`, and `lean` with `LEAN CHECK OK`: `Build completed successfully (3333 jobs)`, 877, 9 and 51 names checked, each `AXIOM GATE OK`) | 306360d |
| `scripts/check-avx2-inlining.sh` | `OK: no out-of-line intrinsic wrappers; verify-only arithmetic fully inlined; verify wrappers realign their frames; 53806 lines of ymm code`; the three `verify_prepared_avx2` instantiations hold 4077, 4966 and 5513 lines of ymm code (K = 4, 6, 8); all nine wrapper instantiations (`verify_internal_avx2`, `verify_prepared_avx2`, `prepare_vk_avx2` for K = 4, 6, 8) print `1` under "stack-realigning wrappers" (`andq $-32, %rsp` or stronger in the first 20 lines of the body) | 306360d |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | 27 result lines (26 test binaries and the doc-tests), 127 tests passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`) | 306360d |
| `cargo +1.86.0 build --features avx2` | builds (the declared MSRV) | 306360d |
| README example test (`cargo test --test readme_example`) | 2 passed | 306360d |
| `scripts/extract_hash.py check` | `extract hash OK`: the 4 files of `lean/Impl` match `extract-report.json` (extraction inputs sha256 7cd7dfdef38482e0fedcd14ee70330a351283e4e15a224f96631edabea5c6036); a fresh extraction on the box leaves `Funs.lean` and `Types.lean` unchanged | 306360d |
| checkct driver | builds (release, `-p driver`) for riscv32imac, thumbv7em and x86_64, each with and without `avx2`, in the default release profile (nightly-2026-10-06) and with nearcore's exact flags (nightly-2026-10-06 and 1.95.0): 18 of 18 cells built. The driver now includes the real `src/fast_verify.rs` through `#[path]` instead of repeating its re-exports, so it follows the source by itself. The BINSEC sweep was not rerun: no source Sign or KeyGen calls changed since the last full profile build and smoke run named above (section 4) | 306360d |

A module counts as proved only after `lean-check.sh` passes. Exact steps to rerun everything are in
[reproduce.md](reproduce.md).

What ties the shipped Rust to the proved Lean (the proofs are about `lean/Impl`, the extraction of `src/`):

- Every push and pull request (`ci.yml`, job `repo-checks`, steps `extract-hash` and `axiom-gate-selftest` of `scripts/ci.sh`):
  `extract-hash` fails if the digest of the extraction inputs (every file under `src/`, `Cargo.toml` without its
  dev-dependencies and with its package `version` replaced by `0.0.0` (so a release version bump does not change the digest), the roots, the Charon and Aeneas pins; file names are part of the digest), the set and contents of the files in
  `lean/Impl` (recursively), or the roots in `scripts/extract-roots.txt` no longer match what `lean/Impl/extract-report.json`
  recorded at the last extraction (`scripts/extract_hash.py`, shared with `scripts/extract.py`), or if there is a symlink under
  `src/` or `lean/Impl`, a build script, an `env!`/`include!`-style macro in `src/`, a root `.cargo` directory or toolchain
  file, or a file name with a control character (inputs the extraction does not see, or that make the manifest ambiguous). It checks that committed files agree with each other and does not re-run the extraction, so editing
  `lean/Impl` and the report together passes it. The self-test runs `scripts/check-axioms.sh` on a missing, an empty and a
  declaration-free list and requires it to fail.
- Manual and weekly, on the large runner (`lean.yml`, before `lean-check.sh`): `scripts/setup-tools.sh`, then the fast check, then
  `scripts/extract.py` into a new empty directory, and the job fails unless every file there is identical to the committed
  `lean/Impl` and neither has files the other lacks (`diff -r`). This is the check that a coordinated edit of `lean/Impl` and the
  report does not pass. It runs only when the heavy runner is configured or on manual dispatch.
- Extraction runs the verified cargo-hax by absolute path, on a crate staged outside the checkout, with a fixed list of
  environment variables and a fresh `CARGO_HOME`. `PATH`, `HOME` and `RUSTUP_HOME` are still inherited (header of `scripts/extract.py`).
- Apple Silicon (`ci.yml`, job `macos-arm64`, `macos-15`): the default suite and the release zeroize suite. Until the
  `stack_residue_signing_key` failures on aarch64 macOS are fixed (three tests, 44/65/87), this job fails.

Threat model. These checks are designed to catch accidental drift between `src/` and `lean/Impl`, and tampering that is hidden
inside generated or cached files (a hand-edited, symlinked or extra file in `lean/Impl`, a modified or shadowed tool). They cannot
stop anyone who can change the workflows or scripts in a commit from disabling them; that is covered by code review of
`.github/` and `scripts/`, not by CI.

Pins and decisions:

| Item | Choice | Why |
|---|---|---|
| Crate | `ml-dsa-lean` (`ml_dsa_lean`), `no_std`, no core dependencies; MSRV 1.86 | extraction closure = this crate + `core` |
| Lean layout | Lake package `MlDsaLean` in `lean/`: extracted code `lean/Impl/` (Aeneas namespace `Impl`), spec `lean/Spec/`, proofs `lean/Proofs/` | names are fixed so proofs don't churn |
| M′ | `sign_internal(p, sk, m_prefix, m, rnd, sig)` and `verify_internal(p, pk, m_prefix, m, sig)`, with M′ = `m_prefix ‖ m` absorbed in two calls | the external API builds 0 ‖ \|ctx\| ‖ ctx (≤ 257 bytes) on the stack, no alloc; the proof needs one sponge lemma (absorbing two slices = absorbing their concatenation) |
| Charon | generic (no `--monomorphize`) | 0 external axioms; `--monomorphize` adds 9 unmodeled index axioms |
| Extraction toolchain | Charon nightly-2026.09.02, Aeneas build-183e4f0, cargo-hax 0.4.2, elan v4.2.4, Rust nightly-2026-08-18, Lean v4.31.0 | pinned in `scripts/setup-tools.sh` and `lean/lean-toolchain`; the cargo-hax and elan downloads are tagged releases checked against recorded SHA-256 values; on every run the installed cargo-hax binary and the whole Aeneas and Charon tool directories (including `hax-metadata.toml`, which names the executables cargo-hax runs) are checked against recorded digests, and the executables must have the execute bit and run (the nightly and the Lean toolchain are fetched and verified by rustup and elan) |
| Extraction gate | Aeneas exit 0, no `[Error]`/`[Warning]`, no local opaque function, no referenced external axiom, every extracted def on standard axioms only | any failure is fixed in the Rust code, not worked around |
| Out of scope | HashML-DSA (Algorithms 4/5) and external μ | no differential oracle for the first; the second is an allowed variant of Algorithms 7/8 that would need its own spec entry and theorems (deferred, not ruled out) |

## 1. What is proved

### 1.1 The `*_exact` theorems: the API against the Lean transcription of the unbounded FIPS 204 algorithms, no premises

For each parameter set NN ∈ {44, 65, 87} and every value of the API argument types:

| Rust function | Theorem (Lean file) |
|---|---|
| `api.verify_NN`, `api.verify_internal_NN` | `verify_NN_exact`, `verify_internal_NN_exact` (`Proofs/PartialAPI.lean`) |
| `api.keygen_NN` | `keygen_NN_exact` (`Proofs/PartialKeyGen.lean`) |
| `api.sign_NN`, `api.sign_internal_NN` | `sign_NN_exact`, `sign_internal_NN_exact` (`Proofs/PartialSign.lean`) |
| `api.pk_from_sk_NN` | `pk_from_sk_NN_exact` (`Proofs/PkFromSk.lean`) |

In words, for Verify: (a) the Rust never returns `fail`, i.e. no panic, arithmetic overflow or out-of-bounds access in
the Aeneas model (stack exhaustion and out-of-memory are not modeled, and the Rust can diverge, `div`, exactly when the
spec returns no result at any fuel, 1.2); (b) if it returns `ok b`, then `Spec.Verify … F = some b` for some fuel `F`; (c) if `Spec.Verify … F =
some b` at any fuel, it returns `ok b`. The verdict is therefore unique across fuels, and the statement holds for every
`pk`, `m`, `ctx` and `σ` of the API types (a wrong length cannot occur: the API takes fixed-size arrays; `verify_internal`
also returns false on any slice length that is not `pk_len`/`sig_len`). KeyGen has the same shape with `(pk, sk)`. For Sign,
(b) and (c) hold with `some σ`, and `api.sign_NN … = ok none` exactly when |ctx| > 255 or the spec's `Exhausted` holds at some
fuel (all `kappaBudget` attempts rejected). The Rust's cap κ + ℓ ≤ 2¹⁶ is the same as `kappaBudget`; it is an implementation
bound FIPS 204 allows (κ is encoded in 16 bits by ExpandMask).

These theorems are about the scalar functions. In the extraction (and so in every build without the `avx2` feature)
`api.verify_NN` and `api.verifying_key_NN` call exactly those. With the `avx2` feature on x86_64 the shipped functions
dispatch at run time to a 4-way body; what is proved about that body, and what is not, is 1.9.

"Fuel" is how the spec makes the FIPS rejection-sampling loops (ExpandA, ExpandS, SampleInBall) total: the spec
returns `none` if a loop runs out of fuel; the Rust loops are unbounded. The older theorems that were stated with premises
(`keygen_internal_spec`, `sign_internal_spec_some`, `verify_internal_spec`, …) still exist and carry them:

- `RejTerm`: the rejection samplers receive enough accepted samples from SHAKE (probabilistic, not provable). Concretely, the
  theorem takes "the spec returns `some` at fuel F" as the hypothesis.
- The κ budget: Sign is compared with `Sign_internal_bounded B`, B = ⌊(2¹⁶ − ℓ)/ℓ⌋ + 1.
- `Params.Std` = `Params.Valid` ∧ `StdParams` (d = 13, γ1/γ2/η of the standard sets, τ ≤ 64, k + ℓ < 256, k ≤ 8, ℓ ≥ 1,
  ω ≤ 255, …), kernel-checked for ML-DSA-44/65/87 (`ML_DSA_NN_std`).

### 1.2 `Divergence.lean`: when the Rust does not terminate

`Proofs/Divergence.lean` (`rustM_div_iff`, `verify_NN_div_iff`, `keygen_NN_div_iff`, `sign_NN_div_iff`,
`pk_from_sk_NN_div_iff`, and the prepared-key analogues): the Rust returns `div` exactly when the spec returns no
result at any fuel, i.e. when FIPS 204's unbounded ExpandA or SampleInBall would never terminate on that input. This
is not a termination proof; termination is probabilistic. Sign's κ loop is bounded, so Sign diverges only through a
sampler. The generic loop lemmas are proved by fixpoint induction in `Proofs/Partial.lean`.

### 1.3 Correctness for honest keys

`Proofs/Correctness.lean`: `correct_internal` and `correct_external` at spec level, and `correct_44`, `correct_65`,
`correct_87` for the Rust: `api.keygen_NN` then `api.sign_NN` then `api.verify_NN` returns true. Premises: `StdParams`,
and that KeyGen and Sign return `some` at the same fuel (`RejTerm`, the κ budget). Building blocks: NTT algebra and
convolution, ‖c·s‖∞ ≤ β, Power2Round/HighBits/UseHint lemmas, codec round trips, SampleInBall weight = τ.

### 1.4 Prepared keys

`Proofs/PreparedVerify.lean` and `PreparedSign.lean`: `verify_prepared_NN_eq`, `verify_internal_prepared_NN_eq`,
`sign_prepared_NN_eq`, `sign_internal_prepared_NN_eq` say that for a key object returned by `verifying_key_NN pk` or
`signing_key_NN sk`, the prepared call equals the one-shot call as a computation (including `fail` and divergence);
`*_exact` versions against the spec exist too. `verifying_key_NN` and `signing_key_NN` never fail and diverge only where
ExpandA does (`Divergence.lean`, `verifying_key_NN_div_iff`). `verify_prepared_NN` runs no ExpandA and has no 4-way body; with the `avx2` feature it is the same proved function compiled
inside a second AVX2 wrapper (1.9). `verifying_key_NN` is dispatched to the 4-way body (1.9). The key structs have private fields and are only built by
those constructors, so the hypothesis `verifying_key_NN pk = ok vk` covers every key a caller can hold. The `Drop` wipe of a
prepared signing key is not in the model.

### 1.5 `SkWellFormed` and `PkFromSk` (optional checks, not FIPS steps)

`Proofs/SkWellFormed.lean` (`skWellFormedAPI_spec`, `skWellFormed_keygen`): `sk_is_well_formed_NN` returns whether every
s1/s2 coefficient that skDecode yields lies in [−η, η]; keys from KeyGen pass. `Proofs/PkFromSk.lean`
(`pk_from_sk_NN_exact`, `skConsistent_keygen`, `skConsistent_sound`): `pk_from_sk_NN` returns `Some pk` iff the range
check passes and recomputing KeyGen steps 5–9 reproduces the stored t0 and tr (K is a free seed, unchecked). `sign_NN`
follows FIPS 204 Algorithm 25 literally and does not call either (E-4 below). `pk_from_sk_NN` agrees with
mldsa-native's `pk_from_sk` on 14 variants per set.

### 1.6 Proof inventory

Each row is a `@[step]` refinement spec of an extracted function against its `lean/Spec` algorithm, under the
representation relations of `Proofs/Repr.lean`.

| Module | What is proved | Extra hypotheses |
|---|---|---|
| `Field`, `Repr` | field ops, masks, infinity norm vs ‖·‖∞, `Params.Valid` for 44/65/87 | canonical inputs |
| `NTT*` | NTT, NTT⁻¹ (Alg 41/42); zeta table by `decide +kernel` | canonical inputs |
| `NTTOps`, `Coeff` | Alg 44–48, vector NTT, CoeffFromThreeBytes/HalfByte (Alg 14/15) | η ∈ {2, 4} |
| `Rounding*` | Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint (Alg 35–40) and polynomial maps; the verify-only `poly_use_hint_pub` (1.9) | γ2 ∈ {95232, 261888} |
| `Encode*` | bit accumulator = SimpleBitPack/BitPack and unpack (Alg 16–19), the verify-only fixed-width `bit_unpack_pub` (1.9), w1Encode, pk/sk encode/decode (Alg 22–25); decoders for every byte string of the right length | coefficient ranges for the encoders |
| `Hint` | HintBitUnpack for every byte string incl. all ⊥ cases; HintBitPack (Alg 20/21) | weight ≤ ω for packing |
| `Keccak*` | Keccak-f[1600]; SHAKE128/256 absorb, finalize, squeeze vs `Spec.SHAKE*`; absorbing a then b = absorbing a ‖ b | none |
| `Keccak4`, `Sample4`, `Sample4Block`, `ExpandA4`, `FastVerify` | the 4-way Keccak-f[1600], RejNTTPoly, ExpandA and verify body, each equal to its scalar counterpart for the plain-Rust instance `Shim4` (1.9) | `Params.Std` for the verify theorems; none for the permutation |
| `SampleA`, `SampleS`, `SampleBall`, `ExpandMask` | RejNTTPoly, ExpandA (Alg 30/32), RejBoundedPoly, ExpandS (Alg 31/33), SampleInBall (Alg 29), ExpandMask (Alg 34) | `RejTerm`; η ∈ {2, 4}; τ ≤ 64; κ + ℓ ≤ 2¹⁶ |
| `SigCodec`, `Steps`, `Bridge` | sigDecode for every byte string of length sigLen, sigEncode; Sign steps 18–21 and 25–26, KeyGen t and Power2Round, Verify t1·2^d and c̃ compare, API ctx prefix; Z_q norm bridges | γ1 ∈ {2¹⁷, 2¹⁹}, γ2, d = 13 |
| `KeyGen`, `Verify`, `Sign` | KeyGen_internal (Alg 6), Verify_internal (Alg 8), Sign_internal (Alg 7, bounded) against the spec | `Params.Std`, `RejTerm`; unconditional versions in `PartialKeyGen`, `PartialAPI`, `PartialSign` |
| `API`, `APIInternal` | Public API (Alg 1/2/3) and internal API for 44/65/87, and the "only if" for `none` | the spec returns `some` (or `Exhausted`) |
| `Witnesses`, `SampleBallWitness`, `TopWitness*` | kernel witnesses for the premises (below) | none |

Internal reviews covered the leaf proofs, the three internal top theorems, the API theorems, the `verify_internal` length guard
and the Sign exhaustion change, and the optional-check proofs: no blockers, findings folded in. These reviews were separate review
passes within this project, not third-party reviews.

### 1.7 Witnesses for the premises

- Parameter premises (`Params.Std`): kernel-checked for 44/65/87.
- Sampler premises at the leaves: kernel witnesses on zero seeds (RejNTTPoly and ExpandA for 44, RejBoundedPoly and ExpandS for
  44 and 65, SampleInBall for 44).
- Top-level `some` premises: for ML-DSA-44 with ξ = 0..31, rnd = 0³², M = [0], ctx = [] and the default fuel, all hypotheses of
  `correct_44` hold on a kernel-checked instance: `Spec.KeyGen` returns a key pair, `Spec.Sign` returns `some` (the first attempt
  is accepted), and `Spec.Verify` returns `some true`. `Proofs.TopWitnessCorrect.correct_44_nonvacuous` bundles these with the
  Rust chain `api.keygen_44` → `api.sign_44` → `api.verify_44 = ok true`. Kernel evaluation runs on list-based equivalents of
  BytesToBits, the bit packers and the Array loops, each proved equal to the spec for all inputs (`TopWitnessFast`); the
  literals come from a native generator and each is re-derived by `decide +kernel`. Checked by `scripts/witness-check.sh` (146
  names, standard axioms), outside the default build: about 47 min cold and about 46 GB peak across modules (about 24 GB for the
  largest declaration). One parameter set and one input only.
- `Exhausted` (Sign's `false` case, all κ attempts rejected): satisfiable only by a counting argument; no witness, probability
  about 2^-thousands per input, untestable in practice.

### 1.8 Cross-check of the spec: `xspec`

The Rust theorems are only as good as the spec. `xspec/` is a separate Lean v4.34 project that vendors `lean/Spec`
byte-identically and proves it equal to ocaml-pq's independent Lean transcription (standard axioms only; 144 headline
names in `xspec/headline-theorems.txt`, 142 equivalence theorems and 2 kernel known-answer tests; gate
`scripts/xspec/check-axioms.sh`; details in `xspec/README.md`). Top level, both directions, all three parameter sets, with
these scope qualifiers:

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

This is a proof about specs, not about the Rust. Other fidelity evidence for the spec: ACVP (`spec-acvp` 63/63 in Lean; the
Rust runs ACVP keyGen 75/75, sigGen 60/60 and sigVer 30/30 of the vendored 120 and 60 cases, with the preHash and external-μ
cases skipped), Wycheproof (below), a component differential against VCVio (1,345,635
in-precondition cases, 0 mismatches, plus a FIPS-literal Python reference; the only difference is HintBitPack with more than ω
ones, which is outside Algorithm 20's precondition and handled differently by the two sides), and three spec reviews against the FIPS PDFs (every
`lean/Spec` def checked step by step; whole-domain rounding check against a FIPS-literal Python reference; SHAKE vs hashlib
around the rate; no transcription errors). Those reviews were internal and the notes of the third are not committed. **No
third-party audit and no CMVP or other validation of this crate or its spec exists.**

### 1.9 The 4-way verify body (the `avx2` feature's fast verify)

**What the code is.** `src/keccak4.rs` has a 4-way Keccak-f[1600] written once against `trait Lanes4`, four lane-wise
operations on `[u64; 4]` values passed by value (`xor`, `andnot`, `rotl::<L, R>`, `splat`; no associated type). It has two
instances. `Shim4` is plain Rust over the four lanes. `avx2::Avx2` (feature `avx2`, x86_64, not Miri) is the same operations as
AVX2 intrinsics; it is crate-private, because its safe trait methods execute AVX2 instructions. On top of the kernel,
`src/sampling.rs` has a 4-way SHAKE128 RejNTTPoly and ExpandA (`rej_ntt_poly_x4`, `expand_a_x4`, `expand_a_into_x4`) and
`src/verify.rs` has `prepare_vk_x4` and `verify_internal_x4`, all generic over `Lanes4`. They are extraction roots
(`scripts/extract-roots.txt`); the generic extraction turns the trait into a Lean structure and the instance into an explicit
argument, so a proof about the generic body never looks inside an instance. In Lean `Sh4` is the extracted `Shim4` instance.
Two facts the sampler relies on: the SHAKE128 rate, 168 bytes, is 56 whole three-byte candidates, so no candidate straddles a
block and a block-synchronous sampler consumes the same candidate sequence as the byte-wise one; and a lane that has its 256
coefficients simply idles while the others finish. Also, `verify_internal_x4` and `prepare_vk_x4` use the verify-only functions below (`poly_use_hint_pub`, `bit_unpack_pub`, and
the arithmetic of `src/verify_arith.rs`, `vec_norm_lt_pub` and `bit_pack_pub`).

**What is proved** (all `Proofs/*.lean`, theorem names in `lean/keccak4-theorems.txt` and `lean/fast-verify-theorems.txt`,
checked for standard axioms only by `scripts/lean-check.sh`; every statement is for the instance `Sh4`):

| Theorem(s) | Says |
|---|---|
| `shim_xor_spec`, `shim_andnot_spec`, `shim_splat_spec`, `shim_rotl_spec` (`Keccak4`) | the extracted `Shim4` operations act lane by lane |
| `round_lane`, `round_spec`, `keccak_f1600_x4_shim_spec` (`Keccak4`) | one 4-way round maps state `i` to `Spec.Keccak.Rnd` of state `i`, and the 24 rounds map state `i` to `Spec.KeccakF1600` of state `i`, for each `i < 4` |
| `keccak_f1600_x4_portable_spec`, `keccak_f1600_x4_portable_eq_scalar` (`Keccak4`) | the same for the extracted portable entry point, and for each `i < 4` the extracted scalar `keccak.keccak_f1600` on lane `i` of the input returns lane `i` of the output |
| `absorb_pad34`, `shake_stream`, `init_state_x4_spec` (`Sample4`) | the initial 4-way state of lane `i` is the padded state of the 34-byte message ρ ‖ s[i] ‖ r[i] before the first permutation, and byte `168b + p` of that message's SHAKE128 output is byte `p` of the state after `b + 1` permutations |
| `laneInv_step`, `push_candidate_spec`, `al_val`, `st6_val`, `st7_val`, `rej_ntt_cands8_spec`, `rej_ntt_block_x4_spec`, `rej_ntt_lane_x4_spec`, `first_256_spec` (`Sample4`, `Sample4Block`) | the branchless parse of a block straight from the lane words (eight candidates from three lanes) performs the same accept-or-skip steps as the byte-wise sampler's fold over the 56 candidates, for each lane |
| `keccak_step_lanes`, `rej_x4_body_spec`, `rej_x4_loop_spec`, `rej_ntt_poly_x4_spec`, `rej_ntt_poly_x4_partial` (`Sample4`) | if the spec's RejNTTPoly returns `P i` for the four seeds at some fuel, the 4-way sampler terminates with polynomials representing `P i` (total form); in any case it is partially correct (`partial`, which covers divergence) |
| `expandA_ent`, `expand_a_x4_partial`, `expand_a_x4_term`, `ReprMat.unique`, `rustM_eq_of_partial`, `expand_a_x4_eq`, `expand_a_x4_eq_std` (`ExpandA4`) | `sampling.expand_a_x4 K L Sh4 ρ = sampling.expand_a K L ρ` as `RustM` values, divergence included, under `Params.Std` |
| `prepare_vk_x4_eq`, `verify_internal_x4_eq` (`FastVerify`) | `verify.prepare_vk_x4 K L Sh4 pk = verify.prepare_vk K L pk` and `verify.verify_internal_x4 K L Sh4 p pk m_prefix m sig = verify.verify_internal K L p pk m_prefix m sig` for every argument, as `RustM` values |
| `verifyInternalX4API_eq`, `verify_internal_x4_NN_eq`, `verify_internal_x4_NN_exact`, `verify_internal_x4_NN_div_iff` for NN ∈ {44, 65, 87} (`FastVerify`) | the body of `api.verify_internal_NN` run with the 4-way verifier equals `api.verify_internal_NN`, has the three-part `_exact` statement of 1.1 (never fails; agrees with `Spec.Verify_internal` whenever either returns), and diverges exactly when the spec returns no verdict at any fuel |

The verify-only rewrites are different: the scalar verify uses them too, so they are in every build, and their theorems are in
`lean/headline-theorems.txt` (the API statements of 1.1 are unchanged; the proofs of the functions that call them were
redone). `rounding.poly_use_hint_pub` computes UseHint with plain arithmetic (a multiply-shift HighBits) on public data, for
both γ2 of the standard sets; `use_hint_g32_spec`, `use_hint_g88_spec` and `poly_use_hint_pub_spec` say it returns
`Spec.UseHint` coefficient by coefficient, with each value below m. `encode.bit_unpack_pub` unpacks 10, 18 or 20 bits per
coefficient with fixed offsets and shifts, and falls back to `bit_unpack` for any other width; `bit_unpack_pub_core` and
`bit_unpack_pub_spec_repr` say its output represents `Spec.SimpleBitUnpack`. Both are used only on verify's path (`pk_decode`,
`unpack_signed`, `verify_internal`); the secret-key decoders still use `bit_unpack`/`unpack_signed_into`, and the
constant-time `poly_use_hint` is unchanged.

**The verify-only arithmetic** (`src/verify_arith.rs`, `rounding::vec_norm_lt_pub`, `encode::bit_pack_pub` and
`encode::w1_encode_pub`). Verify's data is public, so its NTTs, the row sums of Â ∘ NTT(z) − NTT(c) ∘ NTT(t₁·2^d), the
norm check on z and the packing of w₁ need no constant-time idiom; each was rewritten as plain integer code (no intrinsics, no
`unsafe`, no new `#[target_feature]` function) that the compiler vectorizes inside the AVX2 wrapper, and each is proved to
compute what the shared function computes (`Proofs/NTTPub.lean`, `Proofs/VerifyArith.lean`; names in
`lean/fast-verify-theorems.txt`). Signing and key generation keep the shared functions, which are unchanged (the edits to `src/encode.rs` and `src/rounding.rs`
only add the new functions; `src/sign.rs`, `src/keygen.rs`, `src/field.rs` and `src/ntt.rs` are untouched). The scalar verify uses the
new functions too, so they are in every build.

| Theorem(s) | Says |
|---|---|
| `shoup_lazy_nat`, `lazy_layer_spec`, `reduce_lazy_spec`, `ntt_pub_spec`, `ntt_vec_pub_spec` | `verify_arith.ntt_pub` maps a canonical polynomial to a canonical one whose `toZq` is `Spec.NTT` of the input (the statement of `ntt_spec`), and `ntt_vec_pub` does so for each polynomial of a vector. The layers skip every reduction: Shoup multiplication takes any 32-bit input and returns a value in [0, 2q), so a layer grows each coefficient by at most 2q (below 17q after eight layers, reduced once at the end); each wrapping `u32` operation is shown to equal the exact sum |
| `lazy_inv_layer_spec`, `ntt_inverse_pub_spec` | the same for NTT⁻¹ (`Spec.NTTInv`): each layer at most doubles the bound (below 256q < 2^32 before the exact `mul_shoup` scaling by 256⁻¹, which is the only reduction) |
| `mac_row_pub_spec`, `mac_row_pub_spec_mv` | for row i, `mac_row_pub` returns the polynomial of the sum over l of Â[i][l] ∘ ẑ[l], minus ĉ ∘ t̂[i], i.e. `(MatrixVectorNTT M V)[i]! - MultiplyNTT C T`, for inputs representing M[i], V, C and T (L ≤ 255; verify has L ≤ 7). The L + 1 products (q² − c·t standing for −c·t) are summed in 64 bits below (L + 1)·q² < 2^32·q, and two Montgomery reductions (the second by R² = 2^64 mod q) finish it |
| `vec_norm_lt_pub_spec` | for z representing a vector of integer polynomials with ‖z‖∞ ≤ 4190208 and 0 < bound < q, `vec_norm_lt_pub z bound` returns `decide (‖z‖∞ < bound)` |
| `pack4_loop`, `pack6_loop`, `bit_pack_pub_core`, `bit_pack_pub_spec_repr`, `w1_encode_pub_spec_long` | `bit_pack_pub` writes the same bytes as the generic `bit_pack` (two 4-bit or four 6-bit values per step with constant shifts; any other width falls back to `bit_pack`), so `w1_encode_pub` returns `Spec.w1Encode` when every value is at most m − 1 |

The callers' theorems keep their statements except `Verify.verify_loop_spec`, whose loop now holds the whole row computation
(its statement changed with the extracted loop; `verify_core_spec` and `prepare_vk_spec` have the statements they had, and the
API statements of 1.1 are unchanged). `tests/verify_arith.rs` additionally compares each function with its shared counterpart on
corner and random inputs (4,000 random polynomials for the NTTs, rows of L = 4, 5, 7 including all-(q − 1) inputs, norm edges at
the three sets' bounds γ1 − β, taken from the parameter sets, widths 1, 4, 6, 8, 10); that is evidence about the source, not part of the proof.

**What the shipped AVX2 build adds, and its status.** With the `avx2` feature on x86_64 (not under Miri), `src/fast_verify.rs`
exports `verify_internal`, `prepare_vk` and `verify_prepared_internal`, and `api.rs` calls those. Each checks `cpu::has_avx2` (CPUID leaf 7 AVX2, leaf 1
XSAVE, OSXSAVE and AVX, XCR0 bits 1 and 2, cached in an `AtomicU8`; a build that is already compiled for AVX2 skips the check)
and then calls a `#[target_feature(enable = "avx2")]` wrapper (`src/fast_verify/dispatch.rs`) that runs
`verify_internal_x4::<K, L, Avx2>` or the key half (`PreparedVk::zeroed()` followed by `prepare_vk_into_x4::<K, L, Avx2>`, which
is `prepare_vk_x4` by `Proofs.prepare_vk_into_x4_zero`, so that a 57 KB key is built in place and not copied out), or else the scalar function. The third name, the prepared-key
verify, has no 4-way body: its wrapper `verify_prepared_avx2` calls the proved scalar `verify::verify_prepared_internal`, which is
`#[inline(always)]` in this build, so that the proved loops (multiply-accumulate row, lazy NTTs, UseHint, norm check) are
compiled with AVX2 and vectorized by LLVM. Like the other two it is reached only after the cached `cpu::has_avx2()` check, and
it calls nothing but extracted code: no intrinsic, no `Lanes4` method. Each wrapper starts with `align_frame()`, a
`#[repr(align(32))]` local passed to `core::hint::black_box` (contents never read), which makes LLVM realign the wrapper's
stack frame to 32 bytes. Without it LLVM spills the 4-way Keccak's 256-bit vectors to 16-byte-aligned slots and accesses
them unaligned, and at about one stack offset in seven a slot straddles a 4 KiB page, which made one-shot verify and
`verifying_key_NN` up to 7, 13 and 24 µs above the median at that offset (ML-DSA-44, 65, 87) (`bench/results/2026-11-07-p6.md`: diagnosis, and a scan of 257
stack offsets, before and after). `align_frame` is plain safe Rust with no effect on any value, so it is outside the proof like the rest
of the glue; `scripts/check-avx2-inlining.sh` checks that all nine wrapper instantiations realign. Without the feature, on other
targets and under Miri (so also in the extraction) `fast_verify` only re-exports the scalar functions, and nothing of the
dispatch exists. Thus:

- **Portable build:** the code that ships is exactly the extracted code, and 1.1 applies to it.
- **AVX2 build:** the shipped body is the one proved in the table above, over `Avx2` instead of `Shim4`. It is *proved modulo
  the tested equivalence of the AVX2 lane operations to the proved shim*. The link is tested, not proved:
  `tests/keccak4_avx2.rs` compares each AVX2 operation with `Shim4` lane by lane (xor, andnot and splat on 20,000 operands,
  each paired three ways, plus a lane-independence check), every rotation the kernel uses (the list is derived from the kernel
  source and checked against the scalar ρ offsets; at least 4,000 inputs each) and all 63 non-trivial rotation amounts (400
  inputs each), and more than 150,000 whole states against `Shim4` and four scalar permutations plus a chain of 2,000 iterated
  permutations. `tests/fast_verify_x4.rs` compares the 4-way sampler, ExpandA and verify over `Shim4` and over `Avx2` with the
  scalar functions (including the padded last group of ML-DSA-65, whose K·L = 30 is not a multiple of four), and
  `tests/fast_verify.rs` compares the dispatched and the AVX2 verify with the scalar verify on the ACVP sigVer vectors, the
  Wycheproof verify vectors and random valid, corrupted, wrong-length and random inputs, through `verify_NN`,
  `verify_internal_NN` and the prepared-key paths, for all three sets. `tests/fast_verify_dispatch.rs` checks that the public
  functions take the AVX2 path exactly when the CPU has AVX2. The parse has its own boundary tests (`src/sampling.rs`,
  `boundary_tests`: candidates q−1, q, q+1, bit 23 set, a candidate across a lane boundary, the cutoff at 256).
- **The prepared-key verify under `avx2`** is the extracted function itself, so the statements of 1.1 and 1.4 about
  `verify_prepared_NN` and `verify_internal_prepared_NN` apply to it unchanged (no Lean statement or proof was touched for
  it; the only change to the extracted Lean is source line numbers in comments). What is added is trust in the wrapper and in the
  compilation of the proved loops with AVX2 (item 5 of section 2). `tests/fast_verify_dispatch.rs` checks that the public
  prepared-key functions reach `verify_prepared_avx2` exactly when the CPU has AVX2 (and not for a context over 255 bytes),
  and `tests/fast_verify.rs` compares the prepared-key paths with the scalar verify.
- **Outside the proof and not tested to the same degree:** the dispatch glue and the CPU and OS detection; that rustc and LLVM
  compile the `#[target_feature]` clones (the 4-way ones with every `_mm256_*` call inlined into them, and `verify_prepared_avx2`
  with the proved scalar verify inlined into it) to code that computes what the source says
  (`scripts/check-avx2-inlining.sh` checks that no intrinsic is called out of line, that the verify-only arithmetic and
  `verify_prepared_internal` are not defined out of line, and that each of the three `verify_prepared_avx2` instantiations
  (ML-DSA-44, -65, -87) holds ymm code; that matters for speed, not for correctness); and that the intrinsics behave as the vendor documents. No Lean theorem restates `api.verify_NN` or
  `api.verifying_key_NN` with the 4-way body: the proved statements are about `verify_internal_NN` and `prepare_vk`, and the
  wrapper code around the dispatched call is the extracted wrapper code, which is a reading of the source, backed by the tests
  above.
- **Not proved either way:** speed. The portable 4-way Keccak (`Shim4`) is slower than four scalar permutations, so no portable
  build calls it; only the AVX2 instance is dispatched to. A sanity timing on the build box (the ignored timing test of
  `tests/keccak4.rs`, best of 7 runs of 200,000 calls, ns per call of four permutations; not a benchmark): default flags, four
  scalar permutations 1460, `Shim4` 2018, `Avx2` 489; nearcore's flags, 1348, 1790 and 499.

## 2. What each result assumes: the trusted base

1. **Spec fidelity** of `lean/Spec` against FIPS 204/202. Evidence is the list in 1.8 (internal reviews, test vectors, and
   equivalence to other transcriptions); none of it is a proof that the spec is the standard.
2. **Charon/Aeneas translation** (pins in section 0). Extraction runs with `--cfg miri`, so the proved code is the source with
   the `cfg(miri)` variants: `field::opaque_u32` and the RISC-V `black_box` are the identity there, and the AVX2 dispatch is
   absent (CT-1, CT-2 below; `docs/object-code-assurance.md` §3.5). Evidence: the extracted code compiled and run against the
   native Rust on 345,360 cases (Keccak, field, NTT, rounding, samplers, codecs and the full public API incl. 225 ACVP-derived
   cases), 100% agreement; 4 injected bugs all detected (`scripts/impl-eval.sh`, `lean/SpecTests/ImplEval.lean`).
3. **rustc/LLVM** compile the source faithfully. The theorems are about source semantics, not object code. The compiled code
   differs from the proved code by the `black_box` barriers of item 2 (and, with the `avx2` feature, the dispatch and the AVX2
   lane operations, item 5); `black_box` is trusted to be the identity on values.
4. **The Lean kernel** with `propext`, `Classical.choice`, `Quot.sound`.

5. **With the `avx2` feature only** (x86_64): the tested equivalence of the `Avx2` lane operations to the proved `Shim4` (1.9),
   the dispatch glue and CPU detection (`src/fast_verify/dispatch.rs`, `src/cpu.rs`), the three `#[target_feature(enable =
   "avx2")]` wrappers there (`verify_internal_avx2`, `prepare_vk_avx2`, `verify_prepared_avx2`: each a call of one proved
   function, reached only after `cpu::has_avx2()`; each starts with the value-free `align_frame()` of 1.9, and `prepare_vk_avx2`
builds its key in place with the proved `prepare_vk_into_x4`), and rustc and LLVM compiling those clones (the 4-way bodies, and the proved
   scalar prepared-key verify inlined into `verify_prepared_avx2`), besides the same trust in item 3. The NTT's AVX2 copy likewise
   rests on `tests/dispatch.rs` (section 3).

Zeroize, the opt-in AVX2 code (its status is item 5) and anything above `api` are outside the proof.

## 3. What is NOT covered

See also section 7 (known limitations).

- **Stack exhaustion and out-of-memory are not modeled.** Worst-case stack was measured, not proved (release, statically and by
  stack painting, `tools/stack/`): Sign 116/168/240 KB, Verify 50/76/115 KB, KeyGen 64/98/143 KB for 44/65/87 on x86_64; other
  targets within 4%. Prepared keys: `verifying_key_*` 31/52/26, `signing_key_*` 60/99/164, `verify_prepared_*` 34/45/59,
  `sign_prepared_*` 73/101/134 KB, plus the 20.5–81 KB key object in the caller's frame (`tools/stack/README.md`). These
  predate the fast verify; the stack use of the `avx2` feature's 4-way verify body and of the prepared-key verify inside its AVX2 wrapper was not measured.
- **Positive existence for most inputs.** The `_exact` theorems say the Rust never panics and agrees with the spec whenever
  either returns; that the spec returns `some` for a given input has a kernel witness only for the ML-DSA-44 instance in 1.7.
- **The opt-in `avx2` feature** (runtime CPUID dispatch, the crate's only `unsafe`: `forbid(unsafe_code)` without the feature,
  `deny` with it and an `allow` on each of the NTT dispatch, the CPU check, the verify dispatch and the AVX2 lane operations) is
  covered only in part. The 4-way verify body is proved equal to the scalar verify for `Shim4` (1.9). What is outside the
  proof is the AVX2 lane operations (tested equal to `Shim4`), the dispatch glue, the CPU detection and the compilation of the
  AVX2 clone, so the AVX2 build is proved modulo the tested equivalence of the AVX2 lane operations to the proved shim, not
  proved. The AVX2 copy of the NTT is covered by `tests/dispatch.rs`, the KAT suites run with the feature and a static scan, not
  by BINSEC (`docs/object-code-assurance.md` §3.5). **The `zeroize` feature** is outside the proof. `-C target-cpu=x86-64-v3`
  has no `unsafe` and no dispatch, but the binary then requires AVX2 and BINSEC cannot lift its vector code either; for verify it
  was 2.6–5.9% faster than the `avx2` feature on rustc 1.99.1 and 3.2–3.4% for ML-DSA-44 and -87 but 9.9% slower for ML-DSA-65 on
  1.95.0 (section 5, Benchmarks).
- **Crate-private internals** exposed by the `internals` feature (`verify_internal` with a `Params` inconsistent with its
  `K`/`L`; `sign_internal`/`keygen_internal` on wrong-length slices) can panic (E-1). Without the feature the public surface is
  `api` only and every `api` function has a theorem.
- **Out of scope by decision:** HashML-DSA (Algorithms 4/5) and external μ.
- **Randomness** is the caller's: `keygen_NN` takes ξ and `sign_NN` takes `rnd` (`src/api.rs` module docs).
- **Test harnesses** (ACVP, Wycheproof, differentials, fuzzers) were not themselves reviewed; their sensitivity was checked by
  planting bugs (below).

## 4. Constant-time evidence and its scope

Constant time is checked on compiled probes with BINSEC (relational symbolic execution), not proved in Lean.
"Secure" means BINSEC explored the compiled probe to completion and found no secret-dependent branch, memory address
or division operand for all secret values; the lifter, the solver and "instructions take operand-independent time" are
trusted (`docs/object-code-assurance.md` §3.2). Verify handles only public data (public key, message, signature); the property matters for KeyGen and Sign. That includes the
fast verify: the 4-way body, `poly_use_hint_pub`, `bit_unpack_pub`, `vec_norm_lt_pub`, `bit_pack_pub` and `src/verify_arith.rs` are
reached only from verify's path (`src/keygen.rs` and `src/sign.rs` do not call them, and the secret-key decoders use
`bit_unpack`/`unpack_signed_into`), so they have no probes and need none; the checkct driver includes `src/verify_arith.rs` only so that
`src/verify.rs` compiles.

The full sweep below predates the fast verify and was not rerun on this tree. Since 1a72d9e, `src/sign.rs`, `src/keygen.rs` and
`src/field.rs` are unchanged; the changes under `src/` are the 4-way and dispatch code, the verify-only rewrites, and the move of
the AVX2 check and its cache from `src/ntt.rs` into `src/cpu.rs`, which is shared with the NTT dispatch. So the `dispatch` and
`nearcore-dispatch` rows describe a build whose AVX2 check differs from the current one in where it lives.

The harness builds on this tree. `checkct/driver` gained the `keccak4` module, the `cpu` module (with the `avx2` feature on
x86_64, the cfg of `lib.rs`) and a `fast_verify` module (the real `src/fast_verify.rs`, included by `#[path]`; its `mod dispatch;` carries its own `#[path]`, so it resolves from the driver too, and the driver no longer repeats the re-export list that went stale once; since the p6 round). The pre-set anchor in `checkct/run-select.sh` is now the
symbol `driver::cpu::AVX2`. Checked on the `src/`, driver and scripts of commit 6ccc3e6 (the later verify-only arithmetic of 1.9 changed `src/verify.rs`, and the driver gained `src/verify_arith.rs` at 997b2e5 so that `verify.rs` compiles there; after that change the driver was rebuilt for riscv32imac, thumbv7em and x86_64 with and without `avx2`, but the profile sweep and the smoke run below were not repeated): the driver builds for riscv32imac, thumbv7em and x86_64 in
every `run-select.sh` profile (`default`, `nearcore`, `nearcore-novec`, `dispatch`, `nearcore-dispatch`, `avx2`,
`nearcore-avx2`, `nearcore-exact`, `nearcore-exact-dispatch`, `nearcore-exact-novec`, and `ZEROIZE=1` and `EXPERIMENTS=1`
builds), and the dispatch profiles still find exactly one cache symbol to pre-set; `aarch64.sh` (with and without `NONEON=1`) and
`split-run.sh` build their drivers. A BINSEC smoke run of eight probes (the Sign pieces `signing_key_44`, `hint_step_1_44`, `response_1x1_44` and `make_hint_44`, the hashes
`keygen_seed_hash` and `sign_rho_pp_hash`, and the controls `control_early_exit_44` and `control_prepared_branch_44`) gave the same
verdict as the sweep in all 40 cells: 24 in the default profile (riscv32imac, thumbv7em, x86_64), 8 in `dispatch` and 8 in
`nearcore-exact-dispatch` (x86_64; the cache pre-set found its symbol and applied). In the default profile and
`nearcore-exact-dispatch` the instruction counts and check counts are identical to the sweep's; in `dispatch` the four Sign probes
differ slightly in count (for example `signing_key_44`: 998423 instructions against 1000499), which is code layout after the
cache moved. The controls and the `nearcore-exact-dispatch` `unknown` cells give the same verdicts as in the sweep. The full sweep was not
rerun: Sign and KeyGen code is unchanged. Rows: `checkct/results/smoke-fast-verify/`.

Full sweep at 1a72d9e (November 5–6, 2026; the tree with Sign's per-attempt wiping, in-place secret-key decoding and `sign::more_attempts`): 114 entrypoints per run (113 for the `nearcore`, `nearcore-dispatch` and `nearcore-exact*` profiles) plus two whole-Sign censuses, on x86_64 (checkct profile,
`nearcore`, `avx2` dispatch, `nearcore-dispatch`, `nearcore-exact*`), thumbv7em, riscv32imac and AArch64 without NEON. BINSEC
checks compiled probes of every secret-touching step of KeyGen and Sign (listed in `checkct/README.md`): `sk_is_well_formed`,
the SHAKE paths with secret input, ExpandS, NTT, t, Power2Round, skEncode/Decode, the Sign steps, `prepare_sk`/`signing_key`,
plus positive controls. ExpandS is covered only through its per-nibble helper (`coeff_from_half_byte_eta{2,4}`); the sampler
loop itself (`rej_bounded_poly_eta{2,4}`) branches on its public accept/reject outcome, is an expected-insecure probe and has
no constant-time verdict. The whole KeyGen, Sign and `pk_from_sk` functions have no verdict (`sign::attempt` and `sign_internal`
are not probed whole), and the glue between steps is covered by code reading only. Counts
secure / expected insecure / unexpected insecure / unknown / no verdict (OOM), on the 87-probe basis (85 entrypoints and the
two censuses):

| target / profile | secure / expected insecure / unexpected insecure / unknown / OOM |
|---|---|
| x86_64 default (note 3) | 80 / 6 / 0 / 0 / 1 |
| x86_64 `nearcore` | 80 / 7 / 0 / 0 / 0 |
| x86_64 `avx2` dispatch (note 3) | 80 / 6 / 0 / 0 / 1 |
| x86_64 `nearcore-dispatch` (note 3) | 80 / 6 / 0 / 0 / 1 |
| thumbv7em (note 3) | 81 / 4 / 0 / 0 / 2 |
| riscv32imac (notes 1 and 3) | 75 / 6 / 0 / 5 / 1 |
| AArch64 without NEON (note 2) | 73 / 3 / 0 / 11 / 0 |
| x86_64 `nearcore-exact` (113 entrypoints + 2 censuses, not the 87-probe basis) | 61 / 3 / 0 / 51 / 0 |
| x86_64 `nearcore-exact-novec` (same flags, vectorizers off; 113 entrypoints + 2 censuses; the prepared census ran out of memory) | 108 / 6 / 0 / 0 / 1 |

Against the sweep at 15b4ce2 no verdict changed on x86_64 (all profiles), thumbv7em or AArch64, probe for probe, and every leak
and cut path is at the same mnemonic, source line and function. The differences: riscv32imac (was 78 / 6 / 0 / 2 / 1) lost
`prepare_sk_{44,65,87}` (`secure` to `unknown`) and gained `control_prepared_branch_44` (`unknown` to `insecure` within the
sweep run, the expected result) and three `split_prepare_sk_*` pieces (`unknown` to `secure`); the `nearcore-exact-novec` prepared
census went from a public-leak-only verdict to no verdict (out of memory at 110 GB and 150 GB). Nothing else changed.

1. riscv32imac `prepare_sk_{44,65,87}`: one pending path, no leak, stuck at a store in `ntt_body_mut` (identical instruction counts
   at 600 s and 7200 s). The same driver on the `src/` of 15b4ce2 is `secure`, so the stall comes from the Sign change; its mechanism
   is not pinned down. `signing_key_{44,65,87}`, `prepare_sk_1x1_*` and every `split_prepare_sk_*` piece are `secure`.
2. AArch64 has 13 `unknown` rows in all: the 11 above (on the 87-probe basis, two of them censuses) plus the two split pieces
   `split_prepare_sk_87_{7x1,col}`.
3. Not rerun at 1a72d9e: the thumbv7em and riscv32imac censuses and the x86_64 default, `dispatch` and `nearcore-dispatch`
   prepared censuses. Their cells are the results of the last sweep that ran them (e9a1c74, or 15b4ce2 for default and `dispatch`),
   whose `src/` differs from this one (`checkct/README.md`, "Not rerun, and why").

No unexpected leak. Details, the split-probe results and the stop-site evidence for every unknown are in `checkct/README.md`.
Three real leaks were found and fixed (CT-1, CT-2, CT-3 in section 6). Limits:

- **Whole-Sign** has no verdict: the censuses report only the public `sample_in_ball` accept branch, run out of memory
  (thumbv7em, riscv32imac, the x86_64 default, `dispatch` and `nearcore-dispatch` prepared censuses at 120 GB, and the
  `nearcore-exact-novec` prepared census at 150 GB), or are cut at the NTT under
  nearcore's exact build (the riscv32imac internal census is unresolved, with 4 pending paths at 7200 s). Sign is covered by its secret-touching pieces (`response_*`, `hint_step_*`, ExpandMask, hashing,
  `prepare_sk`, `signing_key`).
- **Unknowns** (no leak found, no conclusion): under nearcore's exact build (`nearcore-exact`) the NTT, `compute_t`,
  `prepare_sk`/`signing_key`, `hint_step`, `response` and the two censuses have no verdict, because BINSEC 0.11.3 cannot lift the
  VEX instructions (`vinsertps`, `vblendvps`, `vblendps` on `ymm`) that `+fma` (which implies AVX) lets LLVM emit; one more probe
  is a solver stall (T-9 in section 7). With the vectorizers off all 113 entrypoints get a verdict (108 secure, 5 expected insecure; 6 expected insecure and one out of memory with the two censuses), which is
  evidence about a different binary, not about nearcore's. Elsewhere: five on riscv32imac (`vec_power2round_87`, one census, and the three
  `prepare_sk_*` probes, a solver stall at one store in `ntt_body_mut`; `signing_key_*` and all their split pieces are secure), the
  three `split_vec_power2round_{5,6,7}` capacity probes there, and eleven on AArch64 (one stuck solver query each; thirteen `unknown` rows with the two `split_prepare_sk_87_{7x1,col}`
  pieces), partly covered by split probes.
- **The `nearcore-exact` CT profile is nearcore's exact release build for the crate in isolation** (`overflow-checks = true`,
  nearcore's x86_64 target features, Rust 1.95.0, read from nearcore cd5a94457). It is not nearcore's binary: callers, allocator,
  glibc `memcpy` and the prebuilt `core` differ (`checkct/README.md`, "What this does and does not show").
- **AVX2 and NEON code:** the AVX2 NTT copy is covered by a static scan only, and the AVX2 lane operations of the fast verify have
  no BINSEC coverage (verify is public data; BINSEC 0.11.3 could not lift them either); AArch64 builds with NEON cannot be lifted, so macOS and Apple Silicon builds have no BINSEC coverage.
- **Other builds:** verdicts depend on code shape and hold for the builds measured. The sweep's binaries are built without the
  `zeroize` feature. A separate run built the x86_64 default profile and `nearcore-exact-novec` with it (`ZEROIZE=1`; all probes,
  same verdicts: 109 secure and 5 expected insecure, 108 and 5), which covers the `zeroize` code shape of the probed functions
  (the `_into` functions with their wipes, `prepare_sk_into`, `sk_decode_into`, ExpandS, KeyGen). `sign::attempt` with
  `wipe_attempt` is not probed whole in any build, and other targets and the censuses have no `zeroize` build.
- Hardware timing (variable-latency instructions, speculation, power) is outside the model.

## 5. Other evidence (tests, differentials, fuzzing)

| Evidence | Result |
|---|---|
| ACVP (NIST, vendored subset) | keyGen 75/75, sigGen 60/60 (pure internal and external, deterministic and hedged), sigVer pure 30/30 (`tests/acvp.rs`). The vendored subset has 120 sigGen and 60 sigVer cases; the other half of each (preHash and external-μ groups) is skipped because HashML-DSA and external μ are not implemented |
| Wycheproof (C2SP, d17cc89) | Rust: 1063 vectors pass, 0 fail, 6 known (E-4: out-of-range secret keys), 69 skipped (external-μ only, out of scope); Lean spec: 928/928 agree (631 verify, 236 sign, 61 keygen) (`tests/wycheproof.rs`, `lean/SpecTests/Wycheproof.lean`) |
| RustCrypto `ml-dsa` a3690c4 (oracle) | pk and sk match on 30 seeds per set; Sign matches on 25 cases per set; Verify agrees on 1,260 cases per set (valid, bit flips in c̃/z/h, wrong M, wrong pk); randomized: 200 keygen + 200 sign/verify (M′ up to 10 kB) + 2,000 sign per set; hint-region differential 30k per set; the public API matches upstream's external interface on 72 cases incl. \|ctx\| = 0, 255, 256 (`tests/diff.rs`, `keygen.rs`, `verify.rs`, `random_diff.rs`, `api.rs`) |
| aws-lc-rs 1.18.2 (aws-lc-sys 0.46.0), the backend nearcore calls for ML-DSA-65 | 0 verdict differences in about 3.22M verify comparisons on fixed-length and wrong-length inputs (2.54M also through `api::verify_NN` and `verify_prepared_NN`): bit flips, multi-bit, fill and splice of σ, pk and M; hint encodings; wrong lengths; c̃; edge-value keys; valid cross-signing both ways; forged z at and beyond ±(γ1−β) and ω hints. 610 empty-ctx Wycheproof verify vectors agree. KeyGen from 15,000 seeds byte-identical. aws-lc signs hedged, so signatures are cross-verified, not compared; aws-lc-rs has no ctx parameter, so only ctx = "" is compared. Known API difference: aws-lc-rs also accepts a DER-SPKI-wrapped pk. Limit: verdict-level testing cannot see a dropped "decreasing count" hint check (c̃ rejects anyway); that check is proved (HintBitUnpack) and unit-tested (`tests/leaf.rs`). 4 of 5 injected verifier weaknesses detected (`tests/awslc_diff.rs`). A test, not an equivalence proof |
| libcrux-ml-dsa 0.0.11 (portable + AVX2), mldsa-native v2.0.0 (C + AVX2), RustCrypto | 0 disagreements, 0 crashes: 1.05M keygens and 1.5M signatures byte-identical; 15.4M verify cases (every single-bit flip of σ and pk for 60 cases per set, plus mutation classes covering c̃, z, hint encodings, pk; about 185M verify calls), all 150k honest signatures accepted by all; fuzzing 3.66M `verify_xdiff` and 195k `sign_xdiff` executions. Sensitivity: with the hint zero-padding check removed, 4,012 disagreements. Malformed sk (FIPS-undefined): ours, libcrux and mldsa-native sign identically; RustCrypto panics; mldsa-native's `pk_from_sk` also rejects inconsistent t0/tr/ρ (`crosscheck/`) |
| Differential fuzzing vs RustCrypto (`fuzz/`) | about 50 minutes per target, 0 crashes, 0 disagreements: `verify_diff` 12.1M execs (mutated c̃/z/hints/pk, ctx 0–256, wrong lengths; 96.7% region coverage of `src`), `sign_diff` 787k (98.2%), `decode_roundtrip` 1.1M (Sign on arbitrary sk bytes never panics; matches upstream wherever upstream accepts the key). Sensitivity: with the hint zero-padding check removed, `verify_diff` found it after about 3,800 runs; a removed `count > ω` check was not found in 180 s (it rarely changes the verdict). The κ-exhaustion path was never reached |
| Proof mutation testing | 29 semantic mutants of `src` (rounding edge cases, hint checks, norm bounds, NTT⁻¹ layers and scale, sampler indices, seeds and hash inputs, κ budget, ctx and length guards, parameter constants): every one breaks the Lean build at the spec theorem of the mutated function. `cargo test` missed 5 (λ/4-byte c̃ compare, `infinity_norm` threshold, HintBitUnpack's count > ω check, Verify's ‖z‖∞ `<`, κ budget); regression tests now kill four (`tests/mutants.rs`, the `prefix_eq` unit test in `src/verify.rs`); the κ budget guard (`while κ + ℓ − 1 ≤ 0xFFFF`, now the function `sign::more_attempts`) is tested at its boundary by `sign_loop_guard_allows_the_last_attempt` (the `<` variant of the guard fails it), while that Sign's loop calls the guard is shown by the proof only. Of the 29 mutants, about a third fail the Lean build as unprovable goals and the rest as proof-script shape breaks (the per-mutant record is not kept). The mutation harness itself is not committed, so this row cannot be re-run |
| AVX2 fast verify (needs a CPU with AVX2; `ML_DSA_REQUIRE_AVX2=1` turns a missing AVX2 into a failure) | the link that is tested, not proved (1.9): `tests/keccak4_avx2.rs` (every AVX2 lane operation, every rotation the kernel uses, all 63 rotation amounts and more than 150,000 whole states against `Shim4` and four scalar permutations), `tests/fast_verify_x4.rs` (4-way sampler, ExpandA and verify over `Shim4` and `Avx2` against the scalar functions), `tests/fast_verify.rs` (dispatched and AVX2 verify against scalar verify on ACVP sigVer, Wycheproof verify and random valid, corrupted, wrong-length and random inputs, every API path, all three sets; CPU detection against the standard library's), `tests/fast_verify_dispatch.rs` (the API reaches the AVX2 wrapper exactly when the CPU has AVX2). `tests/verify_arith.rs` (the verify-only NTT, multiply-accumulate row, norm check and w1 packing against the shared functions on corner and random inputs). Last run (2026-11-07, x86_64 Linux build box with AVX2, tree 306360d, release profile): `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` passed in full (127 tests in 27 binaries, every one `ok`, none failed); `keccak4_avx2` 4 tests, `fast_verify` 5, `fast_verify_x4` 2, `fast_verify_dispatch` 1, `dispatch` 1, `keccak4` 3 (plus its ignored timing test), `verify_arith` 4 |
| Leaf and API tests | round trips on upstream bytes, naive references, every HintBitUnpack ⊥ case, the verify-only `poly_use_hint_pub` against `poly_use_hint` on every r < q for all three sets and `bit_unpack_pub` against `bit_unpack` on random, zero, all-ones and single-bit inputs for 10, 18 and 20 bits (`tests/leaf.rs`); the portable 4-way Keccak against four scalar permutations (`tests/keccak4.rs`); the branchless 4-way parse on boundary candidates (`src/sampling.rs`, `boundary_tests`); optional key checks against 200 random mutations per set (`tests/sk_well_formed.rs`, `tests/pk_from_sk.rs`); SHAKE KATs (`tests/shake_kat.rs`, `shake_lanes.rs`); dispatch vs portable NTT (`tests/dispatch.rs`) |
| zeroize | `tests/zeroize.rs` scans the stack below `keygen`, `pk_from_sk`, `signing_key`, `sign`, `sign_prepared` and single Sign attempts (rejected early, rejected late, accepted) for residue of K, s1, s2, t0, ρ″, the mask y and the values derived from it (ŷ, Â ∘ ŷ, w, ĉ, ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩, r0, ⟨⟨ct0⟩⟩, and z and c̃ of rejected attempts), and checks the drop wipe; see Z-1 for the optimization-level caveat |
| Rust CI (`scripts/ci.sh`) | tests for default, `zeroize` (all 24 scans in release; the 3 `signing_key` scans at opt-level 0) and `avx2` (with `ML_DSA_REQUIRE_AVX2=1`, so a runner without AVX2 fails instead of skipping the AVX2 comparisons); `avx2-inlining` (`scripts/check-avx2-inlining.sh`: no `_mm256_*` function is called out of line in the library build under nearcore's flags); thumbv7em; MSRV 1.86; wasm32; nearcore profile on 1.95.0 (fat LTO, overflow checks, panic = abort for the build) incl. zeroize and, with `ML_DSA_REQUIRE_AVX2=1`, `avx2`; 60 s fuzz smoke of three targets; the aws-lc differential; `cargo deny`; `extract-hash` and `axiom-gate-selftest` (section 0); on GitHub, also the default and release zeroize suites on macOS arm64 (`ci.yml`, `macos-arm64`) |

### Benchmarks

**Verify, all three sets.** ML-DSA verify in microseconds, median of 15 rounds, measured on 2026-11-07 by `bench/fast-verify.sh` under
nearcore's build settings: the `nearcore` profile of `bench/Cargo.toml` (opt-level 3, fat LTO, one codegen unit, panic = abort,
overflow checks on) and nearcore's x86_64 target features (`+sse2,…,+pclmulqdq`, no AVX2). One pinned core of an AMD EPYC 9B14
(Zen 4) KVM guest at a measured 3.4 GHz, zero steal, otherwise idle (load average about 1, the benchmark itself); cpu 45 for the
default toolchain (rustc 1.99.1) and cpu 46 for 1.95.0, nearcore's. Same inputs as the 2026-11-06 run (256 messages of 64 bytes,
empty context, one key pair per set). Columns: `scalar` is the build without the `avx2` feature (the proved scalar verify);
`avx2` is the `avx2` feature (the dispatched 4-way verify, 1.9); `v3` is the `avx2` feature plus `-C target-cpu=x86-64-v3`,
where AVX2 is static and nothing is detected. The reference rows are measured in the same runs; the table lists their `avx2`-run
value (they move by up to 4 µs between a run's three variants, which is run-to-run and layout noise, or, for libcrux, static AVX2
under `v3`). Results and raw logs: `bench/results/2026-11-07-p6.md` (the table below, from the final tree of the stack-offset fix; one run per
toolchain, no cell selected between runs; `bench/results/2026-11-07-p6/`), `bench/results/2026-11-07-p5.md` (the AVX2 wrapper of the
prepared-key verify) and `bench/results/2026-11-07-p4.md` (the verify-only arithmetic), and the logs next to them.

| µs | 44, 1.99.1 | 65, 1.99.1 | 87, 1.99.1 | 44, 1.95.0 | 65, 1.95.0 | 87, 1.95.0 |
|---|---|---|---|---|---|---|
| ours, `scalar` | 52.6 | 89.0 | 153.1 | 52.9 | 88.7 | 153.4 |
| ours, `avx2` | 26.5 | 41.8 | 64.6 | 26.2 | 41.9 | 64.7 |
| ours, `v3` | 26.1 | 41.5 | 64.3 | 26.1 | 41.6 | 64.3 |
| `verifying_key_NN` (builds the prepared key), `scalar` | 41.1 | 75.1 | 133.0 | 40.9 | 74.4 | 133.6 |
| `verifying_key_NN`, `avx2` | 17.6 | 32.2 | 51.8 | 17.5 | 32.2 | 51.8 |
| prepared-key verify, `scalar` | 12.3 | 14.5 | 19.8 | 12.4 | 15.4 | 20.3 |
| prepared-key verify, `avx2` | 9.7 | 11.3 | 15.0 | 9.7 | 11.4 | 15.2 |
| aws-lc-rs 1.18.2 | 22.5 | 36.4 | 56.5 | 22.4 | 36.4 | 56.6 |
| mldsa-native v2.0.0, AVX2 | 21.0 | 34.3 | 53.5 | 20.9 | 34.3 | 53.2 |
| libcrux-ml-dsa 0.0.11, AVX2 | 25.5 | 41.0 | 71.9 | 27.1 | 43.2 | 68.1 |
| RustCrypto `ml-dsa` a3690c4 | 112.1 | 171.1 | 271.4 | 111.1 | 171.4 | 270.8 |

What it shows, for these builds and this machine: the dispatched verify runs in 0.42–0.51 of the scalar time and in 1.14–1.18×
the time of aws-lc-rs's uncached verify; ML-DSA-65 verify went from 103.8 µs to 89.0 µs scalar and from 54.0 µs to 41.8 µs
dispatched (1.99.1; 41.9 µs on 1.95.0) with the verify-only arithmetic of 1.9 (a fused multiply-accumulate row, a lazy-reduction NTT, a mask-free
norm check and a fixed-width w1 packing), and these are plain integer code, so the scalar build gets
most of the gain too. Prepared-key verify, which computes no ExpandA, is much faster than aws-lc-rs's uncached verify in every set,
scalar or `avx2` (ML-DSA-65: 14.5 and 11.3 µs against 36.4), and `verifying_key_NN` costs about 0.77 of one `avx2` one-shot verify
(32.2 against 41.8 µs). It is a different operation from one-shot verify: it needs the key to be held, and a bounded cache is a
nearcore decision ([nearcore-integration.md](nearcore-integration.md)). The prepared-key verify runs no ExpandA, so it has no 4-way
body; with the `avx2` feature it is dispatched to a second `#[target_feature(enable = "avx2")]` wrapper around the same proved
scalar function (1.9), which takes it from 12.3, 14.8 and 20.2 µs to 9.8, 11.3 and 15.3 (interleaved A/B; 0.79, 0.76, 0.76), as fast as the `v3`
build, where AVX2 is static (9.5, 11.1, 14.7; `bench/results/2026-11-07-p6.md`). **The stack offset no longer matters.**
Until the last round the `avx2` one-shot verify and `verifying_key_NN` cells moved with the position of the stack (the process
environment decides it): the same binary read 42.1 µs at one offset and 54.7 at another, about one offset in seven, up to 24 µs
above the median for ML-DSA-87 (scan of 257 offsets, ML-DSA-65: median 42.3, maximum 55.4 µs, 23 offsets above 1.1 times the median). The cause is that LLVM spills the 4-way
Keccak's 256-bit vectors to slots that are only 16-byte aligned, and a slot that straddles a 4 KiB page makes every access a page
split; the wrappers now realign their frames to 32 bytes (1.9), and `verifying_key_NN` builds its key in place. After the fix the
same scan has a maximum of 1.02 to 1.03 times the median in every set and operation, with no offset above 1.1 times
(ML-DSA-65 one-shot: median 41.5, maximum 42.5 µs), on rustc 1.99.1 and on 1.95.0, both at 257 offsets (`bench/stackscan.sh`, run
by `bench/fast-verify.sh`, which fails above 1.15; `bench/results/2026-11-07-p6.md`). Sign was A/B-tested against the commit before
the AVX2 changes and did not move beyond run-to-run noise (ML-DSA-65 deterministic sign 356.4 and 352.0 µs), and nothing Sign
calls changed in p6; the sign figures below date from 2026-10-31. Not measured: aarch64, wasm32, Intel and other AMD parts; one key pair per set, hot caches. Reproduce with `bench/fast-verify.sh`
([reproduce.md](reproduce.md)).

**Keygen and sign, ML-DSA-87** (the verify rows of this earlier table were replaced by the table above). Microseconds, median of 15
rounds over 256 messages (64 seeds for keygen), `bench/compare.sh`, nearcore profile (opt-level 3, fat LTO, one codegen unit,
panic = abort), measured on 2026-10-31 on one pinned core of an AMD EPYC 9B14 (Zen 4) virtual machine at 3.40 GHz, rustc 1.99.1,
shared with other jobs (load average 2.2–2.5):

| operation | default | `avx2` feature | `-C target-cpu=x86-64-v3` |
|---|---|---|---|
| keygen | 229 | 193 | 180 |
| sign (deterministic) | 714 | 466 | 429 |
| sign, prepared key | 543 | 312 | 285 |

Uncached ML-DSA-87 sign for comparison on the same machine and profile: libcrux AVX2 219, mldsa-native AVX2 122, so uncached sign
here is 2.1–3.8× behind the AVX2 implementations in the `avx2` column. Spread over the 15 rounds is at most 0.55% for this crate;
one key pair per set, hot caches. The C libraries were built with gcc 13.3 `-O3` and no LTO (a different C compiler or flags
would change their columns). Sign medians depend on the message set through the number of attempts and move by a few percent
with it, the same for all implementations because their signatures are byte-identical. The `avx2` feature's sign gain comes
from the NTT dispatch; the 4-way Keccak applies to verify only. Not measured: aarch64, wasm32, Intel. Reproduce with
`bench/build.sh`, `bench/run.sh` and `bench/compare.sh` ([reproduce.md](reproduce.md)).

## 6. Found and fixed

- **CT-1** (riscv32imac): the mask-select idiom (`ct_select`, `ct_lt_mask` and callers) was turned back into branches on secret
  data because RISC-V has no conditional move. Fixed with a `core::hint::black_box` barrier compiled only for RISC-V and not under
  `cfg(miri)`, so the proved code is unchanged. Applying it on every target cost about 25% in signing. The standalone `ct_lt_mask` probe is insecure on riscv32imac
  anyway: the probe masks its inputs below 2^63, so LLVM folds the compare back into a branch; every in-crate caller is secure.
- **CT-2** (x86_64): LLVM turned the `diff == q − 1` edge select in `rounding::decompose` into a branch around the multiply that
  computes r1, visible only in the inlined signing-step probes. Fixed in 069b439 by `field::opaque_u32` (`black_box` on every
  target, identity under `cfg(miri)`). Cost about +2–3% in Sign.
- **CT-3** (all targets with overflow checks): `sk_is_well_formed` branched on the sign of secret s1/s2 coefficients because the
  `&&` in the old `poly_in_eta` stayed a conditional branch (its right operand could panic). The six `sk_is_well_formed` and
  `encode_sk_is_well_formed` probes were `insecure` under `nearcore-exact` on the earlier tree
  (`checkct/results/nearcore-exact.stage1-600s.txt`) and are `secure` at 15b4ce2 and at 1a72d9e. Fixed in ae6023c: per-coefficient
  mask bits from wrapping differences, one compare at the end, and `wrapping_*` arithmetic where the proofs already exclude
  overflow, so no overflow-check guard remains on a secret value. Affected only the optional key check and `pk_from_sk_*`; Sign
  never called it. Proofs changed only in bodies.
- **E-2:** upstream's `Signature::decode` also rejects ‖z‖∞ ≥ γ1 − β, which FIPS 204 Algorithm 27 does not (Algorithm 8 does).
  Same final verdict; this crate follows FIPS and checks in `verify_internal`.
- **E-3:** the rejection loops have no provable bound (Verify runs RejNTTPoly and SampleInBall on attacker-chosen seeds). Resolved
  for every input by partial correctness plus panic-freedom: the `*_exact` theorems.
- **T-1:** Aeneas colors its log tags, so a substring gate never matched `[Error]`; `scripts/extract.py` strips ANSI escapes.
- **T-2:** see the extraction constraints below (`return` from a loop followed by another loop).
- **T-4, T-5:** extraction runs with `--no-default-features`, so optional wrapper features (`zeroize`) stay out of the extraction
  closure; the Lake `defaultTargets` include `Spec` and `Proofs`, so the axiom check no longer depends on a warm build directory.
- **T-6:** gate pipelines without `pipefail` reported success on failed builds. `scripts/lean-check.sh` is the done-gate (pipefail;
  fails on a nonzero lake exit, any `error:` or `declaration uses 'sorry'` in the full log, or the axiom gate), and
  `scripts/extract-and-build.sh` greps its build log too.

## 7. Known limitations

- **Z-1 (open): zeroize stack-residue scans fail in unoptimized builds.** `tests/zeroize.rs` has 24 stack scans (eight per
  parameter set: `keygen`, `pk_from_sk`, `signing_key`, `sign`, `sign_prepared` and one Sign attempt each rejected early,
  rejected late and accepted) and four wipe tests (drop wipe per set, SHAKE wipe), 28 tests in all. At opt-level 0, 21 of the 24
  scans find copies of secrets in dead stack frames (K, s1, s2, ŝ1, t0, y or the values derived from it); `signing_key` passes
  for all three sets. At dev opt-level 1 (the whole crate and test at opt-level 1) 26 of 28 pass on a Linux x86_64 machine (`keygen_44` and
  `keygen_65` fail, as before; results at opt-level 1 moved with code layout during this work) and 28 of 28 on an aarch64 macOS
  machine. Release passes 28 of 28 on both machines. The stack-residue claims in `src/api.rs`
  hold for optimized builds only; drop and explicit wipes are unaffected. A copy vendored as a workspace member would build at
  opt-level 0 in a dev profile. Open: add wipes at those locals, or keep the scope. `scripts/ci.sh` runs the 3 passing scans at
  opt-level 0 and all 24 in release and under the nearcore profile. Not wiped by design, as documented in `src/api.rs`: moves
  of returned structs, the accepted signature (z, c̃, h), one copy of K and t0 in keygen, t0 in `pk_from_sk`, and anything
  skipped by a panic or `mem::forget`; registers, swap and core dumps are out of reach. The scans look for the first 16
  coefficients of each vector, so a copy the compiler stores in pieces would be missed.
- **FV-1 (by design): the AVX2 fast verify is proved only modulo a tested link.** The 4-way verify body is proved equal to the
  scalar verify for `Shim4` (1.9). The shipped AVX2 build runs it over intrinsic lane operations whose equality with `Shim4` is
  tested (`tests/keccak4_avx2.rs`), not proved, behind dispatch and CPU-detection code and a compiler-generated AVX2 clone that
  are outside the proof. A difference there would change verify verdicts only on that build, so the portable and AVX2 builds
  are tested equal (`tests/fast_verify.rs`), not proved equal; a deployment that needs the verdict of the proved code builds
  without the `avx2` feature. It is not supported in SGX enclaves, where CPUID faults. No BINSEC verdict applies (verify is
  public data; BINSEC 0.11.3 cannot lift AVX2).
- **T-9: two BINSEC limits decide what a `nearcore-exact` sweep can show.** (1) *Overflow-check guards on secret values stall
  BINSEC*: with `overflow-checks = true`, the conditional jump to the panic path after arithmetic such as `a + Q - b` left 65 probes
  at one pending path through 600 to 3600 s on the earlier tree (68 `unknown` at 600 s, 3 of them `secure` at 3600 s;
  `checkct/results/nearcore-exact.stage1-600s.txt`, `.stage2-trace-300s.txt` and `.stage3-trace-3600s.txt`; in the traced pass 48 of the 68
  stopped at the overflow-check guard in `field.rs:39`, nearly all the others at other lines of `field.rs`). The crate no longer has those guards on secret values (CT-3), and
  those probes are no longer stuck there; source that keeps such guards could stall the same way (not tested). One probe,
  `prepare_sk_1x1_65`, still ends with one pending path at 600 s and 3600 s at a `movdqu` store in `ntt_body_mut`, and is `secure`
  under `-novec` with overflow checks on, so the cause is unknown. (2) *BINSEC 0.11.3 cannot lift AVX/VEX instructions.* nearcore
  builds x86_64 with `+fma`, which implies AVX, so LLVM emits VEX forms; under `nearcore-exact` 48 of 113 probes are cut paths at
  `vinsertps`, `vblendvps` or `vblendps` on `ymm` (the NTT, `hint_step`, `response`, `prepare_sk`, `signing_key` family). So
  nearcore's exact build has no BINSEC verdict for the NTT, `hint_step` and `response`; the `-novec` result is evidence about a
  different binary. Workaround: build the analyzed binary without vectorization, or check the VEX code by another route; neither is
  done for the vectorized NTT/product code.
- **T-8: BINSEC out-of-memory kills look like tool errors.** A probe killed at the container's memory cap shows only `error`. Every
  `error` is presumed an OOM kill, with no verdict, unless the kernel log shows no kill in its run window; a census killed alone at
  120 GB is recorded as "needs more than 120 GB". Whole-Sign censuses on thumbv7em and riscv32imac, and the x86_64 default and
  dispatch prepared census, have no verdict for this reason (not rerun at 1a72d9e). No entrypoint probe of the sweep at 1a72d9e
  ended `error`.
- **Other CT unknowns:** riscv32imac `vec_power2round_87` and one census; the three `split_vec_power2round_{5,6,7}` capacity probes;
  riscv32imac `prepare_sk_{44,65,87}` (solver stall at a store in `ntt_body_mut`, cause not pinned down; they were `secure` at
  15b4ce2, and the same driver on the 15b4ce2 source is `secure`, so the stall comes from the Sign change; `signing_key_*`,
  `prepare_sk_1x1_*` and every `split_prepare_sk_*` piece are `secure`); eleven AArch64
  probes (and two split pieces, `split_prepare_sk_87_{7x1,col}`: thirteen rows in all) stuck in one solver query. AArch64 `prepare_sk_87`/`signing_key_87` are covered only stage by stage (skDecode, then the
  in-place NTT of 8 polynomials, both secure); the K = 8 glue has no single verdict. Split pieces are separate monomorphizations,
  so that argument is about the source, not the full-size machine code. The AVX2 copy of the dispatched NTT, AArch64 NEON builds
  and nearcore's vectorized x86_64 NTT cannot be lifted.
- **E-1:** the core decoders index slices directly. `verify_internal` starts with a length guard (valid when `p` agrees with `K`/`L`),
  but `sign_internal` and `keygen_internal` still panic on wrong-length slices and their older theorems keep the length hypotheses;
  the API's fixed-size arrays discharge them. Every module except `api` is crate-private (public only under the `internals` feature
  for tests and fuzzing), so none of these entry points is reachable by a downstream user unless something in the dependency graph
  turns that feature on (Cargo unifies features).
- **E-4: out-of-range secret keys are accepted.** Six Wycheproof sign vectors (two per set) use an expanded secret key whose s1 or
  s2 has a coefficient outside [−η, η] and expect signing to fail. This crate and the Lean spec both sign with them (FIPS 204
  Algorithm 25 says such coefficients "may lie outside [−η, η] if input is malformed", and Section 7.2 says skDecode should run only on
  trusted input); RustCrypto panics. It is a hardening gap for callers who load untrusted expanded keys. `tests/wycheproof.rs`
  counts these as `known`. Sign stays FIPS-literal; `api::sk_is_well_formed_NN` is a separate, proved check that agrees with
  upstream's panic on 200 random mutations per set.
- **Hint check in verdict-level tests:** see the aws-lc row in section 5.
- **No third-party audit, no FIPS or CMVP validation.**

## 8. Extraction constraints (code shape)

The core follows rules learned from extraction failures; each is enforced by the extraction gate:

1. `while i < N { …; i += 1 }` loops over fixed-size arrays. No `for`, ranges, iterator adapters or closures (`for` pulls in `Step`
   axioms; iterator chains and closures fail to extract).
2. Free functions named after the FIPS algorithm, with the step numbers in comments. No operator-trait impls.
3. Native `[u32; 256]`, `[[u32; 256]; K]`, `[u8; N]` and `&[u8]`. No `hybrid-array`, `typenum` or `module-lattice`.
4. `K`/`L` const generics plus a `Params` value; Charon runs without `--monomorphize`.
5. Lift an inner per-coefficient loop into its own function when it reads data the outer body just wrote (nested loops that read
   freshly written outer data are unsupported in Aeneas).
6. One returning loop per function, as the function's last statement before a plain tail value (`return` from a loop followed by
   another loop makes Aeneas drop the function body; T-2: `hint_bit_unpack_rows` / `_row` / `_padding`).
7. Avoid `copy_from_slice`, `to_le_bytes`, `chunks_exact`, `windows` and `rotate_left` (opaque or unmodeled); write the byte loops out.
8. A trait is allowed when generic extraction can carry it: `keccak4::Lanes4` has by-value `[u64; 4]` operations and no associated
   type, and extraction turns it into a Lean structure passed as an explicit argument. Its `#[inline(always)]` attributes are
   gated by `cfg_attr` on the builds that have the AVX2 clone (as in `field.rs` and `ntt.rs`), so the extracted source is
   unchanged.
9. Keep mask idioms for secret-dependent selects (`ct_lt_mask`, `ct_select`, `opaque_u32`) and branch only on public data.

## 9. Rust ↔ FIPS 204 map

Each function's doc comment names its algorithm (`grep -n "Algorithm [0-9]" src/*.rs`). By module:

| Module | FIPS 204 / 202 |
|---|---|
| `api.rs` | Alg 1 KeyGen, Alg 2 Sign, Alg 3 Verify (ctx prefix M′ = 0 ‖ \|ctx\| ‖ ctx ‖ M), prepared keys, `sk_is_well_formed`, `pk_from_sk` |
| `keygen.rs`, `sign.rs`, `verify.rs` | Alg 6 KeyGen_internal, Alg 7 Sign_internal (loop body in `sign::attempt`), Alg 8 Verify_internal (includes sigDecode and the ‖z‖∞ check) |
| `encode.rs` | Alg 16–19 (bit packing via an accumulator, with a Lean lemma relating it to the bit-string spec), Alg 20/21 HintBitPack/Unpack, Alg 22/23 pkEncode/Decode, Alg 24/25 skEncode/Decode, Alg 26/27 sigEncode/Decode, Alg 28 w1Encode |
| `sampling.rs` | Alg 14 CoeffFromThreeBytes, Alg 15 CoeffFromHalfByte, Alg 29 SampleInBall, Alg 30 RejNTTPoly, Alg 31 RejBoundedPoly, Alg 32 ExpandA, Alg 33 ExpandS, Alg 34 ExpandMask; also the 4-way RejNTTPoly and ExpandA (`rej_ntt_poly_x4`, `expand_a_x4`, `expand_a_into_x4`) |
| `rounding.rs` | Alg 35 Power2Round, Alg 36 Decompose, Alg 37 HighBits, Alg 38 LowBits, Alg 39 MakeHint, Alg 40 UseHint |
| `ntt.rs` | Alg 41 NTT, Alg 42 NTT⁻¹, Alg 44–48 (AddNTT … MatrixVectorNTT); the zeta table is a literal that Lean checks against ζ^BitRev8(k); optional AVX2 dispatch |
| `field.rs` | arithmetic in Z_q (reduction is Barrett/Montgomery; FIPS 204 allows any equivalent reduction; Alg 49 is not used), mask helpers |
| `keccak.rs` | FIPS 202 Keccak-f[1600], SHAKE128/256 |
| `keccak4.rs` | four Keccak-f[1600] permutations at once, generic over `Lanes4` (`Shim4` and the AVX2 `Avx2`) |
| `fast_verify.rs`, `fast_verify/dispatch.rs`, `cpu.rs` | no FIPS algorithm: with `avx2`, the run-time choice between the scalar and the 4-way Verify_internal and `prepare_vk`, and the cached CPU check |

Algorithms 9–13 (bit/byte conversions) and 43 (BitRev8) exist only in the Lean spec. HashML-DSA (Alg 4/5) is not implemented.

## 10. Related work

A survey of public READMEs, proof directories and papers on 2026-10-30; it was not re-run afterwards, no one's proofs were
rebuilt, and the descriptions below can be out of date or wrong. "Related" does not mean equivalent in scope.

- **Apple corecrypto** (C; Cryptol/SAW and Isabelle): reported to refine an Isabelle transcription of FIPS 204 for KeyGen, Sign
  and Verify, with Sign/Verify coverage bounded to specific message sizes.
- **Microsoft SymCrypt** (Rust, Charon/Aeneas/Lean, the same toolchain as this crate): described in a September 2026 paper
  (arXiv 2609.15648); the ML-DSA Rust code and proofs were not in the public branch at the survey date.
- **ocaml-pq** (OCaml; Lean 4 proofs over hand-transcribed models): end-to-end theorems for 44/65/87 against models of the OCaml
  code. `xspec/` proves this crate's spec equal to its transcription (section 1.8).
- **libcrux-ml-dsa** (Rust, hax to F\*): proofs cover leaf modules of the portable and AVX2 arithmetic, NTT and serialization
  layers; the top-level modules were not in the proof set at the survey date, and the project does not claim an end-to-end
  proof.
- **mldsa-native** (C; AWS-LC uses its C-only variant): CBMC proofs of absence of undefined behavior for the C code, and HOL
  Light proofs on the object code of selected assembly routines (functional correctness, memory safety and secret-independent
  timing, per routine). The survey found no theorem relating KeyGen, Sign or Verify as a whole to FIPS 204.
- **Formosa Crypto** (EasyCrypt/Jasmin AVX2 ML-DSA-65): in progress at the survey date, with `admit`s in the proofs.

This crate does not claim to be the first or the only formally verified ML-DSA. Its claim is the specific combination in section 1:
a Rust implementation, a Lean model extracted mechanically from it, theorems over every API input for all three parameter sets with
the premises named above, and `Verify(Sign) = true`, re-checkable on standard Lean axioms. Where the other projects prove things
this crate does not (for example object-code properties), they go further.

## 11. Reproducing each piece

[reproduce.md](reproduce.md) has the exact steps and the tool pins.

| Evidence | Command |
|---|---|
| `*_exact`, prepared, correctness, SkWellFormed, PkFromSk, Divergence; axiom gate | `scripts/lean-check.sh` |
| Witnesses | `scripts/witness-check.sh` |
| Extraction is clean and `lean/Impl` is current | `python3 scripts/extract.py` then `git diff lean/Impl`; `scripts/extract-and-build.sh` for extraction, build and axiom gate |
| Spec against ocaml-pq | `scripts/xspec/check-axioms.sh`; executable differential `scripts/xspec/run-diff.sh all` |
| Spec against VCVio | `scripts/diff-vcvio/run.sh all` |
| Spec against ACVP | `lake build spec-acvp && .lake/build/bin/spec-acvp` in `lean/` |
| Extracted Lean vs native Rust | `scripts/impl-eval.sh lean`, `rs`, then `compare` |
| Rust tests and builds on thumbv7em, MSRV, nearcore profile, wasm32, fuzz smoke, `cargo deny` | `scripts/ci.sh` |
| Cross-implementation differential and fuzzing | `crosscheck/README.md` ("How to run") |
| Differential fuzzing vs RustCrypto | `fuzz/` (`cargo fuzz run verify_diff`, `sign_diff`, `decode_roundtrip`) |
| Constant time | `checkct/README.md` |
| Stack | `tools/stack/run.sh` (`tools/stack/README.md`) |
| Fast-verify theorems | `scripts/lean-check.sh` (it also runs the axiom gate on `lean/keccak4-theorems.txt` and `lean/fast-verify-theorems.txt`) |
| AVX2 fast verify tests | `ML_DSA_REQUIRE_AVX2=1 cargo test --features avx2,internals` on an AVX2 machine |
| AVX2 body compiled with AVX2 | `bash scripts/check-avx2-inlining.sh` |
| Performance | `bench/compare.sh` (keygen, sign), `bench/fast-verify.sh` (verify) |

## 12. Wording that stays inside the evidence

Safe: "the extracted Rust for every `api` function is proved, with no premises, to never fail (in the Aeneas model: stack
exhaustion and out-of-memory are not modeled, and the Rust can diverge exactly when the spec returns no result at any
fuel, §1.2) and to agree with the Lean transcription of FIPS 204 whenever either returns (`*_exact`), with the trusted
base in §2"; "constant time is checked by BINSEC on compiled probes for the builds and targets in §4". Not supported:
"formally verified" without that scope; "constant time" for whole-Sign; any statement about aws-lc equivalence; "FIPS validated"
or "FIPS certified"; "first" or "only"; "production-ready" or "audited".

For the `avx2` feature: "in the portable build verify is the proved scalar verify; in the AVX2 build the 4-way verify body is
proved equal to the scalar verify for the plain-Rust shim, and the AVX2 build is proved modulo the tested equivalence of the
AVX2 lane operations to the proved shim (§1.9), with the dispatch, CPU detection and compilation of the AVX2 clone outside the
proof". Not supported: "the AVX2 build is proved" or "verified" without that qualifier; any statement that the AVX2 build's
verdicts are proved equal to the portable build's; a constant-time statement about the AVX2 NTT or lane operations.

The Lean theorems are about source semantics, not object code, and the agreement of Verify verdicts across nodes and builds is a
consensus property that §1.1 gives only for code with the semantics of the extracted source. With the `avx2` feature the
dispatched and portable NTT copies are tested equal (`tests/dispatch.rs`), not proved, and the AVX2 lane operations are tested
equal to the proved shim (`tests/keccak4_avx2.rs`), not proved. The nearcore-profile test run in
`scripts/ci.sh` (`nearcore-test`, overflow checks on) is an empirical check of the compiled code, not a proof.
