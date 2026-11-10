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

Round 12 (the last entry of this section) removed the run-time AVX2 dispatch and the AVX2 NTT: the gate tables and entries of rounds before it describe trees that had a dispatch, a CPU check and `unsafe` calls, and are kept as history; their counts (`lean/headline-theorems.txt` 412, `keccak4-theorems.txt` 6, `fast-verify-theorems.txt` 51 to 105 depending on the round) are not the current ones. The current table is the one at the end of the Round 12 entry.

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

The 3+1 ExpandA (`tr = H(pk, 64)` in the fourth lane of the first groups of the 4-way ExpandA; branch `fv-p7`; 1.9) is a later tree
again, and unlike the two before it changes Lean: `lean/Impl` is re-extracted with real changes to `Funs.lean` (the new
functions, and `expand_a_into_x4` split into a wrapper and `expand_a_from_x4`), four modules are new (`Proofs/TrLane.lean`,
`TrLaneRust.lean`, `TrGroup.lean`, `TrOuter.lean`), `FastVerify.lean` gains `expand_a_tr_into_x4_eq` and a new proof of
`prepare_vk_x4_eq`, and `lean/fast-verify-theorems.txt` goes from 51 to 79 names. No name in `lean/headline-theorems.txt`
(412) and nothing under `lean/Spec` changed, and no existing theorem statement changed except that `x4_body_partial`,
`x4_loop_partial`, `x4_body_term` and `x4_loop_term` name the renamed extracted constants `expand_a_from_x4_loop(.body)` (same
hypotheses and conclusions). Nothing Sign or KeyGen calls changed, and the dispatch wrappers are unchanged. Every gate below ran on
the Linux build box on 2026-11-08, on the tree of commit b1f47e0; the commit that adds this table changes documentation only (`git diff b1f47e0 -- src lean scripts` is empty). The A/B and timing runs of
`bench/results/2026-11-07-p7.md` ran on d89e790 and a503937, which have the same `src/` and `lean/` as b1f47e0.

| Gate | Result | Run on |
|---|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`: `Build completed successfully (3336 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt`, 906 checked, then over the 9 names of `lean/keccak4-theorems.txt` and the 79 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound` | b1f47e0 |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3324 jobs)`, 146 names checked, `AXIOM GATE OK` | b1f47e0 |
| `scripts/ci.sh --lean` | `CI SUMMARY: 21 passed, 0 failed, 0 skipped` (every step, including `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `diff-awslc`, the three fuzz targets at 60 s, `extract-hash`, `axiom-gate-selftest`, and `lean` with `LEAN CHECK OK`: 3336 jobs, 906, 9 and 79 names checked, each `AXIOM GATE OK`) | b1f47e0 |
| `scripts/check-avx2-inlining.sh` | `OK: no out-of-line intrinsic wrappers; verify-only arithmetic fully inlined; verify wrappers realign their frames; 57800 lines of ymm code`; the three `verify_prepared_avx2` instantiations hold 4077, 4966 and 5513 lines of ymm code (K = 4, 6, 8); all nine wrapper instantiations print `1` under "stack-realigning wrappers" | b1f47e0 |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | 28 result lines (27 test binaries and the doc-tests), 129 tests passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`); the new binary is `tests/fast_verify_tr.rs` (2 tests) | b1f47e0 |
| `cargo +1.86.0 build --features avx2` | builds (the declared MSRV) | b1f47e0 |
| README example test (`cargo test --test readme_example`) | 2 passed | b1f47e0 |
| `scripts/extract_hash.py check` | `extract hash OK`: the 4 files of `lean/Impl` match `extract-report.json` (extraction inputs sha256 3adb4fe23cf3a64f91bb70c22a348f474660edb850023bfd3d0ac9bdea9d0cd3) | b1f47e0 |
| checkct driver | builds (release, `-p driver`) for riscv32imac, thumbv7em and x86_64, each with and without `avx2`, in the default release profile (nightly-2026-10-06) and with nearcore's flags (nightly-2026-10-06 and 1.95.0): 18 of 18 cells built. The BINSEC sweep was not rerun: no source Sign or KeyGen calls changed (section 4) | b1f47e0 |
| `bench/stackscan.sh check` (also run by `bench/fast-verify.sh`) | `STACK SCAN OK` at 257 paddings on rustc 1.99.1 and 1.95.0 (largest padding over the median 1.02 and 1.03 for one-shot verify and `verifying_key_NN`; none above 1.1), and at 65 paddings inside `bench/fast-verify.sh` on both | a503937 (same `src/`) |

After review, two commits (1190159, 2c3e126) added the AVX2 run of `tests/fast_verify_tr.rs` (through a checked `internals`-only wrapper in
`src/fast_verify/dispatch.rs`), input validation in the `bench` stack-scan tool, and a measurement-count check in
`bench/stackscan.sh`. Their extracted `lean/Impl/*.lean` files are byte-identical to b1f47e0's (only the extraction-input digest in
`extract-report.json` moves, to b041a215…), so the Lean gates above still apply. On the tree of 2c3e126, on the box:
`extract hash OK` (b041a215c1ac1de358c645238c4197e503768281352a837d80da282d5998e1f7), `ML_DSA_REQUIRE_AVX2=1 cargo test --release
--features avx2,internals` 28 result lines, 129 passed, 0 failed, 1 ignored, and `scripts/check-avx2-inlining.sh` OK (57800 lines of
ymm code).

Round 8 (branch `fv-p8`; 1.9) is a later tree again and changes Lean and the source. `Proofs/Keccak4.lean` is rewritten to
prove the plain-Rust 4-way Keccak directly (no lane-operation specs, no `Sh4` instance), `Proofs/Dispatch.lean` is new, the
extraction covers `cpu.rs`, `fast_verify.rs`, its `dispatch.rs` and 15 `api::*_with` functions, and `lean/keccak4-theorems.txt`
(9 to 6 names) and `lean/fast-verify-theorems.txt` (79 to 102) change. The fast-verify theorems lose the `Sh4` instance
argument and nothing else (`git diff fv-vec -- lean/Proofs` shows each statement). No name in `lean/headline-theorems.txt` is removed. Every gate below ran on the Linux
build box on 2026-11-08 and 2026-11-09 on the tree of commit 428f6e2. The commits that add this table change documentation, benchmark result files and checkct result files only (`git diff 428f6e2 -- src lean scripts checkct/driver tests Cargo.toml` is empty), so the gates apply
to it. Earlier runs of the Lean gates on older trees of the same branch (5f638b7, 2cb3765, c3b856e) are not cited.

| Gate | Result | Run on |
|---|---|---|
| `scripts/lean-check.sh` (the `lean` step of `ci.sh --lean`) | `LEAN CHECK OK`: `Build completed successfully (3337 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt`, 926 checked, then over the 6 names of `lean/keccak4-theorems.txt` and the 102 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound` | 428f6e2 |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3324 jobs)`, 146 names checked, axioms `propext`, `Classical.choice`, `Quot.sound`; `AXIOM GATE OK` | 428f6e2 |
| `scripts/ci.sh --lean` | `CI SUMMARY: 21 passed, 0 failed, 0 skipped` (every step, including `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `diff-awslc`, the three fuzz targets at 60 s, `extract-hash`, `axiom-gate-selftest` and `lean`) | 428f6e2 |
| `scripts/check-avx2-inlining.sh` | `OK: 4-way permutation vectorized in every wrapper; verify-only arithmetic fully inlined; verify wrappers realign their frames; 57465 lines of ymm code`; the three `verify_prepared_avx2` instantiations hold 4077, 4966 and 5513 lines of ymm code (K = 4, 6, 8); all nine wrapper instantiations are vectorized and realigned | 428f6e2 |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | 27 result lines (26 test binaries and the doc-tests), 122 tests passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`); `tests/fast_verify_dispatch.rs` is gone (its hooks were dead code once the token existed) and `tests/fast_verify.rs` now runs each AVX2 wrapper against the scalar function | 428f6e2 |
| `cargo +1.86.0 build --features avx2` | builds (the declared MSRV) | 428f6e2 |
| README example test (`cargo test --test readme_example`) | 2 passed | 428f6e2 |
| `scripts/extract_hash.py check` | `extract hash OK`: the 4 files of `lean/Impl` match `extract-report.json` (extraction inputs sha256 81b73246535d20d36ff25b04ebe980a3c4989e8101076b99e82e8a17783ef3f4) | 428f6e2 |
| checkct driver | builds (release, `-p driver`) for riscv32imac, thumbv7em and x86_64, each with and without `avx2`: 6 of 6 cells. The driver includes the real `src/cpu.rs`, `src/fast_verify.rs` and `src/api.rs` | 428f6e2 |
| BINSEC smoke (`checkct/results/smoke-fast-verify/`) | 40 cells (8 probes: `keygen_seed_hash`, `sign_rho_pp_hash`, `control_early_exit_44`, `control_prepared_branch_44`, `signing_key_44`, `make_hint_44`, `hint_step_1_44`, `response_1x1_44`; default profile on riscv32imac, thumbv7em and x86_64, `dispatch` and `nearcore-exact-dispatch` on x86_64), run with the driver of 428f6e2: all 40 verdicts equal the sweep's (the `driver::cpu::AVX2` cache static was found and pre-set in both dispatch profiles). Against the sweep, instruction and check counts are equal in 33 cells and differ slightly in 7 (`control_prepared_branch_44` on riscv32imac and on x86_64, and four probes in the `dispatch` profile; section 4). One cell needed a rerun: `control_prepared_branch_44` on x86_64 ended `unknown` at the 1800 s timeout (1 pending path, 65173 of 65173 checks passed) while the box was busy with Lean jobs, and gave the sweep's `insecure` when rerun alone at 5400 s (leak found at 3924 s; 989265 instructions, 65173 of 65174 checks, against the sweep's 989292 and 65175 of 65176). `verdicts.tsv` and `build-matrix.txt` (10 profiles plus the zeroize and experiments builds, 30 of 30 cells `secure`; the aarch64 builds, the split-run and `exact-novec-zeroize` were not rerun) were in `checkct/results/smoke-fast-verify/` (now replaced by the round 10 rerun; the round 8 files are in git history, c0c62d6 and 40ee0de) | 428f6e2 |
| `bench/stackscan.sh check` (257 paddings; nine instantiations; rustc 1.99.1 only, 1.95.0 not rerun) | `STACK SCAN OK`; largest padding over the median 1.03 (ML-DSA-87 `verifying_key`), none above 1.1. The scan cannot see the prepared-key anchor of 1.9; the A/B does | 428f6e2 |
| Interleaved A/B against `fast-verify` and `fv-vec` (`bench/results/2026-11-08-p8.md`) | 44/65/87 one-shot, `verifying_key` and prepared verify at paddings 0, 672 and 2752: all 27 cells within 0.9% of `fast-verify` and within about 1.3% of `fv-vec` | 428f6e2 |

Round 9 (branch `fv-p9`; 1.9) is a later tree again. `align_frame()` and its `cfg(miri)` twin are gone: `verify_core` computes w′1 and its
encoding in a `#[repr(align(32))]` `VerifyScratch` (`src/verify.rs`) that it owns, which gives `verify_prepared_avx2` its aligned frame.
`lean/Impl` is re-extracted: `align_frame` is removed, `Types.lean` gains the `VerifyScratch` structure, `verify_core` is the same
function with renamed locals (Aeneas splits the local struct into its fields, and the row loop runs on a borrow of the `w1` field, so
`verify_core_loop` keeps its signature), and `FunsExternal.lean` and `FunsExternal_Template.lean` no longer declare the four unreferenced
`core.iter.range.Step.*.default` axioms (extraction removes them, section 0 pins). **No theorem statement changed**: no name in
`lean/headline-theorems.txt` (412 names), `lean/keccak4-theorems.txt` (6) or `lean/fast-verify-theorems.txt`
(102) changed its statement or gained a hypothesis, and no proof had to be edited: `git diff fv-p8 -- lean/Proofs lean/*.txt` is one docstring in
`Proofs/Dispatch.lean`. The checked count of the first axiom gate is 925 (was 926: `align_frame` was an extracted definition). The new
whole-environment scan (`scripts/check-no-decls.sh`) is part of both Lean gates. Every Lean gate below ran on the Linux build box on
2026-11-09 on the tree of the commit named in the last column; the commits between them (7356bef, f93e94b, 4a3820a) change only
`scripts/check-no-decls.sh` and `scripts/witness-check.sh` (`git diff ff2469d 4a3820a -- src lean` is empty); the commits that add this table and the
result file change documentation, benchmark files and the A/B table script only (`git diff 4a3820a -- src lean scripts checkct tests Cargo.toml` is empty).

| Gate | Result | Run on |
|---|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`: `Build completed successfully (3337 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt`, 925 checked, then over the 6 names of `lean/keccak4-theorems.txt` and the 102 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound`. Then `no-decls text scan: 96 files, 0 forbidden constructs`; `no-decls env scan: 76 modules, 13913 constants, 0 violations` / `NODECLS ENV OK` / `NO-DECLS GATE OK`; `no-decls self-test OK: the Lean scan reported axiom, opaque, implemented_by, extern, sorry and native_decide in an injected Impl module; the text scan named it` | f93e94b |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3324 jobs)`, 146 names checked, axioms `propext`, `Classical.choice`, `Quot.sound`, `AXIOM GATE OK` (f93e94b); on 4a3820a, which also builds the default targets so that the scan covers every module: `Build completed successfully (3337 jobs)`, `no-decls env scan: 95 modules, 14391 constants, 0 violations`, `NO-DECLS GATE OK`, `WITNESS CHECK OK` | f93e94b, 4a3820a |
| `scripts/ci.sh --lean` | `CI SUMMARY: 22 passed, 0 failed, 0 skipped` (every step, including `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `diff-awslc`, the three fuzz targets at 60 s, `extract-hash`, `axiom-gate-selftest`, the new `no-decls-text` and `lean` with `LEAN CHECK OK`) | 4a3820a |
| `scripts/check-avx2-inlining.sh` | rustc 1.99.1: `OK: 4-way permutation vectorized in every wrapper; verify-only arithmetic fully inlined; verify wrappers realign their frames; 57462 lines of ymm code`; the three `verify_prepared_avx2` instantiations hold 4076, 4965 and 5512 lines of ymm code, and all nine wrappers show `andq $-32` (`1 ` in the realign table). rustc 1.95.0: the same `OK` line, 59012 lines, instantiations 4081, 4977 and 5524 | 7356bef |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | 27 result lines (26 test binaries and the doc-tests), 122 tests passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`) | 7356bef |
| `cargo +1.86.0 build --features avx2` | builds (the declared MSRV) | 7356bef |
| README example test (`cargo test --test readme_example`) | 2 passed | 7356bef |
| `scripts/extract_hash.py check` | `extract hash OK`: the 4 files of `lean/Impl` match `extract-report.json` (extraction inputs sha256 3c19e744ca3e8138cfe48b7dc5839b167b4d917bb52d49a9444b3209959c60c1; the recorded hashes are those of the cleaned `FunsExternal*.lean`) | 7356bef, 4a3820a (ci) |
| checkct driver | builds (release, `-p driver`, nightly-2026-10-06) for riscv32imac, thumbv7em and x86_64, each with and without `avx2`: 6 of 6 cells. BINSEC smoke: not rerun in round 9; a comparison of masked disassembly stood in for it, which is not a BINSEC result; the smoke was rerun in round 10, section 4 | f93e94b |
| `bench/stackscan.sh check` (257 paddings; nine instantiations) | rustc 1.99.1 and 1.95.0 (nearcore profile and flags, `OPS=verify,vk,prepared`, sets 44, 65, 87): `STACK SCAN OK` on both; no padding above 1.1 x the median in any of the nine cells (0/257 each); the largest padding over the median is 1.06 (ML-DSA-65 `prepared`, 1.95.0) | 4a3820a |
| Interleaved A/B against `fast-verify` (3b79427) and fv-p8 (40ee0de) (`bench/results/2026-11-09-p9.md`) | 4 interleaved passes at pads 0, 672 and 2752, 27 cells (3 sets, one-shot, `verifying_key`, prepared-key verify): the final tree is within -1.0% to +1.2% of fv-p8 and `fast-verify` is within 0.83%; the prepared-key verify is within -0.6% to +1.2% of fv-p8 (the largest cell, ML-DSA-87 at pad 672, has a run spread of 2.6%); the spread of a cell over the passes is at most 2.6% of its median. The first formulation of the scratch (6e330b0) measured within 1.3% in the same way | 4a3820a |

Round 10 (branch `fv-p10`, from fv-p9 = 8035f65; 1.9) closes the gap that the independent audit of fv-p9 found in the proof's reach: **the
default build's dispatch was not extracted.** In fv-p9 the three `_with` functions of `src/fast_verify.rs` had a second definition under
`#[cfg(not(all(feature = "avx2", any(miri, target_arch = "x86_64"))))]`, so a build without the `avx2` feature ran a body that the Lean
extraction (which always has the feature on) had not seen. The design now:

- `cpu::Avx2` (`src/cpu.rs` :35 and :39) is an inhabited struct where the dispatch exists (feature `avx2` on x86_64, and under `--cfg miri`,
  which is what the extraction sees) and the uninhabited `enum Avx2 {}` everywhere else. The difference between the two builds is a type,
  not a computation.
- `mod dispatch` (`src/fast_verify/dispatch.rs`) is compiled in every build. Its three entry points `verify_internal_on`,
  `verify_prepared_on` and `prepare_vk_on` are safe functions that take the token by value. With the dispatch the body is one `unsafe` call of
  the matching `#[target_feature(enable = "avx2")]` function (:52, :67, :75). Without it the body is `match t {}`: there is no `unsafe` and
  no AVX2 function in the build, and the default build keeps `#![forbid(unsafe_code)]`.
- Each `_with` function in `src/fast_verify.rs` has **one** source definition, the same text in every configuration:
  `match avx2 { Some(t) => dispatch::NAME_on(t, ..), None => <scalar function>(..) }`. `src/api.rs` is unchanged. The cfg inventory below is the
  census that no other cfg-split body exists on the verify path.

**No theorem statement changed or weakened.** `Proofs/Dispatch.lean` still proves, for every `Option<Avx2>` value and as an equality of `RustM`
values (divergence included), that each `_with` function is the scalar function; its some-arm proofs now also unfold
`fast_verify.dispatch.verify_internal_on` and `prepare_vk_on`. The names in `lean/headline-theorems.txt` (412) and `lean/keccak4-theorems.txt`
(6) are unchanged; `lean/fast-verify-theorems.txt` grows from 102 to 105 names (`Proofs.NoDispatch`, below). The checked count of the first
axiom gate is 928 (was 925: the three `_on` functions). `lean/Impl` is re-extracted: `Types.lean` changes only the source line of `cpu.Avx2`,
`Funs.lean` gains the three `_on` functions, and the `_with` bodies call them.

New gates, all in `scripts/ci.sh --lean` and `scripts/lean-check.sh`:

| Gate | What it checks, and its scope |
|---|---|
| `scripts/check-feature-independence.sh` | A second extraction with `--no-default-features` (no `avx2`, still `--cfg miri`) is diffed against `lean/Impl`. It fails for any difference outside the whitelist of `scripts/feature_independence.py`: 7 entries, each with a comment: the `cpu.Avx2` type (struct against uninhabited enum), the three `fast_verify.dispatch.*_on` bodies (one call against `match t {}`) and the three `*_avx2` functions (they exist only where the dispatch does). Seven declarations must be byte-identical in both: the three `_with` functions, `verify::verify_internal`, `verify::prepare_vk`, `verify::verify_prepared_internal` and `cpu::avx2`. Scope: the extracted default configuration at `--cfg miri`. The compiled default build (without `--cfg miri`) differs from the extraction by the cfg sites of `scripts/cfg-inventory.txt`, each justified there |
| `lean/Proofs/NoDispatch.lean` (generated by the same script from the second extraction, built by `lean-check.sh`) | Elaborates the declarations that differ in the default configuration, with its three `_with` functions, and proves them equal to the scalar functions for every `Option cpu.Avx2`: `Proofs.NoDispatch.verify_internal_with_eq`, `verify_prepared_internal_with_eq`, `prepare_vk_with_eq` (3 names, now in `lean/fast-verify-theorems.txt`). `none` is the scalar call and `some` is impossible because `cpu.Avx2` has no value. The gate fails if the file is not the one it would generate from the second extraction, so the proof cannot drift from it |
| `scripts/cfg_inventory.py` (`cfg-inventory` step) | Lists every construct of `src/` that can select what is compiled or read at compile time against the justified whitelist `scripts/cfg-inventory.txt`: `#[cfg(..)]`, `#[cfg_attr(..)]`, `#![cfg..]`, `cfg!`, `cfg_if!`, `cfg_match!`, `env!`, `option_env!`, `include!`, `include_bytes!`, `include_str!`, `is_*_feature_detected!`, a plain `#[path]`, a `macro_rules!` whose body mentions cfg, any other `cfg` identifier, and a build script. The scan blanks comments and string, char and raw-string literals, then matches the tokens whatever whitespace or comments sit between them (`cfg ! [..]`, `# [ cfg (`). At fv-p10 it recognized only `cfg!(..)` and so missed `if cfg! { not(miri) } { return false; }` (round 11, below). A site not listed, a count that differs, a stale entry or an entry without a justification fails, and so does a scan that parses no site. Line numbers are not part of a site, so a new or changed cfg-split body needs a reviewer to write its reason. Scope: the Rust text of `src/`, not `checkct/driver`, `tests/` or `bench/` (225 sites in 15 files on this tree, 92 of them attribute-only `cfg_attr` classes such as `inline`, `allow`, `target_feature`; the two new sites against fv-p10's 223 are the plain `#[path]` attributes of `src/fast_verify.rs`) |
| `scripts/reachable-defs.sh` (in `lean-check.sh`) | A Lean metaprogram (`scripts/lean/ReachableDefs.lean`) walks the constants that the elaborator resolved, transitively, from the 15 verify entry points of `api`, within `Impl`; an unresolved root or reference is an error. It replaces the lexical script `scripts/reachable_defs.py`, which missed six definitions (`field.Q`, `field.QNEG`, `ntt.F_SHOUP`, `sampling.M23`, `sampling.RATE256`, `verify_arith.R2`). Result: 291 declarations: 285 `def`/`abbrev` (the 278 that the lexical scan still finds on this tree, those six, and the `cpu.Avx2` alias) and 6 structure types; structure projection functions are not counted. fv-p9's lexical 275 was 281 with the six. `ntt.*` among them: `F_SHOUP`, `ZETAS`, `ZETAS_NEG_SHOUP`, `ZETAS_SHOUP` (tables only; no `ntt` function) |
| `scripts/check-no-decls.sh` (extended) | The text scan now includes the root modules `lean/Impl.lean`, `lean/Spec.lean`, `lean/Proofs.lean`, and rejects the syntax that makes or adds an opaque or unsafe declaration (`partial`, `unsafe`, `initialize`, `builtin_initialize`, `run_cmd`, `run_elab`, `run_meta`, `addDecl`, `addAndCompile`) besides the old constructs. The Lean scan includes the roots and **refuses a module of the three directories that has no `.olean` unless it is an allowed witness module** (`Proofs.TopWitness*`, 19 modules, built only by `scripts/witness-check.sh`, which scans them with `--all-built`). Those 19 modules get only the text scan in `lean-check.sh` and the full environment scan in `witness-check.sh`: a narrower scope than the other 80 modules of `lean-check.sh`. `--self-test` builds a fixture tree with an axiom in a compiled root module and a `partial def` in an unbuilt module and requires both to be reported, besides the old injected-declaration test |
| `scripts/extract.py`, `scripts/extract_hash.py` | `clean_external` removes the unreferenced external axioms Aeneas declares, and discovery of the references is conservative (round 11): an axiom is kept, and extraction stops with its name, unless the last component of its name appears as a component of any identifier token of `Types.lean`, `Funs.lean` or the rest of the template (comments, string and character literals are blanked by a left-to-right lexer first). So `axiom forward.candidate` used as `candidate` after `open forward in` is found; the four `core.iter.range.Step.*.default` axioms are still all removed on this tree. The self-test runs discovery and cleaning together. A wrongly removed axiom that is still referenced fails Lean's elaboration of `Funs.lean` (unknown identifier), so this check is defense in depth, not the only barrier |
| `scripts/check-avx2-inlining.sh` | Inspects the assembly that the build it just ran wrote to its own path (mbx-managed target placement; no `--target-dir`). It is a performance check only: it shows that the wrappers are vectorized, inlined and realigned, and says nothing about correctness or constant time (verify handles public data only) |
| `scripts/check-readme-counts.py` | The theorem counts that the README states (412 headline, 111 more = 105 + 6) are checked against `lean/*-theorems.txt`. The README said 88 more at fv-p9; the lists had 102 + 6 = 108 |

**The residual of this tree** (outside the Lean proof, on the verify paths, with the feature on x86_64; section 2 item 5 and section 3 have
the full text): the CPU detection and its cache (`src/cpu.rs` :45, :49, :66, :80, :98, and the stub :106 that the extraction sees); the 15 call
lines `NAME_with(cpu::avx2(), ..)` in `src/api.rs`; the 3 `unsafe` calls (`src/fast_verify/dispatch.rs` :52, :67, :75); the attributes
(`dispatch.rs` :116, :132, :149; `src/verify.rs` :53 and :75); and the compiler. Not on any verify path: the NTT dispatch of `src/ntt.rs`
(`unsafe` at :284, :292, :300, :308, :316, :334; tested, section 3) and the test-only `internals` hooks (`src/fast_verify/hooks.rs`,
`src/keccak4.rs` :189). The default build (no `avx2`) has no `unsafe` on the verify path, and the three `_with` functions it runs are the
extracted ones (feature-independence gate). Unchanged from fv-p9 and still true: the compiled build differs from the extraction by
`field::opaque_u32`, `barrier_u32` and `barrier_u64` (`black_box`, the identity under `--cfg miri`; on no verify path) and by the NTT
dispatch.

**The BINSEC rerun that fv-p9 replaced by a comparison of masked disassembly was done** (section 4; tree 5258017, whose `src/` equals the final tree's): the 40-cell smoke (8 probes in the default profile on riscv32imac, thumbv7em and x86_64, and in `dispatch` and `nearcore-exact-dispatch` on x86_64) plus the 8 probes in `nearcore-exact`: **all 48 verdicts equal the sweep's**; instruction and check counts equal in 44 of the 48 cells and different in the 4 `dispatch` cells that already differed in round 8 (same numbers); no `error`, no out-of-memory; build matrix 30 of 30 `secure`. One cell, `control_prepared_branch_44` on riscv32imac, ended `unknown` at 5400 s in the first run (three targets in parallel) and gave the sweep's `insecure` and counts when rerun alone at 10800 s. The masked disassembly comparison is not a BINSEC result and the section 4 text no longer treats it as one.

Every gate below ran on the Linux build box on 2026-11-09 on the tree of the commit named in the last column; the commits after ff54614 change
documentation, benchmark files and `checkct/compare-code.sh` only (`git diff ff54614 HEAD -- src lean scripts Cargo.toml` is empty).

| Gate | Result | Run on |
|---|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`: `Build completed successfully (3338 jobs)`; axiom gate over the extracted definitions and the names in `lean/headline-theorems.txt`, 928 checked, then over the 6 names of `lean/keccak4-theorems.txt` and the 105 of `lean/fast-verify-theorems.txt`; each `AXIOM GATE OK`, axioms used: `propext`, `Classical.choice`, `Quot.sound`. `cfg inventory OK: 223 sites in 15 files, 92 attribute-only, all in the whitelist`; `README counts OK: 412 headline theorems, 111 more`; `no-decls text scan: 100 files, 0 forbidden constructs`; `no-decls env scan: 80 modules, 13935 constants, 0 violations`; `NO-DECLS GATE OK`; both self-tests OK; `reachable: 291 extracted declarations ... REACHABLE OK`; `extract hash OK` (extraction inputs sha256 8ebbd174b98d36dff9220fa5e403172bea6268faa2b45fcdcd41a3b1c22b3009); `feature independence: the two extractions agree except for 7 whitelisted declarations`; `lean/Proofs/NoDispatch.lean matches the second extraction`; `FEATURE-INDEPENDENCE OK` | ff54614 |
| `scripts/ci.sh --lean` | `CI SUMMARY: 25 passed, 0 failed, 0 skipped`: `test-default`, `test-zeroize`, `test-zeroize-release`, `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `nearcore-build`, `nearcore-test`, `nearcore-test-avx2`, `nearcore-test-zeroize`, `wasm32`, `wasm32-zeroize`, the three fuzz targets at 60 s, `diff-awslc`, `deny`, `extract-hash`, `axiom-gate-selftest`, `no-decls-text`, `cfg-inventory`, `readme-counts`, `feature-independence`, `lean` (`LEAN CHECK OK`) | ff54614 |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3324 jobs)`, 146 names checked, axioms `propext`, `Classical.choice`, `Quot.sound`, `AXIOM GATE OK`; then the build of the default targets so that the scan covers every module, including the 19 witness modules: `Build completed successfully (3338 jobs)`, `no-decls text scan: 100 files, 0 forbidden constructs`, `no-decls env scan: 99 modules, 14413 constants, 0 violations`, `NO-DECLS GATE OK` | ff54614 |
| `scripts/check-avx2-inlining.sh` | rustc 1.99.1: `OK: 4-way permutation vectorized in every wrapper; verify-only arithmetic fully inlined; verify wrappers realign their frames; 57462 lines of ymm code` (fv-p9: 57462); all nine wrappers show `1` in the realign table | ff54614 |
| `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals` | 27 result lines, 122 tests passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`); without the feature, `cargo test` (`test-default` of `ci.sh`) passed; README example test (`cargo test --test readme_example`): 2 passed, with and without `avx2` | ff54614 |
| MSRV 1.86 and `thumbv7em-none-eabihf` | `msrv-1.86` (`cargo +1.86 build --release`, and with `zeroize,avx2`) and `thumbv7em` passed in `ci.sh` | ff54614 |
| checkct driver | builds (release, `-p driver`, nightly-2026-10-06) for riscv32imac, thumbv7em and x86_64, each without and with `avx2`: 6 of 6 binaries (`checkct/compare-code.sh build`) | c5f3292 |
| Sign and KeyGen code of the default build | `checkct/compare-code.sh compare` of the driver binaries of fv-p9 and of this tree (default release profile): 234, 239, 234 functions without `avx2` and 234, 239, 235 with it (riscv32imac, thumbv7em, x86_64), **every function identical** after masking addresses, address-like immediates and symbol hashes, none added or removed. This is a comparison of instruction streams, not a BINSEC verdict, and the nearcore-flag profiles are not covered. The source says the same: `git diff fv-p9 -- src` touches `cpu.rs`, `fast_verify.rs`, `fast_verify/dispatch.rs`, `fast_verify/hooks.rs` and `lib.rs` only (no `sign.rs`, `keygen.rs`, `field.rs` or `api.rs` line) | c5f3292 |
| `bench/stackscan.sh check` (257 paddings; nine instantiations) | rustc 1.99.1 and 1.95.0 (nearcore profile and flags, `OPS=verify,vk,prepared`, sets 44, 65, 87): `STACK SCAN OK` on both; no padding above 1.1 x the median in any cell (0/257 each); the largest padding over the median is 1.06 (ML-DSA-87 `vk`, 1.99.1) | ff54614 |
| Interleaved A/B against fv-p9 (8035f65) (`bench/results/2026-11-09-p10.md`) | 4 interleaved passes at pads 0, 672 and 2752, 27 cells (3 sets, one-shot, `verifying_key`, prepared-key verify): all within -0.3% to +1.2% of fv-p9. The two cells above +0.5% (ML-DSA-87 `verifying_key` at pads 0 and 2752, +1.2%) were rerun alone with 8 interleaved passes each and have equal medians (47.87 against 47.87 and 47.89 against 47.87 microseconds). The box carried the BINSEC containers (load 4 to 15) | ff54614 |
| `scripts/extract_hash.py check` | `extract hash OK` (the digest above): the 4 files of `lean/Impl` match `extract-report.json` | ff54614 |

Round 11 (branch `fv-p11`, from fv-p10 = aa0ca78; 1.9) changes no file under `src/` and no Lean file: it fixes the six findings of a second independent audit of fv-p10,
which found no gap on the verify path but six places where a gate or a sentence claimed more than it checked. Each finding was
executed first as a counterexample and is now a negative fixture in the gate's self-test, which CI runs.

| Finding | What was wrong | What changed | Fixture |
|---|---|---|---|
| P2 `cfg_inventory.py` | Only the exact text `cfg!(` was recognized: `if cfg! { not(miri) } { return false; }` in `verify_internal_with` compiled, passed the inventory and left the extraction unchanged, so production would have diverged from the proof model | The scan is token-aware (comments, strings, char literals and raw strings of any hash count and prefix are blanked; `cfg`, `!` and any of `(`, `[`, `{` may be separated by whitespace or comments; attributes with whitespace, `cfg_attr`, `#![cfg..]`). It also lists `cfg_if!`, `cfg_match!`, `cfg_select!`, `env!`, `option_env!`, `include!`, `include_bytes!`, `include_str!`, `is_*_feature_detected!`, a plain `#[path]`, a `macro_rules!` that mentions cfg, any stray `cfg` identifier and a build script, and fails when it parses no site | 40 spellings that must be reported, 7 look-alikes that must not, a `build.rs`, a `build =` key and three empty scans (`python3 -I scripts/cfg_inventory.py --self-test`); 31 of the fixtures (the audited counterexample among them) pass unnoticed through the fv-p10 scanner |
| P2 `clean_external` | Liveness was lexical: `axiom forward.candidate : Nat` used as `open forward in noncomputable def f : Nat := candidate` was not found, and the cleaner removed a live axiom | An axiom is kept (extraction stops with its name) unless the last component of its name appears as a component of no identifier token of any generated file outside the axiom blocks, after a real left-to-right lexing of comments and literals. The four `core.iter.range.Step.*.default` axioms are all still removed | `scripts/extract_hash.py` self-test: 11 uses that must be found (open, `namespace`, full name, `_root_`, «», dot notation, after a string holding `/-`, after a quote character literal, after an unclosed comment) and 4 look-alikes that must not; it runs discovery and cleaning together |
| P2 `ci.sh` | `ML_DSA_FEATURE_INDEPENDENCE_DONE=1` was set unconditionally, so `--strict --lean --only lean` ran the check nowhere and reported success | `ci.sh` sets the flag only after its own `feature-independence` step passed in the same invocation, and removes any inherited value; `lean-check.sh` runs the check itself otherwise, and a run with module arguments says `PARTIAL` | `scripts/ci-selftest.sh` (step `ci-selftest`): the real `ci.sh` and `lean-check.sh` against recording stubs, eight cases (lean alone, with its own step, step failing, step skipped with and without `--strict`, inherited flag, a module argument, a full run without the flag) and a copy of `ci.sh` with the old unconditional flag, on which the first case must fail |
| P2 `compare_code.py` | Two empty function maps compared equal, so a header-only disassembly printed `COMPARE OK` | A comparison needs real listings with at least 100 functions and 10000 instructions and the driver's entry points and three probes on both sides; anything else exits 2 with `COMPARE ERROR` | `python3 -I checkct/compare_code.py --self-test`: the header-only listing, an empty string, non-objdump text, labels without instructions, a few functions, a missing entry point, a probe without instructions. On the build box `compare fv10 fv10` and `fv9 fv10` still print `COMPARE OK` with the same 6 cells as before |
| P1 `assurance.md` section 4 | Unchanged BINSEC instruction counts were read as unchanged compiled code, and a count difference between two riscv32imac runs as nondeterministic exploration | Rewritten to the observed outcomes only: the verdicts, the counts, the timeout with a pending path against the leak found, and that `unknown` means incomplete. No cause is given. No other document reasons from counts to binary identity (`docs/` and `bench/results/` were searched) | none (prose). The BINSEC driver `checkct/run-select.sh` now prints the SHA-256 of the analyzed ELF and of the script next to each result, so later reruns can be compared by file identity; it was not rerun |
| P3 section 12 and leftovers | The recommended wording still described tested AVX2 lane operations, a shim and an unproved dispatch | Section 12 states the current residual and points to section 2, item 5. Stale "lane operations" comments in `bench/Cargo.toml`, `bench/keccak4.sh`, `bench/fast-verify.sh` and `bench/src/bin/expanda.rs`, and "shim" for the CPU check in `docs/object-code-assurance.md`, are fixed. Dated result files under `bench/results/` and the CHANGELOG describe the rounds in which those words were true and are left as they are | none (prose) |

`lean/Impl` is byte-identical to the fv-p10 tree: the cleaner change does not alter the output, and a fresh extraction into an empty directory
is identical to the committed files (`diff -r`). The extraction digest is unchanged because nothing under `src/` or `Cargo.toml` changed.

Every gate below ran on the Linux build box on 2026-11-09 on the tree of 4288dd9; the commit after it changes `docs/assurance.md` and one docstring of
`checkct/compare_code.py` only (`git diff 4288dd9 HEAD --stat -- src lean scripts Cargo.toml` is empty).

| Gate | Result |
|---|---|
| `scripts/ci.sh --lean` | `CI SUMMARY: 26 passed, 0 failed, 0 skipped` (25 steps of round 10 and the new `ci-selftest`): `test-default`, `test-zeroize`, `test-zeroize-release`, `test-avx2`, `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `nearcore-build`, `nearcore-test`, `nearcore-test-avx2`, `nearcore-test-zeroize`, `wasm32`, `wasm32-zeroize`, the three fuzz targets at 60 s, `diff-awslc`, `deny`, `extract-hash`, `axiom-gate-selftest`, `no-decls-text`, `cfg-inventory`, `readme-counts`, `ci-selftest`, `feature-independence` (25 s), `lean` |
| `scripts/lean-check.sh` (the `lean` step; it printed `feature independence: already checked by scripts/ci.sh in this invocation`) | `LEAN CHECK OK: `, `Build completed successfully (3339 jobs)`; `cfg inventory OK: 225 sites in 15 files, 92 attribute-only, all in the whitelist`; `README counts OK: 412 headline theorems, 111 more`; axiom gates over 928, 6 and 105 names, each `AXIOM GATE OK` with `propext`, `Classical.choice`, `Quot.sound`; `no-decls text scan: 100 files, 0 forbidden constructs`; `no-decls env scan: 80 modules, 13935 constants, 0 violations`; both no-decls self-tests OK; `REACHABLE OK` (291 declarations) |
| `scripts/check-feature-independence.sh`, run alone | `lean/Proofs/NoDispatch.lean matches the second extraction`, `FEATURE-INDEPENDENCE OK`; the seven declarations are byte-identical in both extractions |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`; default targets `Build completed successfully (3338 jobs)`; `no-decls env scan: 99 modules, 14413 constants, 0 violations` |
| `scripts/extract_hash.py check`; a fresh `scripts/extract.py` into an empty directory | `extract hash OK`, extraction inputs sha256 `8ebbd174b98d36dff9220fa5e403172bea6268faa2b45fcdcd41a3b1c22b3009` (unchanged from fv-p10); the fresh extraction is byte-identical to `lean/Impl` (`diff -r`), 4 external axioms declared, 0 referenced, 4 removed |
| `cargo test`, and `ML_DSA_REQUIRE_AVX2=1 cargo test --features avx2` | 113 passed, 0 failed; 122 passed, 0 failed, 1 ignored (the timing test of `tests/keccak4.rs`) |
| `python3 -I scripts/cfg_inventory.py --self-test`, `scripts/ci-selftest.sh`, `checkct/compare_code.py --self-test` | each OK; `checkct/compare-code.sh compare` prints `COMPARE OK` for fv10 against fv10 and for fv9 against fv10 (6 binaries each, 234 to 239 functions) |

Round 12 (branch `fv-p12`, from fv-p11 = 1a8d3e2; 1.9) replaces the run-time AVX2 dispatch of verify by the 4-way code in every build, and removes the AVX2 NTT dispatch of 0.1.0. The crate has no `unsafe` (`#![forbid(unsafe_code)]`
in every configuration; `grep -rn unsafe src/` finds comments only) and no run-time CPU detection. Earlier tables in this section describe trees with the dispatch (history); the gate table at the end of this entry is the current one.

- **Decision (Phase 1, `bench/results/2026-11-09-p12.md`).** Option A, always call the 4-way code with no selector and no `cfg`, was chosen over a compile-time selector. One-shot verify, µs (ML-DSA-44 / 65 / 87, Zen 4, rustc 1.99.1): with nearcore's flags (no AVX2) 38.6 / 57.9 / 96.2 for the 4-way code against 52.5 / 88.4 / 152.6 for the scalar code; with nearcore's flags plus `+avx2` 26.1 / 38.4 / 60.7 against 49.5 / 85.9 / 149.8;
  baseline x86-64 76.6 / 115.7 / 190.0 against 75.8 / 122.4 / 202.7 (1.2 % slower for 44, 5 to 6 % faster for 65 and 87); aarch64 (NEON) 42 / 49 / 53 % faster with no flags. With `+avx2` the 4-way code is at parity with fv-p11's dispatch. The AVX2 numbers need `+avx2` target features, which nearcore's flags do not have; this document does not claim that nearcore's feature floor (FMA, BMI2, MOVBE) guarantees AVX2.
  The cost: stack (`verify_NN` 64 / 90 / 132 KB, was 45 / 71 / 111; section 3). A second choice sits inside it: the verify chain is `#[inline(always)]` (4d4bedb). With it, a build with `+avx2` is stable across stack offsets and, under fat LTO (nearcore's profile), the static stack of `verify_NN` is 63 / 90 / 131 KB; without it, 48 / 72 / 110 KB, but 30 of 257 stack offsets are slow in a build with `+avx2`. (The round 12 text here gave painted figures of 259 / 313 / 399 KB and 85 / 115 / 170 KB; those came from the dev-profile block of the harness output, not from an LTO build. Corrected in round 13, below.) Both options, with the data, are in `bench/results/2026-11-09-p12.md` ("Decision point") and `docs/nearcore-integration.md`; the tree has the attribute.
- **`src/`.** `api.rs` calls the plain functions (`verify::verify_internal_x4`, `prepare_vk_into_x4`); `src/cpu.rs`, `src/fast_verify*.rs`, the `#[target_feature]` wrappers, the token and the 15 call lines are deleted. The verify chain (47 functions in `sampling.rs`, `keccak4.rs`, `verify.rs`, `encode.rs`, `rounding.rs`, `verify_arith.rs`) is `#[inline(always)]` without a `cfg_attr`: it keeps the frames 32-byte aligned (section 1.9). The Cargo feature `avx2` is kept as a deprecated no-op (`avx2 = []`).
- **NTT dispatch (separable commit 5c1f2c9).** `ntt.rs` lost its AVX2 butterflies, the `#[target_feature]` functions and the CPUID check; `field.rs` its `unsafe` helpers; `src/cpu.rs` and `tests/dispatch.rs` are deleted. The Lean files `NTT.lean`, `NTTInverse.lean` and `NTTOps.lean` lose the dispatch names from five `unfold` lists (no statement changes). Sign and KeyGen of an `avx2`-feature user get slower: without `+avx2` target features Sign by 14 to 17 %, KeyGen by 2 to 6 %; with them -1.9 % to +1.1 % (`bench/results/2026-11-09-p12.md`). Users who did not enable the feature are unaffected. The default-build verify, sign and keygen code is compared against fv-p11 in the gate table. Reverting 5c1f2c9 alone conflicts in `src/ntt.rs` (comment lines edited by ec0e0fc) and in the `extract-report.json` digest, so the commit is separable in content but not a clean `git revert`.
- **Lean.** `Proofs/Dispatch.lean` and `Proofs/NoDispatch.lean` are deleted; `Proofs/FastVerifyCore.lean` holds `verify_internal_x4_eq`, `prepare_vk_x4_eq`, `expand_a_tr_into_x4_eq` and the lemmas about `prepare_vk_into_x4`. `API.lean` and `APIInternal.lean` state `verifyAPIX4_eq` and `verifyInternalX4API_eq` for the plain functions; the `api_verify_*_eq` headline theorems keep their names and now speak about the function that runs. Theorem lists: `lean/headline-theorems.txt` 412 → 412 (no name changed), `lean/keccak4-theorems.txt` 6 → 6 (no change), `lean/fast-verify-theorems.txt` 105 → 79. Removed from the last list, each because the thing it was about no longer exists: `Proofs.NoDispatch.{prepare_vk_with_eq, verify_internal_with_eq, verify_prepared_internal_with_eq}` and `Proofs.{prepare_vk_with_eq, prepare_vk_avx2_eq, verify_internal_with_eq, verify_prepared_internal_with_eq}` (statements about the `_with` functions that took the CPU-check token); `Proofs.{verifyAPIWith_eq, verifyInternalAPIWith_eq, verifyPreparedAPIWith_eq, verifyInternalPreparedAPIWith_eq}` (the API-level `_with` statements); the fifteen `Proofs.api_{verify, verify_internal, verify_prepared, verify_internal_prepared, verifying_key}_{44,65,87}_with_eq` (the dispatched entry points). `Proofs.verifyInternalX4API_eq` is now `Proofs.APIInternal.verifyInternalX4API_eq` (moved into the file that has the statement; same text). **The statement of every one of the 412 headline names is textually identical to fv-p11's** (a script that cuts each declaration at its `:=`, normalizes whitespace and compares the two trees; 412 of 412 equal, none missing). The statements speak about `api.verify_*` and the other extracted functions, which are now different code (they call the 4-way functions directly); that is what "the Rust verify is the spec" now means, and no premise was added or dropped.
- **Feature independence.** `scripts/check-feature-independence.sh` (`scripts/feature_independence.py`) extracts the crate twice, with `--cfg miri` and with `--cfg miri -C target-feature=+avx,+avx2`, and requires `lean/Impl` byte-identical in both; **the whitelist of differing declarations is empty**. It cannot pass vacuously: the recorded rustflags of the two runs must differ, 13 verify-path declarations must be present and identical in both, and the positive-control crate `scripts/fi-probe` (`cfg!(target_feature = "avx2")`) must extract as `false` without and `true` with the flags. Each subcommand runs the gate's self-test first. This replaces `NoDispatch.lean`, which listed the seven declarations that differed between the two extractions of the dispatch era.
- **cfg inventory.** `scripts/cfg-inventory.txt` has no `avx2`, `cpu` or `dispatch` entry (118 sites in 9 files, 21 attribute-only; was 225 in 15, 92); the three kinds that remain are `miri`, `zeroize` and `internals`.
- **`check-avx2-inlining.sh`** is a performance check now (header of the script): the 4-way permutation must be vectorized to 256 bits in the nine public functions that run it, and the fifteen verify functions must realign their frames. It is not a correctness check.
- **BINSEC.** The dispatch cells of the matrix are gone (`checkct/README.md`). Results: section 4.

Commits on the branch, oldest first: 4fe6198 (verify always 4-way; Lean), 4a67f78 (`ci.sh`), **5c1f2c9 (the NTT dispatch removal; separable)**, 00bc002 (checkct, bench), ec0e0fc (documentation in `src/`, re-extraction), a0292a3 (documents), 4d4bedb (`#[inline(always)]` restored, check script), 06cbdef (stack figures), ccc7143 (BINSEC results of the NTT probes and the smoke, code comparison), 6ff6e28 (the rest of this entry, the other BINSEC results, the decision tables) and 476ec12 (stack-scan figures read from the tables). Only 5c1f2c9 is the NTT removal; it is not the last commit, and a plain `git revert 5c1f2c9` conflicts in `src/ntt.rs` and `lean/Impl/extract-report.json` (the later commits edited comments and the digest), so it is separable in content, not a clean revert.

Every gate below ran on the Linux build box on 2026-11-09 on the tree of 06cbdef; the commits after it change documents and `checkct/results/smoke-p12/` only (`git diff 06cbdef HEAD --stat -- src lean scripts Cargo.toml` is empty). `ci.sh` ran the `lean` step, so `lean-check.sh` ran twice on this tree (once alone, once inside `ci.sh`).

| Gate | Result |
|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK: `, `Build completed successfully (3338 jobs)`; `cfg inventory OK: 118 sites in 9 files, 21 attribute-only, all in the whitelist`; `README counts OK: 412 headline theorems, 85 more (fast-verify + keccak4)`; axiom gates over 898, 6 and 79 names (extracted definitions plus `lean/headline-theorems.txt`, `lean/keccak4-theorems.txt`, `lean/fast-verify-theorems.txt`), each `AXIOM GATE OK` with `propext`, `Classical.choice`, `Quot.sound` only; `no-decls text scan: 99 files, 0 forbidden constructs`, `no-decls env scan: 79 modules, 13846 constants, 0 violations`, its self-test OK; `REACHABLE OK` (242 extracted declarations reachable from the 15 verify entry points; `ntt.*` among them: the four constants `F_SHOUP`, `ZETAS_SHOUP`, `ZETAS`, `ZETAS_NEG_SHOUP`); `FEATURE-INDEPENDENCE OK` |
| `scripts/check-feature-independence.sh` (inside the above, and as the `feature-independence` step of `ci.sh`) | the extractions with rustflags `--cfg miri` and `--cfg miri -C target-feature=+avx,+avx2` are the same Lean, whitelist 0 entries, 13 verify-path declarations present and identical; the probe `cfg!(target_feature = "avx2")` extracted as `false` without and `true` with the flags |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`: `Build completed successfully (3337 jobs)`, 146 names checked, axioms `propext`, `Classical.choice`, `Quot.sound`, `AXIOM GATE OK`; `no-decls env scan: 98 modules, 14324 constants, 0 violations` |
| `scripts/ci.sh --lean` | `CI SUMMARY: 26 passed, 0 failed, 0 skipped`: `test-default`, `test-zeroize`, `test-zeroize-release`, `test-avx2` (`cargo test --features avx2`, then `RUSTFLAGS="-C target-feature=+avx2" ML_DSA_REQUIRE_AVX2=1 cargo test`), `avx2-inlining`, `thumbv7em`, `msrv-1.86`, `nearcore-build`, `nearcore-test`, `nearcore-test-avx2` (nearcore's flags plus `+avx,+avx2`, `--features avx2`), `nearcore-test-zeroize`, `wasm32`, `wasm32-zeroize`, the three fuzz targets at 60 s, `diff-awslc`, `deny`, `extract-hash`, `axiom-gate-selftest`, `no-decls-text`, `cfg-inventory`, `readme-counts`, `ci-selftest`, `feature-independence`, `lean` |
| Tests in the three configurations | the default build, `--features avx2` (a no-op) and `-C target-feature=+avx2` (a CPU with AVX2 is required, `ML_DSA_REQUIRE_AVX2=1`): all passed inside the `test-default`, `test-avx2` and `nearcore-test-avx2` steps; README example test (`cargo test --test readme_example`): 2 passed in the default build, with `--features avx2` and with `-C target-feature=+avx2` |
| MSRV 1.86 and `thumbv7em-none-eabihf` | `msrv-1.86` (`cargo +1.86.0 build`, and with `--features zeroize,avx2`) and `thumbv7em` passed in `ci.sh` |
| `scripts/check-avx2-inlining.sh` (a performance check) | `OK: 4-way permutation vectorized to 256 bits in the nine functions that run it; the fifteen verify functions realign their frames; 136160 lines of ymm code`: the realign table shows `1` for all fifteen |
| `bench/stackscan.sh check` (257 paddings; `OPS=verify,vk,prepared`, sets 44, 65, 87; CPU pinned) | `STACK SCAN OK` in four scans of the final code (two builds, nearcore flags with and without `+avx,+avx2`, each scanned twice; the gate fails above 1.15 times the median). The table of the last scan of each build: 0/257 paddings above 1.1 times the median in all nine cells, the largest padding at 1.033 times the median. The first scan after the build had one outlier at padding 0 (32.6 µs against a median of 25.6, ML-DSA-44 `verify`, with `+avx,+avx2`) and printed `STACK SCAN FAIL`; the four reruns of the same binaries did not reproduce it |
| `grep -rn unsafe src/` | `src/lib.rs` (the comment and `#![forbid(unsafe_code)]`) and one doc line in `src/verify_arith.rs` (`no unsafe`); no `unsafe` code, `forbid` unconditionally |
| Default-build Sign and KeyGen code against fv-p11 (`checkct/compare-code.sh`, `checkct/results/smoke-p12/compare-code.txt`) | **not unchanged**: the tree before the NTT commit is identical to fv-p11 in every function (234, 239, 234), this branch differs in 185 of 233 (riscv32imac), 107 of 236 (thumbv7em) and 39 of 233 (x86_64) functions, among them the NTT callers `matrix_vector_ntt_into`, `scalar_vector_ntt_inverse_into`, `response_into`, `hint_step_into`, `sign_internal`, `compute_t` and `prepare_sk_into` (the listing is in the file; the cause of each difference was not examined); `a0292a3` and the final tree are identical in all functions. Section 4, "Round 12", has the BINSEC reruns |
| BINSEC (section 4, "Round 12"; `checkct/results/smoke-p12/`) | NTT probes: 81 of 84 cells `secure`, the 3 others are the whole-Sign census (`error` on two targets, `unknown` on one); smoke: 23 of 24 cells equal to round 10 in verdict and counts, one `unknown` (x86_64 `control_prepared_branch_44`, a timeout), and the x86_64 control rerun alone ended `insecure` after 3.4 s with round 10's counts |
| `scripts/extract_hash.py check` | `extract hash OK`: extraction inputs sha256 `48da7b5384953b3a222c0bac52b185af368f680410f6a691d8e38d925a5431e0`; the 4 files of `lean/Impl` match `extract-report.json` (Aeneas exit 0, 0 errors, 0 warnings, 0 local opaque functions, 0 referenced external axioms; 266 LLBC function declarations, 478 Lean definitions) |
| Interleaved timings (`bench/results/2026-11-09-p12.md`) | Phase 1 tables (section 5, Benchmarks); the dispatch removal costs Sign/KeyGen of `avx2`-feature users 14 to 17 % / 2 to 6 % without `+avx2` |

A module counts as proved only after `lean-check.sh` passes. Exact steps to rerun everything are in
[reproduce.md](reproduce.md).

What ties the shipped Rust to the proved Lean (the proofs are about `lean/Impl`, the extraction of `src/`):

- Every push and pull request (`ci.yml`, job `repo-checks`, steps `extract-hash`, `axiom-gate-selftest`, `no-decls-text`, `cfg-inventory`, `readme-counts` and `ci-selftest` of `scripts/ci.sh`):
  `extract-hash` fails if the digest of the extraction inputs (every file under `src/`, `Cargo.toml` without its
  dev-dependencies and with its package `version` replaced by `0.0.0` (so a release version bump does not change the digest), the roots, the Charon and Aeneas pins; file names are part of the digest), the set and contents of the files in
  `lean/Impl` (recursively), or the roots in `scripts/extract-roots.txt` no longer match what `lean/Impl/extract-report.json`
  recorded at the last extraction (`scripts/extract_hash.py`, shared with `scripts/extract.py`), or if there is a symlink under
  `src/` or `lean/Impl`, a build script, an `env!`/`include!`-style macro in `src/`, a root `.cargo` directory or toolchain
  file, or a file name with a control character (inputs the extraction does not see, or that make the manifest ambiguous). It checks that committed files agree with each other and does not re-run the extraction, so editing
  `lean/Impl` and the report together passes it. The self-test runs `scripts/check-axioms.sh` on a missing, an empty and a
  declaration-free list and requires it to fail. `no-decls-text` runs the text half of `scripts/check-no-decls.sh` (its self-test, then a scan of every `.lean` file under `lean/Impl`, `lean/Spec` and `lean/Proofs` for `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, `implemented_by` and `extern`, comments and strings excluded); the Lean half, which walks the environment's constants, runs in `lean-check.sh`.
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
| Extraction gate | Aeneas exit 0, no `[Error]`/`[Warning]`, no local opaque function, no referenced external axiom (and the unreferenced ones Aeneas declares are removed, `extract_hash.clean_external`, so `lean/Impl` declares none), every extracted def on standard axioms only, and no `axiom`/`opaque`/`sorry`/`admit`/`native_decide`/`implemented_by`/`extern` anywhere in `lean/Impl`, `lean/Spec`, `lean/Proofs` (`scripts/check-no-decls.sh`) | any failure is fixed in the Rust code, not worked around |
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
| `Keccak4`, `Sample4`, `Sample4Block`, `ExpandA4`, `TrLane`, `TrLaneRust`, `TrGroup`, `TrOuter`, `FastVerify` | the 4-way Keccak-f[1600], RejNTTPoly, ExpandA (also with `tr = H(pk, 64)` in the fourth lane) and verify body, each equal to its scalar counterpart (1.9) | `Params.Std` for the verify theorems; none for the permutation |
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

### 1.9 The 4-way verify (what every build runs)

**What the code is.** `src/keccak4.rs` is a 4-way Keccak-f[1600] in plain safe Rust: no trait, no lane operation, no intrinsic.
The state is `[[u64; 4]; 25]` (`s[k][i]` is lane `k` of state `i`). `round25` is one round (θ, ρ, π, χ, ι) on a scalar state, written
out; `lane_rounds2` loads the 25 lanes of state `i`, applies `round25` twice and stores them back; `keccak_f1600_x4` is a loop over
the 12 pairs of rounds around a loop over the four states. (`round25` and `lane_rounds2` are generated by
`scripts/gen_keccak4_round.py`, whose `--check` the `avx2-inlining` CI step runs.) On top of it, `src/sampling.rs` has a 4-way
SHAKE128 RejNTTPoly and ExpandA (`rej_ntt_poly_x4`, `expand_a_x4`, `expand_a_into_x4`, `expand_a_from_x4`) and the variant that
also hashes the public key (`rej_ntt_poly_x3_tr`, `expand_a_tr_into_x4`, below), and `src/verify.rs` has `prepare_vk_x4` and
`verify_internal_x4`. All of these are extraction roots (`scripts/extract-roots.txt`) and ordinary extracted functions; none has an
instance argument. Two facts the sampler relies on: the SHAKE128 rate, 168 bytes, is 56 whole three-byte candidates, so no candidate
straddles a block and a block-synchronous sampler consumes the same candidate sequence as the byte-wise one; and a lane that has
its 256 coefficients simply idles while the others finish. Also, `verify_internal_x4` and `prepare_vk_x4` use the verify-only
functions below (`poly_use_hint_pub`, `bit_unpack_pub`, and the arithmetic of `src/verify_arith.rs`, `vec_norm_lt_pub` and
`bit_pack_pub`).

Whether the loop over the four states becomes 256-bit code is up to LLVM's loop vectorizer and the target features of the build:
with `-C target-feature=+avx,+avx2` (or `-C target-cpu=x86-64-v3`) it does, without them it becomes 128-bit SSE2 code. That is a
performance property: the code is correct whether or not it is vectorized, and `scripts/check-avx2-inlining.sh` (a CI step) fails if the
permutation stops being vector code in a build with those target features. It is not an assumption of any theorem.

**What is proved** (all `Proofs/*.lean`, theorem names in `lean/keccak4-theorems.txt` and `lean/fast-verify-theorems.txt`,
checked for standard axioms only by `scripts/lean-check.sh`):

| Theorem(s) | Says |
|---|---|
| `round25_spec`, `lane_rounds2_spec`, `keccak_x4_states_loop_spec`, `keccak_f1600_x4_spec`, `keccak_f1600_x4_eq_scalar`, `RndC_eq` (`Keccak4`) | the extracted plain-Rust round `keccak4.round25 a rc` computes the spec round with round constant `rc` on the lanes of `a` (`RndC`: the round with an arbitrary constant; `RndC_eq` says that with the `ir`-th constant of `Spec.Keccak.RCs` it is `Spec.Keccak.Rnd A ir`); `lane_rounds2` applies two such rounds to state `i` and leaves the other three alone; the loop over the four states and the 12 round pairs map state `i` to `Spec.KeccakF1600` of state `i` for each `i < 4`, so `keccak_f1600_x4` is four runs of the extracted scalar `keccak.keccak_f1600`. These are theorems about the extracted source itself: nothing is assumed of an "instance" |
| `absorb_pad34`, `shake_stream`, `init_state_x4_spec` (`Sample4`) | the initial 4-way state of lane `i` is the padded state of the 34-byte message ρ ‖ s[i] ‖ r[i] before the first permutation, and byte `168b + p` of that message's SHAKE128 output is byte `p` of the state after `b + 1` permutations |
| `laneInv_step`, `push_candidate_spec`, `al_val`, `st6_val`, `st7_val`, `rej_ntt_cands8_spec`, `rej_ntt_block_x4_spec`, `rej_ntt_lane_x4_spec`, `first_256_spec` (`Sample4`, `Sample4Block`) | the branchless parse of a block straight from the lane words (eight candidates from three lanes) performs the same accept-or-skip steps as the byte-wise sampler's fold over the 56 candidates, for each lane |
| `keccak_step_lanes`, `rej_x4_body_spec`, `rej_x4_loop_spec`, `rej_ntt_poly_x4_spec`, `rej_ntt_poly_x4_partial` (`Sample4`) | if the spec's RejNTTPoly returns `P i` for the four seeds at some fuel, the 4-way sampler terminates with polynomials representing `P i` (total form); in any case it is partially correct (`partial`, which covers divergence) |
| `expandA_ent`, `expand_a_x4_partial`, `expand_a_x4_term`, `ReprMat.unique`, `rustM_eq_of_partial`, `expand_a_x4_eq`, `expand_a_x4_eq_std` (`ExpandA4`) | `sampling.expand_a_x4 K L ρ = sampling.expand_a K L ρ` as `RustM` values, divergence included, under `Params.Std` |
| `HS_succ`, `HS_final`, `shake256_byte`, `xorBlock_eq_xor17`, `blkT_last`, `blkT_getD_full` (`TrLane`) | the SHAKE256 absorb of a key by whole blocks: `HS pk t` is the sponge state after the first `t` blocks of the padded key, one step XORs block `t` and permutes, block `⌊\|pk\|/136⌋` is the rest of the key followed by the padding, and the first 64 bytes of `HS pk (⌊\|pk\|/136⌋ + 1)` are `SHAKE256(pk, 64)` |
| `set_lane3_spec`, `lane3_state_spec`, `squeeze64_spec`, `absorb_block_lane3_spec`, `tr_tail_lanes_spec`, `tr_finish_scalar_spec` (`TrLaneRust`) | the extracted helpers of the hashing lane: lane 3 of the 4-way state is loaded from and stored to a 25-word sponge state; a block (read from `pk`, or the padded tail lanes) is XORed into lane 3 and nothing else changes; the tail lanes are the lanes of the last padded block; the scalar finish from any `t ≤ q + 1` blocks done yields the first 64 bytes of `HS pk (q + 1)` |
| `rej3_body_spec`, `rej3_loop_spec`, `rej3_loop_partial`, `rej_ntt_poly_x3_tr_spec`, `rej_ntt_poly_x3_tr_partial` (`TrGroup`) | the three-lane group sampler with the lane-3 absorb: lanes 0 to 2 are the sampler's lanes as before, lane 3 holds `HS pk t` after `t` permutations while `t ≤ q`, and at the end the carried sponge state is `HS pk t'` with `t' ≤ q + 1` (total form under a fuel for the three seeds, and partial form that covers divergence) |
| `tr_body_partial`, `tr_loop_partial`, `tr_body_term`, `tr_loop_term`, `expand_a_from_x4_partial`, `expand_a_from_x4_term`, `tr_groups_ok`, `bytesA_tr`, `expand_a_tr_into_x4_partial`, `expand_a_tr_into_x4_term` (`TrOuter`) | the group loop for any number of hashing groups `g3`: it keeps "the matrix entries below `first` are right" and "the carried state is `HS pk t`", the rest of the matrix is the plain 4-wide loop, the scalar finish returns `SHAKE256(pk, 64)`, and the whole function is partially correct and terminates when ExpandA has a result |
| `expand_a_tr_into_x4_eq` (`FastVerify`) | `sampling.expand_a_tr_into_x4 ρ pk a = (expand_a K L ρ >>= fun a1 => hash_pk pk >>= fun tr => ok (tr, a1))` as `RustM` values, divergence included, for every matrix `a` it starts from, under `Params.Std` |
| `prepare_vk_x4_eq`, `verify_internal_x4_eq` (`FastVerify`) | (`prepare_vk_x4_eq` keeps its statement; its proof goes through `expand_a_tr_into_x4_eq`) `verify.prepare_vk_x4 K L pk = verify.prepare_vk K L pk` and `verify.verify_internal_x4 K L p pk m_prefix m sig = verify.verify_internal K L p pk m_prefix m sig` for every argument, as `RustM` values |
| `verifyInternalX4API_eq` (`APIInternal`), `verify_internal_x4_NN_eq`, `verify_internal_x4_NN_exact`, `verify_internal_x4_NN_div_iff` for NN ∈ {44, 65, 87} (`FastVerify`) | the body of `api.verify_internal_NN` run with the 4-way verifier equals `api.verify_internal_NN`, has the three-part `_exact` statement of 1.1 (never fails; agrees with `Spec.Verify_internal` whenever either returns), and diverges exactly when the spec returns no verdict at any fuel |

**`tr = H(pk, 64)` in the fourth lane of the 4-way ExpandA** (branch `fv-p7`). Verify's ExpandA runs `K·L` independent SHAKE128
sponges four at a time through `keccak_f1600_x4`, and `tr` is one SHAKE256 sponge over the key, a chain of `⌊|pk|/136⌋ + 1`
permutations (10, 15, 20) that cannot be split across lanes. `expand_a_tr_into_x4` (used by `prepare_vk_x4` and
`prepare_vk_into_x4`, hence by the one-shot verify and by `verifying_key_NN`) runs the first `g3 = tr_groups(n, q)` groups with
three ExpandA entries each (`rej_ntt_poly_x3_tr`) and the key's sponge in lane 3, carries the sponge between groups as a 25-word
state, finishes the groups of four as before (`expand_a_from_x4`), and finishes whatever blocks of the hash the lane did not
reach with the scalar permutation (`tr_finish_scalar`; for ML-DSA-65 the last five). `g3` is 2, 2 and 4 for 44, 65 and 87
(`bench/results/2026-11-07-p7.md`: the schedule and why). The proof does not depend on `g3`: `expand_a_tr_into_x4_eq` holds for the
function as written, so the schedule is a speed choice, outside the correctness argument. Everything is plain Rust: no new trait, no intrinsic, no `unsafe`.
The proof is over the extracted source as it is, with no assumption about how it is compiled; `tests/fast_verify_tr.rs` additionally
compares `expand_a_tr_into_x4` (run in the default build and in a build with AVX2 target features) with `expand_a` and the scalar
SHAKE256 for the three parameter-set shapes and for key lengths on both sides of every 136-byte block edge. Intermediate lemma statements: the
extracted loop of `expand_a_into_x4` is now `expand_a_from_x4_loop` (the function is split into the `from` form and a wrapper that starts at 0),
so `x4_body_partial`, `x4_loop_partial`, `x4_body_term` and `x4_loop_term` name the renamed constants and have no other
change; every hypothesis and conclusion is as before. No statement in `lean/headline-theorems.txt` changed.

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
`unsafe`, no `#[target_feature]` function) that the compiler vectorizes with the target features of the build, and each is proved to
compute what the shared function computes (`Proofs/NTTPub.lean`, `Proofs/VerifyArith.lean`; names in
`lean/fast-verify-theorems.txt`). Signing and key generation keep the shared functions, which are unchanged (the edits to `src/encode.rs` and `src/rounding.rs`
only add the new functions; `src/sign.rs` and `src/keygen.rs` are untouched, and the removal of the NTT dispatch in round 12 left the portable
NTT bodies as they were). The scalar verify uses the
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

**How the API reaches the 4-way code** (round 12; before it there was a run-time choice, which is history, see the Round 12 entry in
section 0). There is nothing between `api` and the 4-way functions:

- `api::verify_NN` and `api::verify_internal_NN` call `verify::verify_internal_x4`; `api::verifying_key_NN` builds a
  `PreparedVk::zeroed()` in the result slot and calls `verify::prepare_vk_into_x4` on it (which is `prepare_vk_x4` by
  `prepare_vk_into_x4_zero`, so that a 20 to 66 KB key is built in place and not copied out); `api::verify_prepared_NN` and
  `api::verify_internal_prepared_NN` call the scalar `verify::verify_prepared_internal`, which has no 4-way body (the prepared key
  already holds Â, so there is no ExpandA to run four at a time). The functions are ordinary extracted functions: the extraction
  sees the text the build compiles, with no stub, no token and no `cfg` that selects code. The scalar `verify::verify_internal` and
  `verify::prepare_vk` stay in the crate as the reference that the 4-way functions are proved equal to.
- `Proofs/FastVerifyCore.lean` holds `verify_internal_x4_eq`, `prepare_vk_x4_eq` (through `expand_a_tr_into_x4_eq`), and
  `prepare_vk_into_x4_zero` and `prepare_vk_x4_zeroed_bind` (the in-place construction equals `prepare_vk`). `Proofs/API.lean` has
  `verifyAPIX4` (the generic body of `api.verify_NN` with the 4-way verifier) and `verifyAPIX4_eq` (it equals `verifyAPI`, the generic body
  with the scalar one); `Proofs/APIInternal.lean` has the same pair for `verify_internal` (`verifyInternalX4API`,
  `verifyInternalX4API_eq`); `Proofs/PreparedVerify.lean` proves `verifying_key_NN_def` through `prepare_vk_x4_zeroed_bind` and
  `prepare_vk_x4_eq`. The headline theorems `verify_NN_eq` and `verify_internal_NN_eq` keep their statements: each says that
  `api.verify_NN` (`api.verify_internal_NN`) is the generic API body at the parameter set, and the proofs go through the lemmas above.
  So the theorems of 1.1 to 1.4 are statements about the function the build runs, with no step in between.

**Target features, not a dispatch.** What the compiler emits for this Rust depends on the target features of the build, and on nothing at
run time. A build without AVX2 target features (the default, and nearcore's flags) runs the 4-way code as SSE2 code. A build with
`-C target-feature=+avx,+avx2` or `-C target-cpu=x86-64-v3` runs it as 256-bit code and requires a CPU with AVX2; the binary is not
portable to CPUs without it, which is the ordinary meaning of such a build. The crate has no `unsafe`, no `#[target_feature]`
function and no CPU detection (`#![forbid(unsafe_code)]` holds in every configuration, `grep -rn unsafe src/` finds only comments), and
the Cargo feature `avx2` is a deprecated no-op that changes no code. **The extraction does not depend on the target features:** the crate is extracted twice,
as it is and with `-C target-feature=+avx,+avx2`, and the Lean files are byte-identical (`scripts/check-feature-independence.sh`, whose whitelist is
empty; section 0, Round 12). So the proofs are about the Rust text, which is the same text under every target feature. What rustc and
LLVM make of it is the trust of section 2, item 3, the same trust as for the rest of the crate. Tests exercise both
compilations:

- `tests/keccak4_long.rs` compares the permutation with four scalar permutations on more than 150,000 whole states (random, one-hot,
  edge cases, equal-lane states) and a chain of 2,000 iterations; `tests/keccak4.rs` is the short version;
- `tests/fast_verify_x4.rs` compares the 4-way sampler, ExpandA and verify with the scalar functions (including the padded last group of
  ML-DSA-65, whose K·L = 30 is not a multiple of four); `tests/fast_verify_tr.rs` does the same for `expand_a_tr_into_x4`;
- `tests/fast_verify.rs` compares `verify_internal_x4`, `prepare_vk_x4` and `prepare_vk_into_x4` with the scalar functions, and the public
  `verify_NN`, `verify_internal_NN` and the prepared-key paths with them, on the ACVP sigVer vectors, the Wycheproof verify vectors and random
  valid, corrupted, wrong-length and random inputs, for all three sets. The parse has its own boundary tests (`src/sampling.rs`, `boundary_tests`);
- `scripts/ci.sh` runs the whole suite in three configurations: default, `--features avx2` (the no-op), and `RUSTFLAGS="-C target-feature=+avx2"`
  with `ML_DSA_REQUIRE_AVX2=1`, which turns a machine without AVX2 from a printed note into a failure.

- **Stack frames.** In a build with AVX2 target features every function that owns a `#[repr(align(32))]` object gets a 32-byte aligned stack frame
  from it, with no code that exists only for that purpose. `PreparedVk` (`src/verify.rs`) is one: `api::verify_NN`, which builds the
  key on its stack, has the frame from it. `VerifyScratch` (`src/verify.rs`) is the other: `verify_core` creates one and computes in it (w′1 is its
  `w1` field, written by the row loop and read by `w1_encode_pub`; the encoding is its `w1_enc` field, written by `w1_encode_pub` and read by the
  SHAKE256 absorb), so every function that inlines `verify_core` has it, in particular the prepared-key verify, which only borrows a key.
  Aeneas ignores `repr`; the struct and its field accesses are in the extraction and in the proofs (`Proofs/Verify.lean`: `verify_loop_spec`,
  `verify_core_spec`), which is the point: the object is used by the computation, so LLVM has no reason to drop it, and no code exists only
  under `cfg(not(miri))`. Without a realigned frame LLVM spills 256-bit vectors to 16-byte aligned slots and accesses them unaligned, and at about
  one stack offset in seven a slot straddles a 4 KiB page, which made one-shot verify and `verifying_key_NN` up to 7, 13 and 24 µs above the
  median at that offset (`bench/results/2026-11-07-p6.md`). LLVM may split or drop an aligned aggregate (scalar replacement, dead-store
  elimination), which nothing in the source prevents, so `scripts/check-avx2-inlining.sh` stays an object-code check: it requires
  `andq $-32, %rsp` in `api::verify_NN` and in the three instantiations of `verify::verify_decoded`. The stack-offset scan
  (`bench/stackscan.sh`) is the timing check: `STACK SCAN OK` on this tree (section 0, Round 12).
- **Performance, not correctness:** that LLVM vectorizes the 4-way permutation to 256 bits in a build with AVX2 target features (the check
  requires a `vpsllq` on `%ymm` for every permutation rotation amount that is a shift, in `keccak4::keccak_f1600_x4`) and that the frames
  are aligned. A miss makes the build slower, never wrong.
- **Speed.** Measured on the build box (AMD EPYC 9B14, rustc 1.99.1; `bench/results/2026-11-09-p12.md`), one-shot verify for ML-DSA-44 / 65 / 87:
  **under nearcore's current flags** (`-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq`, no AVX2) the 4-way verify takes
  38.6 / 57.9 / 96.2 µs, against 52.5 / 88.4 / 152.6 µs for the scalar functions of the same build; with `+avx,+avx2` added it takes
  26.1 / 38.4 / 60.7 µs. The AVX2 numbers need AVX2 target features: nearcore's flags do not enable them. The feature floor of nearcore's flags (FMA, BMI1, BMI2, MOVBE and the rest) is not claimed here to guarantee AVX2 on the machines that run nearcore, and nothing in the crate relies on it: a binary built with AVX2 target features runs only on a CPU that has AVX2.

## 2. What each result assumes: the trusted base

1. **Spec fidelity** of `lean/Spec` against FIPS 204/202. Evidence is the list in 1.8 (internal reviews, test vectors, and
   equivalence to other transcriptions); none of it is a proof that the spec is the standard.
2. **Charon/Aeneas translation** (pins in section 0). Extraction runs with `--cfg miri`, so the proved code is the source with
   the `cfg(miri)` variants: `field::opaque_u32` and the RISC-V `black_box` are the identity there (CT-1, CT-2 below;
   `docs/object-code-assurance.md` §3.5). Nothing else differs: the crate has no `unsafe`, no CPU detection and no `cfg` that selects code
   by CPU feature, so the extraction sees the functions the build compiles, and the extraction does not depend on the target features of the
   build (`scripts/check-feature-independence.sh`, empty whitelist; section 0, Round 12). Evidence: the extracted code compiled and run against the
   native Rust on 345,360 cases (Keccak, field, NTT, rounding, samplers, codecs and the full public API incl. 225 ACVP-derived
   cases), 100% agreement; 4 injected bugs all detected (`scripts/impl-eval.sh`, `lean/SpecTests/ImplEval.lean`).
3. **rustc/LLVM** compile the source faithfully, for the target features of the build (the default, nearcore's flags, or a build with
   `-C target-feature=+avx2`; the proofs are about the Rust text, which is the same under all of them). The theorems are about source semantics, not
   object code. The compiled code differs from the proved code by the `black_box` barriers of item 2 (on no verify path); `black_box` is
   trusted to be the identity on values. That the compiler vectorizes the 4-way Keccak loop, and realigns the frames, is a performance property
   (`scripts/check-avx2-inlining.sh`), not a premise.
4. **The Lean kernel** with `propext`, `Classical.choice`, `Quot.sound`.

The residual is items 1 to 4: the spec transcription, Charon/Aeneas, rustc/LLVM, the Lean kernel, and the hardware that runs the binary. It is
the base of a 0.1.0 build without its `avx2` feature. **Since round 12 there is nothing else:** the run-time AVX2 check (`src/cpu.rs`), the token, the 15 token-passing call
lines of `src/api.rs`, the `unsafe` calls of the verify dispatch and the NTT dispatch, and the `#[target_feature]` wrappers no longer exist, and the
assumption "the CPU and OS can execute AVX2 whenever the check reports it" is gone with them. (A build with AVX2 target features needs a CPU
with AVX2, as any such build does; that is a deployment requirement, not a premise of a theorem.) Item 5 of the earlier rounds, the residual of the dispatch, is history:
section 0, rounds 5 to 11.

## 3. What is NOT covered

See also section 7 (known limitations).

- **Stack exhaustion and out-of-memory are not modeled.** Worst-case stack was measured, not proved (release, statically and by
  stack painting, `tools/stack/`; x86_64, other targets within 4%; ML-DSA-44 / 65 / 87, in KB): Sign 116/168/240, Verify 64/90/132, KeyGen
  64/98/143. Prepared keys: `verifying_key_*` 50/74/111, `signing_key_*` 60/99/164, `verify_prepared_*` 34/45/59, `sign_prepared_*` 73/101/134,
  plus the 20.5–81 KB key object in the caller's frame (`tools/stack/README.md`). **Round 12 raised the verify figures**, because verify always runs the
  4-way ExpandA now: one-shot `verify_*` by 19/19/21 KB and `verifying_key_*` by 15/17/76 KB over fv-p11 (`bench/results/2026-11-09-p12.md`; the 87 figure of
  `verifying_key_*` is a compiler copy of the key that the build-in-place code does not need; round 13 tried to remove it and the stack growth of verify and did not, `bench/results/2026-11-09-p13.md` section 2). Under `lto = "fat"` (nearcore's release profile) the static walk gives +18/+19/+28 KB for `verify_*` and -6/-20/+9 KB for `verifying_key_*`; the painted stack of a release build with fat LTO agrees with the static walk (63.0 / 89.7 / 130.6 KB for `verify_*`, `bench/results/2026-11-09-p13.md`). The 259 / 313 / 399 KB that the round 12 documents gave for it were the dev-profile (opt-level 0) block of the harness output, not an LTO figure; there is no unexplained LTO growth.
- **Positive existence for most inputs.** The `_exact` theorems say the Rust never panics and agrees with the spec whenever
  either returns; that the spec returns `some` for a given input has a kernel witness only for the ML-DSA-44 instance in 1.7.
- **Compiled code of the verify path.** Every Rust line reachable from `api::verify_*`, `api::verify_internal_*`, `api::verifying_key_*`,
  `api::verify_prepared_*` and `api::verify_internal_prepared_*` is in an extracted function (`scripts/reachable-defs.sh` walks the Lean environment
  and counts the reachable declarations; no `ntt::*` function body other than the tables `ZETAS`, `ZETAS_SHOUP`, `ZETAS_NEG_SHOUP` and `F_SHOUP` is read
  by verify). The crate has no `unsafe` (`#![forbid(unsafe_code)]` in every configuration), no CPU detection and no `#[target_feature]` function;
  the Cargo feature `avx2` changes nothing. What is not proved is the compilation: rustc and LLVM turn the proved source into code for the target features
  of the build, and the object code is neither proved nor checked by BINSEC for verify (verify takes only public data). The `black_box` of
  `field::opaque_u32`, `barrier_u32` and `barrier_u64` (identity under extraction) is on no verify path. **The `zeroize` feature** is outside the proof.
  A build with `-C target-feature=+avx2` (or `-C target-cpu=x86-64-v3`) requires a CPU with AVX2 and BINSEC cannot lift its vector code; for
  Sign and KeyGen the constant-time claims are for the build named in section 4 (section 0, Round 12: the AVX2 NTT copy of 0.1.0 and its dispatch are gone,
  so there is no longer a second NTT whose object code is outside the evidence).
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

**Round 12 BINSEC rerun** (checkct profile `default`, which is the crate's default build with opt-level 3 and no extra target features; the tree of a0292a3, whose `src/` differs from the final one only by `#[inline(always)]` on verify-chain functions and comments; `checkct/compare-code.sh` finds all functions of the driver identical between the two, 233, 236 and 233 on riscv32imac, thumbv7em and x86_64). The dispatch profiles
and the `avx2` driver feature are gone (no run-time choice exists), so the matrix is `default`, `nearcore`, `nearcore-novec`, `avx2`, `nearcore-avx2`, `nearcore-exact` and `nearcore-exact-novec`; the last two have VEX code on x86_64 (nearcore's `+fma` implies AVX) and were not rerun.
What changed in the code BINSEC reads: removing the NTT dispatch changes how Sign's and KeyGen's NTT callers compile in the default build. `checkct/compare-code.sh` (instruction streams with addresses and symbol hashes masked; not a constant-time result) finds
the driver of fv-p11 and the driver of the tree after 4a67f78 (the verify dispatch removed, NTT dispatch still there) identical in every function (234, 239 and 234 functions), and the driver of this branch **different**: 185 of 233 functions on riscv32imac, 107 of 236 on thumbv7em and 39 of 233 on x86_64 (`checkct/results/smoke-p12/compare-code.txt`). So the sweep's verdicts, and the
round 10 smoke, are for a different binary, and these runs are the evidence for this one:
- `checkct/select-ntt.sh` (every probe that runs the NTT, the pointwise product or the field products, plus the whole-Sign census; 28 probes on three targets, `TIMEOUT=5400`, 64 GB cap): 84 cells, **81 `secure`**, none `insecure`; `census_sign_internal_44` ended `error` on thumbv7em and on x86_64 (killed by the container's 64 GB cap shared with 8 parallel jobs: the kernel log has two `Killed process (binsec)` cgroup entries in the window) and `unknown` on riscv32imac (a timeout with pending paths, as in the sweep). The sweep recorded the thumbv7em census as out of memory above 120 GB, and got a verdict for the x86_64 census (`insecure`, the public accept test of `sample_in_ball` only) with one job and a 110 GB cap; that cell has **no verdict on this tree**, the sweep's is for an earlier binary, and the census was not rerun with a larger cap (`checkct/README.md`: do not raise the cap again). `checkct/results/smoke-p12/select-ntt-default.log`.
- The round 10 smoke (8 probes, 3 targets, 24 cells, `TIMEOUT=3600`): 19 `secure`, 4 `insecure` (the controls `control_early_exit_44` on three targets and `control_prepared_branch_44` on riscv32imac), 1 `unknown`. **Every verdict and every instruction and check count equals round 10's** (`checkct/results/smoke-p12/verdicts.tsv`), including `secure` for `control_prepared_branch_44` on thumbv7em (the sweep's invalid control: the compiler lowers the branch to a select). The one cell that does not match is the x86_64 `control_prepared_branch_44`, the slowest probe of the run: `unknown` at the 3600 s timeout with 1 pending path, 989265 instructions and 65173 of 65173 checks, no leak found in the time; round 10 found its leak in 2.25 s (989292 instructions, 65175 of 65176 checks, no rerun needed). The counts differ and so do the binaries (the comparison above); no cause is given. Rerun alone on the final tree (`JOBS=1`, `TIMEOUT=10800`): `insecure`, the leak found after 3.4 s (0x219d1d), 0 pending paths, 989292 instructions, 65175 of 65176 checks: the counts of round 10. That run built the driver of the final tree, a different ELF from the smoke's (`checkct/results/smoke-p12/control-prepared-branch-x86_64-rerun.log`), with one job instead of four; no cause is given for the difference between the two runs. With that run the smoke's 8 probes have the expected verdicts on x86_64.
- The same eight probes in profile `nearcore` (x86_64, opt-level 3, fat LTO, one codegen unit, no extra target features; `TIMEOUT=3600`): 6 `secure` and 2 `insecure` (the controls `control_early_exit_44` and `control_prepared_branch_44`, the latter found at 988446 instructions), no `unknown` (`verdicts-nearcore.tsv`).
- The same eight probes in profile `nearcore-exact` (x86_64, nearcore's release profile with overflow checks and nearcore's target features, rustc 1.95.0): **verdicts and counts equal round 10's in all 8 cells**: `secure` for `keygen_seed_hash`, `sign_rho_pp_hash` and `make_hint_44`, `insecure` for `control_early_exit_44`, `unknown` for `signing_key_44`, `hint_step_1_44`, `response_1x1_44` and `control_prepared_branch_44` (cut at the VEX instruction, as in the sweep; BINSEC 0.11.3 cannot lift it) (`verdicts-nearcore-exact.tsv`).
**Which profiles have a verdict on this tree:** `default` (the NTT probes and the smoke), `nearcore` and `nearcore-exact` (the smoke only, 8 of 113 probes each; the latter is cut at VEX for 4 of the 8). `nearcore-novec`, `avx2`, `nearcore-avx2`, `nearcore-exact-novec`, the AArch64 runs, the `ZEROIZE=1` builds and every probe not listed above have **no verdict on this tree**; the sweep's verdicts for them are for the binary of 1a72d9e, and the code comparison shows that binary differs from this one in the NTT callers of Sign and KeyGen.
Equal counts are not evidence that two binaries are equal (and the comparison above shows these are not), so this document draws no conclusion from them beyond the verdicts. The `error` and `unknown` cells are no verdict. A BINSEC `error` was checked against the kernel log before being read as out of memory, as `checkct/README.md` asks.
The containers (`ct-p12-ntt`, `ct-p12-smoke`, `ct-p12-ctl`, `ct-p12-nex`, `ct-p12-nc`) had exited when the box was checked (`docker ps` empty).

(History, rounds 8 to 11: the rest of this section describes trees with the dispatch; where it speaks of `dispatch` profiles, the `cpu` module or the `avx2` driver feature, those no longer exist.)

The full sweep below predates the fast verify and was not rerun on this tree. Since 1a72d9e, `src/sign.rs`, `src/keygen.rs` and
`src/field.rs` are unchanged; the changes under `src/` are the 4-way and dispatch code, the verify-only rewrites, and the move of
the AVX2 check and its cache from `src/ntt.rs` into `src/cpu.rs`, which is shared with the NTT dispatch. So the `dispatch` and
`nearcore-dispatch` rows describe a build whose AVX2 check differs from the current one in where it lives.

The harness builds on this tree. `checkct/driver` gained the `keccak4` module, the `cpu` module (with the `avx2` feature on
x86_64, the cfg of `lib.rs`) and a `fast_verify` module (the real `src/fast_verify.rs`, included by `#[path]`; its `mod dispatch;`
carries its own `#[path]`, so it resolves from the driver too), and since round 8 also the real `src/api.rs`, so the probes enter
through the public functions and the `_with` functions callers reach. The pre-set anchor in `checkct/run-select.sh` is the symbol
`driver::cpu::AVX2`. Checked on the `src/`, driver and scripts of commit 428f6e2: the driver builds for riscv32imac, thumbv7em and
x86_64 in every `run-select.sh` profile except the aarch64 ones (`default`, `nearcore`, `nearcore-novec`, `dispatch`,
`nearcore-dispatch`, `avx2`, `nearcore-avx2`, `nearcore-exact`, `nearcore-exact-dispatch`, `nearcore-exact-novec`, and
`ZEROIZE=1` and `EXPERIMENTS=1` builds; one cheap probe each, 30 of 30 cells `secure`), and the dispatch profiles find exactly one
cache symbol to pre-set. `aarch64.sh` (with and without `NONEON=1`), `split-run.sh` and the `exact-novec-zeroize` build were not
rerun this round (they compile the same driver sources; the `cpu.rs` stub they use is the one riscv32imac and thumbv7em build).
**Round 10 BINSEC rerun** (fv-p10 tree 5258017, whose `src/` is the final tree's; the commits after it change scripts, documentation and `lean/Proofs` only). The same smoke as round 8 was run
again: eight probes (the Sign pieces `signing_key_44`, `hint_step_1_44`, `response_1x1_44` and `make_hint_44`, the hashes `keygen_seed_hash` and
`sign_rho_pp_hash`, and the controls `control_early_exit_44` and `control_prepared_branch_44`) in 40 cells: 24 in the default profile (riscv32imac,
thumbv7em, x86_64), 8 in `dispatch` and 8 in `nearcore-exact-dispatch` (x86_64; the `driver::cpu::AVX2` cache pre-set found its symbol and applied
in both); plus, beyond the 40, the 8 probes in `nearcore-exact` (x86_64, nearcore's flags without the dispatch). **All 40 verdicts, and the 8 extra
ones, equal the sweep's** (`secure` for `keygen_seed_hash`, `sign_rho_pp_hash`, `make_hint_44` everywhere and for `signing_key_44`, `hint_step_1_44`,
`response_1x1_44` in the default and `dispatch` profiles; `insecure` for `control_early_exit_44` everywhere and for `control_prepared_branch_44` in
the default and `dispatch` profiles except `secure` on thumbv7em, the sweep's expected-invalid control there; `unknown` for `signing_key_44`,
`hint_step_1_44`, `response_1x1_44` and `control_prepared_branch_44` in the two `nearcore-exact*` profiles, cut at the same VEX instruction as in the
sweep). The instruction and check counts that BINSEC reports (the instructions it visited or unrolled, and the control-flow checks it made) equal the sweep's in 36 of the 40 cells and in all 8
`nearcore-exact` cells; they differ in 4 cells, all in `dispatch` on x86_64 (`signing_key_44` 998423 instructions against the sweep's 1000499,
`make_hint_44` 173 against 154, `hint_step_1_44` 72276 against 75660, `response_1x1_44` 101989 against 102221), the same four cells with the same
counts as in the round 8 smoke run. This document draws no conclusion about the compiled code from these counts: they describe one symbolic
exploration, so equal counts do not show that two binaries are equal and different counts do not show that they differ, and no cause is given for
the four differences. No cell ended `error` or out of memory (the kernel log of the box had no `Killed process` entry). The build matrix (one
cheap probe, `sign_rho_pp_hash`, in the 12 profiles including `zeroize` and `experiments`) gave 30 of 30 cells `secure`, with the pre-set cache
addresses unchanged; the aarch64 builds, the split-run and `exact-novec-zeroize` were not rerun. One cell is not clean: `control_prepared_branch_44`
on riscv32imac, default profile, ended `unknown` in the first run (three targets in parallel, 5400 s timeout, 1 pending path, 2230863
instructions, 108951 of 108951 checks, no leak found in the time) and `insecure` when rerun alone (10800 s timeout, one job): the leak was found at
0.885 s (the sweep: 0.910 s), with 2230914 instructions and 108953 of 108954 checks, the sweep's counts. The two runs ended differently, one at the timeout with a pending path
and no verdict and the other with the intentional leak found, and reported different counts. `unknown` means the analysis did not finish; it is not
a `secure` result, and this cell is `insecure` only because of the rerun. The binaries of the two runs were not compared, so nothing is stated here about whether they were the same, and the
round 8 text that attributed small count differences in this probe to code layout is withdrawn: that attribution was not established. The x86_64 default cell of this probe needed no rerun this time (989292 instructions, 65175 of 65176 checks, equal to the sweep, in
2.25 s). The full sweep was not rerun: no Sign or KeyGen source changed since it. Rows: `checkct/results/smoke-fast-verify/` (`verdicts.tsv`,
`verdicts-nearcore-exact.tsv`, `build-matrix.txt` and the logs of this run; the round 8 files are in git history, c0c62d6 and 40ee0de).

Round 9 (fv-p9: `VerifyScratch`, no `align_frame`, an extraction without axiom declarations) changed no Sign or KeyGen source, and replaced the
smoke run by a function-by-function comparison of the driver binaries of fv-p8 and fv-p9 with addresses and symbol hashes masked. That
comparison is not a BINSEC result: it compares instruction streams after masking, without the lifter, the solver or the flags of the
nearcore profiles, so it does not stand in for a rerun, and the round 10 rerun above is the evidence for this tree. The comparison itself is kept as
`checkct/compare-code.sh` and was repeated for fv-p9 against fv-p10 (default release profile, riscv32imac, thumbv7em and x86_64, each without and with `avx2`):
234, 239 and 234 functions without `avx2` and 234, 239 and 235 with it, every function identical after masking, none added or removed
(`bench/results/2026-11-09-p10.md`); that supports, and is not a substitute for, the statement that the default build's Sign and KeyGen code is unchanged.

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
- **AVX2 and NEON code:** builds with AVX2 target features have no BINSEC verdict for the probes that contain vector code (BINSEC 0.11.3 cannot lift VEX instructions), and the
  4-way verify has no BINSEC coverage at all (verify is public data); AArch64 builds with NEON cannot be lifted, so macOS and Apple Silicon builds have no BINSEC coverage.
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
| 4-way verify (run in the default build and in a build with AVX2 target features, which needs a CPU with AVX2; `ML_DSA_REQUIRE_AVX2=1` turns a missing AVX2 target feature into a failure) | the compiler's translation of proved source (1.9): `tests/keccak4_long.rs` (the permutation against four scalar permutations on more than 150,000 whole states), `tests/fast_verify_x4.rs` (4-way sampler, ExpandA and verify against the scalar functions), `tests/fast_verify_tr.rs`, `tests/fast_verify.rs` (the 4-way verify and the public verify against the scalar verify on ACVP sigVer, Wycheproof verify and random valid, corrupted, wrong-length and random inputs, every API path, all three sets). `tests/verify_arith.rs` (the verify-only NTT, multiply-accumulate row, norm check and w1 packing against the shared functions on corner and random inputs). Last run: see section 0, Round 12 |
| Leaf and API tests | round trips on upstream bytes, naive references, every HintBitUnpack ⊥ case, the verify-only `poly_use_hint_pub` against `poly_use_hint` on every r < q for all three sets and `bit_unpack_pub` against `bit_unpack` on random, zero, all-ones and single-bit inputs for 10, 18 and 20 bits (`tests/leaf.rs`); the portable 4-way Keccak against four scalar permutations (`tests/keccak4.rs`); the branchless 4-way parse on boundary candidates (`src/sampling.rs`, `boundary_tests`); optional key checks against 200 random mutations per set (`tests/sk_well_formed.rs`, `tests/pk_from_sk.rs`); SHAKE KATs (`tests/shake_kat.rs`, `shake_lanes.rs`); dispatch vs portable NTT (`tests/dispatch.rs`) |
| zeroize | `tests/zeroize.rs` scans the stack below `keygen`, `pk_from_sk`, `signing_key`, `sign`, `sign_prepared` and single Sign attempts (rejected early, rejected late, accepted) for residue of K, s1, s2, t0, ρ″, the mask y and the values derived from it (ŷ, Â ∘ ŷ, w, ĉ, ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩, r0, ⟨⟨ct0⟩⟩, and z and c̃ of rejected attempts), and checks the drop wipe; see Z-1 for the optimization-level caveat |
| Rust CI (`scripts/ci.sh`) | tests for default, `zeroize` (all 24 scans in release; the 3 `signing_key` scans at opt-level 0) and `avx2` (the no-op feature, then `RUSTFLAGS="-C target-feature=+avx2"` with `ML_DSA_REQUIRE_AVX2=1`, so a runner without AVX2 fails instead of silently running the 128-bit build); `avx2-inlining` (`scripts/check-avx2-inlining.sh`, a performance check: the 4-way permutation is 256-bit code and the verify frames are 32-byte aligned in the library build under nearcore's flags plus `+avx,+avx2`); thumbv7em; MSRV 1.86; wasm32; nearcore profile on 1.95.0 (fat LTO, overflow checks, panic = abort for the build) incl. zeroize and, with `ML_DSA_REQUIRE_AVX2=1`, AVX2 target features; 60 s fuzz smoke of three targets; the aws-lc differential; `cargo deny`; `extract-hash` and `axiom-gate-selftest` (section 0); on GitHub, also the default and release zeroize suites on macOS arm64 (`ci.yml`, `macos-arm64`) |

### Benchmarks

**Verify, all three sets (round 12).** ML-DSA verify in microseconds, median over 4 passes of 7 rounds, measured on 2026-11-09 by `bench/ab.sh` (interleaved binaries) with the
`nearcore` profile of `bench/Cargo.toml` (opt-level 3, fat LTO, one codegen unit, panic = abort, overflow checks on), on one pinned core of an AMD EPYC 9B14 (Zen 4) at a measured 3.4 GHz,
rustc 1.99.1, no other timing job on the core (the box was not idle: load average about 3). The flags are the point, because nothing at run time chooses
any more: `none` is no target flags (baseline x86-64), `nearcore` is nearcore's x86_64 target features (`+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq`,
no AVX2), `nearcore+avx2` adds `-C target-feature=+avx,+avx2`. `4-way` is `verify_NN` of this tree; `scalar` is the same binary's scalar functions
(`verify::verify_internal`, `prepare_vk`), kept as the reference and not reachable from `api` any more. Raw tables and the method: `bench/results/2026-11-09-p12.md`.

| µs | 44 | 65 | 87 |
|---|---|---|---|
| one-shot, `none`, scalar / 4-way | 75.8 / 76.6 | 122.4 / 115.7 | 202.7 / 190.0 |
| one-shot, `nearcore`, scalar / 4-way | 52.5 / **38.6** | 88.4 / **57.9** | 152.6 / **96.2** |
| one-shot, `nearcore+avx2`, scalar / 4-way | 49.5 / 26.1 | 85.9 / 38.4 | 149.8 / 60.7 |
| `verifying_key_NN`, `nearcore`, scalar / 4-way | 42.1 / 27.4 | 75.2 / 45.0 | 133.1 / 79.5 |
| `verifying_key_NN`, `nearcore+avx2`, scalar / 4-way | 41.8 / 17.9 | 74.1 / 27.6 | 131.9 / 47.0 |
| prepared-key verify, `nearcore` | 12.4 | 14.6 | 20.1 |
| prepared-key verify, `nearcore+avx2` | 9.5 | 10.9 | 15.4 |
| aws-lc-rs 1.18.2 (from `bench/results/2026-11-07-p7.md`, same machine and toolchain) | 22.5 | 36.4 | 56.6 |
| mldsa-native v2.0.0, AVX2 (same source) | 20.9 | 34.3 | 53.3 |

What it shows, for these builds and this machine. **Under nearcore's current flags fast verify runs at 38.6 / 57.9 / 96.2 µs** (0.73, 0.66 and 0.63 of the scalar time); the 26.1 / 38.4 / 60.7 µs
figures need `+avx2` target features, which nearcore's flags do not have, and a binary built with them runs only on a CPU with AVX2. This document does not claim
that nearcore's feature floor guarantees AVX2. On baseline x86-64 the 4-way verify is 1.2 % slower for ML-DSA-44 and 5 to 6 % faster for 65 and 87; on aarch64 (NEON baseline) it is 42 to 61 % faster than scalar with no flags.
With AVX2 target features it is at parity with the run-time dispatch of fv-p11 (1a8d3e2) under nearcore's flags (one-shot 26.05 / 38.46 / 60.67 against 26.10 / 38.36 / 60.74 µs; `verifying_key_44` was 5.9 % slower in
that run, which was of the tree without the inline attribute (a0292a3); the final tree's median is 16.80 µs in the stack scan, with `+avx,+avx2`, `bench/results/2026-11-09-p12.md`). Prepared-key verify runs no ExpandA; it is the same scalar function
in every build. An uncached verify with AVX2 target features is 1.06 to 1.16 times aws-lc-rs's.
**The stack offset does not matter** (`bench/stackscan.sh`, a scan of 257 environment paddings, run by `bench/fast-verify.sh`): the largest padding is within the 1.1 times the median that the scan
tolerates (`STACK SCAN OK` in four of five scans of this tree, nearcore flags with and without `+avx,+avx2`, sets 44, 65, 87, `OPS=verify,vk,prepared`; the table of the last scan of each build has 0 of 257 paddings above 1.1 times the median in all nine cells, the largest padding at 1.033 times the median; the fifth scan, the first run after the build, had one outlier at padding 0, 32.6 µs against a median of 25.6 for ML-DSA-44 `verify`, which did not recur in the four reruns) The cause of the old effect was LLVM spilling 256-bit vectors to 16-byte aligned slots, so that a slot straddling a 4 KiB page made each access a page split
(`bench/results/2026-11-07-p6.md`); the `#[repr(align(32))]` objects the proved code computes in realign the frames in a build with AVX2 target features.
Earlier rounds measured the dispatched wrappers of fv-p5 to fv-p11 (`bench/results/2026-11-07-p3.md` to `2026-11-09-p11.md`); those tables describe code that no longer exists and are not repeated here. Not measured: wasm32, Intel and other AMD parts; one key pair per set, hot caches. Reproduce with
`bench/ab.sh` and `bench/fast-verify.sh` ([reproduce.md](reproduce.md)).

**Sign and KeyGen, round 12.** The NTT dispatch of 0.1.0's `avx2` feature is gone. Microseconds, median of 3 runs of 7 rounds, `bench/ab.sh` on the same core, ML-DSA-44 / 65 / 87; `old` is fv-p11 built with
nearcore's flags and `--features avx2` (the dispatch is live on this machine), `new` is this tree:

| µs | 44 | 65 | 87 |
|---|---|---|---|
| keygen, nearcore flags, old / new | 65.6 / 69.2 | 140.2 / 145.7 | 186.7 / 191.0 |
| sign (hedged), nearcore flags, old / new | 216.5 / 247.6 | 342.9 / 402.6 | 416.1 / 472.1 |
| keygen, `nearcore+avx2`, old / new | 63.5 / 63.6 | 136.2 / 137.6 | 183.8 / 180.2 |
| sign (hedged), `nearcore+avx2`, old / new | 214.0 / 215.1 | 342.2 / 341.0 | 408.3 / 404.1 |

For a user of the old `avx2` feature on a build without AVX2 target features, Sign is 14 to 17 % slower and KeyGen 2 to 6 % slower now; with AVX2 target features there is no difference beyond
noise (-1.9 to +1.1 %). A user who never enabled the feature ran the portable NTT before and after. The earlier table of 2026-10-31 (ML-DSA-87: keygen 229 / 193 / 180 µs, deterministic sign 714 / 466 / 429 µs, prepared sign 543 / 312 / 285 µs for the
default build, the `avx2` feature and `-C target-cpu=x86-64-v3`, rustc 1.99.1, `bench/compare.sh`) describes 0.1.0; its `avx2` column no longer exists. Uncached ML-DSA-87 sign on that run, for comparison: libcrux AVX2 219,
mldsa-native AVX2 122. The C libraries were built with gcc 13.3 `-O3` and no LTO. Not measured: aarch64 Sign and KeyGen, wasm32, Intel. Reproduce with `bench/build.sh`, `bench/run.sh` and `bench/compare.sh` ([reproduce.md](reproduce.md)).

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
- **FV-1 (closed in round 12; history).** Until round 12 the AVX2 fast verify was proved at source level while the run-time CPU check, its 15 call lines, three `unsafe` calls and the compilation of
  the `#[target_feature]` wrappers were trusted. The dispatch is gone: verify runs the 4-way body in every build, proved equal to the scalar verify (1.9), and what remains outside the proof is the ordinary compiler trust
  of section 2, item 3. A binary built with AVX2 target features requires a CPU with AVX2; nothing is detected at run time, so SGX enclaves (where CPUID faults) are no longer a special case. No BINSEC verdict
  applies to verify (public data; BINSEC 0.11.3 cannot lift AVX2).
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
  120 GB is recorded as "needs more than 120 GB". Whole-Sign censuses on thumbv7em and riscv32imac, and the x86_64 default prepared census
  (and, until round 12, the `dispatch` one), have no verdict for this reason (not rerun at 1a72d9e). No entrypoint probe of the sweep at 1a72d9e
  ended `error`.
- **Other CT unknowns:** riscv32imac `vec_power2round_87` and one census; the three `split_vec_power2round_{5,6,7}` capacity probes;
  riscv32imac `prepare_sk_{44,65,87}` (solver stall at a store in `ntt_body_mut`, cause not pinned down; they were `secure` at
  15b4ce2, and the same driver on the 15b4ce2 source is `secure`, so the stall comes from the Sign change; `signing_key_*`,
  `prepare_sk_1x1_*` and every `split_prepare_sk_*` piece are `secure`); eleven AArch64
  probes (and two split pieces, `split_prepare_sk_87_{7x1,col}`: thirteen rows in all) stuck in one solver query. AArch64 `prepare_sk_87`/`signing_key_87` are covered only stage by stage (skDecode, then the
  in-place NTT of 8 polynomials, both secure); the K = 8 glue has no single verdict. Split pieces are separate monomorphizations,
  so that argument is about the source, not the full-size machine code. AArch64 NEON builds
  and vectorized x86_64 builds (AVX2 target features, nearcore's `+fma` with vectorizers on) cannot be lifted.
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
8. No `#[target_feature]` function and no `unsafe` (since round 12): a build that wants AVX2 code gets it from `-C target-feature=+avx2`, and the extraction is the same under both
   (`scripts/check-feature-independence.sh`). `#[repr(align(32))]` on `PreparedVk` and `VerifyScratch` is ignored by Aeneas and changes no value.
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
| `ntt.rs` | Alg 41 NTT, Alg 42 NTT⁻¹, Alg 44–48 (AddNTT … MatrixVectorNTT); the zeta table is a literal that Lean checks against ζ^BitRev8(k); one portable body per function (LLVM vectorizes it with the build's target features) |
| `field.rs` | arithmetic in Z_q (reduction is Barrett/Montgomery; FIPS 204 allows any equivalent reduction; Alg 49 is not used), mask helpers |
| `keccak.rs` | FIPS 202 Keccak-f[1600], SHAKE128/256 |
| `keccak4.rs` | four Keccak-f[1600] permutations at once, plain Rust (a loop over the four states) |
| `keccak4.rs`, `verify.rs` (`verify_internal_x4`, `prepare_vk_into_x4`) | no FIPS algorithm: the 4-way Keccak-f[1600], SHAKE128 and ExpandA, and the Verify_internal and `prepare_vk` built on them, proved equal to the scalar ones (1.9) |

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
| 4-way verify tests | `cargo test`, and `RUSTFLAGS="-C target-feature=+avx2" ML_DSA_REQUIRE_AVX2=1 cargo test` on an AVX2 machine |
| 4-way permutation is 256-bit code with AVX2 target features (performance) | `bash scripts/check-avx2-inlining.sh` |
| Feature independence of the extraction | `bash scripts/check-feature-independence.sh` |
| Performance | `bench/compare.sh` (keygen, sign), `bench/fast-verify.sh` (verify) |

## 12. Wording that stays inside the evidence

Safe: "the extracted Rust for every `api` function is proved, with no premises, to never fail (in the Aeneas model: stack
exhaustion and out-of-memory are not modeled, and the Rust can diverge exactly when the spec returns no result at any
fuel, §1.2) and to agree with the Lean transcription of FIPS 204 whenever either returns (`*_exact`), with the trusted
base in §2"; "constant time is checked by BINSEC on compiled probes for the builds and targets in §4". Not supported:
"formally verified" without that scope; "constant time" for whole-Sign; any statement about aws-lc equivalence; "FIPS validated"
or "FIPS certified"; "first" or "only"; "production-ready" or "audited".

For verify: "`verify_NN` runs a 4-way body that is proved, as source, to compute what the scalar Verify computes, and the extraction does not depend on the target features of the build; the crate has no `unsafe` and detects nothing
at run time. What stays outside the proof is the ordinary compiler trust: rustc and LLVM compiling the proved source for the target features of the build (tested against the scalar functions in the default build and
in a build with AVX2 target features, not proved)." Not supported: "the compiled AVX2 code is proved equal to the portable build's"; any statement that nearcore's feature floor guarantees AVX2; a
constant-time statement about verify or about builds with AVX2 target features; "no assumptions" (section 2 lists the base).

The Lean theorems are about source semantics, not object code, and the agreement of Verify verdicts across nodes and builds is a
consensus property that §1.1 gives only for code with the semantics of the extracted source. The compilation of the verify functions, in the default build and in a build with AVX2 target
features, is tested equal to the scalar functions (`tests/fast_verify.rs`, `tests/fast_verify_x4.rs`, `tests/keccak4_long.rs`), not proved; §2, items 2 and 3 are the exact residual. The nearcore-profile test run in
`scripts/ci.sh` (`nearcore-test`, overflow checks on) is an empirical check of the compiled code, not a proof.
