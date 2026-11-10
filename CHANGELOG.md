# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.2.0](https://github.com/r-near/ml-dsa-lean/compare/v0.1.0...v0.2.0) - 2026-11-10

### Other

- Round 13 entry (code identity, stack decision, 32-bit counts, gates, BINSEC sweep and censuses), limitations, README, CHANGELOG, reproduce
- replace the stale prepare_vk doc comments (100 KB / 83 KB, 132 KB / 115 KB) with a description of the current design; re-extract (line-number comments only)
- restore the plain dispatch wrapper module of round 11 (no choice inside); default-build object code is identical to fv-p11 again
- stack figures and stack-offset scan for the inline-always tree
- keep the verify chain #[inline(always)] so frames stay 32-byte aligned; check-avx2-inlining checks the nine public functions; re-extract (line numbers)
- README speed claims state their build flags; CHANGELOG as the net change; limitations, nearcore-integration, reproduce, object-code-assurance, checkct README for round 12; bench results of the round; stackscan builds with target features
- documentation of the always-4-way verify, stack figures, no dispatch left in comments; re-extract (comments only)
- remove the NTT AVX2 dispatch: the crate has no unsafe and no run-time detection
- always call the 4-way code; delete the run-time AVX2 dispatch
- unsafe calls now in fast_verify/dispatch.rs; reproduce.md and CHANGELOG describe the new gates
- README theorem counts checked against the lists (108 was 88, now 111 with NoDispatch); ci.sh and lean-check.sh run the new gates
- cpu.rs and lib.rs docs for the one-text dispatch; Cargo.toml avx2 comment rewritten for the current design; lean/Impl re-extracted
- one _with text in every build; Avx2 is uninhabited without the dispatch
- the AVX2 residual and the CPU-detection assumption stated the same way everywhere; README and changelog for round 9
- run the row loop on a borrow of the scratch's w1 field
- src, docs: a false AVX2 report is undefined behavior, not a crash; precise unsafe-call wording in fast_verify.rs
- an aligned scratch owned by verify_core replaces the black_box align_frame anchor
- keep a value-free align_frame() in verify_prepared_avx2 (empty under extraction); the prepared-key verify is 2-8% slower without it
- the 4-way Keccak is plain proved Rust and the AVX2 dispatch is extracted and proved; list what stays outside the proof
- extracted *_with functions take an Avx2 token; api::*_with carry the flag; drop align_frame and the test hooks in dispatch.rs
- module docs
- round25 (one scalar round on [u64; 25]) called twice per lane iteration; generator --check; lab: reference copy, q variant
- allow clippy::manual_rotate on the generated body
- plain-Rust 4-way kernel (loop over the four states around a straight-line two-round body); remove Lanes4, Shim4 and the AVX2 intrinsics
- also run the tr-lane ExpandA over Avx2, through a checked internals-only wrapper (re-extracted: digest only)
- p7 results (tr in the fourth lane of the 4-way ExpandA), assurance 1.9 and benchmarks, nearcore-integration 6, changelog
- compute tr = H(pk, 64) in the fourth lane of the first 4-way ExpandA groups
- allow dead_code on the never-read anchor of align_frame (inputs digest only)
- build the prepared key in place in prepare_vk_avx2 (verifying_key_87: 69.6 us at every stack offset after the realignment, 52.0 now)
- realign every AVX2 wrapper's stack frame to 32 bytes (page-split spills made verify up to 12 us slower at some stack offsets)
- checkct driver: include the real src/fast_verify.rs instead of repeating its re-export list
- second AVX2 wrapper for the prepared-key verify (verify_prepared_avx2)
- bit_pack_pub_spec is in Proofs/VerifyArith.lean, not Proofs/Encode.lean; re-extract (only the extraction-input digest moves)
- fixed-width w1Encode (bit_pack_pub, w1_encode_pub)
- lazy-reduction NTT and NTT^-1 (ntt_pub, ntt_inverse_pub, ntt_vec_pub)
- fused multiply-accumulate row for w'_Approx (mac_row_pub)
- z norm check without constant-time masks (vec_norm_lt_pub)
- Fix stale comments: bit_unpack_pub theorem names, Shim4 description, avx2 feature note, spike-b references
- state the avx2 fast verify's proof status in the README and limitations
- bit_unpack_pub, fixed-width unpacking of t1 (10 bits) and z (18, 20 bits) for pkDecode and sigDecode
- parse the 4-way rejection candidates straight from the Keccak lanes (eight per three lanes), no byte buffer
- build each round's output row by row into a second buffer (ping-pong), 24 rounds as 12 double rounds
- UseHint with plain arithmetic (public data), multiply-shift HighBits, vectorizable; verify_core/decoded inline into the AVX2 body
- deterministic boundary tests for the branchless 4-way rejection parse
- parse the 4-way SHAKE128 blocks branchlessly from a byte buffer, and prove it
- make the AVX2 lane operations crate-private; tests reach them through checked wrappers
- keccak_f1600_x4_avx2 is test and bench only; say so instead of warning
- narrow dead_code to Shim4 and keccak_f1600_x4_portable, with a reason
- replace the line-padding comment with a short note on the dispatch contract
- dispatch to the proved verify_internal_x4 and prepare_vk_x4; delete the stand-in
- x4 entry points: generic order <K, L, X> (const generics first), as the dispatch calls them
- build the lane-4 words from literals and a constant shift, re-extract
- describe the avx2 feature's verify dispatch (Cargo.toml, README); fast_verify.rs states the proof as the target; bench: TOOLCHAIN option
- Extract the 4-way ExpandA and verify body (new roots); unroll the rho loads, loop on a flag
- 4-way ExpandA and verify body generic over Lanes4, with shim differential tests
- fast-verify.sh (scalar vs dispatched verify under nearcore's flags); scripts: check-avx2-inlining.sh; stub: inline the prepare functions into the AVX2 wrapper
- keep the extracted Lean byte-identical (one-line api import, fast_verify.rs always present, ntt.rs line numbers unchanged)
- one cached CPU detector (cpu.rs) and a run-time dispatcher for verify and prepare_vk
- document the AVX2 entry point's safety requirement; tests: allow needless_range_loop; refresh extract-report digest
- 4-way Keccak-f1600 kernel generic over a Lanes4 trait, shim impl extracted

This section is the net change since 0.1.0. The branch went through a run-time AVX2 dispatch for verify on the way (rounds 1 to 11 of
`docs/assurance.md`, section 0); the last round removed it, so none of it ships.

### Added

- `verify_NN`, `verify_internal_NN` and `verifying_key_NN` run a 4-way body (4-way Keccak-f[1600], SHAKE128 and ExpandA, with `tr = H(pk, 64)` in the spare
  fourth lane of the first groups) in every build. It is plain Rust, proved equal to the scalar verify on every input, divergence included, in Lean
  (`docs/assurance.md` section 1.9, `lean/keccak4-theorems.txt`, `lean/fast-verify-theorems.txt`); nothing selects it at run time and nothing is
  `cfg`'d: the public functions call it directly. One-shot verify for ML-DSA-44 / 65 / 87 takes 38.6 / 57.9 / 96.2 µs under nearcore's current flags (no AVX2) against
  52.5 / 88.4 / 152.6 µs for the scalar functions, and 26.1 / 38.4 / 60.7 µs with `-C target-feature=+avx,+avx2` added (AMD EPYC 9B14, rustc 1.99.1;
  `bench/results/2026-11-09-p12.md`). **The AVX2 numbers need AVX2 target features at compile time**; a binary built that way runs only on a CPU with AVX2.
- Verify-only arithmetic on public data (`src/verify_arith.rs`, `rounding::poly_use_hint_pub`, `rounding::vec_norm_lt_pub`, `encode::bit_unpack_pub`,
  `encode::bit_pack_pub`): a lazy-reduction NTT and NTT⁻¹, one fused multiply-accumulate row for Â ∘ NTT(z) − NTT(c) ∘ NTT(t₁·2^d), UseHint and the unpacking of
  t1 and z in plain arithmetic, a norm check without constant-time masks and a fixed-width w1Encode, each proved equal to the specification
  (`Proofs/NTTPub.lean`, `Proofs/VerifyArith.lean`; 5 more names in `lean/headline-theorems.txt`, 412 in all). Signing and key generation are unchanged by it.
  `tests/verify_arith.rs` compares each function with its shared counterpart.
- Lean theorems for the 4-way verify: 6 names in `lean/keccak4-theorems.txt` and 79 in `lean/fast-verify-theorems.txt`, gated by `scripts/lean-check.sh`. The 4-way Keccak
  has no trait, no lane operation and no intrinsic: `keccak_f1600_x4` is a loop over four states around a straight-line scalar round, which LLVM vectorizes
  (256-bit with AVX2 target features, 128-bit without).
- Gates: `scripts/check-feature-independence.sh` extracts the crate twice, as it is and with `-C target-feature=+avx,+avx2`, and requires `lean/Impl` to be
  byte-identical (the whitelist is empty; it cannot pass vacuously: a probe crate shows that the second extraction really had the target feature, and the recorded
  flags must differ); a census of every `cfg` site in `src/` (`scripts/cfg_inventory.py`, token-aware, covering `cfg_if!`, `env!`, `include!`,
  `is_*_feature_detected!`, `#[path]`, `macro_rules!` and build scripts) against `scripts/cfg-inventory.txt`; a walk of the Lean environment from the verify entry points
  (`scripts/reachable-defs.sh`); `scripts/check-no-decls.sh` (no `axiom`, `opaque`, `sorry`, `admit`, `native_decide`, `implemented_by` or `extern` in `lean/Impl`,
  `lean/Spec` or `lean/Proofs`, with a self-test); a check of the theorem counts in the README; `scripts/ci-selftest.sh`; and `checkct/compare_code.py` rejects empty
  or truncated disassemblies. `scripts/check-avx2-inlining.sh` and `bench/fast-verify.sh` check performance only (256-bit permutation code, 32-byte aligned verify frames, a
  stack-offset scan `bench/stackscan.sh`).
- `verify_core` computes w′1 and its encoding in a `#[repr(align(32))]` `VerifyScratch` that it owns, which gives the functions that inline it a 32-byte aligned stack
  frame from an object the proved code uses (no code exists only in the compiled build).
- Extraction no longer leaves unreferenced `axiom` declarations in `lean/Impl/FunsExternal.lean` (`scripts/extract_hash.py` `clean_external`, with a self-test).

### Changed

- **The crate has no `unsafe` and detects nothing at run time.** `#![forbid(unsafe_code)]` holds in every configuration, `src/cpu.rs` and the NTT's AVX2 dispatch
  (`#[target_feature]` copies and a cached CPUID check, the `avx2` feature of 0.1.0) are gone, and `src/api.rs` has no token-passing call lines. The Cargo feature `avx2`
  stays as a deprecated no-op so that `features = ["avx2"]` still resolves; to get AVX2 code build with `-C target-feature=+avx2` or `-C target-cpu=x86-64-v3`.
  The residual of the proofs for verify is the base shared with 0.1.0 (the spec transcription, Charon/Aeneas, rustc/LLVM, the Lean kernel and the hardware): the CPU
  detection and its assumption, the 15 call lines and the 3 `unsafe` calls no longer exist.
- **Cost for users of the 0.1.0 `avx2` feature** (`bench/results/2026-11-09-p12.md`): with nearcore's flags and no AVX2 target features, Sign is 14 to 17 % slower
  (ML-DSA-65 hedged 342.9 → 402.6 µs) and KeyGen 2 to 6 % slower (ML-DSA-65 140.2 → 145.7 µs), because the AVX2 copy of the NTT is gone. With `+avx2` target features
  there is no difference beyond noise (-1.9 % to +1.1 %). Users who did not enable the feature see no change in Sign or KeyGen speed.
- The one-shot verify and `verifying_key_NN` use more stack: `verify_NN` 64 / 90 / 132 KB (was 45 / 71 / 111) and `verifying_key_NN` 50 / 74 / 111 KB (was 35 / 58 / 35);
  the ML-DSA-87 `verifying_key` figure includes a second copy of the key that the compiler does not elide (`bench/results/2026-11-09-p12.md`).
- The NTT entry points (`ntt`, `ntt_in_place`, `ntt_inverse`, `ntt_inverse_in_place`, `multiply_ntt`) call their one body through the plain, safe module `ntt::dispatch`, which
  holds no choice. The module costs nothing at run time; it is kept because it decides how the bodies are inlined into Sign and KeyGen, and with it the machine code that
  BINSEC analyzed: with the module the default-build driver of `checkct/` is identical, function by function (address-masked disassembly, `checkct/compare-code.sh`),
  to the one of the tree that had the dispatch (234, 239 and 234 functions on riscv32imac, thumbv7em and x86_64); without it 185 of 233, 107 of 236 and 39 of 233 functions differed.
- Stack of verify (`bench/results/2026-11-09-p13.md`): the figures above are unchanged. Variants that split the inlined chain into frames came within 4 to 10 KB of the old
  stack under fat LTO but made some stack offsets slow in a build with `+avx2` and in one with nearcore's flags, so the one-frame design stays. Painted in a release build with
  fat LTO, `verify_NN` takes 63.0 / 89.7 / 130.6 KB, the static walk; the 259 / 313 / 399 KB quoted for it in earlier notes were the dev-profile figures.
- On 32-bit targets the 4-way verify executes 17 to 23 % fewer instructions than the scalar one (Cortex-M4 and riscv32imac, instruction counts under an emulator,
  `bench/emu/`), so there is no compile-time selector.
- The checkct driver includes the real `src/api.rs`; its `avx2` feature and the `dispatch` BINSEC profiles are gone.
- Round 14 (nothing under `src/` or `lean/` changes): the cfg inventory records a digest of every cfg-selected body, so editing a `cfg(not(miri))` body fails it; the stack guidance is recomputed from a fresh `tools/stack` run (one-shot `verify_44` leaves about 1.3 KB of a 64 KiB stack; `verify_prepared_*` leaves 16 to 34 KB) and the stale 0.1.0-era tables are replaced.

## [0.1.0] - 2026-11-06

Initial release.

- Formally verified ML-DSA-44/65/87 key generation, signing and verification, proved in Lean to never panic and to match FIPS 204.
