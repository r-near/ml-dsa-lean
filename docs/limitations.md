# Scope and limitations

The README states the result in one line. This page is exactly what that line covers and what it doesn't. The complete
version, with the exact theorem statements, the trusted base and the evidence for every claim, is
[assurance.md](assurance.md). nearcore, which the constant-time notes below use as a build profile, is only an
integration target studied here ([nearcore-integration.md](nearcore-integration.md); no affiliation).

## What the proof says

For every parameter set and every value of the argument types of `api::keygen_NN`, `api::sign_NN`, `api::verify_NN`,
their `_internal` variants and `api::pk_from_sk_NN`, and with no unproved premises, the extracted Rust code:

- never fails in the Aeneas model (no panic, arithmetic overflow or out-of-bounds access), and
- returns exactly what the Lean transcription of FIPS 204 returns, whenever either returns a result. The Rust can diverge
  exactly when the specification's rejection samplers never terminate on that input, which the proofs characterize but do not
  rule out. `sign_NN` returns `None` exactly for a context longer than 255 bytes or when the specification's bounded
  attempt loop (κ + ℓ ≤ 2¹⁶) is exhausted.

This is partial correctness plus absence of panics. For honestly generated keys, a separate theorem shows that Verify
accepts what Sign produces (its premises are named in [assurance.md](assurance.md)). The prepared-key functions are proved
equal to the one-shot ones. The theorems are checked with only the standard Lean axioms (`propext`, `Classical.choice`,
`Quot.sound`). `scripts/witness-check.sh` kernel-checks instances showing the premises are satisfiable, for one ML-DSA-44
input.

## What the proof does not say

- **It is about the Rust source as modeled by Aeneas.** Stack exhaustion, out-of-memory, rustc and LLVM, and the instruction
  set are trusted.
- **Extraction runs with `--cfg miri`**, so the proved code is the source with its `cfg(miri)` variants: the `black_box`
  barriers (`field::opaque_u32` and the RISC-V mask barrier) are the identity there (none is on a verify path). Nothing else differs:
  the crate has no `unsafe`, no CPU detection and no `cfg` that selects code by CPU feature, and the extraction is the same under every target feature
  ([assurance.md](assurance.md) sections 1.9 and 2).
- **The specification is trusted.** `lean/Spec` is our transcription of FIPS 204; the standard itself is not formalized. It
  has been cross-checked against test vectors and against ocaml-pq's independent transcription (proved equal in `xspec/`,
  with the qualifiers in [assurance.md](assurance.md) section 1.8: their Sign loop stops after 821 attempts, their key import
  rejects inconsistent keys that FIPS 204 accepts, and some directions assume their rejection samplers terminate).
- **The `zeroize` feature is outside the proof.**
- **Verify runs a 4-way body in every build, and rustc/LLVM compile it.** `verify_NN`, `verify_internal_NN` and `verifying_key_NN` call a 4-way body (4-way
  Keccak-f[1600], SHAKE128 and ExpandA, with `tr = H(pk, 64)` hashed in a spare lane); the prepared-key verify runs the scalar function. Lean proves the 4-way body equal to the
  scalar verify on every input, divergence included, and the public functions call it directly
  (`lean/fast-verify-theorems.txt`, [assurance.md](assurance.md) section 1.9). The crate has no `unsafe`, no `#[target_feature]` function and no
  run-time CPU detection (`#![forbid(unsafe_code)]` in every configuration); the Cargo feature `avx2` is a deprecated no-op. What is outside the proof is what is outside it for
  the rest of the crate: the compilation of the proved source by rustc and LLVM for the target features of the build. That the compiler turns the 4-way Keccak loop into 256-bit code
  with `-C target-feature=+avx2`, and aligns the stack frames, is a performance property (`scripts/check-avx2-inlining.sh`), not a premise. **The AVX2 speed needs AVX2
  target features at compile time**: under nearcore's current flags (no AVX2) the 4-way verify takes 38.6 / 57.9 / 96.2 µs for ML-DSA-44 / 65 / 87 and 26.1 / 38.4 / 60.7 µs with
  `+avx,+avx2` added, and a binary built with them runs only on a CPU with AVX2. nearcore's feature floor is not claimed to guarantee AVX2.
  The 4-way verify uses more stack than the scalar one did (`verify_NN` 56 / 80 / 118 KB, `verifying_key_NN` 50 / 73 / 108 KB; [assurance.md](assurance.md) section 3).
  The AVX2 NTT dispatch that 0.1.0's `avx2` feature gave Sign and KeyGen is gone: a user of that feature who builds without AVX2 target features signs 14 to 17 % and generates keys 2 to 6 % slower.
- **HashML-DSA and external μ are not implemented.**
- **Constant time is not proved.** It is checked on compiled code with BINSEC (next section).
- **Not audited by any third party, not FIPS-validated, and not a certified module.**

## Constant time

BINSEC checks compiled probes of every secret-touching step of KeyGen and Sign (listed in `../checkct/README.md`), on x86_64
(several build profiles), thumbv7em, riscv32imac and AArch64 without NEON. No unexpected leak is open; three real ones were
found and fixed. The limits:

- Verify, including the 4-way verify, handles only public data (public key, message, signature), so it has no probes and
  needs none. Sign and KeyGen do not call the 4-way body or the verify-only `poly_use_hint_pub` and `bit_unpack_pub`. The
  full sweep predates the fast verify and the removal of the NTT dispatch and was not rerun on this tree: removing the dispatch changes the compiled NTT
  callers of Sign and KeyGen in the default build (39 of 233 functions on x86_64), so the sweep's verdicts are for an earlier binary. The harness
  (`../checkct/driver`) builds on this tree for every target and profile, and a BINSEC run on this tree reproduced the sweep's verdicts for the probes it covered
  (assurance.md section 4, "Round 12").
- The whole KeyGen, Sign and `pk_from_sk` functions have no verdict, and the glue between steps is covered by code reading
  only. ExpandS is covered only through its per-nibble helper; its sampler loop branches on its public accept/reject
  outcome.
- BINSEC 0.11.3 cannot lift AVX/VEX instructions. Under nearcore's exact release build (`nearcore-exact`, where `+fma`
  implies AVX), 49 of 113 probes and both Sign censuses have no verdict (61 secure / 3 expected insecure / 0 unexpected /
  51 unknown, including the NTT, `hint_step`, `response`, `compute_t`, `prepare_sk` and `signing_key`). The same flags with
  the vectorizers off get a verdict for every probe, but that is a different binary.
- AArch64 builds with NEON, and therefore macOS and Apple Silicon builds, have no BINSEC coverage.
- Some probes on other targets (riscv32imac `prepare_sk_*`, AArch64 `prepare_sk_*` and `signing_key_*`) and the whole-Sign
  censuses have no verdict.

Per-target counts: [assurance.md](assurance.md) section 4 and `../checkct/README.md`.

## Testing

Tests are evidence, not proofs.

- **Differential tests** against RustCrypto `ml-dsa`, `aws-lc-rs` (0 verdict differences in about 3.2M verify comparisons;
  empty context only), libcrux-ml-dsa and mldsa-native (`../crosscheck/`).
- **4-way verify** (run in the default build and in a build with AVX2 target features, which needs a CPU with AVX2): the permutation against four scalar
  permutations (`../tests/keccak4_long.rs`); the 4-way sampler, ExpandA and verify against the scalar functions (`../tests/fast_verify_x4.rs`,
  `../tests/fast_verify_tr.rs`); the public verify against the scalar verify on ACVP, Wycheproof and random inputs through every API path (`../tests/fast_verify.rs`).
- **Test vectors:** NIST ACVP (keyGen, sigGen, sigVer; the preHash and external-μ cases are skipped) and Wycheproof.
- **Fuzzing:** differential fuzz targets against RustCrypto (`../fuzz/`) and the other implementations.

## Known limitations

The full list is [assurance.md](assurance.md) section 7.

- **`zeroize`:** stack-residue wiping holds for optimized builds (release). The stack-residue scans fail at opt-level 0, except
  `signing_key_*`, and `keygen_44`/`keygen_65` fail at opt-level 1 on Linux (Z-1, open). Sign wipes the mask y and the other
  per-attempt secrets on every exit of an attempt (`src/api.rs` module docs). Not wiped by design: moves of returned
  structs, the signature (z, c̃, h of the accepted attempt), one copy of K and t0 in KeyGen, and anything skipped by a panic
  or `mem::forget`.
- **Malformed secret keys:** expanded secret keys with out-of-range coefficients are accepted by `sign_NN`, as FIPS 204
  specifies. Use `sk_is_well_formed_NN` (or `pk_from_sk_NN`) on untrusted keys (E-4).
- **`internals` feature:** the crate-private internals it exposes are meant for tests and can panic on wrong-length slices.
- **Stack use** is measured, not proved: Sign needs up to about 240 KB for ML-DSA-87, one-shot verify about 118 KB (`../tools/stack/README.md`).
- **Secret keys** are the 2560/4032/4896-byte expanded encoding, not the 32-byte seed.
