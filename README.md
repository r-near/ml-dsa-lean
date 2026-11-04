# ml-dsa-lean

An ML-DSA (FIPS 204) implementation in Rust with a machine-checked Lean proof that its public API computes exactly what a
Lean transcription of the standard's algorithms computes (partial correctness plus absence of panics); the transcription
is trusted, see "What this does not say" below. The Rust is written so that Charon and Aeneas can extract it to Lean: one
function per FIPS 204 algorithm, plain loops over native arrays, `no_std`, no allocation, no dependencies (the optional
`zeroize` feature adds one). Extraction runs with `--cfg miri`, so the proved code is the source with its `cfg(miri)` variants:
the `black_box` barriers (`field::opaque_u32` and the RISC-V mask barrier) are the identity there, and the AVX2 dispatch is
absent. Those are not in the proved code (`docs/assurance.md` section 2). It supports ML-DSA-44, ML-DSA-65 and ML-DSA-87.

Version 0.1.0. **Not audited by any third party, not FIPS-validated, and not a certified module.** An independent personal
project; not affiliated with or endorsed by NEAR or any employer. [nearcore](https://github.com/near/nearcore) appears
only as an integration target that was studied (`docs/nearcore-integration.md`).

## What is proved

For every parameter set and every value of the argument types of `api::keygen_NN`, `api::sign_NN`, `api::verify_NN`,
their `_internal` variants and `api::pk_from_sk_NN`, and with no unproved premises, the extracted Rust code:

- never fails in the Aeneas model (no panic, arithmetic overflow or out-of-bounds access), and
- returns exactly what the Lean transcription of FIPS 204 returns, whenever either returns a result. The Rust can diverge
  exactly when the specification's rejection samplers never terminate on that input, which the proofs characterize but do not
  rule out. `sign_NN` returns `None` exactly for a context longer than 255 bytes or when the specification's bounded
  attempt loop (κ + ℓ ≤ 2¹⁶) is exhausted.

For honestly generated keys, a separate theorem shows that Verify accepts what Sign produces (its premises are named in
`docs/assurance.md`). The prepared-key functions are proved equal to the one-shot ones. The theorems are checked with only
the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

**What this does not say.** The proof is about the Rust *source* as modeled by Aeneas: stack exhaustion, out-of-memory,
rustc and LLVM, and the instruction set are trusted. The specification (`lean/Spec`) is our transcription of FIPS 204 and is
trusted; it has been cross-checked against test vectors and against ocaml-pq's independent transcription (proved equal, with
the qualifiers in `docs/assurance.md` section 1.8: their Sign loop stops after 821 attempts, their key import rejects
inconsistent keys that FIPS 204 accepts, and some directions assume their rejection samplers terminate), but the standard
itself is not formalized. The `zeroize` and `avx2` features are outside the proof. HashML-DSA and external μ
are not implemented. Constant time is **not** proved: it is checked on compiled code with BINSEC (below). The exact scope,
the trusted base and the list of what is not covered are in [docs/assurance.md](docs/assurance.md); please read it before
relying on any claim here.

## Usage

```rust
use ml_dsa_lean::api::{keygen_65, sign_65, verify_65};

fn main() {
    // The caller supplies all randomness: a 32-byte seed for key generation and 32 bytes for signing
    // (32 zero bytes make signing deterministic). Use a cryptographically secure generator in real code;
    // the all-zero values here are for the example only.
    let seed = [0u8; 32];
    let rnd = [0u8; 32];

    let (pk, sk) = keygen_65(&seed);

    // `ctx` is the FIPS 204 context string (at most 255 bytes); `sign_65` returns `None` if it is longer.
    let ctx = b"example";
    let sig = sign_65(&sk, b"message", ctx, &rnd).expect("context string is at most 255 bytes");

    assert!(verify_65(&pk, b"message", ctx, &sig));
    assert!(!verify_65(&pk, b"another message", ctx, &sig));
}
```

`tests/readme_example.rs` runs this example and fails if the block above changes without it. The API is stateless free
functions on fixed-size arrays, three sets (`_44`, `_65`, `_87`), sizes in bytes:

| Set | public key | secret key (expanded) | signature |
|---|---|---|---|
| ML-DSA-44 | 1312 | 2560 | 2420 |
| ML-DSA-65 | 1952 | 4032 | 3309 |
| ML-DSA-87 | 2592 | 4896 | 4627 |

Prepared keys (`verifying_key_NN` with `verify_prepared_NN`, `signing_key_NN` with `sign_prepared_NN`) cache the expanded
matrix and NTT forms for repeated use with one key. `sk_is_well_formed_NN` and `pk_from_sk_NN` are optional checks on
untrusted expanded secret keys; `sign_NN` itself follows FIPS 204 and does not call them (E-4 in
[docs/assurance.md](docs/assurance.md)). Module docs in `src/api.rs` have the details.

Features:

- `zeroize` (off by default): wipes the secret material the library handles. Stack-residue wiping holds for optimized builds
  only; the stack-residue scans fail at opt-level 0 (Z-1 in the assurance document).
- `avx2` (off by default, x86_64 only): runtime CPUID dispatch to an AVX2 compilation of the NTT bodies. This is the crate's
  only `unsafe` and is outside the proof; without the feature the crate has `forbid(unsafe_code)`.

Minimum supported Rust version: 1.86. A benchmark table (ML-DSA-87, with dates and conditions) is in
[docs/assurance.md](docs/assurance.md), section 5.

## Evidence

Nearly all of it can be re-run; see "Check it yourself" below, which also lists the exceptions.

- **Proof gates.** `scripts/lean-check.sh` (770 declarations, standard axioms only), `scripts/witness-check.sh` (146 names,
  kernel-checked instances showing the premises are satisfiable for one ML-DSA-44 input), and `scripts/ci.sh` (17 Rust
  steps) all passed at 9d51b57, with extraction byte-identical to the committed `lean/Impl`. The only later commit to the
  gated tree, 3fac023, changed one echo string in `scripts/ci.sh` (`docs/assurance.md` section 0).
- **Constant time.** BINSEC checks compiled probes of every secret-touching step of KeyGen and Sign (listed in
  `checkct/README.md`), on x86_64 (several build profiles), thumbv7em, riscv32imac and AArch64 without NEON. The whole KeyGen,
  Sign and `pk_from_sk` functions have no verdict, and the glue between steps is covered by code reading only. No unexpected
  leak is open; three real ones were found and fixed. Under nearcore's exact release build (`nearcore-exact`), 49 of 113
  probes and both Sign censuses have no verdict (61 secure / 3 expected insecure / 0 unexpected / 51 unknown, including
  `hint_step`, `response`, `compute_t`, `prepare_sk` and `signing_key`), because BINSEC cannot lift the AVX instructions
  that `+fma` allows; the same flags with the vectorizers off get a verdict for every probe, but that is a different binary.
  AArch64 builds with NEON, and therefore macOS and Apple Silicon builds, have no BINSEC coverage. Details and limits:
  `checkct/README.md`, assurance document section 4.
- **Differential tests** against RustCrypto `ml-dsa`, `aws-lc-rs` (verdict differences: 0 in about 3.2M verify
  comparisons; empty context only; a test, not a proof), libcrux-ml-dsa and mldsa-native (`crosscheck/`).
- **Test vectors:** NIST ACVP (keyGen, sigGen, sigVer; the preHash and external-μ cases are skipped) and Wycheproof.
- **Fuzzing:** differential fuzz targets against RustCrypto (`fuzz/`) and the other implementations (`crosscheck/`).
- **Spec cross-check:** `xspec/` proves `lean/Spec` equal to ocaml-pq's independent Lean transcription, with the
  qualifiers in `docs/assurance.md` section 1.8 (Sign attempt bound, key-import difference, sampler-termination assumption).

## Check it yourself

[docs/reproduce.md](docs/reproduce.md) has the exact commands: toolchain pins (Lean, Charon, Aeneas, Rust), re-extracting
the Rust to Lean and diffing `lean/Impl`, the Lean gates, the Rust check list, and the BINSEC harness.

## Known limitations

Short list; the assurance document has the full one (section 7):

- Stack residue wiping fails to hold at opt-level 0 (Z-1, open).
- BINSEC 0.11.3 cannot lift AVX/VEX instructions. Under nearcore's exact release build (`+fma` implies AVX), 49 of 113
  probes (the NTT, `hint_step`, `response`, `compute_t`, `prepare_sk`, `signing_key` and others) and both Sign censuses have
  no verdict; the same flags with the vectorizers off give a verdict for every probe, which is evidence about a different
  binary. The AVX2 copy has no verdict either, and AArch64 builds with NEON (so macOS and Apple Silicon) have no BINSEC
  coverage. Some probes on other targets and the whole-Sign censuses have no verdict too.
- Expanded secret keys with out-of-range coefficients are accepted by `sign_NN` as FIPS 204 specifies; use
  `sk_is_well_formed_NN` on untrusted keys.
- The crate-private internals (visible only with the `internals` feature, meant for tests) can panic on wrong-length slices.
- Stack use is measured, not proved (`tools/stack/README.md`).

## Security

To report a vulnerability, see [SECURITY.md](SECURITY.md).

## License and attribution

MIT OR Apache-2.0, at your option (`LICENSE-MIT`, `LICENSE-APACHE`).

- The code skeleton started from RustCrypto's [`ml-dsa`](https://github.com/RustCrypto/signatures) (MIT OR Apache-2.0),
  which is also the main differential-test oracle.
- `crosscheck/` vendors parts of [mldsa-native](https://github.com/pq-code-package/mldsa-native) (Apache-2.0 OR ISC OR MIT)
  for comparison tests.
- The `checkct/` harness is ported from RustCrypto's `ml-dsa` constant-time harness (a3690c4); origin notes are in the
  copied files and in `checkct/README.md`.
- Test vectors come from NIST ACVP and C2SP [Wycheproof](https://github.com/C2SP/wycheproof); their licenses and sources are in
  `tests/data/*/README.md`.
- `xspec/` compares against [ocaml-pq](https://github.com/thevilledev/ocaml-pq) (ISC license).
- Tools: Charon, Aeneas, Lean 4 and Mathlib, BINSEC and cargo-checkct.
