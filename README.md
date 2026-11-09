# ml-dsa-lean

**Formally verified ML-DSA in Rust.** A machine-checked Lean proof shows that, for every input, this implementation of
FIPS 204 post-quantum signatures never panics and computes exactly what the standard specifies.

That covers key generation, signing and verification for ML-DSA-44, ML-DSA-65 and ML-DSA-87, all the way down to the NTT
and the bit packing. Lean also proves that signatures made with a generated key always verify. The proofs use only Lean's standard
axioms, and anyone can re-check them.

The Rust is deliberately plain: one function per FIPS 204 algorithm, fixed-size arrays and loops, `no_std`, no allocation,
no required dependencies. [Charon and Aeneas](https://github.com/AeneasVerif/aeneas) translate it to Lean, where it is proved
equal to a Lean transcription of the standard.

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

The API is plain functions on byte arrays, one set per parameter set (`_44`, `_65`, `_87`). Sizes in bytes:

| Set | public key | secret key | signature |
|---|---|---|---|
| ML-DSA-44 | 1312 | 2560 | 2420 |
| ML-DSA-65 | 1952 | 4032 | 3309 |
| ML-DSA-87 | 2592 | 4896 | 4627 |

To sign or verify many times with one key, `signing_key_NN`/`sign_prepared_NN` and `verifying_key_NN`/`verify_prepared_NN`
cache the per-key work. `sk_is_well_formed_NN` checks secret keys loaded from untrusted storage. The docs in `src/api.rs`
cover the rest.

Optional features:

- `zeroize` wipes dropped signing keys and, best effort, secret intermediates.
- `avx2` adds runtime-dispatched AVX2 code on x86_64: a fast verify whose 4-way body, and the run-time choice between it and the
  scalar verify (for either answer of the CPU check), are proved equal to the scalar verify at source level; and an AVX2 NTT for
  signing and key generation that is tested, not proved. Outside the proof on the verify paths: the CPU detection (assumed: the CPU and OS
  support AVX2 whenever it reports it; a false report is undefined behavior), the 15 token-passing call lines in `src/api.rs`, the 3
  `unsafe` calls in `src/fast_verify.rs`, and the `target_feature`/`repr`/`inline` attributes under the ordinary compiler trust; see
  `docs/limitations.md`.

Requires Rust 1.86 or newer.

## How it's checked

- **Proof.** 412 Lean theorems, from the top-level API down to the arithmetic (listed in `lean/headline-theorems.txt`), and
  111 more for the 4-way verify (`lean/fast-verify-theorems.txt`, `lean/keccak4-theorems.txt`).
- **Constant time.** [BINSEC](https://binsec.github.io/) checks the compiled secret-handling code for secret-dependent
  branches and memory accesses on x86_64, 32-bit Arm, RISC-V and AArch64.
- **Tests.** Differential testing against RustCrypto, aws-lc-rs, libcrux and mldsa-native, NIST ACVP and Wycheproof
  vectors, and differential fuzzing.

[docs/reproduce.md](https://github.com/r-near/ml-dsa-lean/blob/main/docs/reproduce.md) has the commands to re-run all of
it, from re-extracting the Rust to Lean through the constant-time harness. The trusted base, the exact scope and the known
limitations are in [docs/limitations.md](https://github.com/r-near/ml-dsa-lean/blob/main/docs/limitations.md); every claim
and its evidence is in [docs/assurance.md](https://github.com/r-near/ml-dsa-lean/blob/main/docs/assurance.md).

## Security

Please report vulnerabilities privately; see [SECURITY.md](https://github.com/r-near/ml-dsa-lean/blob/main/SECURITY.md).

## License

MIT OR Apache-2.0, at your option (`LICENSE-MIT`, `LICENSE-APACHE`). An independent personal project, not affiliated with
or endorsed by NEAR or any employer.

The code started from a skeleton derived from RustCrypto's [`ml-dsa`](https://github.com/RustCrypto/signatures) (MIT OR
Apache-2.0), which is also the main differential-test oracle. The constant-time harness in `checkct/` is ported from the same
project. `crosscheck/` vendors parts of [mldsa-native](https://github.com/pq-code-package/mldsa-native) (Apache-2.0 OR ISC
OR MIT). Test vectors come from NIST ACVP and C2SP [Wycheproof](https://github.com/C2SP/wycheproof) (sources and licenses in
`tests/data/*/README.md`), and `xspec/` compares the specification against
[ocaml-pq](https://github.com/thevilledev/ocaml-pq) (ISC). Built with Charon, Aeneas, Lean 4 and Mathlib; checked with
BINSEC and cargo-checkct.
