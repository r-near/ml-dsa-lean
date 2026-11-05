# ml-dsa-lean

ML-DSA (FIPS 204) post-quantum signatures in Rust, with a machine-checked Lean proof that the code matches a formal
transcription of the standard.

The Rust is deliberately plain: one function per FIPS 204 algorithm, fixed-size arrays and loops, `no_std`, no allocation,
no dependencies. That plainness is what makes the proof possible. The code is translated to Lean with
[Charon and Aeneas](https://github.com/AeneasVerif/aeneas), and Lean checks that, for every input, the translated code never panics and,
whenever it returns, returns exactly what our Lean transcription of the FIPS 204 algorithms returns. The transcription
itself, the compiler and the translation tools are trusted, not proved.

It supports ML-DSA-44, ML-DSA-65 and ML-DSA-87.

> **Status:** version 0.1.0. Not audited and not FIPS-validated. An independent personal project, not affiliated with or
> endorsed by NEAR or any employer. Read [docs/limitations.md](docs/limitations.md) before relying on it.

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

The API is plain functions on byte arrays, one set per parameter set (`_44`, `_65`, `_87`):

| Set | public key | secret key | signature |
|---|---|---|---|
| ML-DSA-44 | 1312 | 2560 | 2420 |
| ML-DSA-65 | 1952 | 4032 | 3309 |
| ML-DSA-87 | 2592 | 4896 | 4627 |

If you sign or verify many times with one key, `signing_key_NN`/`sign_prepared_NN` and
`verifying_key_NN`/`verify_prepared_NN` cache the expensive per-key work. If you load secret keys from somewhere you
don't fully trust, check them with `sk_is_well_formed_NN` first. The docs in `src/api.rs` cover the rest.

Optional features:

- `zeroize` wipes secret material when the library is done with it (in release builds; see the limitations).
- `avx2` adds a faster NTT on x86_64 CPUs that support it, chosen at runtime. It is the crate's only `unsafe` code and
  is not covered by the proof.

Requires Rust 1.86 or newer.

## How it's checked

- **Proof.** 407 headline theorems, checked using only Lean's standard axioms. They also show that
  Verify accepts what Sign produces for honestly generated keys.
- **Constant time.** The compiled code is checked for secret-dependent branches and memory accesses with
  [BINSEC](https://binsec.github.io/), on x86_64, 32-bit Arm, RISC-V and AArch64 (without NEON). This is checked, not proved, and the
  coverage has gaps.
- **Tests.** Differential testing against RustCrypto, aws-lc-rs, libcrux and mldsa-native, NIST ACVP and Wycheproof
  vectors, and differential fuzzing.

What the proof does and doesn't cover, where constant-time coverage stops, and the known limitations are in
[docs/limitations.md](docs/limitations.md). The full details are in [docs/assurance.md](docs/assurance.md).

## Check it yourself

Nearly everything above can be re-run. [docs/reproduce.md](docs/reproduce.md) has the commands (and the exceptions), from re-extracting the Rust to Lean
through the proof gates, the tests and the constant-time harness.

## Security

Please report vulnerabilities privately; see [SECURITY.md](SECURITY.md).

## License

MIT OR Apache-2.0, at your option.

The code started from a skeleton derived from RustCrypto's [`ml-dsa`](https://github.com/RustCrypto/signatures) (MIT OR
Apache-2.0), which is also the main differential-test oracle. The constant-time harness in `checkct/` is ported from the same
project. `crosscheck/` vendors parts of [mldsa-native](https://github.com/pq-code-package/mldsa-native) (Apache-2.0 OR ISC
OR MIT). Test vectors come from NIST ACVP and C2SP [Wycheproof](https://github.com/C2SP/wycheproof) (sources and licenses in
`tests/data/*/README.md`), and `xspec/` compares the specification against
[ocaml-pq](https://github.com/thevilledev/ocaml-pq) (ISC).
