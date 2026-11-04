# crosscheck: cross-implementation differential testing

Standalone crate (own `[workspace]`, like `fuzz/`) that compares `ml-dsa-lean`, through its public `api` only,
against three independent implementations:

| Oracle | Pinned | Backends exercised |
|---|---|---|
| libcrux-ml-dsa (Cryspen) | crates.io `=0.0.11` (with `libcrux-sha3 0.0.11`, `libcrux-intrinsics 0.0.9`, `libcrux-platform 0.0.4`), features `acvp` (Sign_internal/Verify_internal) and `simd256` | portable and AVX2 (each called explicitly, AVX2 only after a run-time `is_x86_feature_detected!`) |
| mldsa-native (pq-code-package, C) | tag `v2.0.0`, commit `834a90d5e846ffa1e1611bd24e160bb2e9b86d35`, vendored verbatim in `vendor/mldsa-native/mldsa` and built by `build.rs` with the `cc` crate (cc 1.10.0; gcc 13.3) | portable C, and x86_64 AVX2 (native arithmetic and Keccak plus the `.S` files); two namespaced builds linked into one binary |
| RustCrypto `ml-dsa` | git `a3690c4a0bd861fcf2bde0e38b3609e86c3fe89e` (the revision the main crate's tests and `fuzz/` use; deprecated expanded-key API for skEncode bytes) | its single portable backend |

All versions are locked in `Cargo.lock`. `XC_NO_AVX2=1` (build time and run time) drops the AVX2 backends.

mldsa-native is driven through `keypair_internal` (Algorithm 6 from ξ), `keypair` (Algorithm 1, ξ supplied through a
randombytes hook), `signature_internal` (Algorithm 7 with an explicit rnd and an explicit prefix/message split of
M′), `signature` (Algorithm 2, rnd through the hook), `verify_internal`, `verify` and `pk_from_sk`. External-mu
and HashML-DSA entry points are not exercised (the crate under test does not offer them).

## What is checked

Case `idx` of a parameter set under a master seed is a pure function of (seed, set, idx), so every result is
replayable (`xcheck --replay 65 12345`) regardless of thread count.

Sign side (per case: random ξ; hedged or all-zero rnd; message 0 to 2048 bytes with extra weight on the SHAKE-256 rate
boundaries; context length 0, 1, 255 or 256 with fixed shares, otherwise 2 to 254):

- KeyGen: pk and sk byte-identical across all implementations (mldsa-native through both entry points).
- Sign (Algorithm 2) and Sign_internal (Algorithm 7, on M′ = 0 ‖ |ctx| ‖ ctx ‖ m, or ctx ‖ m when |ctx| = 256)
  byte-identical across all implementations; Sign equals Sign_internal on M′. |ctx| = 256 must be refused by every
  implementation.

Verify side (per case; every tuple (pk, m, ctx, σ) goes through Verify and Verify_internal on all implementations,
and all verdicts must be equal and no implementation may panic):

- the honest signature (must be accepted everywhere; for |ctx| = 256 Verify must reject, Verify_internal accept),
- 12 random single-bit flips of σ spread over c̃, z, hint positions, hint counts and anywhere, plus the first and last
  byte of each of those four regions, 4 single-bit flips of pk (ρ and t1), t1 saturated or zeroed,
- z all 0xFF or 0x00, c̃ zeroed, σ all 0x00 or 0xFF,
- 19 hint encodings: nonzero padding (just after the last position, random, last slot), a count above ω, final count 255,
  decreasing counts, final count below the total, counts claiming a phantom position, duplicate and decreasing
  positions, a valid extra hint, a dense valid hint, one polynomial holding all ω, counts zeroed with stale positions,
  random hint bytes, random but strictly increasing positions,
- message tweak, context tweak, context extended to 256 bytes,
- `--exhaustive N`: every single-bit flip of σ and of pk for the first N cases of each set,
- wrong-length pk and σ: only RustCrypto takes slices (the others take arrays or sized pointers, so a wrong length
  cannot be expressed); it must reject, never panic.

Informational (FIPS 204 leaves Sign undefined): signing with a secret key that skDecode accepts but KeyGen could not
have produced (s1/s2 coefficient outside [−η, η], inconsistent t0/tr/ρ, all-zero and all-0xFF keys). The table records
each implementation's behavior (same signature as ours, other signature, error, panic, hang).

A disagreement is minimized (message and context emptied if possible, then each edited byte reverted to the honest
value while the implementations still disagree) and written under `--out` (default `xc-out/`) with the full inputs
in hex.

## Layout

- `src/oracle.rs`: uniform `Imp` wrapper over the six implementations; panics are caught.
- `src/mldsa_native.rs`, `csrc/`, `build.rs`, `vendor/mldsa-native/`: the C side.
- `src/cases.rs`: seeded PRNG, case generation, mutations. `src/check.rs`: running a case, minimizing.
- `src/undefined.rs`: malformed-key behavior table.
- `src/bin/xcheck.rs`: the deterministic driver.
- `fuzz/`: cargo-fuzz targets `verify_xdiff` and `sign_xdiff` (own workspace; the C code is built with libFuzzer
  coverage instrumentation when the `fuzzing` cfg is set, `XC_NO_COV=1` turns that off).

## How to run

On a Linux x86_64 machine with the Rust toolchains and a C compiler (plain `cargo`):

```
(cd crosscheck && cargo run --release --bin xcheck -- --cases 50000 --exhaustive 60 --out /tmp/xc-out)
(cd crosscheck && cargo +nightly fuzz run verify_xdiff --target x86_64-unknown-linux-gnu -s none -- -fork=14 -max_len=16384 -max_total_time=1800)
(cd crosscheck && cargo +nightly fuzz run sign_xdiff   --target x86_64-unknown-linux-gnu -s none -- -fork=14 -max_len=16384 -max_total_time=1800)
```

`xcheck` options: `--seed N --cases N --threads N --exhaustive N --sets 44,65,87 --sig-flips N --pk-flips N
--skip-sk --only-sk --only-wl --sk-trials N --replay SET IDX --out DIR`. Exit status 0 means no disagreements.
Cases are per parameter set.

## Results

All runs on one Linux machine (AMD EPYC, AVX2 present, so both AVX2 backends ran; the machine was shared with other jobs). Master
seed `0x5EED0204`. The deterministic run took 97 minutes wall (503 CPU-minutes), mostly the exhaustive flips, which run
serially inside a 16-case work chunk (so `--exhaustive N` uses only about N/16 threads; use a smaller N or a smaller
chunk if wall time matters).

### Deterministic driver: 0 disagreements

`xcheck --cases 50000 --exhaustive 60` (command above), plus `--only-wl`:

| | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 | total |
|---|---|---|---|---|
| sign cases (ξ, rnd, m, ctx) | 50,000 | 50,000 | 50,000 | 150,000 |
| keygen results compared with ours (pk and sk each; 6 oracle runs per case, mldsa-native through two entry points) | 350,000 | 350,000 | 350,000 | 1,050,000 |
| signatures compared byte for byte (Sign and Sign_internal, 6 oracle runs each) | 500,000 | 500,000 | 500,000 | 1,500,000 |
| sign calls made (all implementations) | 600,000 | 600,000 | 600,000 | 1,800,000 |
| cases with \|ctx\| = 256 (all implementations refused) | 5,022 | 5,053 | 4,974 | 15,049 |
| verify cases (tuples, each evaluated by all 6 implementations through Verify and Verify_internal) | 4,339,925 | 5,074,628 | 6,014,436 | 15,428,989 |
| individual Verify / Verify_internal calls | 52.1 M | 60.9 M | 72.2 M | 185.1 M |
| honest signatures (accepted by all) | 50,000 | 50,000 | 50,000 | 150,000 |
| mutated inputs accepted by every implementation | 0 | 0 | 0 | 0 |
| disagreements | 0 | 0 | 0 | 0 |

Of the 15.4 M verify cases, 7.78 M are the exhaustive pass (every single-bit flip of σ and of pk, for the first 60
cases of each set: 4,970,880 σ flips and 2,810,880 pk flips) and 7.65 M are the random mutation set. Per mutation class
(all with 0 disagreements and 0 accepted): sig bit flips in c̃ 450k (+300k edge bytes), z 450k (+300k), hint positions
300k (+300k), hint counts 300k (+300k), anywhere 300k; pk bit flips 600k; 19 hint-encoding classes at about 150k each
(nonzero padding x3, count above ω, final count 255, decreasing counts, final count below total, phantom position,
duplicate, swapped, valid extra hint, dense valid hint, all-ω-in-one-polynomial, counts zeroed with stale positions,
random hint bytes, random increasing positions); z all 0xFF / 0x00, c̃ zeroed, σ all 0x00 / 0xFF, t1 all 0xFF / 0x00,
message tweak, context tweak, context extended to 256 bytes (150k each).

Wrong-length inputs (`--only-wl`, 100 cases per set, 8 length variants plus other-level lengths and keys): 3,600 checks,
RustCrypto (the only slice-taking API) rejected all, 0 failures. libcrux takes arrays and mldsa-native sized pointers, so
a wrong length cannot be expressed there.

### Fuzzing: 0 crashes, 0 disagreements

`-fork=14 -max_len=16384 -max_total_time=1800`, `-s none`, nightly-2026-10-28. C code instrumented with
`-fsanitize-coverage=inline-8bit-counters,pc-table,trace-cmp`, so libFuzzer's feedback includes mldsa-native's portable
and AVX2 C (the AVX2 `.S` files are not instrumented).

| target | wall | executions | libFuzzer cov / ft / corpus | crashes |
|---|---|---|---|---|
| `verify_xdiff` | 1801 s | 3,656,908 | 3997 / 9238 / 709 | 0 |
| `sign_xdiff` | 1823 s | 194,921 | 8433 / 20860 / 853 | 0 |

(A 40 s smoke run of each preceded these and shares the corpus.) Each execution of `verify_xdiff` is one tuple through all
12 verify calls; each `sign_xdiff` execution is 7 keygens, 12 signs and a light mutation set, about 100 ms.

Region coverage of this crate's `src/` when replaying the final corpora (`cargo fuzz coverage`, `llvm-cov`): `verify_xdiff`
93.96% regions / 94.03% lines, `sign_xdiff` 96.01% / 95.64%; per file, `field`, `keccak`, `keygen`, `ntt`, `rounding`,
`sampling` 100%, `sign` 99.4%, `verify` 99.0%, `encode` 90.9% (the part not reached is `sk_is_well_formed`, which no
oracle has), `api` 72.6% (verify target) and 90.3% (sign target), `params` 57%.

### Sensitivity: the harness catches a planted verdict bug

Throwaway worktree (`git worktree add --detach <dir> HEAD`, removed afterwards), with the zero-padding check removed from
`hint_bit_unpack_padding` in `src/encode.rs` (the `if y[j] != 0 { return false; }` body deleted):

- Driver, `--cases 300 --skip-sk`: 4,012 disagreements among 45,870 verify cases (the 300-case run takes seconds).
  Every one has ours = accept and all five other implementations reject (RustCrypto "signature decode", libcrux
  `MalformedHint`, mldsa-native `INVALID_SIGNATURE`). Classes: all three nonzero-padding hint classes 894/894 (every
  applicable case), `sig bit flip edge HintPositions` 894 of 1800 (the flips that land in padding), `sig bit flip
  HintPositions` 428, `sig bit flip Anywhere` 8. Each was minimized to a single byte edit of the honest signature,
  for example `4618:00->10` (ML-DSA-87, hint byte 4618 is a padding slot).
- Fuzzer: `verify_xdiff` in the same worktree stopped on the first disagreement within seconds (17 s wall including
  start-up in the run that reused a 202-input corpus; a clean-corpus rerun also crashed on its own). The
  panic text lists every implementation's verdict.

### Behavior on a malformed secret key (informational; FIPS 204 Algorithm 25 leaves Sign undefined)

Deterministic Sign, empty context, 4 random keys per variant per parameter set; all three parameter sets gave the same
pattern. "same sig" means byte-identical to ours; "(valid)"/"(invalid)" is whether the signature verifies under the original
public key.

| key variant | ours `sk_is_well_formed` | mldsa-native `pk_from_sk` | ours, libcrux (portable, AVX2), mldsa-native (portable, AVX2) | RustCrypto |
|---|---|---|---|---|
| valid key | true | ok | same sig (valid) | same sig (valid) |
| one s1 coefficient out of range (first or last) | false | INVALID_KEY | same sig (invalid) | panic |
| one s2 coefficient out of range (first or last) | false | INVALID_KEY | same sig (valid) | panic |
| all s1 fields / random s1 bytes out of range | false | INVALID_KEY | same sig (invalid) | panic |
| all s2 fields out of range | false | INVALID_KEY | same sig (valid) | panic |
| t0 one bit flipped (in range) | true | INVALID_KEY | same sig (valid) | same sig (valid) |
| tr one bit flipped | true | INVALID_KEY | same sig (invalid) | same sig (invalid) |
| ρ one bit flipped | true | INVALID_KEY | same sig (invalid) | same sig (invalid) |
| K one bit flipped | true | ok | same sig (valid) | same sig (valid) |
| sk all 0x00 | true | INVALID_KEY | same sig (invalid) | same sig (invalid) |
| sk all 0xFF | false | INVALID_KEY | same sig (invalid) | panic |

So four independent decoders (ours, libcrux, mldsa-native in both builds) apply skDecode literally and sign without any
error, producing identical bytes; none returns an error or panics, and none hangs. RustCrypto panics in key decoding
(`assertion failed: z.0 <= (a + b).0`). Whether the resulting signature verifies depends on the key (an out-of-range s2
still yields a valid signature; an out-of-range s1 does not). All-zero keys decode in range (η − 0), so `sk_is_well_formed`
accepts them even though the key is inconsistent; mldsa-native's `pk_from_sk` additionally compares t0 and tr and rejects them.
mldsa-native has no runtime check inside `signature` ("assumed to be valid" in its header); the optional validation is
`pk_from_sk`.

Other behavior outside FIPS 204 that the oracles agree on: |ctx| = 256 is refused by every implementation (ours `None`,
libcrux `ContextTooLongError`, mldsa-native `INVALID_ARG`, RustCrypto `Err`) and Verify returns false; wrong-length inputs
are a type-level matter except for RustCrypto's rejection above.

### Limits

- Equality of verdicts is checked, not that a verdict is "right": a bug shared by all four independent code bases
  would not show, and the mutation classes are chosen by hand plus random bit flips.
- libcrux 0.0.11 and mldsa-native v2.0.0 are the pins; the AVX2 backends were run on one CPU model.
- Sign cases with extremely rare κ exhaustion were not observed (every case signed).
- The fuzz runs had a shared, loaded machine; `sign_xdiff` is slow per execution (about 100 ms), so its execution count is
  small compared with the 12 M of `fuzz/verify_diff`.
