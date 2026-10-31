# Performance baseline and optimization plan

Status: measurement only. Nothing under `src/`, `lean/`, `xspec/`, `crosscheck/`, `fuzz/` or `checkct/` was changed to
produce this document; the harness lives in `bench/` (a standalone crate with its own `[workspace]`). Every
"estimate" below is derived from a measured microbenchmark or profile on the machine described in section 1 and is
marked as such; nothing in the optimization list has been implemented in `src/`.

## Summary

- Nearcore-like profile, default `target-cpu`, ML-DSA-87, median per call. This crate: keygen 233 us, sign 798 us
  (deterministic), verify 242 us. Portable competitors are 1.2 to 1.4 times faster (mldsa-native C: 176 / 568 / 187 us;
  libcrux portable: 198 / 620 / 204 us). AVX2 implementations are 2.2 to 3.8 times faster (libcrux AVX2: 105 / 219 /
  109 us) and 4.2 to 6.6 times faster (mldsa-native AVX2: 55 / 122 / 55 us). RustCrypto `ml-dsa` is 4 to 15% slower
  than this crate on sign and verify and 1.65 to 1.9 times slower on keygen.
- The permutation is not the problem. Our Keccak-f[1600] runs in 356 ns, the same as the `keccak` crate (363 ns) and
  libcrux portable. What costs time is (a) the byte-at-a-time sponge glue around it (about 0.6 us per SHAKE128
  stream of 840 bytes, on top of 1.8 us of permutations), (b) expanding the 56 polynomials of Â for every verify
  and keygen (56% of verify-87, 58% of keygen-87), and (c) scalar NTT/pointwise arithmetic that no compiler
  vectorizes because of the u128 Barrett multiply.
- Caching Â in a verifying-key type is the biggest single portable win, and it needs no proof to be redone: a
  prototype built from the crate's own functions verifies in 109 us (Â cached, 2.2 times faster) or 82 us (Â, t̂1 and
  tr cached, 3.0 times faster) at ML-DSA-87, against 243 us today. That beats every uncached AVX2 implementation here
  except mldsa-native's.
- The second lever is vectorization of the field arithmetic. A lazy signed-i32 (Montgomery) NTT, NTT⁻¹ and
  pointwise product is only 10 to 20% faster as scalar code on this CPU, but when the same Rust is compiled for
  AVX2 it is 3.3, 4.3 and 5 times faster respectively. libcrux portable shows the same effect end to end (sign-87
  620 us at the default target, 382 us at x86-64-v3); ours barely moves (798 us to 761 us). This needs runtime
  dispatch (or a build flag) and is the item with the largest uncertainty about the proof and extraction workflow.
- `target-cpu=native` makes this crate 4 to 33% slower on this Zen 4 machine (the AVX-512 code LLVM generates for
  the scalar u128 Barrett and Keccak code is slower); `x86-64-v3` makes it 4 to 7% faster.
- Recommended first batch (keeps the Lean cost to new files plus roughly 0.9k lines of re-proved sponge glue and 0.4 to 0.8k lines of rounding lemmas): the
  prepared verifying key, a lane-wise sponge (absorb and squeeze whole 64-bit lanes), and a cleanup of
  `decompose`/`use_hint`. Projected: verify-87 244 us to about 210 us uncached, and to about 78 us cached; sign-87
  809 us to about 735 us. Then the lazy vectorizable NTT (projected cached verify-87 about 40 us, sign-87 about
  430 us). Details in sections 6 and 7.

## 1. Machine and method

### Machine

| item | value |
|---|---|
| CPU | AMD EPYC 9B14 (Zen 4, AVX2 and AVX-512 available), 60 vCPUs = 30 cores x 2 threads, KVM guest |
| clock | 3.40 GHz measured with a dependent-add chain before and after every run (the guest reports 2.6 GHz nominal) |
| governor, turbo | not visible from the guest (no cpufreq sysfs); the measured clock was constant at 3.40 GHz in every run |
| steal time | 0 jiffies in every run |
| caches | L1d 32 KiB, L2 1 MiB per core, L3 32 MiB per instance (4 instances), as reported by `lscpu` |
| kernel, toolchain | Linux 7.0 (GCP), rustc 1.99.1, gcc 13.3.0 |
| pinning | `taskset -c 10` (hyper-thread sibling cpu 40 idle); a second full run on cpu 20 for the repeatability check |
| other load | the box is shared: load average was 1.1 to 1.9 during the runs, from jobs on other cores; none pinned to cpu 10, 20, 40 or their siblings |
| profiler | `perf` is not usable (`perf_event_paranoid` 4, no root, no valgrind); see section 4 for the fallback |

### Harness (`bench/`)

- One binary (`bench`) links all implementations behind identical closures: this crate (`ml-dsa-verified`), RustCrypto
  `ml-dsa` (git rev a3690c4), `libcrux-ml-dsa` 0.0.11 (portable and AVX2), and mldsa-native v2.0.0 C (portable and AVX2)
  through `crosscheck`'s build, as a path dependency.
- Inputs: one key pair per parameter set; 256 messages of 64 bytes with empty context; 64 keygen seeds. All
  implementations get identical inputs, and the binary asserts that all of them produce byte-identical keys,
  signatures (deterministic and hedged, with the same `rnd`) and verification results before timing anything. Because
  signatures are byte-identical, every implementation runs the same number of rejection-loop attempts per message.
- A "round" is a full pass over all 256 messages (or 64 seeds for keygen), so each reported number averages over the
  same message-dependent attempt counts. Each cell: a warm-up of at least 0.3 s, then 15 rounds of at least about
  0.12 s each, then 3 passes of per-call latency timing (for percentiles). Reported: median over rounds, plus
  (max - min) / median over rounds as the spread.
- Mean rejection-loop attempts per sign over the 256 messages: ML-DSA-44 4.57 (deterministic) and 4.29 (hedged);
  ML-DSA-65 5.15 and 4.95; ML-DSA-87 4.11 and 3.51. These are sampling noise around the expected 4.25, 5.1, 3.85, so
  the deterministic vs hedged difference in the tables is not a property of the modes.
- Builds (all on the box, plain `cargo`, no target-dir override):
  - `release`: the workspace's default release profile.
  - `nearcore`: opt-level 3, lto = "fat", codegen-units = 1, panic = "abort".
  - Each with default `target-cpu` (x86-64 baseline, SSE2 only), with `-C target-cpu=native` (AVX-512 on this host), and
    for the nearcore profile also with `-C target-cpu=x86-64-v3` (AVX2, BMI2, FMA; no AVX-512).
  - The two C libraries are compiled by their `build.rs` through the `cc` crate (gcc, optimization level 3, default
    architecture for the portable backend, its own AVX2 flags for the AVX2 backend, no LTO), so `RUSTFLAGS` and the
    Rust profile do not change them; their columns are the same up to noise in every variant, which doubles as a noise
    check.

### Repeatability

- Spread over the 15 rounds ((max - min) / median): median 0.19% over all 81 rows of the nearcore build, at most
  1.6% (RustCrypto sign-hedged, 65), at most 0.55% for this crate.
- Same binary, cpu 10 versus cpu 20: the largest difference of any row is 1.6%, the median 0.28%.
- Per-call latency in the nearcore build, verify-87: this crate p10 / p50 / p90 / p99 = 238 / 239 / 250 / 257 us;
  mldsa-native AVX2 54.3 / 54.4 / 57.8 / 64.0 us. (The tail is the sampling of 256 different messages and timer noise.)

## 2. Baseline

Median microseconds per call, nearcore-like profile (`opt-level 3`, `lto = "fat"`, `codegen-units = 1`,
`panic = "abort"`), default `target-cpu`, pinned to cpu 10. In brackets: time relative to this crate (below 1.00x is
faster than this crate). `rustcrypto` re-derives its signing key and decodes its verifying key from bytes on every
call, like this crate and the other bindings; the `+cached-sk` and `+cached-vk` rows reuse the expanded key objects,
see section 3.

ML-DSA-44 (median per call, microseconds; in brackets: time relative to this crate)

| implementation | keygen | sign (deterministic) | sign (hedged) | verify |
|---|---|---|---|---|
| ours | 84.2 (1.00x) | 406.7 (1.00x) | 386.8 (1.00x) | 90.9 (1.00x) |
| rustcrypto | 159.9 (1.90x) | 464.0 (1.14x) | 440.3 (1.14x) | 100.0 (1.10x) |
| rustcrypto+cached-sk | n/a | 402.7 (0.99x) | 378.4 (0.98x) | n/a |
| rustcrypto+cached-vk | n/a | n/a | n/a | 49.3 (0.54x) |
| libcrux-portable | 68.9 (0.82x) | 312.5 (0.77x) | 297.2 (0.77x) | 75.2 (0.83x) |
| libcrux-avx2 | 35.5 (0.42x) | 105.8 (0.26x) | 101.2 (0.26x) | 39.6 (0.44x) |
| mldsa-native-portable | 64.9 (0.77x) | 299.4 (0.74x) | 284.1 (0.73x) | 74.7 (0.82x) |
| mldsa-native-avx2 | 20.0 (0.24x) | 67.1 (0.17x) | 64.0 (0.17x) | 22.0 (0.24x) |

ML-DSA-65 (median per call, microseconds; in brackets: time relative to this crate)

| implementation | keygen | sign (deterministic) | sign (hedged) | verify |
|---|---|---|---|---|
| ours | 157.0 (1.00x) | 649.0 (1.00x) | 628.6 (1.00x) | 147.6 (1.00x) |
| rustcrypto | 261.8 (1.67x) | 748.1 (1.15x) | 724.6 (1.15x) | 155.8 (1.06x) |
| rustcrypto+cached-sk | n/a | 646.0 (1.00x) | 621.4 (0.99x) | n/a |
| rustcrypto+cached-vk | n/a | n/a | n/a | 67.1 (0.45x) |
| libcrux-portable | 135.9 (0.87x) | 496.2 (0.76x) | 481.8 (0.77x) | 127.0 (0.86x) |
| libcrux-avx2 | 64.8 (0.41x) | 164.2 (0.25x) | 160.1 (0.25x) | 67.4 (0.46x) |
| mldsa-native-portable | 120.8 (0.77x) | 451.7 (0.70x) | 440.2 (0.70x) | 116.4 (0.79x) |
| mldsa-native-avx2 | 35.5 (0.23x) | 100.4 (0.15x) | 98.0 (0.16x) | 36.0 (0.24x) |

ML-DSA-87 (median per call, microseconds; in brackets: time relative to this crate)

| implementation | keygen | sign (deterministic) | sign (hedged) | verify |
|---|---|---|---|---|
| ours | 232.9 (1.00x) | 798.3 (1.00x) | 714.7 (1.00x) | 242.1 (1.00x) |
| rustcrypto | 384.1 (1.65x) | 889.1 (1.11x) | 794.4 (1.11x) | 250.8 (1.04x) |
| rustcrypto+cached-sk | n/a | 710.6 (0.89x) | 619.4 (0.87x) | n/a |
| rustcrypto+cached-vk | n/a | n/a | n/a | 96.7 (0.40x) |
| libcrux-portable | 197.5 (0.85x) | 619.8 (0.78x) | 555.2 (0.78x) | 204.3 (0.84x) |
| libcrux-avx2 | 104.8 (0.45x) | 218.8 (0.27x) | 201.0 (0.28x) | 109.3 (0.45x) |
| mldsa-native-portable | 175.5 (0.75x) | 568.3 (0.71x) | 511.9 (0.72x) | 187.1 (0.77x) |
| mldsa-native-avx2 | 54.8 (0.24x) | 121.6 (0.15x) | 110.9 (0.16x) | 55.3 (0.23x) |

### Build variants

Same measurements across builds (medians, microseconds). Verify, ML-DSA-87:

| implementation | release-default | nearcore-default | release-native | nearcore-native | nearcore-v3 |
|---|---|---|---|---|---|
| ours | 244.0 | 242.1 | 269.2 | 313.9 | 226.1 |
| rustcrypto | 253.7 | 250.8 | 346.7 | 308.7 | 227.3 |
| rustcrypto+cached-vk | 97.9 | 96.7 | 98.2 | 98.9 | 89.2 |
| libcrux-portable | 206.5 | 204.3 | 199.2 | 225.4 | 157.1 |
| libcrux-avx2 | 109.7 | 109.3 | 50.0 | 54.8 | 64.0 |
| mldsa-native-portable | 187.1 | 187.1 | 187.1 | 187.2 | 186.9 |
| mldsa-native-avx2 | 54.6 | 55.3 | 55.5 | 55.1 | 54.8 |

Sign (deterministic), ML-DSA-87:

| implementation | release-default | nearcore-default | release-native | nearcore-native | nearcore-v3 |
|---|---|---|---|---|---|
| ours | 808.8 | 798.3 | 848.2 | 916.9 | 760.9 |
| rustcrypto | 920.6 | 889.1 | 1022.7 | 998.2 | 815.9 |
| rustcrypto+cached-sk | 745.1 | 710.6 | 750.1 | 769.1 | 658.1 |
| libcrux-portable | 637.2 | 619.8 | 455.8 | 507.0 | 381.7 |
| libcrux-avx2 | 216.9 | 218.8 | 151.7 | 164.1 | 160.4 |
| mldsa-native-portable | 567.2 | 568.3 | 568.6 | 567.9 | 568.4 |
| mldsa-native-avx2 | 121.6 | 121.6 | 121.4 | 121.4 | 121.6 |

Keygen, ML-DSA-65:

| implementation | release-default | nearcore-default | release-native | nearcore-native | nearcore-v3 |
|---|---|---|---|---|---|
| ours | 159.6 | 157.0 | 168.8 | 201.4 | 147.9 |
| rustcrypto | 278.6 | 261.8 | 339.6 | 308.1 | 239.2 |
| libcrux-portable | 139.6 | 135.9 | 140.6 | 152.1 | 111.4 |
| libcrux-avx2 | 64.1 | 64.8 | 30.4 | 32.4 | 38.0 |
| mldsa-native-portable | 120.9 | 120.8 | 120.9 | 120.7 | 121.2 |
| mldsa-native-avx2 | 35.7 | 35.5 | 35.8 | 35.8 | 36.0 |

Reading:

- The nearcore profile is worth 0.3 to 3% over plain release for this crate; RustCrypto gains more (up to 6% on keygen).
- `native` on this host is a loss for this crate (4 to 12% in the release profile, 12 to 33% in the nearcore profile)
  and for RustCrypto (up to 37%). For libcrux AVX2 it halves keygen (35 to 18 us at 44), probably because it can then use
  AVX-512VL rotate and ternary-logic instructions (not checked). libcrux portable gains 27 to 30% on sign under native
  and 37 to 39% under x86-64-v3 because its lazy i32 arithmetic auto-vectorizes (section 5).
- `x86-64-v3` is a gain for every Rust portable implementation: 4 to 7% for this crate, 7 to 10% for RustCrypto and
  37 to 39% for libcrux portable sign.
- Where a downstream wants a baseline above SSE2, it should be `x86-64-v3`, not `native`, for this code. On non-x86
  hosts this was not measured.

## 3. Verify with a precomputed Â

Nearcore verifies repeatedly against stored keys, so the per-key work that does not depend on the signature can be
paid once. In FIPS 204 verify that is ExpandA (Â), the NTT of t1·2^d, and tr = H(pk).

| implementation | can cache per key? | what exists today |
|---|---|---|
| RustCrypto `ml-dsa` | yes | `VerifyingKey` (decoded once) keeps Â, NTT(t1·2^d) and tr; measured below |
| libcrux-ml-dsa 0.0.11 | no | `verify` takes the encoded public key every call and re-expands Â |
| mldsa-native v2.0.0 | no | `crypto_sign_verify` takes the encoded public key every call; there is no prepared-key type |
| this crate | no (prototype only) | `api::verify_NN` takes bytes; the prototype below is in `bench/src/bin/micro.rs` |

RustCrypto, release profile, default target (microseconds; "decode" is the baseline row of section 2):

| set | verify, decode every call | verify, cached `VerifyingKey` | speedup |
|---|---|---|---|
| 44 | 100.6 | 49.4 | 2.04x |
| 65 | 158.6 | 68.0 | 2.33x |
| 87 | 253.7 | 97.9 | 2.59x |

This crate: a prototype (not in `src/`; written in the benchmark crate from the crate's own `expand_a`, `ntt_vec`,
`matrix_vector_ntt`, `use_hint`, `w1_encode`, ...; checked against `api::verify_NN` on all 256 valid signatures and
against a corrupted signature). Release profile, default target, microseconds:

| set | verify, nothing cached | A-hat cached | A-hat, t1-hat and tr cached | speedup (A-hat) | speedup (all three) |
|---|---|---|---|---|---|
| 44 | 92.2 | 53.5 | 39.9 | 1.73x | 2.31x |
| 65 | 149.3 | 77.2 | 56.7 | 1.93x | 2.63x |
| 87 | 243.2 | 108.9 | 81.6 | 2.23x | 2.98x |

The cached object is Â (K·L·1 KiB: 16 / 30 / 56 KiB), t̂1 (K KiB: 4 / 6 / 8 KiB) and tr (64 bytes): about 20 / 36 /
64 KiB for 44 / 65 / 87. Sign has the same structure: caching Â, ŝ1, ŝ2, t̂0 removes ExpandA (136 us), NTT of the
secret vectors (42 us) and skDecode (9 us) from every sign-87 call, 23% of 800 us; RustCrypto's `+cached-sk` row
shows 13 to 19% on sign.

## 4. Profile of this crate

### Method (and the fallback for `perf`)

`perf record` is blocked on the box, so two independent methods were used and cross-checked:

1. **Instrumented replica.** `bench/src/bin/micro.rs` re-implements `verify_internal`, `sign_internal` and
   `keygen_internal` step by step from the crate's own public internals (`--features internals`), with a nanosecond
   monotonic timer around each step. It asserts that its outputs equal the public API's. Its summed time agrees with the
   API call to within 0.6% for verify and keygen (for example verify-87 244.7 us versus 243.2 us) and within 2.2% for
   sign (sign-87 800.2 versus 802.9 us; sign-44 410.0 versus 419.3 us; the replica leaves out some per-attempt
   bookkeeping). Sign step times are totals over all rejection-loop attempts of one call (mean 4.1 attempts at 87).
2. **Sampling.** `bench/src/bin/prof.rs` uses `pprof` (SIGPROF at 1000 Hz, 20 s per implementation, set and operation,
   frame pointers and debug info, inlined frames resolved) and `bench/categorize.py` buckets each sample by its
   innermost recognizable function. Sampling covers every implementation, which the replica cannot. The profiling build
   itself is within 4% of the benchmark build.

Buckets: Keccak-f (the permutation), sponge glue and rejection parsing (absorb/squeeze loops, 3-byte and nibble
parsers; merged because inlining moves cycles between them depending on the implementation), NTT and NTT⁻¹,
pointwise/add/sub, rounding/hints/norms (Decompose, MakeHint, UseHint, norm checks), encoding (pk/sk/sig pack and
unpack, w1 encoding), copies and other.

### Step breakdown, this crate, ML-DSA-87 (replica, microseconds, release build)

Verify:

| step | time (us) | share |
|---|---|---|
| pkDecode | 2.9 | 1.2% |
| sigDecode | 4.9 | 2.0% |
| ExpandA | 135.8 | 55.5% |
| H(pk) | 9.7 | 4.0% |
| H(tr,M') | 0.6 | 0.2% |
| SampleInBall | 0.7 | 0.3% |
| NTT(z) | 12.6 | 5.2% |
| A.z (matrix-vector) | 24.0 | 9.8% |
| NTT(c) | 1.8 | 0.7% |
| NTT(t1*2^13) | 14.8 | 6.0% |
| c.t1 and subtract | 3.4 | 1.4% |
| NTT^-1 | 17.6 | 7.2% |
| UseHint | 8.8 | 3.6% |
| w1Encode | 2.3 | 0.9% |
| H(mu,w1) | 4.4 | 1.8% |
| norm and compare | 0.6 | 0.2% |
| sum of steps | 244.7 | 100% |

Sign (deterministic; totals over all attempts of one call):

| step | time (us) | share |
|---|---|---|
| skDecode | 8.8 | 1.1% |
| NTT(s1,s2,t0) | 41.6 | 5.2% |
| ExpandA | 135.8 | 17.0% |
| H(tr,M') | 0.7 | 0.1% |
| H(K,rnd,mu) | 0.6 | 0.1% |
| ExpandMask | 84.2 | 10.5% |
| NTT(y) | 51.7 | 6.5% |
| A.y (matrix-vector) | 99.0 | 12.4% |
| NTT^-1(w) | 72.1 | 9.0% |
| HighBits(w) | 26.7 | 3.3% |
| w1Encode | 9.3 | 1.2% |
| H(mu,w1) | 18.0 | 2.2% |
| SampleInBall | 2.8 | 0.3% |
| NTT(c) | 7.5 | 0.9% |
| c.s1, NTT^-1 | 74.3 | 9.3% |
| c.s2, NTT^-1 | 84.8 | 10.6% |
| z=y+cs1, w-cs2 | 5.5 | 0.7% |
| LowBits(w-cs2) | 28.8 | 3.6% |
| norms | 4.5 | 0.6% |
| c.t0, NTT^-1 | 20.9 | 2.6% |
| MakeHint | 17.1 | 2.1% |
| sigEncode | 5.8 | 0.7% |
| sum of steps | 800.2 | 100% |

Keygen:

| step | time (us) | share |
|---|---|---|
| H(xi) -> rho, rho', K | 0.6 | 0.2% |
| ExpandA | 136.0 | 58.1% |
| ExpandS | 18.9 | 8.1% |
| NTT(s1) | 12.9 | 5.5% |
| A.s1 (matrix-vector) | 23.9 | 10.2% |
| NTT^-1, + s2 | 18.3 | 7.8% |
| Power2Round | 1.4 | 0.6% |
| pkEncode | 4.0 | 1.7% |
| H(pk) | 9.8 | 4.2% |
| skEncode | 8.1 | 3.5% |
| sum of steps | 233.9 | 100% |

### Category breakdown (sampling, share of samples)

This crate:

| profile | Keccak + sponge + parsing | of which Keccak-f | NTT and NTT^-1 | pointwise, add, sub | rounding, hints, norms | encoding | copies, other |
|---|---|---|---|---|---|---|---|
| ours.44.keygen | 64% | 43% | 18% | 8% | 0% | 8% | 1% |
| ours.44.sign-det | 22% | 19% | 46% | 12% | 16% | 4% | 1% |
| ours.44.verify | 51% | 39% | 26% | 13% | 4% | 6% | 0% |
| ours.65.keygen | 70% | 43% | 13% | 8% | 2% | 6% | 0% |
| ours.65.sign-det | 22% | 18% | 44% | 14% | 16% | 3% | 1% |
| ours.65.verify | 56% | 42% | 26% | 9% | 3% | 5% | 1% |
| ours.87.keygen | 72% | 50% | 12% | 10% | 1% | 5% | 0% |
| ours.87.sign-det | 26% | 22% | 40% | 16% | 15% | 3% | 0% |
| ours.87.verify | 60% | 45% | 19% | 14% | 3% | 4% | 0% |

libcrux portable:

| profile | Keccak + sponge + parsing | of which Keccak-f | NTT and NTT^-1 | pointwise, add, sub | rounding, hints, norms | encoding | copies, other |
|---|---|---|---|---|---|---|---|
| libcrux-portable.44.keygen | 71% | 21% | 18% | 8% | 0% | 3% | 0% |
| libcrux-portable.44.sign-det | 30% | 28% | 52% | 15% | 1% | 2% | 0% |
| libcrux-portable.44.verify | 54% | 53% | 28% | 11% | 5% | 2% | 0% |
| libcrux-portable.65.keygen | 75% | 75% | 13% | 9% | 0% | 2% | 0% |
| libcrux-portable.65.sign-det | 29% | 25% | 49% | 18% | 1% | 2% | 0% |
| libcrux-portable.65.verify | 60% | 59% | 23% | 14% | 1% | 1% | 0% |
| libcrux-portable.87.keygen | 74% | 63% | 13% | 11% | 0% | 2% | 0% |
| libcrux-portable.87.sign-det | 31% | 29% | 44% | 23% | 1% | 2% | 0% |
| libcrux-portable.87.verify | 62% | 62% | 19% | 14% | 4% | 1% | 0% |

Other implementations, ML-DSA-65 only. mldsa-native portable folds pointwise multiplication into its NTT code, and
most of RustCrypto's frames land in "other" because its generic code is not matched by the bucket rules. For the
AVX2 backends the intrinsic-heavy functions are classified coarsely, so only the "Keccak + sponge + parsing" column
is meant to be compared:

| profile | Keccak + sponge + parsing | of which Keccak-f | NTT and NTT^-1 | pointwise, add, sub | rounding, hints, norms | encoding | copies, other |
|---|---|---|---|---|---|---|---|
| mldsa-native-portable.65.keygen | 75% | 52% | 18% | 5% | 0% | 1% | 1% |
| mldsa-native-portable.65.sign-det | 27% | 25% | 71% | 0% | 0% | 1% | 0% |
| mldsa-native-portable.65.verify | 58% | 50% | 41% | 0% | 0% | 2% | 0% |
| libcrux-avx2.65.keygen | 76% | 54% | 5% | 0% | 0% | 18% | 0% |
| libcrux-avx2.65.sign-det | 68% | 47% | 8% | 17% | 1% | 6% | 0% |
| libcrux-avx2.65.verify | 74% | 47% | 0% | 8% | 0% | 17% | 0% |
| mldsa-native-avx2.65.keygen | 80% | 72% | 8% | 2% | 0% | 6% | 4% |
| mldsa-native-avx2.65.sign-det | 55% | 52% | 23% | 5% | 1% | 14% | 2% |
| mldsa-native-avx2.65.verify | 80% | 73% | 11% | 3% | 1% | 2% | 3% |
| rustcrypto.65.keygen | 42% | 28% | 0% | 0% | 0% | 0% | 58% |
| rustcrypto.65.sign-det | 20% | 16% | 0% | 0% | 0% | 0% | 80% |
| rustcrypto.65.verify | 49% | 39% | 0% | 0% | 0% | 0% | 51% |

Shares and times side by side (microseconds = share x the release-build median; the mldsa-native rows are 65 only):

| set, operation | implementation | total | Keccak + sponge + parsing | NTT, pointwise, add/sub | rounding, hints, norms | encoding | copies, other |
|---|---|---|---|---|---|---|---|
| 87 verify | ours | 244.0 | 146.4 | 79.8 | 7.4 | 9.3 | 1.1 |
| 87 verify | libcrux-portable | 206.5 | 129.0 | 66.6 | 8.0 | 2.8 | 0.1 |
| 87 sign-det | ours | 808.8 | 212.9 | 452.4 | 118.9 | 21.6 | 2.9 |
| 87 sign-det | libcrux-portable | 637.2 | 194.5 | 423.7 | 7.0 | 11.8 | 0.1 |
| 87 keygen | ours | 233.7 | 167.5 | 52.8 | 1.5 | 11.4 | 0.5 |
| 87 keygen | libcrux-portable | 202.7 | 150.5 | 48.0 | 0.0 | 3.8 | 0.3 |
| 65 verify | ours | 152.1 | 85.0 | 53.7 | 5.0 | 7.4 | 0.9 |
| 65 verify | libcrux-portable | 128.8 | 77.0 | 48.0 | 1.9 | 1.8 | 0.0 |
| 65 verify | mldsa-native-portable | 116.5 | 67.1 | 47.2 | 0.0 | 1.8 | 0.4 |
| 65 sign-det | ours | 651.3 | 141.3 | 377.5 | 107.4 | 18.7 | 6.5 |
| 65 sign-det | libcrux-portable | 509.5 | 148.7 | 342.0 | 6.0 | 12.7 | 0.1 |
| 65 sign-det | mldsa-native-portable | 451.8 | 122.8 | 322.6 | 0.0 | 6.1 | 0.4 |

Caveats on the buckets: the Keccak + sponge + parsing sum is comparable between implementations; the split between
"Keccak-f" and "sponge glue" is only reliable for this crate (libcrux's permutation is inlined into its squeeze
functions). Rounding in libcrux and mldsa-native is inlined into other buckets, so the rounding column is not
comparable across implementations (the 112 us difference in sign-87 mostly is not real, see section 5).

### Building blocks (microbenchmarks, nanoseconds, one pinned core, same binary compiled three ways)

| operation (ns) | default | x86-64-v3 | native |
|---|---|---|---|
| keccak_f1600 (one permutation) | 356 | 300 | 427 |
| shake128 absorb 34 B + finalize (1 permutation) | 398 | 343 | 468 |
| ... + squeeze 168 B in one call | 519 | 462 | 594 |
| ... + squeeze 168 B as 56 calls of 3 B (the RejNTTPoly pattern) | 622 | 564 | 692 |
| shake128 34 B in, 840 B out in one call (5 permutations) | 2444 | 2155 | 2879 |
| rej_ntt_poly | 2397 | 2145 | 2732 |
| libcrux-sha3 portable shake128, 34 B in, 840 B out | 1744 | 1525 | 3035 |
| keccak crate 0.2.2 f1600 (one permutation) | 363 | 319 | 692 |
| shake256 66 B in, 136 B out in one call (2 permutations) | 528 | 469 | 593 |
| rej_bounded_poly (eta 2) | 882 | 823 | 943 |
| rej_bounded_poly (eta 4) | 1239 | 1157 | 1381 |
| shake256 absorb 2592 B + finalize (20 permutations) | 9622 | 8429 | 10847 |
| ntt (one poly) | 1786 | 1606 | 2035 |
| ntt_inverse (one poly) | 2201 | 2287 | 2356 |
| multiply_ntt (one poly) | 354 | 364 | 381 |
| add_poly (one poly) | 45 | 23 | 24 |
| w1_encode (ML-DSA-65 shape, 6 polys, incl. building the input) | 1973 | 1568 | 1577 |

The `native` build doubles the `keccak` crate's permutation (319 to 692 ns) and slows libcrux-sha3's portable SHAKE
by 1.7 times, which fits RustCrypto's regression under `native` in section 2 (RustCrypto uses the `keccak` crate); the
end-to-end libcrux portable columns do not regress, and why was not investigated.

AVX2 4-way SHAKE128 through `libcrux-sha3` measured 5.7 / 2.3 / 1.4 us per four streams of 840 bytes at the default,
x86-64-v3 and native builds. The spread says intrinsics wrappers inline differently per build, so this number is not
used for estimates; the end-to-end AVX2 columns of section 2 and the mldsa-native AVX2 profile are.

Candidate arithmetic, written in `bench/src/bin/micro.rs` (not in `src/`), checked equal to the crate's `ntt`,
`ntt_inverse` and `multiply_ntt` on random and constant inputs after normalization:

| candidate (one polynomial, ns) | default target | x86-64-v3 (AVX2) | native (AVX-512) |
|---|---|---|---|
| crate ntt (Barrett u128, canonical) | 1783 | 1610 | 2035 |
| ntt: canonical u32, Montgomery multiply by zeta*R, add/sub still reduce | 1831 | 1878 | 2145 |
| ntt: lazy signed i32, no add/sub reduction (output in (-9q, 9q)) | 1521 | 418 | 728 |
| ntt: lazy signed i32 + normalize to [0, q) (drop-in for the crate's ntt) | 1605 | 489 | 744 |
| crate ntt_inverse | 2198 | 2292 | 2355 |
| ntt_inverse: lazy signed i32 + normalize (drop-in) | 1761 | 532 | 577 |
| crate multiply_ntt | 357 | 364 | 388 |
| multiply_ntt: two Montgomery reductions (canonical in and out) | 641 | 165 | 119 |
| multiply_ntt: one Montgomery reduction, result carries 2^-32 (signed i32) | 411 | 73 | 75 |

The candidates are: Montgomery multiplication by zeta·2^32 on canonical u32 with the usual add/sub reductions;
"lazy signed" i32 with no add/sub reduction (values stay in (-9q, 9q) through the layers) and a final
normalization to [0, q) so that it is a drop-in for the canonical interface; and pointwise product with either two
Montgomery reductions (canonical in and out) or one (result carries a 2^-32 factor, which a lazy pipeline folds into the
NTT⁻¹ scale constant). Bounds were checked by assertion on constant inputs and by equality of the normalized outputs on random inputs, not proved.

## 5. Where the gap comes from

This crate takes 1.22 to 1.40 times as long as mldsa-native C portable and 1.18 to 1.30 times as long as libcrux
portable, across sets and operations. For ML-DSA-87 in absolute microseconds, release build, from the table above:

- **verify-87, 244 vs libcrux portable 206 (+38 us):** Keccak + sponge + parsing +17, NTT/pointwise +13, encoding +6.5,
  copies +1, rounding about 0. At 65 against mldsa-native: +18 Keccak and sponge, +6.5 NTT/pointwise, +5.6 encoding.
- **keygen-87, 234 vs 203 (+31):** Keccak and sponge +17, NTT/pointwise +5, encoding +7.5.
- **sign-87, 809 vs 637 (+172):** Keccak and sponge +18, NTT/pointwise +29, encoding +10; the remaining 110 us shows
  in the rounding bucket but is partly an artifact of inlining in the other implementations. Our replica puts
  HighBits, LowBits, MakeHint and the norm checks at 77 us in total (9.6% of the call), which is the number to trust.
  Per coefficient, `poly_high_bits` costs 2.9 ns (about 10 cycles) and `poly_low_bits` 3.3 ns; `poly_use_hint` about
  3.9 ns.

Why each piece is slow, with the evidence:

1. **Sponge glue.** `Shake::absorb`/`squeeze` move one byte per iteration (`xor_byte`, shift and mask) and test the rate
   boundary per byte. Measured: absorbing 34 bytes plus one permutation costs 398 ns against 356 ns for the bare
   permutation; squeezing 168 bytes adds 121 ns (0.7 ns per byte); 840 bytes through five permutations costs 2444 ns
   against 5 x 356 = 1780 ns bare. About 620 to 660 ns of every 2.4 us RejNTTPoly is glue, about 27%. ExpandA is
   56 such streams at 87.
2. **Permutation quality is fine.** 356 ns per permutation (1210 cycles) equals the `keccak` crate's 363 ns, and
   libcrux portable cannot be faster than 349 ns per permutation given its 1744 ns for five. Lane complementing and
   unrolling would move this by at most 5 to 10% of the Keccak-f share (18 to 50% of the call, depending on the
   operation): 1 to 5% overall. x86-64-v3 already gives 16% on the permutation (356 to 300 ns) through BMI.
3. **Expanding Â on every call.** 56 polynomials at 87 = 136 us = 56% of verify and keygen, 17% of sign.
4. **Field arithmetic is scalar and not vectorizable as written.** `barrett_reduce` goes through u128 (`mul` + shift +
   `small_reduce`), and `add`/`sub` do a conditional subtraction each. LLVM does not vectorize this, which is why
   `x86-64-v3` gives 10% on the forward NTT and nothing on the inverse one, and why `native` is slower (NTT +14%; the
   likely cause is the AVX-512 code LLVM emits for the u128 path, not checked). The
   lazy-signed-i32 form has no conditional operations in the butterflies and vectorizes (section 4 table): NTT 1610 to
   489 ns, NTT⁻¹ 2290 to 530 ns, pointwise 364 to 73 ns (one reduction) at x86-64-v3. libcrux portable's sign time
   falling from 620 to 382 us between the default and v3 nearcore builds is the same effect measured end to end. The scalar Montgomery
   canonical variant is not faster (1.03 to 1.17 times slower), so this is not a Barrett versus Montgomery question
   on x86-64 with a fast 64-bit multiplier; it is a laziness and vectorizability question.
5. **Rounding and hints.** `decompose` takes the parameter set as a run-time `Params` struct (shift and multiplier are
   loaded, not constants), uses two 64-bit multiplies plus a `black_box` barrier for the constant-time edge case,
   and `make_hint` decomposes twice; `use_hint` divides by a run-time modulus. Cost: 77 us of sign-87 and 8.8 us of
   verify-87.
6. **Encoding.** Bit-packing is per-coefficient byte logic: pk decode + sig decode + w1 encode = 9.8 us at verify-87
   against libcrux's 2.8 us.
7. **Copies.** By-value `[u32; 256]` returns and `let mut w = *w` copies are 0 to 1% of samples. They cost stack (section 6
   items 8 and 9), not time.

Not measured (no hardware): aarch64, wasm32, Intel. Expectations only, stated so they can be tested: on wasm32
`u128` multiplication is a runtime library call, so the Barrett path should be considerably worse there than here and a
u64-only reduction (Montgomery, 32 x 32 to 64) should win; on aarch64 NEON is baseline, so the lazy i32 pipeline
should auto-vectorize without dispatch (4 lanes); aarch64's `eor3`/`bcax`/`rax1`/`xar` instructions are what libcrux
and mldsa-native use to speed up Keccak there.

## 6. Ranked optimizations

Estimated effects are for ML-DSA-87 against the release-build medians (verify 244 us, sign 809 us, keygen 234 us),
derived from the measurements above; "proof cost" counts lines of the existing Lean files whose proofs would be
re-done, from `lean/Proofs/*.lean` (24.5k lines in total), plus an estimate of new Lean; stack numbers refer to
`tools/stack` (Sign 239 KB, Verify 131 KB, KeyGen 134 KB at 87). Items 1 to 3 are independent of each other and of
the rest.

| # | Optimization | Estimated effect | Proof cost | Stack | Risk |
|---|---|---|---|---|---|
| 1 | **Prepared verifying key** (`prepare(pk)` caches Â, t̂1·2^d and tr; `verify_prepared`). API addition. | Measured on a prototype: verify 2.2x with Â, 3.0x with all three (87: 244 to 109 / 82 us; 65: 149 to 77 / 57; 44: 92 to 53 / 40) | None re-done. New: split `verify` into `prepare` and `verify_prepared`, prove `verify_prepared (prepare pk) = verify pk` by unfolding; 300 to 500 new lines, `Verify.lean` (627) and `PartialVerify.lean` (325) stay as they are | Verify frame loses Â and t̂1 (about 65 KB, 131 to about 66 KB); the key object holds about 64 KiB at 87 (36 at 65, 20 at 44) in the caller's memory | Low. Opaque type must be constructible only from `prepare`, and must carry or check the pk bytes it was built from. Memory per cached key is the nearcore trade-off |
| 2 | **Lane-wise sponge**: absorb and squeeze whole 8-byte lanes (with a byte tail), one rate check per lane, and a RejNTTPoly parser that reads 3-byte groups out of the lanes instead of through a per-byte squeeze | ExpandA about 25 to 35 us cheaper at 87 (glue 620 ns per stream to about 150 to 250 ns): verify -10 to 14%, keygen -11 to 15%, sign -5% (also helps ExpandMask and H); zero in cached verify | Re-done: `Keccak.lean` (214), `KeccakBytes.lean` (345), `KeccakSponge.lean` (311) about 870 lines, if the `Shake` interface and its `absorb`/`squeeze` specs are kept so `SampleA`, `ExpandMask`, `SampleBall` and everything above stay untouched. Permutation proof (`KeccakPerm.lean`, 536) untouched | None | Low to medium (constant time is unaffected: straight-line lane operations; re-run `checkct`) |
| 3 | **Rounding cleanup**: parameter set as constants (const generics or per-set functions instead of the run-time `Params`), a single multiply plus correction in `decompose`, `make_hint` through `high_bits` only, division-free `use_hint` (compare and select) | sign about -3 to 5% (30 to 50% of the 77 us); verify -1.5% (UseHint 8.8 to about 4 us); keygen about 0 | `Rounding.lean` (801) and `Hint.lean` (1112) partly: `decompose_spec` and `use_hint_spec` leaf lemmas re-proved, statements above them kept; est. 400 to 800 lines touched | None | Medium: the `black_box` in `decompose` exists for a checkct finding (CT-1); re-run checkct and re-check the generated code, do not trust source-level constant time |
| 4 | **Lazy signed-i32 NTT, NTT⁻¹ and pointwise** behind the existing canonical-in canonical-out interface (normalize at the end) | Scalar target: NTT -10%, NTT⁻¹ -20%, pointwise +15% (slower), so about -1 to 3% overall; this is the enabler for item 5 | `NTT.lean` (211) and `NTTInverse.lean` (248): loop invariants change from "canonical" to "bounded and congruent", new Montgomery and bound lemmas in `Field.lean` (115); est. 700 to 1000 lines new or re-done. `NTTOps.lean` (529), `CorrNTT.lean` (986) and everything above keep their statements because the external contract (canonical in, canonical out, equal in Z_q to the spec NTT) does not change | None (in place possible, see 9) | Medium: bounds must be proved (the prototype only asserts them); signed arithmetic and `>>` on negatives in Aeneas need the usual care |
| 5 | **Vectorized builds of item 4**: either ship with `-C target-cpu=x86-64-v3`, or compile the same body twice (`#[target_feature(enable = "avx2")]` clone and baseline) and choose at run time (`is_x86_feature_detected!`); NEON is baseline on aarch64, so it should need neither (unmeasured) | At AVX2 (measured on the candidates): NTT 3.3x, NTT⁻¹ 4.3x, pointwise 5x. Projected 87: cached verify 82 to about 40 us; uncached verify -50 to -60 us (-20 to 25%); sign -300 us (-37%, 809 to about 500); keygen -40 us (-17%) | No new proof if the clone is the same source (one extracted body, two compiled copies). Whether Charon/Aeneas extracts a `#[target_feature]` function, or whether the dispatch shim has to live outside the extracted crate as unverified glue (and so enter the object-code assurance argument of `docs/object-code-assurance.md` §4), has not been tested and is the main unknown | None | Medium: auto-vectorization is a compiler outcome, not a guarantee; it needs a benchmark gate in CI. Not available on x86-64 hosts without AVX2 (fallback is item 4's scalar speed) |
| 6 | **4-way SHAKE** for ExpandA, ExpandS and ExpandMask (SymCrypt-style): four streams per call | Keccak + sponge + parsing falls 2.6 to 4x in the mldsa-native AVX2 profile (65: 85 us for this crate against about 29 us). 87: verify -70 to -100 us (-30 to 40%), keygen -90 to -125 (-40 to 50%), sign -100 to -130 (-12 to 16%). Overlaps item 2 | Highest of the performance items: a new x4 permutation and its refinement to four independent copies of the proved permutation (est. 600 to 1000 lines reusing `KeccakPerm`'s round lemmas), ExpandA restructured to batches of four (`SampleA` 661, `PartialSample` 350 touched). If done with `std::arch` intrinsics: a Lean model for each instruction (SymCrypt-style shims, `docs/object-code-assurance.md` §4), several thousand lines. A portable `[[u64; 4]; 25]` formulation relies on auto-vectorization and needs AVX-512VL for cheap rotates (see section 4) | Small (4 x 200 byte states, a 4 KB output buffer) | High (proof effort, dispatch, per-architecture code) |
| 7 | **Keccak-f quality** (lane complementing, explicit unrolling, fewer `%`-index loops) | At most 5 to 10% of the Keccak-f share: 2 to 5% overall. The permutation is already at the `keccak` crate's speed | `KeccakPerm.lean` (536) and `KeccakLanes.lean` (67) re-done | None | Low risk, low value |
| 8 | **Streaming Â row by row** (generate one row of 7 polynomials, multiply and accumulate, drop it) in verify and keygen | Time: about 0. Stack: Verify 131 to about 35 to 40 KB, KeyGen 134 to about 35 to 40 KB (tools/stack estimate). Not for Sign (Â is reused every attempt, ExpandA would run about 4 times) and mutually exclusive with item 1 in the same call | `matrix_vector_ntt` fused with `expand_a`; `Verify`, `KeyGen`, `SampleA` entry lemmas touched; est. 400 to 800 lines | about -90 to -100 KB (verify, keygen) | Medium |
| 9 | **Avoid by-value array copies, in-place transforms** (`ntt(&mut [u32; 256])`, out-parameters for `expand_*`, `*_decode`, `ntt_vec`, merge `s1`/`s2`/`t0` NTT in place) | Time: at most 1 to 2% (copies are 0 to 1% of samples; a 1 KB copy is about 30 ns against a 1.6 to 1.8 us NTT). Stack: about 25 KB in Sign, 16 KB in `sig_decode`, 9 KB in `pk_decode`, 31 KB in KeyGen, 47 KB more in Sign by dropping plain `s1/s2/t0` (tools/stack list) | Mechanical but wide: every function whose spec changes from "returns an array" to "writes through `&mut`", plus every caller proof; touches `Steps.lean` (1041), `Sign.lean` (1222), `Repr.lean` (889), `Verify.lean`, `KeyGen.lean` | The largest stack cut of the list (Sign 239 KB to about 110 KB) | Medium (churn, not difficulty) |
| 10 | **Prepared signing key** (cache Â, ŝ1, ŝ2, t̂0) | sign -23% (186 of 800 us at 87); RustCrypto `+cached-sk` shows -13 to -19% | None re-done; new definitions only, as item 1 | Object about 80 KiB at 87 | Low; the object is secret material (zeroization policy) |
| 11 | **Word-wise bit packing** in pk/sig/sk encode and decode | verify -6 us (2.5%), keygen -8 us (3%), sign -8 us (1%) | `Encode.lean` (522), `EncodeBits.lean` (503), `EncodeKeys.lean` (1112), `SigCodec.lean` (537), `CorrCodec.lean` (1846): the largest re-proof for the smallest gain | None | Low value, high proof cost: do last |
| 12 | **Montgomery or Barrett variants for scalar `mul`** | None on x86-64: canonical Montgomery NTT is 1.03 to 1.17 times slower than the u128 Barrett, and a canonical-in canonical-out Montgomery pointwise product needs two reductions (1.8 times slower). Possible win on wasm32 and 32-bit targets where u128 is a library call (unmeasured) | `Field.lean` only (115 lines) if `mul` keeps its signature | None | Do not do without a measurement on those targets |
| 13 | **Hand-written SIMD NTT** (AVX2 and NEON intrinsics) | Beyond item 5's auto-vectorized result perhaps another 1.5 to 2 times on the NTT (est., no measurement); about -10 to 15 us on verify-87 | Lean models of every intrinsic used plus a refinement proof per transform (SymCrypt-style); highest per-line cost | small | High; only after items 1 to 6 have been exhausted |

Ordering rationale: items 1 to 3 cost almost no re-proving. Item 4 and 5 give the largest portable gain on every
operation and cost a bounded rewrite of two proof files with their contract unchanged. Item 6 is the only route to the
AVX2 competitors' sign and keygen numbers. Items 7, 11 and 12 are not worth their proof cost on current evidence. Items
8 and 9 are the stack program; they are independent of speed and should be scheduled with the stack target for the
deployment (wasm32, threads) in mind.

## 7. Recommended first batch

1. **Prepared verifying key** (item 1). The nearcore workload is "many verifications against stored keys", this is
   the largest measured win (2.2 to 3.0 times), and it is an API addition with essentially no Lean redone. Decide the
   memory budget per cached key (20 / 36 / 64 KiB) and whether the object stores the pk bytes. Add the prepared
   signing key (item 10) in the same pass if validators sign.
2. **Lane-wise sponge** (item 2). A bounded, local proof change under an unchanged `Shake` interface (about 870 lines
   of Lean re-done, none above them). Worth 10 to 15% on uncached verify and keygen and about 5% on sign.
3. **Rounding cleanup** (item 3), after a first measurement of how much `decompose` improves in isolation (the harness
   already has the per-step replica for it). Keep it optional if the checkct re-run turns up anything.
4. **A no-proof experiment before the next batch:** check whether a `#[target_feature(enable = "avx2")]` function (or a
   generic `#[inline(always)]` body instantiated inside one) goes through Charon and Aeneas, and how the dispatch shim
   enters the assurance argument. This decides whether item 5 is "free" or needs an unverified glue layer, and it can be
   answered without touching `lean/`.

Projected results of batch 1 (estimates from the measurements above, not implemented), ML-DSA-87: verify 244 us to
about 210 us uncached or about 78 us cached; sign 809 us to about 735 us; keygen 234 us to about 200 us.

### Status: prepared keys implemented

Items 1 and 10 are implemented and proved (`api::verifying_key_NN`, `verify_prepared_NN`, `verify_internal_prepared_NN`;
`api::signing_key_NN`, `sign_prepared_NN`, `sign_internal_prepared_NN`; Lean in `Proofs/PreparedVerify.lean` and
`Proofs/PreparedSign.lean`). Measured with the method of section 9 (nearcore-default, pinned to one CPU, medians; the
CPU was one with no other job on it or its sibling), microseconds:

| set | verify | verify, prepared key | sign-det | sign-det, prepared key | sign-hedged | sign-hedged, prepared key |
|---|---|---|---|---|---|---|
| ML-DSA-44 | 93.2 | 39.0 (0.42x) | 408.6 | 343.0 (0.84x) | 388.7 | 324.1 (0.83x) |
| ML-DSA-65 | 150.4 | 55.1 (0.37x) | 650.4 | 539.7 (0.83x) | 630.9 | 520.1 (0.82x) |
| ML-DSA-87 | 248.5 | 78.7 (0.32x) | 816.6 | 624.6 (0.76x) | 731.2 | 539.8 (0.74x) |

Prepared object sizes: verifying key 20,544 / 36,928 / 65,600 bytes, signing key 28,768 / 48,224 / 80,992 bytes
(ML-DSA-44 / 65 / 87). The crate is `no_std` without `alloc`, so callers `Box` them. Signing keys hold secrets; with the
`zeroize` feature, dropping a `SigningKeyNN` wipes ŝ1, ŝ2, t̂0 and K. That `Drop` impl is `cfg`-gated and outside the
extraction (Aeneas models neither `Drop` nor volatile writes), so the Lean theorems are about the code without it. The
prepared signing path performs the operations of `sign_NN` in the same order and adds no branch on secret data; the
only change is that skDecode, the three NTTs and ExpandA run in `signing_key_NN` instead of on every call.

### Status after batch 1 (2026-10-31): prepared keys, lane-wise sponge, Shoup/Montgomery NTT, optional AVX2 dispatch

Also merged: item 2 (8-byte-lane absorb and squeeze, 2–4% overall) and the NTT rewrite from `experiments/simd/`
(Shoup butterflies with precomputed ζ·2³²/q, two-step Montgomery pointwise product, values canonical between layers,
only 32×32→64-bit multiplies so LLVM vectorizes them). Every theorem statement is unchanged; the new field lemmas
are in `Proofs/FieldFast.lean`. The runtime AVX2 dispatch is the opt-in `avx2` feature (see the crate's
`Cargo.toml` and `docs/object-code-assurance.md` §3.5).

`bench/compare.sh merged 8` at main after the merge: nearcore profile, pinned to cpu 8 (sibling idle), load average
2.2–2.5 on 60 threads, medians in microseconds. `default` = generic x86_64, `avx2` = generic x86_64 with the `avx2`
feature (runtime dispatch), `v3` = `-C target-cpu=x86-64-v3` (static AVX2, no dispatch, no `unsafe`).

| set | op | default | avx2 feature | v3 | baseline (section 2, default) |
|---|---|---|---|---|---|
| 44 | keygen | 79.5 | 66.2 | 62.2 | 84.2 |
| 44 | sign-det | 342.1 | 228.5 | 213.2 | 406.7 |
| 44 | sign-det, prepared key | 286.3 | 180.0 | 166.2 | |
| 44 | verify | 84.0 | 66.5 | 62.4 | 90.9 |
| 44 | verify, prepared key | 35.6 | 20.1 | 19.1 | |
| 65 | keygen | 151.8 | 129.9 | 119.6 | |
| 65 | sign-det | 557.3 | 360.9 | 332.6 | |
| 65 | sign-det, prepared key | 458.5 | 273.5 | 251.9 | |
| 65 | verify | 139.7 | 111.5 | 101.3 | |
| 65 | verify, prepared key | 52.6 | 27.7 | 25.0 | |
| 87 | keygen | 229.4 | 192.8 | 179.6 | 232.9 |
| 87 | sign-det | 713.5 | 466.4 | 429.1 | 798.3 |
| 87 | sign-det, prepared key | 542.6 | 311.7 | 285.2 | |
| 87 | verify | 234.6 | 188.7 | 175.4 | 242.1 |
| 87 | verify, prepared key | 81.6 | 38.8 | 34.9 | |

For comparison (section 2, same profile, uncached keys): ML-DSA-87 sign-det 218.8 / 121.6 us and verify 109.3 /
55.3 us for libcrux AVX2 / mldsa-native AVX2; RustCrypto's cached-key verify-87 is 96.7 us. A prepared-key verify
is not the same operation as an uncached one: it skips pk decoding, ExpandA and the NTT of t1, which is what a
validator verifying many signatures under stored keys can do. Uncached verify and sign are still 2–4× behind the
AVX2 C and Rust implementations; the remaining gap is ExpandA (scalar SHAKE128, item 6) and the scalar parts of the
signing loop.

Second batch: items 4 and 5 (lazy NTT with its contract unchanged, plus a vectorized build or dispatch). Projected:
cached verify-87 about 40 us (below every uncached AVX2 figure here), uncached verify-87 about 155 us, sign-87 about
430 us, keygen-87 about 160 us. Third batch: item 6 (4-way SHAKE) if sign and keygen need to approach the AVX2
implementations (sign-87 219 us libcrux, 122 us mldsa-native), and the stack program (items 8 and 9) when the
deployment target requires it.

## 8. Caveats

- One key pair per parameter set, 256 messages, hot caches (everything fits in L2). Cold-cache behavior with many
  different keys, and the memory cost of caching many `Prepared` keys, are not measured.
- Sign medians depend on the message set through the number of attempts (section 1): changing the messages moves a sign
  median by a few percent, the same for all implementations because their signatures are byte-identical.
- The C libraries are built by gcc 13.3 with the `cc` crate's optimization level 3, no LTO and no link-time inlining
  into Rust; a different C compiler or flags would change their columns. The AVX2 backends were run with their own
  intrinsics code; neither library has an AVX-512 backend that was used here.
- The samples in section 4 attribute inlined code to the innermost recognizable function; the buckets are a
  classification, not an exact accounting. The replica and the API agree to 0.6% (verify, keygen) and 2.2% (sign), the buckets agree with the replica
  within a few percentage points (for example ExpandA is 55.5% of verify-87 in the replica, Keccak + sponge + parsing 60%
  in the samples).
- Constant-time properties were not part of this work. Items 2, 3, 4 and 6 all rewrite code that `checkct` covers and
  need a `checkct` re-run.
- The candidate arithmetic in section 4 is a prototype in the benchmark crate with assertion-level bounds. The
  measured speedups say what is available; they are not a proof that the bounds hold for all inputs.
- Not measured: aarch64, wasm32, AMD without AVX-512, Intel.

## 9. Reproducing

All commands are run from the repository root on the build box (never on a laptop), through `rx`. Large scratch goes
under `~/rx/scratch/<name>`.

```sh
rx submit pf-build -- 'set -o pipefail; bash bench/build.sh $HOME/rx/scratch/pf-build 2>&1 | tail -40'
rx submit pf-bench -- 'set -o pipefail; bash bench/run.sh $HOME/rx/scratch/pf-build 10 $HOME/rx/scratch/pf-bench 2>&1 | tail -5'
rx submit pf-prof  -- 'set -o pipefail; mkdir -p $HOME/rx/scratch/pf-prof; taskset -c 10 $HOME/rx/scratch/pf-build/micro-release-default | tee $HOME/rx/scratch/pf-prof/micro.txt'
rx wait pf-build; rx logs pf-bench 80
```

- `bench/build.sh OUTDIR [extra]`: builds `bench` as release / nearcore x default / native, nearcore x86-64-v3, the
  `micro` binary (default, native, v3) and the profiling build (`extra` builds only the nearcore-v3, micro and profiling binaries).
- `bench/run.sh BINDIR CPU OUTDIR [variants...] [-- bench args]`: runs each variant pinned with `taskset`; output
  is the TSV `ROW label set op impl median_ns mean_ns min_ns max_ns call_p10 call_p50 call_p90 call_p99 rounds reps n`.
- `bench/table.py headline|variants|repeat|spread FILE...` turns the TSV into the tables in this document.
- `bench/src/bin/prof.rs OUTDIR [--secs N] [--impl a,b]` writes folded stacks;
  `bench/categorize.py --table FILE.folded...` buckets them.
- The `bench/Cargo.lock` pins the dependency set (libcrux-ml-dsa 0.0.11, RustCrypto at the git rev above, keccak 0.2.2,
  pprof 0.15).
