# SIMD feasibility experiment

Question: can this crate get a 2 to 4 times faster NTT and pointwise product with the end-to-end theorem staying
unconditional (no new Lean axioms, no change to the statements the proofs above `Field.lean` rely on)?

Everything here is under `experiments/simd/`; `src/` and `lean/` are untouched. Toolchain: Rust nightly-2026-08-18,
Charon nightly-2026.09.02, Aeneas build-183e4f0, extraction with `RUSTFLAGS=--cfg miri` (as `scripts/extract.py` does).
All builds, extractions, Lean checks and benchmarks ran on the build box through `rx`.

## Short answer

1. **Yes, and the cheap path needs no intrinsics at all.** The crate's NTT does not speed up at x86-64-v3 because one
   operation, the u64 x u64 -> u128 Barrett multiply, has no vector instruction, so LLVM keeps a scalar `mulx` per
   lane inside the vectorized loop. Replacing that multiply with a 32 x 32 -> 64 one (Shoup's trick for the
   fixed-zeta butterflies, two unsigned Montgomery steps for the variable-operand pointwise product) makes the plain
   loops vectorize. The statements stay the same (canonical in, canonical out, `mul` = `a*b % q`).
2. **Measured** (256-coefficient polynomial, median ns, one pinned idle core, Zen 4 VM, `#[target_feature(avx2)]`
   clone of the same source body, baseline build otherwise):

   | operation | crate today | rewrite, AVX2 clone | speedup |
   |---|---|---|---|
   | forward NTT, canonical (Shoup) | 1800 | 560 | 3.2x |
   | inverse NTT, canonical (Shoup) | 2210 | 600 to 650 | 3.4 to 3.7x |
   | pointwise product (2x Montgomery) | 390 | 155 to 165 | 2.4 to 2.5x |
   | forward NTT, lazy signed i32 + normalize | 1800 | 450 | 4.0x |
   | forward NTT, hand-written AVX2 on a shim | 1800 | 375 to 385 | 4.7x |

3. **Recommended path: Shoup NTT/NTT^-1 + Montgomery pointwise, one shared `#[inline(always)]` body compiled twice
   (portable and `target_feature = "avx2"`), runtime dispatch kept outside the proof.** About 2.5 to 3.5x on these
   kernels, no new axiom, no change to the NTT-level proofs' statements. Lazy reduction and hand-written AVX2 buy 20%
   and 35% more for a much larger proof bill (section 5).

## 1. `#[target_feature(enable = "avx2")]` on a safe fn

Crate `x1_tf/`, evidence in `evidence/x1-extraction.txt` and `evidence/x1-rustc-rules.txt`.

- rustc rules (checked on 1.81, 1.86 and the pinned nightly):
  - A *safe* `fn` with `#[target_feature]` needs Rust 1.86 or later; on 1.81 only `unsafe fn` is allowed (E0658).
  - Calling it from a fn without the feature needs `unsafe { }` (E0133, with the help text "requires avx2"). Calling it
    from a fn that has the same feature is safe.
  - It cannot be coerced to a safe fn pointer (E0308); only to an `unsafe` one.
  - `#[inline(always)]` cannot be combined with `#[target_feature]` (hard error). So the shape is: the shared body
    is `#[inline(always)]` (or generic), the feature-enabled entry point is a thin wrapper that calls it and inlines
    it, getting AVX2 codegen.
- Extraction: it works. Charon records the attribute in LLBC (`attr_info` has `Builtin::TargetFeature` with the
  feature list and spans, and `Builtin::Inline`); Aeneas ignores both. A `#[target_feature]` fn extracts exactly like
  the plain one, the `unsafe {}` call site disappears, and a wrapper becomes a plain call:

  ```lean
  def add_avx2 (a : Array Std.U32 8#usize) (b : Array Std.U32 8#usize) : RustM (Array Std.U32 8#usize) := do
    add_body a b
  ```

  So `body_avx2 = body` holds by unfolding. Const-generic `#[inline(always)]` bodies instantiated inside a feature fn
  extract fine too (`sum_n`).
- Consequence for the proof: the AVX2 clone costs nothing to prove (same Lean term). What the theorem cannot see is
  that rustc/LLVM compile the clone with different instructions; that is the same trust in the compiler already placed
  in the scalar build.

## 2. Dispatch: `is_x86_feature_detected!`, `__cpuid`, `cfg(target_feature)`

Crate `x2_dispatch/`, evidence in `evidence/x2-extraction.txt` and `evidence/x2-cfg-avx2-branch.txt`. All seven
shapes extract (rc 0); the Lean of `dispatch_std`, `dispatch_cpuid` and the intrinsic crates (`vadd`, `mulw`) compiles
against the pinned Aeneas library.

| shape | what Aeneas emits | axioms |
|---|---|---|
| `is_x86_feature_detected!("avx2")` | `let b ← std_detect.detect.arch.x86.__is_feature_detected.avx2; if b then body_avx2 a b else body a b` | 1 (`: RustM Bool`) |
| `__cpuid_count(7,0)` + bit test | `let r ← core.core_arch.x86.cpuid.__cpuid_count 7#u32 0#u32 ...` plus a `CpuidResult` structure | 1 |
| cached in an `AtomicU8` | atomic type and `new/load/store` axioms, `CACHE` global | 4 |
| `#[cfg(target_feature = "avx2")]` arms | resolved by rustc: only one arm exists. Without avx2 it is `body a b`, with `-C target-feature=+avx2` it is `body_avx2 a b` | 0 |
| `if cfg!(target_feature = "avx2")` | both arms type-check, the condition is a constant; the taken arm is emitted | 0 |
| `#[cfg(miri)]` twin (the `barrier_u64` pattern in `src/field.rs`) | the portable fn only | 0 |
| predicate in its own fn | `has_avx2 : RustM Bool` plus the std_detect axiom | 1 |

`scripts/extract.py` fails when `Funs.lean` references an external axiom, so the usable shapes are the `cfg` ones.
Two ways to put the shim in the proof:

- **Invisible (recommended):** `#[cfg(miri)] fn ntt(..) { ntt_body(..) }` and `#[cfg(not(miri))] fn ntt(..)` with the
  cached CPUID/XGETBV check and the `unsafe { ntt_avx2(..) }` call. The theorem is about the portable body; the shipped
  shim is five lines whose two arms call the same body. Zero axioms, the same pattern the crate already uses and
  documents for `barrier_u64`. The gap is that the shipped dispatch function is not literally the extracted one.
- **Visible:** let `is_x86_feature_detected!` extract (one axiom, `RustM Bool`) and prove the theorem for both
  outcomes: since `body_avx2` unfolds to `body`, the proof is `split` followed by the same lemma twice, with no axiom
  about the value. It costs an exemption in the extract.py axiom gate and does not make the claim stronger.

Practical notes: `__cpuid` traps on VMs (about 3.8 us per call on the box, twice an NTT), so the result must be cached
(`AtomicU8`, relaxed). Measured dispatch overhead with the cache is 3 to 8% over calling the clone directly (not
isolated further). A correct check needs CPUID leaf 7 EBX bit 5 *and* OSXSAVE plus `XGETBV` (YMM state enabled);
`x4_ntt/src/lib.rs::has_avx2` does all three. For `no_std`, `core::arch::x86_64::{__cpuid_count, _xgetbv}` suffice;
`std_detect` needs `std`.

## 3. `core::arch::x86_64` intrinsics and the SymCrypt model

Crates `x3_intrinsics/` and `x5_shim/`, evidence in `evidence/x3-extraction.txt` and `evidence/x5-extraction.txt`.

- **What Aeneas emits for an intrinsic call:** an opaque axiom per intrinsic, `core.core_arch.x86.avx2._mm256_add_epi32`,
  `..._mm256_mul_epi32`, `..._mm256_blend_epi32`, ..., with immediates as explicit arguments and `__m256i` as an
  opaque type (`core.core_arch.x86.__m256i`). A function using them extracts (`vadd` is
  `core.core_arch.x86.avx2._mm256_add_epi32 a b`) and Lean compiles. Using them would put 15 to 20 axioms into
  `FunsExternal`, which both fails the extract.py gate and makes the theorem conditional on them. Loads and stores
  through `*const __m256i` casts make Charon error ("Raw ptr casts are only supported between pointers to literal
  types"), so kernels cannot use `_mm256_loadu_si256(ptr as *const _)` directly either.
- **SymCrypt (`feature/verifiedcrypto`, c2e575a):** a cargo feature `verify` redirects the same intrinsic names to Rust
  shims over lane arrays (`src/verify/intrinsics/`). The shims are extracted by Aeneas and proved against a byte-level
  Lean register model, with differential tests against the hardware. Axioms remain only for AES-NI, SHA-NI, PCLMULQDQ
  and raw memory ops. CPU feature dispatch is a single axiom `cpu_features_present : U32 → Result Bool`. Their own
  AVX2 NTT path is marked experimental and disabled, so the modelling approach is demonstrated, the NTT use is not.
- **What I built:** `x5_shim` has 19 AVX2 operations as plain Rust over `[u32; 8]` (`shim.rs`, 223 lines: add, sub,
  mullo, `mul_epi32`, and, shifts, cmpgt, `shuffle_epi32`, `permute4x64`, `blend`, `permutevar8x32`, unpack,
  `permute2x128`, load/store from an array with an index, set1/setr), a `real.rs` (100 lines) binding the same names to
  `core::arch`, and one kernel (`kernel.rs`, 160 lines, the lazy NTT) written once and `include!`d against either set of
  names. Results:
  - The shim kernel extracts with **no new axiom** (only the four baseline `Step::*` ones) and the Lean compiles
    (`Types`, `FunsExternal`, `Funs` all rc=0).
  - Differential test, `x5_bench`: shim vs the real intrinsic on 296,080 randomized comparisons over the 19 operations
    and all 904 immediates used: 0 mismatches. Kernel: shim kernel vs the scalar lazy NTT bit-exact on 20,003
    polynomials, real kernel vs shim kernel 0 mismatches, canonical `ntt_vec` vs the crate's `ntt` 0 mismatches.
  - So the model of about 15 to 19 intrinsics costs about 220 lines of Rust and a day of test-driving, and no axiom,
    **but** the shim is a *definition* and the link "shim = hardware" is tested, not proved. That link is the residual
    trust (SymCrypt accepts it for the same reason). Proving the kernel itself on top of the shim (lane-wise
    arithmetic plus the permutation layout of the narrow layers) is the large cost, estimated below.
- **Cost of axiomatizing instead:** 15 to 20 one-line axioms are cheap, but then "unconditional" is lost, so I do not
  recommend it.

## 4. Why the crate's NTT does not vectorize, and what does

Crate `x4_ntt/` (verbatim copies of `src/field.rs` and `src/ntt.rs` checked with `cmp`, plus the rewrites),
`x4_bench/`, evidence in `evidence/x4-asm-report.txt`, `evidence/x4-bench.txt`.

**Diagnosis.** At `-C target-cpu=x86-64-v3` LLVM's loop vectorizer *does* vectorize the NTT loops (remarks: "vectorized
loop (vectorization width: 8)" at `src/ntt.rs:32,37,49,54,93,104,115,125`). But `barrett_reduce` multiplies a u64 by a
128-bit constant, and AVX2 has no 64 x 64 -> 128 multiply, so the vector body extracts each lane, does a scalar
`mulx`/`imul`, and reinserts: `ntt` has 1679 ymm instructions and still 400 `mulx`/`imul` (`ntt_inverse`: 1388 ymm,
296 scalar multiplies). The gain from v3 is only about 10% (1790 to 1615 ns). This matches the baseline report
(`docs/performance-baseline.md`, "no compiler vectorizes because of the u128 Barrett multiply").

**Rewrites tried** (all extract with Charon and Aeneas, rc 0; see `x4_ntt/src/`):

| variant | multiply | contract | notes |
|---|---|---|---|
| F `fold.rs` | three folds with 2^23 = q + 8191, u64 only | same as crate | needs 64-bit multiplies; slower at baseline (1990 ns), 1.5x for pointwise |
| S `shoup.rs` | `hi = (x*zp)>>32; r = z*x - hi*q` (mod 2^32), one conditional subtract | same as crate | `zp = floor(z*2^32/q)`, second 256-entry table; 32-bit only |
| M `mont2.rs` | two unsigned Montgomery steps, R = 2^32, then conditional subtract | `mul(a,b) = a*b % q` for a, b < q | for the pointwise product (both operands variable) |
| L `lazy.rs` | signed Montgomery, no reduction after add/sub | state is "bounded and congruent" until a final `normalize` | needs bound invariants (below) |
| hand `x5_shim` | as L, hand-written lanes and shuffles | as L | against the shim |

All variants are checked against the crate's functions: `fold_reduce` exhaustive below 2^31 plus 2e8 random;
`mul_shoup` for all 256 zetas, negated zetas and the scale factor, over all x < q plus 2e5 random x < 2^32 each;
`mont2::mul` all pairs of edge values and 4e8 random pairs; 20,004 polynomials (zero, q-1, 1, alternating, random)
through every forward/inverse/pointwise variant including the AVX2 clones: 0 mismatches everywhere.

**Measurements** (`evidence/x4-bench.txt`; `jobs/x4-bench.sh`; AMD EPYC 9B14 (Zen 4) VM, one idle physical core chosen
by `jobs/pick-cpu.py`, interleaved rounds across all variants, median of each; two repetitions agree within 3%):

Per 256-coefficient polynomial, ns, medians (range over the two repetitions where it differs):

| | default target (x86-64), clone | x86-64-v3 whole build |
|---|---|---|
| NTT: crate (Barrett u128) | 1800 | 1620 |
| NTT: F fold | 1990 plain / 1190 clone | 1180 to 1220 |
| NTT: S shoup | 1090 plain / **560 to 566 clone** | 555 to 594 |
| NTT: S shoup, narrow layers block-indexed | 1090 / 540 to 548 clone | 546 to 587 |
| NTT: L lazy + normalize | 1520 plain / **450 clone** | 430 to 438 |
| NTT: S shoup through the dispatch shim | 577 to 610 | 551 to 570 |
| NTT^-1: crate | 2210 to 2240 | 2280 to 2340 |
| NTT^-1: S shoup | 1170 to 1240 plain / **600 to 660 clone** | 583 to 600 |
| pointwise: crate | 385 to 394 | 386 to 397 |
| pointwise: M mont2 | 664 to 673 plain / **155 to 168 clone** | 154 to 166 |
| pointwise: F fold | 405 to 424 plain / 233 to 261 clone | 235 to 246 |

Hand-written AVX2 on the shim (`evidence/x5-bench.txt`, `jobs/x5-bench.sh`, same method):
lazy + normalize 375 to 387 ns (crate 1800), transform only 311 to 362 ns vs the autovectorized lazy clone 414 to 421.
Per layer (hand): LEN 128/16/8 about 22 to 25 ns, LEN 4: 57 to 63, LEN 2: 79 to 81, LEN 1: 46 to 48, so the three
narrowest layers are about 60% of the hand kernel. Autovectorized lazy, per layer at v3: LEN 128 to 8: 25 to 29,
LEN 4: 104, LEN 2: 74, LEN 1: 44. The same layers are where Shoup is slowest too (94, 97, 83, 57 vs 37 for wide layers).

Reading the table:
- Without AVX2 codegen the rewrites are not uniformly better: Shoup NTT is still faster than the crate (1090 vs 1800
  ns, 32-bit multiplies only), but F fold is slower (1990 ns) and M mont2 pointwise is 1.7x *slower* than the crate's
  scalar Barrett (664 vs 390 ns, two reductions instead of one). The pointwise win comes only from vectorizing, so the
  dispatched AVX2 clone (or a v3 build) is required for it.
- At v3 the "clone" rows equal the plain rows (already compiled with AVX2), as expected; the difference between
  default+clone and v3 is within noise.
- The dispatch shim (cached) costs 3 to 8% over a direct clone call.
- Caveats: one machine (Zen 4, 256-bit datapath, no AVX-512 used), a VM with other tenants (the box had load of 8 to
  10 during runs; interleaving and an idle-core pick bring repetition spread to about 3%), and kernels measured in a
  loop over a warm 1 KiB polynomial. I did not measure sign/verify end to end.

**Lazy-reduction bounds** (`x4_ntt/src/lazy.rs`; `evidence/x4-bench.txt` line "CHECK lazy bound"):
- Input canonical, `0 <= w < q`. Twiddles are centered Montgomery forms, `|z| <= q/2`, so the product `z*w` fits
  `i64` and satisfies `|z*w| < 2^31 * q`, which is the precondition of the signed Montgomery step.
- `mont(a) = (a - (a as i32 * QINV as i32) as i64 * q) >> 32` has `|mont(a)| <= |a|/2^32 + q/2`; with `|a| <= (q/2)*B`
  and `B <= 5.2q` this is below `q/2 + q/64`.
- After layer `l` (1 to 8): `|w| <= q + l*(q/2 + q/64)`, i.e. 1.52q, 2.03q, ..., 5.1q. Observed maxima over 10,000
  random inputs: 1.50q, 1.99q, 2.48q, 2.87q, 3.28q, 3.73q, 4.05q, 4.39q (the analytic bound is within about 1.2x).
- Everything stays below `2^31` by a factor of about 50 (5.1q is 4.3e7), and `normalize` (`t = (x + 2^22) >> 23;
  r = x - t*q; r += (r >> 31) & q`) is correct for `|x| <= 2^30`, so there is room to skip even more reductions, and no
  overflow obligation is tight. The obligations are: per-layer bound, per-lane congruence mod q, final normalization.

**Lean cost probe** (`lean/ProofsX4.lean`, compiles against the extracted `x4_ntt` Lean with the pinned Aeneas and
Mathlib; run `jobs/lean-proofs.sh`). Same style and statement shape as `lean/Proofs/Field.lean`:
- `fold.small_reduce` spec (same statement as the crate's), proved with `step*`.
- `mul_shoup_spec`: for `z < q`, `zp = floor(z*2^32/q)`, any `x : U32`, the extracted `shoup.mul_shoup z zp x` returns
  `(z*x) % q` and `< q`. About 45 lines plus a pure-Nat Shoup lemma (`mul_shoup_nat`, 30 lines).
- `mont_u_spec`: the extracted `mont2.mont_u a` satisfies `r < 2q` and `r * 2^32 % q = a % q`, with the number-theoretic
  core (`mont_div`, `mont_core`) by `omega`.
- Not completed: `fold_reduce` at the extracted level (`step*` times out; the arithmetic core `fold_nat` is proved by
  `omega`), the composition `mont2.mul` (two `mont_u` calls plus `small_reduce`), and the 256-entry table lemma
  `ZETAS_SHOUP[i] = ZETAS[i] * 2^32 / q` (expected `decide +kernel`, untested).
- Lean-side arithmetic cost, then: the field-level replacement is a few hundred lines. Nothing above `Field.lean` is
  touched if `mul` keeps its statement, except where the butterfly now takes `zp` from a table and needs the table
  lemma and `z < q` side conditions. The lazy variant changes the state invariant of every layer lemma
  (`NTT.lean`, `NTTInverse.lean`, `NTTOps.lean`, `CorrNTT.lean` are about 2,000 lines together) from "canonical" to
  "bounded and congruent".

## 5. Options, ranked by cost

All figures for the forward NTT unless stated. "Proof cost" figures are estimates, not measurements, except where the
Lean probe above covers them.

| option | speedup (fwd NTT / inv / pointwise) | new axioms | proof cost | other cost |
|---|---|---|---|---|
| **A. Shoup + 2x Montgomery, shared body, `target_feature` clone, `cfg(miri)` dispatch twin** | 3.2x / 3.4 to 3.7x / 2.4x | none | field lemmas (Shoup and Montgomery specs written; table lemma and `mul` composition open): a few hundred lines; layer proofs patched where the butterfly calls `mul` (about 1 to 3 days) | extra tables (about 2 KiB); ~60 lines of Rust for dispatch (cached CPUID + XGETBV, `unsafe` call to the clone); pointwise is slower than today on non-AVX2 CPUs (664 vs 390 ns), so keep the old `multiply_ntt` as the fallback body or accept it |
| B. A + lazy signed i32 NTT, inverse and pointwise | 4.0x measured / 4.3x / 5x (the last two are the baseline report's figures, not re-measured here) | none | bound invariants for 8 forward and 8 inverse layers, per-lane congruence, normalize; rewrites state of ~2,000 lines of NTT proofs; estimate 1 to 2 weeks | only +20% over A for the forward NTT; "bounded and congruent" intermediate state leaks into proof APIs |
| C. B + hand-written AVX2 kernel on the 19-op shim | 4.7x | none (shim extracted), link shim = hardware is tested only | kernel proof on lanes plus shuffle layout for the three narrow layers; estimate several weeks | +15% over B autovectorized; shim 220 lines, differential tests 904 immediates; a second code path to keep in sync |
| D. SymCrypt-style full model (`verify` feature redirect + Lean register model proved against byte semantics) | as C | few (SymCrypt: AES/SHA/PCLMUL only) | C plus the register model | largest; justified only if many kernels will use intrinsics |
| E. Axiomatize 15 to 20 intrinsics as in raw extraction | as C | 15 to 20 | C | **loses "unconditional"; not recommended** |
| F. Build-time `-C target-cpu=x86-64-v3` only (no dispatch) | 1.1x for the current code; 2.9x with A's rewrite | none | none beyond A | binary requires AVX2; incompatible with a portable crate |

**Recommendation: option A.** It reaches the 2 to 4x target on all three kernels, keeps the end-to-end theorem axiom-free
(the clone and the shim are invisible to Lean, and `body_avx2 = body` by unfolding), and leaves the proof statements of
NTT, NTT^-1 and pointwise unchanged. Add B later if the extra 20% on the forward NTT or the larger inverse/pointwise gain matters; skip C, D, E.

Rough end-to-end effect from the profile shares in `docs/performance-baseline.md` (NTT + pointwise 56% of sign-87,
33% of verify-87): applying 3.2x to NTT and 2.4x to pointwise gives about 1.6x for sign and 1.3x for verify. Add/sub are
already vectorizable and not included. This is arithmetic on someone else's profile, not a measurement; note also that
the baseline report projects larger gains for B (cached verify-87 about 40 us), and that is where C/B would matter.

## 6. Implementation notes for option A

1. Add `mul_shoup(z, zp, x)` and `mont2::mul` to `field.rs`; keep `field::mul` for non-hot paths.
   `small_reduce` is unchanged.
2. Make `ntt_layer` bodies `#[inline(always)]` and shared; add `#[target_feature(enable = "avx2")] fn ntt_avx2` that
   calls the body; dispatch in `ntt()` under `#[cfg(not(miri))]` with a cached `has_avx2()` (CPUID leaf 7 bit 5,
   OSXSAVE, XGETBV YMM bits). `#[cfg(miri)] fn ntt` calls the body, which is what Charon sees.
3. Table lemma `ZETAS_SHOUP[i] = ZETAS[i] * 2^32 / q`: generate the tables with a script like `x4_ntt/gen_tables.py` (no
   hand-copied constants); close the lemma by `decide +kernel` (untested) or by `norm_num` per entry.
4. Rust 1.86 or later is required for safe `#[target_feature]` fns; the pinned nightly is fine. Using `unsafe fn` instead
   works on older toolchains and extracts identically.
5. The zeta table for narrow layers gets indexed per block; a block-indexed layout for LEN <= 4 ("S shoup block-indexed",
   540 vs 560 ns) is a minor further gain.

## 7. Reproducing

Everything runs through `rx` from the worktree root; scripts are in `jobs/`.

```
rx run -- bash experiments/simd/jobs/x1-compile.sh              # rustc rules for target_feature
rx run -- bash experiments/simd/jobs/extract.sh x1 experiments/simd/x1_tf x1_tf
rx run -- bash experiments/simd/jobs/each-root.sh x2 experiments/simd/x2_dispatch x2_dispatch::dispatch_std ...
rx run -- bash experiments/simd/jobs/x2-avx2.sh                 # the cfg(target_feature) arm that has avx2
rx run -- bash experiments/simd/jobs/each-root.sh x3 experiments/simd/x3_intrinsics x3_intrinsics::vadd ...
rx run -- bash experiments/simd/jobs/x4-asm.sh && rx run -- bash experiments/simd/jobs/x4-asm-report.sh
rx submit simd-bench -- bash experiments/simd/jobs/x4-bench.sh  # forward/inverse/pointwise/layers, default and v3
rx run -- bash experiments/simd/jobs/x5-bench.sh                # differential tests + hand-written kernel
rx run -- bash experiments/simd/jobs/lean-check.sh simd-x5      # extracted Lean compiles
rx run -- bash experiments/simd/jobs/lean-proofs.sh simd-x4 ProofsX4.lean
```

`extract-mini.sh` runs one crate through the pinned `cargo hax extract generic` (Charon) and Aeneas with
`RUSTFLAGS="--cfg miri"`; override with `SIMD_RUSTFLAGS`. `evidence/` holds the raw logs with machine paths scrubbed.
Directory map: `x1_tf` (attribute), `x2_dispatch` (dispatch), `x3_intrinsics` (raw intrinsics), `x4_ntt` + `x4_bench`
(rewrites and measurements), `x5_shim` + `x5_bench` (AVX2 shim, kernel and differential tests), `lean/` (cost probe).
