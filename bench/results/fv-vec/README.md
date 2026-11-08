# fv-vec: a plain-Rust 4-way Keccak that LLVM vectorizes

Research on `fv-vec` (from `fast-verify` 3b79427). Question: can the fast verify run only proved plain Rust, with no
`Avx2` intrinsics, compiled inside the existing `#[target_feature(enable = "avx2")]` wrappers?
Measured on the Linux build box with the nearcore target features. Nothing here is merged, pushed or proved in Lean.

## Answer: yes

Write the permutation as a loop over the four states around a straight-line scalar body, and let LLVM's **loop**
vectorizer (not the SLP vectorizer) widen it:

```rust
pub fn keccak_f1600_x4(s: &mut [[u64; 4]; 25]) {          // s[k][i] = lane k of state i
    let mut r = 0;
    while r < 24 {
        let mut i = 0;
        while i < 4 { lane_rounds2(s, i, RC[r], RC[r + 1]); i += 1; }   // unit stride in i
        r += 2;
    }
}
fn lane_rounds2(s, i, rc0, rc1) {  // 25 loads s[k][i], two calls of `round25(&[u64; 25], rc) -> [u64; 25]`, 25 stores }
```

`round25` is generated straight-line scalar code (`scripts/gen_keccak4_round.py`, same operations and association order as
the scalar `keccak_f1600`). The kernel is ordinary safe Rust: no intrinsics, no `core::arch`/`core::simd`, no `unsafe`,
no `black_box`, no inline asm, no trait. Both functions are `#[inline(always)]` exactly where the old kernel was.

Evidence, standalone permutation in a `#[target_feature(enable = "avx2")]` function (`lab/`, `lab-table.txt`):
the loop body is **528 instructions for two rounds, 519 ymm, 0 scalar rotates: the same count, and the same mix
(152 vpxor, 42 vpsllq, 54 vpsrlq, 4 shuffles), as the intrinsic `Avx2` instance (528 / 519)**.

| ns per 4-way permutation (`lab-table.txt`) | rustc 1.86.0 | 1.95.0 | 1.99.1 (current stable) |
|---|---|---|---|
| `Avx2` intrinsics (fast-verify) | 393.9 | 388.4 | 387.7 |
| **new kernel (`lq2` in the lab = the crate's shape)** | **395.0** | **387.8** | **387.3** |
| `Shim4` unchanged (the spike) | 1255.8 | 1254.4 | 1254.8 |
| 4 x scalar `keccak_f1600` | 1266.7 | 1280.4 | 1284.3 |

rustc 1.98.1 was run in earlier, separate lab runs (not in `lab-table.txt`): `ld2`/`lq2` about 394 ns, same asm shape. All measured toolchains are within 1.5% of `Avx2`.

## Integration (this branch)

`src/keccak4.rs` is rewritten; `Lanes4`, `Shim4`, `keccak4::avx2` (all intrinsics) and the `<X: Lanes4>` parameter of
`sampling`/`verify` are gone. The dispatch wrappers call `verify_internal_x4::<K, L>` etc. directly. Every function keeps its
behavior (one change: `absorb_block_lane3` xors `w` into lane 3 with `st[k][3] ^= w` instead of `st[k] = xor(st[k], [0,0,0,w])`;
lanes 0 to 2 were xored with 0). The crate's only remaining `unsafe` is the dispatch (call of a `#[target_feature]` function
after `has_avx2`) and the NTT dispatch.

- **Tests:** `ML_DSA_REQUIRE_AVX2=1 cargo test --release --features avx2,internals`: all pass (the equivalence tests now compare the
  AVX2 compilation with the portable compilation and with four scalar permutations on 150,000+ states; the lane-operation tests are
  gone with the lane operations). Default-feature `cargo test --release`, MSRV 1.86 builds (`--release`, `--features zeroize,avx2`)
  and the thumbv7em build pass.
- **Extraction** (scratch, `scripts/extract.py`, pinned Charon/Aeneas): `extract-report.json`: aeneas_errors 0, aeneas_warnings 0,
  local_opaque_funs [], external_axioms_referenced 0, 271 LLBC functions, 483 Lean defs.
- **End to end** (`bench/ab.sh`, interleaved; `ab-summary.txt`, raw `bench-final.txt`): fast-verify
  `Avx2` vs this branch, microseconds. ML-DSA-65 one-shot verify 38.46 -> 38.55 (pad 0), 38.47 -> 38.55 (672), 38.46 -> 38.43 (2752);
  `verifying_key_65` 28.51 -> 28.73, 28.53 -> 28.70, 28.54 -> 28.73. Every cell (44/65/87, one-shot, `verifying_key`, prepared)
  at all three pads is within 1.1% of fast-verify, and on rustc 1.95.0 (pad 0) within 0.8%. Prepared verify is unchanged, as expected.
  (The bench crate needs rustc >= 1.87, so there is no end-to-end run on 1.86.0.)
- **Stack scan** (`bench/stackscan.sh check`, 129 paddings, sets 44/65/87, verify/vk/prepared): max/median <= 1.03, STACK SCAN OK.

## Experiments

All are `#[target_feature(enable = "avx2")]` functions compiled with nearcore flags and `-O3` (release, 1 CGU), checked for correctness
against 4 x scalar (except the `norot` probes, which are wrong on purpose). `ins/ymm/rol` are from the asm of rustc 1.95.0 (the same on
1.99.1 unless noted); ns per 4-way permutation on 1.86.0 / 1.95.0 / 1.99.1. Source: `lab/src/v.rs`, `lab/src/lanes.rs`.

| id | Rust shape | vectorized? (ins / ymm / scalar rot) | ns 1.86 / 1.95 / 1.99 |
|---|---|---|---|
| `avx2` | intrinsics (reference) | yes (528 / 519 / 0) | 394 / 388 / 388 |
| `shim` | fast-verify's `Lanes4` over by-value `[u64; 4]` (the spike) | no (2091 / 0 / 232 rorx) | 1256 / 1254 / 1255 |
| `rotl_x`, `xor_x`, `add_x` | same, rotate written `rotate_left`, `^`, `+` instead of `\|` | no, identical to `shim` (LLVM re-forms the funnel shift) | 1255 each |
| `norot_x` (probe, wrong results) | same, every rotate replaced by identity | yes, partly (618 / 397 / 0, 178 xmm, 73 shuffles) | 412 / 496 / 340 |
| `nod_x`, `norho_x` (probes) | only theta's rotate-by-1 removed / only rho's removed | no (2044, 1928) | 1250 / 1165 |
| `noinl` | `round` out of line (`inline(never)`), so its stores to `dst` are real stores for SLP | 1.95/1.99: no (1060 / 0 / 116). 1.86: partly (396 / 291 ymm / 127 xmm) | 738 / 1748 / 1748 |
| probes `t_*`, `p_*`, `rows_N` (`lab/src/t.rs`, `rows.rs`) | pieces of the round, out of line, store seeds | a lone rotate: no. xor then rotate: yes. theta alone: yes. theta + 1 row: yes. 2 rows: partly. 3+ rows: no | - |
| `passes` | hypothesis 3: separate theta / rho-pi / chi loops over memory-resident `[[u64;4];25]` | partly (606 / 206 / 138 xmm, 80 shuffles) | 2839 / 2925 / 2931 |
| `lv_for` (`ld1`) | the new shape, 1 round per state iteration | yes (326 / 317 / 0) | 446 / 413 / 413 |
| `lvl1`, `lvl2b` | new shape with the crate's *loop-form* scalar round (`while` loops, RHO table) | yes but worse (352 / 343; 631 / 622) | 609 / 465 / 465; 684 / 475 / 475 |
| `lvl2` | same with an inner `while j < 2` over rounds | no (inner loop is what gets vectorized; 295 / 0 / 29 rol) | 1506 / 1506 / - |
| `lv2` | new shape, gather/scatter by `while` loops into `[u64; 25]`, `rs(&a, &mut o, rc)` twice | yes (529 / 520 / 0) | 396 / 388 / 387 |
| `ld2` | new shape, 25 `let a_k = s[k][i]` loads, 2 straight-line rounds on locals, 25 stores | yes (528 / 519 / 0) | 395 / 388 / 387 |
| `ld4` | 4 rounds per state iteration | yes (959 / 950 / 0) | 393 / 388 / 387 |
| **`lq2`** | **new shape, `round25(&[u64;25], rc) -> [u64;25]` called twice (adopted)** | **yes (528 / 519 / 0)** | **395 / 388 / 387** |

Extra robustness probes on the lab kernel (`lq2`/`ld2`; 1.86.0 and 1.99.1): `-Copt-level=2` and `-Ctarget-cpu=x86-64-v3` are as fast as `Avx2`
(387-395 ns). **`-Copt-level=s` is not vectorized (1368 ns, 58 scalar rotates)** while the intrinsic version is unaffected: a size-optimized
build of the library would silently be 3.5x slower on the verify path. nearcore builds at opt-level 3; the CI check below fails on it.

## Why LLVM refuses the old shape, and why the new one works

SLP remarks (`-Cremark=slp-vectorizer`, rustc 1.95.0): the only SLP "missed" remarks are horizontal-reduction attempts on the xor
chains ("not beneficial with cost 355..493"); store-seeded trees for the round are silently dropped. Bisecting with probes: the same
code **with the rotations replaced by identity vectorizes** (`norot_x`: 412 / 496 / 340 ns), a rotate by itself is kept scalar
(`t_rot`: four `rorx` beat vector shl+shr+or in the cost model), and a rotate behind an xor is vectorized; with the full round, trees
for the first row or two vectorize with near-zero gain (costs -1 to -5, each extracting shared scalars `d_x` for the unvectorized rows)
and the rest never pays off. No spelling of the rotate helps (`rotate_left`, `^`, `+`, shifts split across trait methods: instcombine forms the same
funnel shift), nor does making the round out of line on 1.95+. I could not read the SLP cost trace (release LLVM has no `-debug-only`), so the
exact cost numbers behind "not beneficial" are unconfirmed; the rotate dependence is established by the probes.

The loop vectorizer has no such tree-by-tree greedy step. It costs the whole loop body for VF=4 against 4 x the scalar body, sees
unit-stride loads and stores (`s[k][i]`, `i` the induction variable, `noalias` from `&mut`), and widens every instruction; a vector
rotate (shl + shr + or) is a small part of ~330 operations per round. After vectorization the 12-iteration round loop keeps the 25 state
vectors in registers/spill slots exactly as the intrinsic version does, so the instruction stream is the same (528 vs 528).
The state loop has trip count 4 and a body of ~500 instructions, so the full unroller (which would hand it back to SLP) does not fire.

## CI regression check (implemented)

`scripts/check-avx2-inlining.sh` (run by `scripts/ci.sh avx2-inlining`; `TOOLCHAIN=<tc>` selects the compiler) now requires, in each of the six
`verify_internal_avx2` / `prepare_vk_avx2` instantiations (K = 4, 6, 8), a `vpsllq $N, %ymm` for each of the 21 rho/theta rotation amounts
that LLVM implements as a shift (62 28 27 36 44 6 55 20 3 10 43 25 39 41 45 15 21 18 2 61 14; the other three are an add and byte shuffles).
A scalar (`rol`/`rorx`) or SSE-width permutation has none, so the check fails with `the 4-way Keccak permutation is not vectorized in a wrapper`.
It replaces the old guard against out-of-line `_mm256_*` wrappers (there are no intrinsics left) and keeps the inlining, ymm-volume and
stack-realignment checks. Results: passes on 1.86.0, 1.95.0, 1.98.1 and 1.99.1; it **fails** (negative test) when the loop over the four states
is hand-unrolled into four calls, which defeats the loop vectorizer. `ci.sh` also runs `scripts/gen_keccak4_round.py --check` (the generated block of
`src/keccak4.rs` is current). Suggested extra matrix entries: run the script under `TOOLCHAIN=1.86.0` (MSRV) and the nearcore toolchain, and on
every compiler bump of the pinned nightly.

## Proof impact (not done; estimate)

Compared with today's `Keccak4.lean` (294 lines, plus ~40 `Sh4` mentions elsewhere):

- **Deleted:** the four lane-operation specs (`shim_xor/andnot/splat/rotl_spec`, `ln_make4`, ~100 lines) and the `attribute [local step]` lines
  (`TrLaneRust.lean:17` has one too); `keccak_f1600_x4_portable_spec`, the generic
  instance `Sh4` and the `Lanes4` parameters in every theorem statement.
- **Kept as is:** `St4`, `pj`, `at4`, `at4_set`, `iota_getElem`, `rhoOffsets_eq`, `Dv'`, `Bf`, `XV`, `Bf_eq`, `rnd_getElem`, `rot_of_bv`,
  and the final bridge to the extracted scalar `keccak_f1600` (`keccak_f1600_x4_portable_eq_scalar`, now about the plain kernel).
- **New:** (1) `round25_spec`: `round25 a rc ⦃ o => toLanes o = Rnd (toLanes a) ir ⦄`. This is `round_lane` with the lane vectors and trait steps
  removed (same 25-case `simp` against `XV`/`Bf`/`Dv'`; U64 operations are bridged with the existing `xor_of_bv`/`and_of_bv`/`not_of_bv`/`rot_of_bv`),
  plus one lemma that the 25-element array literal reads back its elements (like `ln_make4`, for 25). Easier than before: no `ln`/`pj` projections inside the round.
  (2) `lane_rounds2_spec`: 25 loads, two applications of (1), 25 stores; the result projects to `Rnd (Rnd (pj s i))` on state `i` and leaves the other
  three states unchanged. Needs a 2-D update lemma (`s[k][i] = v` as `at4_set` then an inner update), ~30 lines. (3) The loop theorem: the existing
  `loop.spec_decr_nat` proof gains an inner loop over `i` with the invariant "states `< i` advanced two rounds, the rest unchanged" (~40 lines).
  Estimate: 250 to 350 new lines in `Keccak4.lean`, so the file ends up about the same size or a little smaller.
- **Mechanical edits:** `Sample4.lean` (4 `Sh4` mentions), `ExpandA4.lean` (10), `FastVerify.lean` (8), `TrGroup.lean` (5), `TrOuter.lean` (8): drop the `Sh4` argument and rename `keccak_f1600_x4_shim_spec` to the new spec name (same statement).
  `Sample4Block.lean` and `TrLane.lean` have no mentions.
- **Re-proved:** `absorb_block_lane3_spec` in `TrLaneRust.lean` (lines 193 to ~247), because `absorb_block_lane3` now does `st[k][3] ^= w`
  instead of a lane-vector xor with `[0,0,0,w]`; the proof gets simpler (lanes 0 to 2 are untouched by construction) but it is a re-proof.
- **Regenerate** `lean/Impl` (Funs.lean changes), `lean/keccak4-theorems.txt`, `lean/fast-verify-theorems.txt` and the extract digest.
- Rough size: 1 to 2 days of Lean work, 400 to 600 changed or new lines, low risk; nothing uses a new technique. One possible snag is `simp`
  time on the 25-case goal, which is why the Rust has `round25` as its own function (one round per proof, not two).
- Option: the scalar `keccak_f1600` could call `round25` too, which would share one round proof between the scalar and 4-way paths and let
  `KeccakPerm.lean`'s theta/rho/chi loop proofs go; not done (it changes proved scalar code and its benchmarks).

What the proof still cannot say: that LLVM vectorizes. Correctness of the AVX2 compilation is the compiler's translation of the proved source
(the same trust as for every other Rust function), checked here by differential tests and by the asm check above.

## Uncertain / not done

- The rotate explanation is from bisection probes, not from the SLP cost trace.
- Only the fast-verify wrappers were measured end to end (rustc 1.99.1 at three pads, 1.95.0 at pad 0). There is no end-to-end run on 1.86.0 (the bench
  crate needs 1.87); on 1.86.0 the evidence is the standalone permutation (395.0 vs 393.9 ns) and the asm check on the real library (vector in all six wrappers).
- Vectorization is a heuristic. A future LLVM could regress it; it did not on the four rustc releases tested. Size-optimized builds regress (see above).
- On x86 machines without AVX2 the dispatch uses the scalar path, as before. The portable (non-AVX2) compilation of the new kernel is not used by any API
  path, only by the tests and the extraction.
- Docs (`docs/assurance.md`, `docs/limitations.md`, `docs/object-code-assurance.md`, README, CHANGELOG), `lean/` and `lean/Impl` were not updated;
  they still describe `Avx2`/`Shim4`. The extract digest in `lean/Impl/extract-report.json` is stale on this branch by construction.
- `bench/results/2026-11-07-p*.md`, `bench/keccak4.sh` and the `checkct` driver reference the old kernel only in comments, except `checkct`, which `#[path]`-includes
  the real `src/keccak4.rs` and was not built here.

Files: `lab/` (standalone crate with every variant, `tools/run.sh TOOLCHAIN [variant...]` for asm + timing), `lab-table.txt` (raw), `ab-summary.txt`,
`bench-final.txt` (raw A/B and scan output), `stackscan.txt`, `extract-report.json`.
