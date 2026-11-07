# Fast verify, spike B: can a 4-way Keccak-f1600 be extracted and proved in our pipeline?

Branch `fv-spike-b` (based on `fast-verify` e132941). Status: **go**. The 4-way kernel is written once against a trait of lane-wise
operations, is extracted by the pinned Charon + Aeneas with zero new axioms, and the extracted shim instantiation is proved, for all four
lanes and all 24 rounds, equal to the extracted scalar `keccak::keccak_f1600`. The proof file elaborates in 34 s and 3.0 GB.

## What was built

| File | Content |
|---|---|
| `src/keccak4.rs` | `trait Lanes4`, `Shim4` (plain Rust over `[u64; 4]`), the unrolled `round<L: Lanes4>`, `keccak_f1600_x4<L>`, `keccak_f1600_x4_portable`, and `avx2::{Avx2, keccak_f1600_x4_avx2}` (feature `avx2`, x86_64, not Miri) |
| `scripts/gen_keccak4_round.py` | prints the body of `round` (the unrolled θ, ρ+π, χ, ι); the output is pasted into `src/keccak4.rs` |
| `scripts/extract-roots.txt` | two temporary roots: `keccak4::keccak_f1600_x4_portable` and the generic `keccak4::keccak_f1600_x4` |
| `lean/Impl/*` | re-extracted by `scripts/extract.py` (a structure, a type alias and 10 new function definitions) |
| `lean/Proofs/Keccak4.lean` | the proof (about 290 lines); `lean/keccak4-theorems.txt` is its axiom list |
| `tests/keccak4.rs` | differential tests and a sanity timing |

`src/keccak.rs` changes by one word: `RC` is `pub(crate)` so that the kernel uses the very same round-constant table as the scalar code.

## Kernel shape

State layout: `s: [[u64; 4]; 25]`, `s[k][i]` is lane `k = x + 5y` of state `i`. All vector values are `[u64; 4]` passed **by value**, so the
trait has no associated type and no raw register type appears in the extracted code.

```rust
pub trait Lanes4 {
    fn xor(a: [u64; 4], b: [u64; 4]) -> [u64; 4];
    fn andnot(a: [u64; 4], b: [u64; 4]) -> [u64; 4];            // !a & b, like _mm256_andnot_si256
    fn rotl<const L: u32, const R: u32>(a: [u64; 4]) -> [u64; 4]; // R = 64 - L, 0 < L < 64
    fn splat(x: u64) -> [u64; 4];
}
```

`round` is straight-line code (131 lane operations, 25 loads and 25 stores) with the scalar permutation's association order, so the Lean proof closes by `rfl` after
rewriting: `C[x] = (((a[x] ^ a[x+5]) ^ a[x+10]) ^ a[x+15]) ^ a[x+20]`, `D[x] = C[x-1] ^ rotl(C[x+1], 1)`, `b = rotl(a ^ D, ρ)` (ρ fused with the
θ xor and with π's placement), `a' = b ^ andnot(b1, b2)`, and ι as `xor(chi0, splat(rc))`. `keccak_f1600_x4` is a 24-iteration `while` loop around
`round`, with `RC[r]` from the crate's table.

The shim ops are literal four-element arrays (`[a[0] ^ b[0], ..., a[3] ^ b[3]]`), no loops. The real impl loads the array into a `__m256i`,
applies the intrinsic and stores it back. After inlining, LLVM's SROA removes the memory round trips: the `#[target_feature(enable = "avx2")]`
entry point `keccak_f1600_x4_avx2` compiles to one 342-line function with **no calls**, `vpsllq`/`vpsrlq` with immediates for all 24 rotations, 25
`vpandn`, 76 `vpxor` and 27 `vpor` in the round loop body.

Rotations use the variable-count intrinsics `_mm256_sll_epi64(v, _mm_cvtsi32_si128(L))`. The immediate forms `_mm256_slli_epi64::<L>` cannot take `L`
from an enclosing const generic on stable (generic const expressions), and LLVM turns the constant count into the immediate form anyway.

## What Charon/Aeneas make of it

Extraction runs generic (no `--monomorphize`), so a trait becomes a Lean **structure** and the kernel takes the instance as an explicit argument:

```lean
structure keccak4.Lanes4 (Self : Type) where
  xor    : Array Std.U64 4#usize → Array Std.U64 4#usize → RustM (Array Std.U64 4#usize)
  andnot : Array Std.U64 4#usize → Array Std.U64 4#usize → RustM (Array Std.U64 4#usize)
  rotl   : forall (L : Std.U32) (R : Std.U32), Array Std.U64 4#usize → RustM (Array Std.U64 4#usize)
  splat  : Std.U64 → RustM (Array Std.U64 4#usize)

def keccak4.Shim4 := Unit                       -- @[reducible]
def keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.xor (a b : Array U64 4#usize) : RustM ... -- one def per method, straight-line
def keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4 : keccak4.Lanes4 keccak4.Shim4 := { xor := ..., rotl := fun L R => ..., ... }  -- @[reducible]
def keccak4.round {L : Type} (Lanes4Inst : keccak4.Lanes4 L) (s : Array (Array U64 4#usize) 25#usize) (rc : U64) : RustM ...
def keccak4.keccak_f1600_x4_loop {L : Type} (Lanes4Inst : keccak4.Lanes4 L) (s) (r : Usize) : RustM ...   -- @[rust_loop]
def keccak4.keccak_f1600_x4_portable (s) : RustM ... := keccak4.keccak_f1600_x4 Shim4.Insts... s
```

* A method with const generics (`rotl<const L, const R>`) becomes a dependent function field `forall (L R : U32)`. This worked first time.
* Inside `round` every operation is `Lanes4Inst.xor a b`, `Lanes4Inst.rotl 36#u32 28#u32 a44`, and so on. For the shim instance the projection
  reduces by itself, so `@[step]` lemmas about the three concrete shim definitions fire without any unfolding of the instance.
* `round` extracts to a flat 180-binding `do` block. `step*` runs it in about 6 s and discharges the shift-range side conditions of the 29 rotations
  (`0 < L < 64`, `R = 64 - L` for literal arguments) by itself.
* Extraction report: `aeneas_errors 0`, `aeneas_warnings 0`, `external_axioms_referenced 0`; `llbc_fun_decls` 223 → 230, `lean_defs` 368 → 378.
* The AVX2 module is not seen at all: extraction uses `--no-default-features`, and the module is also `cfg(not(miri))`.
* `#[inline(always)]` is applied with the same `cfg_attr` condition `field.rs` and `ntt.rs` use (only in builds that have the second
  compilation). Without it, LLVM does not inline the generic kernel into the `#[target_feature]` wrapper.

### Rust-side findings

* **`#[target_feature]` + generics + `inline(always)`:** works. `keccak_f1600_x4_avx2` is a plain (non-generic) `#[target_feature(enable = "avx2")]`
  function that calls `keccak_f1600_x4::<Avx2>`. The generic kernel and the trait methods are `#[inline(always)]`; they inline into the
  target-feature caller, which has the superset of features. Trait impl methods cannot carry `#[target_feature]` themselves.
* **`unsafe`:** the `Avx2` impl needs `unsafe` blocks around every intrinsic and every load/store. That is true on 1.86 (MSRV) and on the pinned
  nightly 2026-08-18 and 1.99: the trait methods are not themselves `#[target_feature]`, so the calls are unsafe in every version. The only
  `unsafe` is in `mod avx2` (`#[allow(unsafe_code)]`), under `feature = "avx2"`; without the feature `forbid(unsafe_code)` still holds. `cargo +1.86.0
  build --features avx2` and the default build pass; clippy is clean for the new module (the entry point carries a `# Safety` doc).
* `Avx2` is a public type whose methods are only sound inside AVX2-enabled code. In a real integration it should be private (`pub(crate)`) and
  reachable only through the dispatching entry point; here it is public only for the differential tests.
* The portable instantiation is **slower than scalar** (see below). A shipped build must dispatch to the scalar permutation when AVX2 is absent,
  never to `Shim4`. `Shim4` exists to be extracted and to be the executable specification of `Avx2`.

## Differential tests (box, x86_64 with AVX2; `tests/keccak4.rs`)

`cargo test --release --features avx2 --test keccak4 -- --nocapture`:

```
portable x4 vs scalar: 20258 states, 0 mismatches
avx2 x4 vs shim vs scalar: 20258 states, 0 mismatches
shim ops vs intrinsics: xor, andnot, splat and 24 rotations, 4003 inputs each, 0 mismatches
test result: ok. 4 passed (incl. the ignored timing test run with --include-ignored)
```

States are random plus edge cases (all zero, all ones, 256 single-bit states). The 24 rotation amounts tested are exactly the 24 distinct `rotl::<L, R>`
the kernel uses (checked by script against the source), each with the `(L, 64 - L)` pair the kernel passes. `cargo test --release --test keccak4` (no `avx2` feature)
runs the portable test alone.

## Performance sanity (not a benchmark; shared box, release profile)

`cargo test --release --features avx2 --test keccak4 -- --ignored --nocapture`, best of 7 runs of 200k calls, ns per call (4 permutations):

| build | 4 × scalar | shim ×4 | AVX2 ×4 | AVX2 speedup |
|---|---|---|---|---|
| default flags | 1460 | 2018 | 489 | **2.99×** |
| nearcore `-Ctarget-feature=+sse2,...,+pclmulqdq` (no AVX2 baseline) | 1348 | 1790 | 499 | **2.70×** |

The "4 × scalar" figure includes gathering lane `i` out of the interleaved layout and scattering it back (a few ns). Spike A owns the real
numbers (ExpandA end to end, with transposes and the sampler).

## The proof (`lean/Proofs/Keccak4.lean`)

Statements, all `⦃ ⦄` weakest-precondition forms (no failure, no divergence):

| Theorem | Says |
|---|---|
| `shim_xor_spec`, `shim_andnot_spec`, `shim_splat_spec`, `shim_rotl_spec` | the extracted shim ops act lane-wise (`ln r j = ln a j ^^^ ln b j`, `~~~a &&& b`, `rotl`) |
| `round_lane` | for each `i < 4` and any `ir` with `toU64 rc = RCs[ir]!`: `pj (round s rc) i = Spec.Keccak.Rnd (pj s i) ir` |
| `round_spec` | the same for all four `i` at once, from a single run |
| `keccak_f1600_x4_shim_spec` | the 24-round loop: `pj s' i = Spec.KeccakF1600 (pj s i)` for every `i < 4` |
| `keccak_f1600_x4_portable_spec` | the same for the extracted portable entry point |
| `keccak_f1600_x4_portable_eq_scalar` | **for every `i < 4`, the extracted scalar `keccak.keccak_f1600` on `laneArr s i` returns `laneArr s' i`** |

`pj s i : Spec.Keccak.State` is state `i` of the interleaved state, `laneArr s i : Array U64 25#usize` the same thing as the extracted scalar's
`[u64; 25]`; `toLanes_laneArr` ties them together, and the last theorem composes with the existing `keccak_f1600_spec`.

Proof strategy, which is what the ExpandA work would reuse:

1. **Ops.** Each shim op returns `Array.make 4 [f x0 y0, ..., f x3 y3]`; `step*` gives the four lane equations, `rcases j = 0 ∨ 1 ∨ 2 ∨ 3` and `simp`
   close them (the same `xor_of_bv`/`and_of_bv`/`not_of_bv` bridge lemmas as `KeccakPerm.lean`; a new `rot_of_bv` for the rotation).
2. **Round.** `unfold keccak4.round; step*` leaves one goal. After `intro k`, a 25-way split, and one `simp` with the ~190 `_post` hypotheses of
   `step*` and a few lemmas, the left side becomes a closed scalar expression in `ln (at4 s k) i`. The right side is `Spec.Keccak.Rnd` unfolded by a
   new explicit formula `rnd_getElem` (`XV`, `Bf`, `Dv'`, built from `KeccakPerm.lean`'s `theta_getElem`, `rho_getElem`, `pi_getElem`, `chi_getElem`).
   The two sides are syntactically equal because the kernel keeps the scalar association order. Two small facts were needed: `rotl v 0 = v` (lane 0 has
   ρ offset 0) and a table `rhoOffsets = #[0, 1, 62, ...]` by `decide +kernel`.
3. **Loop.** `loop.spec_decr_nat` with invariant `∀ i < 4, pj s i = (List.range r).foldl Rnd (pj s₀ i)`, exactly the shape of `keccak_f1600_spec`.
   `round_spec` returns all four lanes from one run (via `round_lane` at `i = 0` and determinism), so the loop needs no per-lane bookkeeping.

Lean cost (box, Lean v4.31.0, one thread per file): `Proofs/Keccak4.lean` (about 290 lines) takes **34 s wall and 3.0 GB peak** including the import of `Proofs.KeccakPerm`
(whose own compile is separate). `round_lane` is most of it (Lean profiler, cumulative: `simp` 21 s, almost all of it the 25 big `simp` calls of `round_lane`; `step*` 6 s on the 180-binding round; `dsimp` 1.2 s; `grind` 0.8 s; import 1.4 s). There is no `sorry`, `native_decide`, `axiom`, `opaque`, `implemented_by` or `extern`; only `maxHeartbeats 4000000` on `round_lane`.

Gates (box):

* `bash scripts/lean-check.sh` → `Build completed successfully (3325 jobs)`, `checked: 790 reported: 790 axioms used: ['Classical.choice', 'Quot.sound', 'propext']`,
  `AXIOM GATE OK`, `LEAN CHECK OK:` (wall 16 min, peak 40.8 GB RSS). The 790 includes the 10 new extracted `Impl.keccak4.*` definitions.
* `bash scripts/check-axioms.sh --list keccak4-theorems.txt --no-impl` → `checked: 9 reported: 9 axioms used: ['Classical.choice', 'Quot.sound', 'propext']`.
* `bash scripts/witness-check.sh` → `Build completed successfully (3321 jobs)`, `checked: 146 reported: 146`, `AXIOM GATE OK`, `WITNESS CHECK OK: Proofs.TopWitnessCorrect` (wall 41 min, peak 46.1 GB RSS).
* `python3 -I scripts/extract_hash.py check` → `extract hash OK`.
* `lean/headline-theorems.txt` is unchanged.

## Recommendation: go

### Kernel and trait

Keep this shape. The trait is small (4 ops), the vector type is a by-value `[u64; 4]`, there is no associated type, the instance is an ordinary Lean structure
argument, and the proof never needs to look inside an instance (only at the shim's four definitions). The real impl is free to be anything that is
lane-wise equal to the shim; the claim is "proved modulo the intrinsic models", with the shim ≡ hardware link tested (this spike: 24 rotations ×
4003 inputs, plus 20k full states), not proved.

One design point to decide before building on it: the ExpandA needs two more lane-wise primitives only if the transposes are vectorized (loads and
stores of `[[u64;4];25]` ↔ byte buffers). Do **not** add them. Pack and unpack in plain Rust over `[u64; 4]` (the extractor handles it, the existing
`load_lane`/`store_lane` lemmas apply), and let LLVM vectorize it or not; it is a small part of the cost.

### ExpandA-4way: shape and proof plan

Rate 168 = 56 × 3 bytes, so a SHAKE128 block holds exactly 56 whole 3-byte candidates and **no candidate ever straddles a block boundary**. That makes a
block-synchronous sampler exactly equal to the byte-wise one:

1. For 4 seeds `ρ‖s‖r`, build the padded first block directly in the interleaved state (seed bytes 0..33, `0x1F` at byte 34, `0x80` at byte 167) with plain Rust.
2. Loop: `keccak_f1600_x4`; then for each lane run the scalar candidate loop over the 56 triples of the 168-byte block (accept while that lane's `j < 256`);
   stop when all four lanes have `j = 256`. Lanes that are done just idle (their permutation work is wasted but harmless). K·L is 16, 30, 56 for ML-DSA-44/65/87,
   so the last group of 4 is padded with a repeated seed whose output is discarded.
3. Proof, per lane `i`, reusing what exists:
   * *Seed to state:* `pj s₀ i` is the absorbed-and-padded state `Spec.Keccak.absorb`/`pad101` produces for `M = ρ‖s‖r`. This is the one new Sponge-level lemma
     (the existing `ShakeAbs`/`ShakeSqz` relations in `KeccakSponge.lean` are phrased on `Impl.keccak.Shake`, whose `finalize` also permutes; the new lemma stops one step earlier).
     Estimate (not measured) 150–250 lines.
   * *Block b is stream bytes [168b, 168(b+1)):* from `keccak_f1600_x4_portable_spec` plus `Spec.Keccak.squeeze` unrolled; 100–200 lines.
   * *Block sampler = `stepA` fold:* the invariant of `SampleA.rej_body_spec` (`stA T n` over triples `n`) carries over to a nested loop (blocks × 56 triples).
     The triple index is `56 b + t`, the fold lemmas `stA_succ`, `stA_stable`, `triple_bytes` are reused as they are. Estimate 300–500 lines.
   * *Termination:* the same `RejTerm` premise (`expandA_isSome`), now per group of four: the loop runs `max` of the four lanes' fuels, bounded by the existing
     per-poly fuel; 100–150 lines.
   * *Assembly:* `expand_a_spec` is a nested loop over (r, s) with an `Option` fold; grouping four consecutive (r, s) per call changes the loop structure and the
     `ReprMat` write-back (`ReprMat.set'` four times). Estimate 250–400 lines.
   Total, as an estimate from the sizes of the templates: **about 900–1500 lines of Lean and 2–4 days of proof work**, with no new proof technology: every ingredient has a template in `KeccakPerm`, `KeccakSponge`
   and `SampleA`. The permutation, the part with the most arithmetic, is done and costs 34 s.
4. Verify integration (`verify.rs::expand_a_into` already writes into `&mut a`) is a drop-in: same output, `Repr` statement unchanged.

### Main risks

1. **Dispatch trust and the scope of the claim.** The AVX2 build is "proved modulo intrinsic models". The tested link (shim ≡ intrinsic, 24 rotations
   × 4003 inputs, 20k states) plus the 342-line inlined body is real but not a proof; BINSEC cannot lift AVX2 either (`docs/object-code-assurance.md` 3.5). Say so in the same
   words as the NTT dispatch. The portable build stays literally the proved code.
2. **Performance of the whole ExpandA, not just the permutation.** 2.7–3.0× on the permutation is promising but ExpandA also has packing, 168-byte block
   reads and the (data-dependent, 99.9% accepting) triple loop. A polynomial needs about 256.3 triples on average, so 5 blocks (280 triples) nearly always
   and a sixth essentially never; lanes therefore stay in step and little permutation work is wasted. Spike A should measure end-to-end before the
   proof work starts.
3. **`inline(always)` and register pressure.** The whole round is straight-line code on 25 live `ymm` values, so it spills (112 stack references in the
   loop body), which is what the numbers above already include. A future compiler may change what SROA does with the by-value `[u64; 4]`s. A bench regression test
   (not just correctness tests) would catch it. If it ever breaks, the fallback is an associated `type V: Copy` (`__m256i` in the real impl), which costs one more
   structure field type in Lean and nothing in the proofs of the ops.
4. **Lean elaboration.** `round_lane` needs `maxHeartbeats 4000000` (it ran well under that, but 200k, the default, is not enough for `step*` on 180 operations). A larger fused kernel
   (for example a 4-way round with the sampler inlined) should be expected to scale at least linearly in operation count; keep the permutation a separate function.
5. **Process.** The `lean-check` gate peaked at 40.8 GB here; this spike adds about 35 s to it and nothing to its peak memory.

## Reproduce

```sh
# kernel + tests (box)
rx run -- 'cargo test --release --features avx2 --test keccak4 -- --nocapture --include-ignored'
rx run -- 'cargo +1.86.0 build --features avx2 && cargo +1.86.0 build'
# extraction (writes lean/Impl on the box; fetch it in the same job, a later rx run overwrites the box copy)
rx run -- 'python3 scripts/extract.py >&2 && tar -C lean/Impl -cf - . | base64 -w0' | tail -n1 | base64 -d | tar -C lean/Impl -xf -
python3 -I scripts/extract_hash.py check
# proofs and gates (box)
rx submit gate -- 'bash scripts/lean-check.sh; bash scripts/check-axioms.sh --list keccak4-theorems.txt --no-impl'
```
