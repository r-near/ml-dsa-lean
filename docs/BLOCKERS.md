# Extraction blockers on upstream master (`a3690c4`), sign and verify closures

Toolchain: cargo-hax 0.4.2 (driver only), Charon nightly-2026.09.02, Aeneas build-183e4f0 run directly, `--cfg miri`,
no default features, `--monomorphize`. Opaque by flag: `ml_dsa::crypto` (accepted SHAKE wrapper) and `hybrid_array`
except `hybrid_array::Array`. Roots are `cfg(hax)` call-through wrappers appended to a run copy of master (extraction
only; master itself is unchanged). Runs: `logs/master-{sign-open,verify-open}` and the single-root ML-DSA-44 runs
`logs/master-r-*`.

## How the list was built, and its limits

- **Aeneas-observed** (`logs/*/classified.json`, from `tools/classify.py`): every "Could not translate" diagnostic,
  grouped by definition span.
- **Static inventory** (`logs/*/inventory.{txt,json}`, from `tools/inventory.py`): walks the Charon LLBC call graph from
  the roots and lists every local (ml-dsa or module-lattice) function that calls an iterator adapter, closure,
  `hybrid_array::from_fn` or `flatten`, or that is an operator-trait impl. This catches constructs Aeneas never reached.
- Every master run that touches SHAKE, NTT or matrix code ends with `Uncaught exception: Not_found` during
  post-processing of transparent functions, after the translation errors (B-X1). Aeneas therefore never reports on
  every function, so the inventory is the complete list. One exception: closure bodies reached only through
  `FnMut::call_mut` are not followed (for example `rej_ntt_poly` under `expand_a`'s closure). Those were added by hand
  from the campaign's earlier lanes and from the source-identity check (`diff/fn-identity.md`).
- `for i in a..b` range loops are **not** counted as blockers. They extract, but they pull four `core::iter::range::Step`
  default methods into `FunsExternal_Template.lean` as unreferenced axioms. The campaign still factored one away
  (F-BALL). The fork avoids them.

**Count before:** 35 distinct Rust source locations in the sign and verify closures:
- 29 from the inventory: B-A1..A19, B-B1..B8, B-C1 and B-C3;
- 5 seen only by Aeneas: B-C2, the two spans of B-C4, B-O1 and B-O2;
- 1 added by hand: B-S1.

On top of these come the `hybrid_array` trusted-model family (B-O4) and three tool-level failure modes (B-X1..B-X3).
B-O3 is a second symptom at B-A14's location. **Count after, in `fork-skeleton/`:** 0 locations. Aeneas exits 0 with no errors or warnings, `lake build`
succeeds, and all 180 extracted definitions use only `propext`, `Classical.choice` and `Quot.sound`
(`logs/master-fork-generic/lake.log`). Step 4 (factoring master itself) was not done, so there is no "after" count for
master (see `patches/README.md`).

Fields per entry: location; construct; minimal rewrite (as the fork writes it, which is also the minimal upstream
rewrite); where it lives; diff size if done upstream; a maintainer-facing justification; whether a campaign lane-copy
factoring already exists.

## A. Iterator chains over `hybrid_array` (`iter().map().collect()`, `zip`, `fold`, `sum`) — TOOL-12

All of these fail with `[Error] Unimplemented` (`interp/Interp.ml:617`, "Could not translate the function signature of
`Iterator::map`") or an internal error at the closure signature. The rewrite is the same everywhere: write a
`while i < N` loop over the fixed-size array, with an explicit output array.

| ID | Location (master) | Construct | Where | Diff | Justification | Existing factoring |
|---|---|---|---|---|---|---|
| B-A1 | `ml-dsa/src/algebra.rs:200` `AlgebraExt for Polynomial::mod_plus_minus` | `iter().map(mod_plus_minus).collect()` | ml-dsa | ~6 | coefficient-wise loop matches FIPS notation | none |
| B-A2 | `algebra.rs:204` `Polynomial::infinity_norm` | `iter().map(infinity_norm).fold(ct-max)` | ml-dsa | ~7 | explicit CT max is easier to audit for checkct | none |
| B-A3 | `algebra.rs:222` `Polynomial::high_bits` | map/collect | ml-dsa | ~6 | as B-A1 | none |
| B-A4 | `algebra.rs:231` `Polynomial::low_bits` | map/collect | ml-dsa | ~6 | as B-A1 | none |
| B-A5 | `algebra.rs:242` `Vector::mod_plus_minus` | map/collect over polys | ml-dsa | ~6 | as B-A1 | none |
| B-A6 | `algebra.rs:246` `Vector::infinity_norm` | map/fold | ml-dsa | ~7 | as B-A2 | none |
| B-A7 | `algebra.rs:264` `Vector::high_bits` | map/collect | ml-dsa | ~6 | as B-A1 | none |
| B-A8 | `algebra.rs:273` `Vector::low_bits` | map/collect | ml-dsa | ~6 | as B-A1 | none |
| B-A9 | `ntt.rs:96` `Ntt for Vector::ntt` | `iter().map(Polynomial::ntt).collect()` | ml-dsa | ~6 | none needed; same codegen | keygen-lean-20261028 F-NTT |
| B-A10 | `ntt.rs:158` `NttInverse for NttVector` | map/collect | ml-dsa | ~6 | as B-A9 | keygen-lean-20261028 F-INTT |
| B-A11 | `hint.rs:64` `Hint::new` (MakeHint over vectors) | nested `zip().map().collect()` | ml-dsa | ~10 | FIPS Alg 7 l.26 is a coefficient loop | none |
| B-A12 | `hint.rs:82` `Hint::hamming_weight` | `map(filter().count()).sum()` | ml-dsa | ~8 | count loop is CT-visible (no `filter` branch) | none |
| B-A13 | `hint.rs:89` `Hint::use_hint` | nested zip/map/collect | ml-dsa | ~10 | as B-A11 | none |
| B-A14 | `hint.rs:128` `Hint::bit_unpack` | `iter().map(usize::from).collect()`, `windows(2).all`, `copied().max()`, `enumerate` | ml-dsa | ~25 | Alg 21 is written as index loops; malformed-input checks become explicit | the campaign's `decode_hint_row` (verification registration, local-fix inventory) covers only the inner row |
| B-A15 | `encode.rs:97` `BitPack::unpack` for `Vector` | `into_iter().map(unpack).collect()` | ml-dsa | ~6 | as B-A9 | skencode-20261029 F-VPACK covers `pack` only |
| B-A16 | `signing.rs:331` `try_raw_sign_mu` | `for kappa in signing_nonces()` (`StepBy<RangeInclusive<u16>>`) | ml-dsa | ~6 | `while kappa + L - 1 <= u16::MAX { …; kappa += L }` states the #1488 bound inline | signing-original-closure-v2 selected the closure body only |
| B-A17 | `signing.rs:681` `signing_nonces` | `(0..=MAX-(L-1)).step_by(L)` returning `impl Iterator` | ml-dsa | −5 (deleted) | folds into B-A16 | none |
| B-A18 | `module-lattice-0.2.3/src/encoding.rs:175` `Encode for Vector::encode` | map/collect then `flatten` | module-lattice | ~8 | | skencode-20261029 F-VPACK (ml-dsa side) |
| B-A19 | `module-lattice …/encoding.rs:180` `Encode for Vector::decode` | `unflatten` then map/collect | module-lattice | ~8 | | none |

## B. Operator-trait impls on references with iterator bodies — TOOL-12 / TOOL-7 class

These fail with `[Error] Internal error, please file an issue` (the erased impl-level region check in
`interp/InterpUtils.ml:151`, plus the `map` failure inside). Rewrite: a plain free function that takes `&[[u32; 256]; N]`
and returns an array, called by name. The scalar `Elem` operator impls (`module-lattice algebra.rs:139/147/155/163`,
by value) **extract fine** (ARITH-02/03), so they are not listed.

| ID | Location | Construct | Where | Diff | Justification | Existing factoring |
|---|---|---|---|---|---|---|
| B-B1 | `ml-dsa/src/algebra.rs:33` `Mul<&NttVector<L>> for &NttMatrix<K,L>` (new in #1444) | operator impl + `self.0.iter().map(\|row\| &**row * rhs).collect()` over `MaybeBox` rows | ml-dsa | ~10 | free `matrix_vector_ntt` = FIPS Alg 48 by name | keygen-lean-20261028 F-MAT was on module-lattice's matrix, which master no longer uses |
| B-B2 | `module-lattice …/algebra.rs:226` `Mul<&NttPolynomial> for &NttPolynomial`… (dot/ scalar-vector) | operator + map/collect | module-lattice | ~8 | | keygen F-DOT |
| B-B3 | `…/algebra.rs:284` `Add for &Vector` | operator + zip/map/collect | module-lattice | ~8 | | keygen F-ADD (`addFwd`) |
| B-B4 | `…/algebra.rs:298` `Sub for &Vector` | operator + zip/map/collect | module-lattice | ~8 | | none |
| B-B5 | `…/algebra.rs:312` `Mul for &NttVector` (scalar·vector, verify) | operator + map/collect | module-lattice | ~8 | | none |
| B-B6 | `…/algebra.rs:320` `Neg for &Vector` | operator + map/collect | module-lattice | ~6 | | none |
| B-B7 | `…/algebra.rs:508` `Sub for &NttVector` | operator + zip/map/collect | module-lattice | ~8 | | none |
| B-B8 | `…/algebra.rs:525` `Mul<&NttVector> for &NttPolynomial` (ĉ·ŝ) | operator + map/collect | module-lattice | ~8 | | keygen F-DOT (related) |

## C. Closures and `hybrid_array` constructors

| ID | Location | Construct | Where | Diff | Justification | Existing factoring |
|---|---|---|---|---|---|---|
| B-C1 | `ml-dsa/src/algebra.rs:25` `NttMatrix::from_fn` (new in #1444) | `Array::from_fn(\|i\| MaybeBox::new(f(i)))` with a caller-supplied `FnMut` | ml-dsa | ~8 | an index loop with in-place row stores does the same row-at-a-time offload | sampling-lean-20261028 F-EXA (on the pre-#1444 `NttMatrix::new(Array::from_fn(..))`; needs redoing) |
| B-C2 | `hybrid-array-0.4.15/src/from_fn.rs:16` `Array::from_fn` signature (via `expand_a`, `expand_mask`, `expand_s`) | generic `FnMut` closure parameter | hybrid-array (call sites in ml-dsa) | ~6 per call site | | F-EXA / F-EXS |
| B-C3 | `ml-dsa/src/sampling.rs:197` `expand_mask` | `Vector::new(Array::from_fn(\|r\| …))` | ml-dsa | ~8 | | none (master moved the XOF into `expand_mask_xof`, #1484) |
| B-C4 | `module-lattice …/encoding.rs:80/84` `flatten`/`unflatten` | `hybrid_array::flatten` | module-lattice + hybrid-array | ~10 | byte offsets `i*32*c` are what FIPS 204 writes | skencode F-BENC is adjacent |

## O. Aeneas-only observations (not in the inventory's classes)

| ID | Location | Construct / failure | Where | Diff | Justification | Existing factoring |
|---|---|---|---|---|---|---|
| B-O1 | `ml-dsa/src/lib.rs:175` `MuBuilder::internal` | `for m in Mp` over `&[&[u8]]`: internal error at the slice iterator of references | ml-dsa | ~5 | `while i < Mp.len() { h = h.absorb(Mp[i]) }` | none (HASH-03 used wrapper statements) |
| B-O2 | `lib.rs:185` `MuBuilder::message` | same | ml-dsa | ~5 | same | none |
| B-O3 | `hint.rs:128` `bit_unpack`, via `r-sig-decode` | "Name clash detected … `core.iter.traits.iterator.Iterator.{all,collect,map}.default` (the generated code will be incorrect)", from monomorphized iterator defaults (TOOL-5-adjacent) | ml-dsa | covered by B-A14 | | none |
| B-O4 | `hybrid_array` `Index`/`IndexMut`/`Deref`/`split_ref`/`Default`/`Clone` (every function) | opaque by flag; no Aeneas model, so trusted hand models (sampling lane §4) | hybrid-array | n/a; replaced by native arrays | native `[T; N]` indexing has an Aeneas model (`Array.index_usize`) | trusted models in sampling-lean-20261028 |

## S. Added by hand (closure bodies the inventory does not follow)

| ID | Location | Construct | Where | Diff | Justification | Existing factoring |
|---|---|---|---|---|---|---|
| B-S1 | `ml-dsa/src/sampling.rs:83` `rej_ntt_poly` (text identical to the pin) | `for chunk in buf.chunks_exact(3)` | ml-dsa | ~6 | | sampling-lean-20261028 F-NTT (sampler lane's name) |

## X. Tool-level failure modes

| ID | Where seen | What | Status |
|---|---|---|---|
| B-X1 | every master run except `r-sig-decode` | `Uncaught exception: Not_found` in Aeneas post-processing of transparent functions, after translation errors; Aeneas exits 2 and writes **no** Lean | Observed only. Hypothesis, **not tested**: a cascade from functions whose signatures failed to translate. In the fork run there are no translation errors and no crash, which fits the hypothesis but does not prove it. |
| B-X2 | `r-sig-decode` | Name clash, "the generated code will be incorrect" (B-O3) | Output must not be accepted. |
| B-X3 | `fork-mono` (`--monomorphize`) | 9 external axioms for instantiated `core::array::Index<RangeTo>`/`IndexMut`, `slice::Index<Range>` and `slice::len` (`logs/master-fork-mono/lean/Survey/FunsExternal_Template.lean`) | Avoided by **not** passing `--monomorphize` for the fork: the generic run has 0 referenced external axioms. |

## F. Constructs the fork itself hit (style rules, with evidence)

| ID | Where | Construct | Rule |
|---|---|---|---|
| B-F1 | first `fork-generic` run: `fork-skeleton/src/sign.rs` `attempt`, inner loop at 40:8–42:9 (`logs/master-fork-generic` was regenerated; failure text quoted in SURVEY.md §4) | nested loop whose outer body first assigns `w[i] = ntt_inverse(..)`, then an inner loop reads `w[i][j]` and writes `w1[i][j]`: `[Error] Unimplemented` (`Interp.ml:617`) | Lift the inner loop into a per-polynomial function (`poly_high_bits`, `poly_low_bits`). Reading an element written earlier in the same outer iteration through a nested loop is unsupported. |
| B-F2 | `fork-generic` with `for` ranges | `for i in 0..N` pulls in `core::iter::range::Step` defaults (4 template axioms, unreferenced) | Use `while` loops only. |
| B-F3 | `fork-mono` | `--monomorphize` with slice and array range indexing (B-X3) | Keep generic `K`/`L` const generics; do not monomorphize. |

## Fork style rules, summarized

1. `while` loops over fixed-size arrays. No `for`, ranges, iterator adapters or closures.
2. Free functions named after the FIPS algorithm. No operator-trait impls (scalar arithmetic is `field::{add,sub,mul,neg}`).
3. Native `[u32; 256]`, `[[u32; 256]; K]` and `[u8; N]`. No `hybrid-array`, `typenum`, `module-lattice` or `MaybeBox`.
4. `K`/`L` const generics plus a `Params` value. No associated-type parameter traits, and Charon runs without `--monomorphize`.
5. Lift any inner per-coefficient loop that reads freshly written outer data into its own function (B-F1).
6. Avoid `copy_from_slice`, `to_le_bytes`, `chunks_exact` and `windows` (opaque or unmodeled in this Aeneas). Write the byte loops out.
