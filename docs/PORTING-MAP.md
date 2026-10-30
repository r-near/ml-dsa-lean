# Porting map: campaign Lean lemmas to ml-dsa-verified

Scope: which Lean results from the earlier RustCrypto `ml-dsa` verification campaign can be reused here, from where,
and what has to change. All paths are relative to the campaign root and prefixed `campaign/`. The campaign is
read-only; nothing here was built or replayed. Where a claim was read from a campaign report but not re-checked, it is
labeled "per report". "Not checked" means I did not look.

## Summary

1. Cheap ports (pure Nat/Int lemmas, no Aeneas): Barrett and reciprocal-division correctness, Decompose/UseHint
   integer lemmas, the twiddle-table `decide +kernel` check, the FIPS 202 bit-level spec and sponge model, the
   rejection-sampler spec facts, bit-pack byte-formula lemmas. The constants in `rounding.rs` match the campaign's
   lemma constants exactly (36/360800, 38/524800, `>> 48` with 1477838210/537395713, 28/32768).
2. Needs restating, proof scripts mostly reusable: field `add/sub/neg/mul/small_reduce/barrett_reduce` (same
   expressions as module-lattice 0.2.3), the NTT layer/loop machinery (same `ntt_layer<LEN,ITERATIONS>(w, m)` shape,
   different loop form: `Range` iterator becomes `while`), the SHAKE sponge-to-FIPS bridge (new `finalize` permutes
   eagerly), the XofSim/ShakeSim interface and its satisfiability model.
3. Does not carry at all: every theorem about extracted RustCrypto code (Funs.lean-dependent), the ADAPTER/Kani
   joins, hybrid_array/typenum/`Elem` machinery, the PKCS#8 and wrapper-layer lemmas.
4. Must be written fresh: a complete FIPS 204 spec. The campaign has only fragments (Alg 6 lines 1-10, 9/12/13/16/17/
   22/24, 29-33, 35, 41/42, 45) in `Nat`/`Aeneas Array U32 256` form. There is no ZMod, no `Vector`, no Alg 2/3/7/8
   spec, no MakeHint (Alg 39), no FIPS-shaped HighBits/LowBits (Alg 37/38 exist only as the integer-level `high`/`low` in `native-use-hint-decompose-integer-v1/Decompose.lean`), no infinity-norm lemma.
5. Also absent in Lean anywhere in the campaign: the correctness argument (w - cs2 + ct0 = Az - ct1*2^d, the
   `UseHint(h, w-cs2+ct0) = HighBits(w-cs2)` step, norm bounds), BitUnpack, SimpleBitUnpack, pk/sig decode specs, and
   any proof that NTT is a ring homomorphism (the NTT proofs show "implementation = FIPS 41/42 schedule" only; the
   sibling `theory/NttKernel.lean` proves only butterfly inversion and twiddle pairing).
6. FIPS 202 Lean spec exists and is good: `campaign/skencode-20261029/lean/HashShake/Fips202.lean` (144 lines,
   bit-level, imports only `Mathlib.Tactic`). Sponge model with generic-permutation theorem
   `absorb_pad_read_eq_sponge`; lane-level Keccak-f proven equal to it (`lPerm_fips`). All 3 standard axioms only.
7. NTT loop invariants: handled by induction on a `remaining` counter plus a pure recursive model, never by
   unrolling 256 elements. Whole forward NTT lane builds in about 40 s cold (1,749 jobs); see Performance.
8. Lean/Aeneas pins are identical to this repo: Lean v4.31.0, Aeneas `build-183e4f0`, hax-lean v0.3.30. One sibling
   directory (`theory/`) used Lean 4.35.0; its files only import `Std.Tactic` and are untested on 4.31.0 (not checked).
9. Surprises: (a) the campaign's SHAKE spec evaluates only via a lane-materialized kernel trick (`TermWit/Stream.lean`),
   so `#eval` of `Fips202.xof*` as written is not known to work (not checked); (b) a real-SHAKE kernel check costs
   about 10 GB and 30 s per 5-block call; (c) ERR-15: both original XOF interfaces were unsatisfiable by any finite
   state, so every "conditional" sampler/keygen theorem was vacuous until fixed; (d) UseHint's integer theorem needed
   five attempts and 62 s of Lean time before it passed (timeouts at 30 s per invocation).
10. Biggest reuse by value: NTT machinery (about 1,700 lines), field proofs (206 lines), FIPS 202 + sponge (about
    1,700 lines), sampler spec + facts (about 500 lines), XofSim/ShakeSim (about 1,500 lines, but tied to RustCrypto
    `Sampling.Backend`/`Keygen.Backend` classes).

## 0. Where things live, versions, how to find canonical files

The campaign has about 24,100 `.lean` files, mostly generated `Funs.lean`/`Types.lean`, vendored Aeneas snapshots, and
lane copies. For human-written proofs use these:

| Purpose | Canonical location | Notes |
|---|---|---|
| Cumulative latest Lean project (superset of the keygen/sampling/hash/NTT lanes) | `campaign/skencode-20261029/lean/` | one lake project `SamplingLean`; libs: NttForward, MlDsa, NttWholeForward, NttWholeInverse, Keygen, Sampling, HashShake, AbsorbCursor, MuBuilderBridge, MuSegmentation, ReadCursor, ShakeIntegration, XofFix, ShakeStateX, ShakeMulti, Adapter, Cleanup, TermWit, ExtInst, SkEnc, SkComp |
| Field arithmetic | `campaign/bridge/field-reduction/completed-operations/` | cumulative of `completed-reduction` and `completed-multiplication` |
| NTT forward / inverse | `campaign/ntt/lean-forward-v4/`, `campaign/ntt/lean-inverse-v5/` | v5 contains v4 |
| Pure-math kernel (Arithmetic, Decomposition, NttKernel) | `campaign/../theory/*.lean` | sibling of `campaign/`, from the earlier campaign pass; Lean 4.35.0 |
| UseHint/Decompose integer lemmas | `campaign/native-use-hint-integer-composition-v4/`, `campaign/native-use-hint-decompose-integer-v1/`, `campaign/native-use-hint-integer-lemmas-v1/`, `campaign/native-use-hint-low-coercion-bridge-v3/` | import chain Reciprocal -> Decompose -> ResidueBridge -> CanonicalLow -> HintSteps -> HintComposition |
| Hint pack/unpack | `campaign/parsing/hint-pack-v27/lean-acceptance-{44,65,87}[-alloc]/` | latest of v19-v27 |

Toolchain and dependencies (from `lake-manifest.json` in those lanes):

- `lean-toolchain`: `leanprover/lean4:v4.31.0` (all lanes above except `theory/`).
- Aeneas `https://github.com/cryspen/aeneas` rev `build-183e4f0` (commit 183e4f06...), subDir `backends/lean`.
- hax-lean `https://github.com/cryspen/hax-lean` rev `v0.3.30`.
- Mathlib rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`, pulled in through Aeneas's backend. Mathlib is only imported
  directly by `HashShake/Fips202.lean` (`import Mathlib.Tactic`); the rest uses Aeneas `Std`, core Lean, and omega.
- `lean/lakefile.toml` in this repo already requires the same Aeneas rev; hax-lean is not listed there, but it is a
  direct `[[require]]` in every campaign lakefile I opened. Whether any human-written proof file imports it, and
  whether this repo needs it: not checked.

Representation used throughout the campaign (this is the main restating cost):

- Coefficients are `Nat` with `% 8380417`, or Aeneas `Std.U32`. Polynomials are `Aeneas.Std.Array Std.U32 256#usize`
  (alias `Vec`, `Poly`; `Vec` is defined in `NttForward/Verification.lean`). There is no `ZMod q`, no `Vector`, no `Fin 256 -> _` anywhere in the campaign (grep for
  `ZMod` finds only an unrelated ReadCursor file).
- Canonicality predicate: `NttRefinement.Canonical w := ∀ i, i.val < 256 -> w[i]!.val < 8380417`
  (defined at `campaign/ntt/lean-forward-v4/NttForward/FirstInner.lean:7`, with `canonical_set` at line 19) and `KeygenSpec.Can`.
- Bytes are `List Nat` in specs, `Slice Std.U8` in extracted code. Bits are `List Bool`.

## 1. Field arithmetic: add, sub, neg, mul, small_reduce, barrett_reduce (ARITH-02/03)

- Canonical file: `campaign/bridge/field-reduction/completed-operations/MlDsa/Proof.lean` (206 lines).
  Also `campaign/bridge/field-reduction/completed-reduction/` (6 theorems) and `completed-multiplication/` (14 total
  in operations).
- Key theorems (stated with Aeneas `WP.spec` notation, which excludes failure and divergence):
  ```lean
  theorem small_reduce_total (x : U32) (hx : x.val < 2 * 8380417) :
    small_reduce x ⦃ y => y.val = x.val % 8380417 ⦄
  theorem barrett_reduce_total (x : U64) (hx : x.val < 8380417^2) :
    barrett_reduce x ⦃ y => y.val = x.val % 8380417 ⦄
  theorem field_mul_total (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    algebra.proof_field_mul a b ⦃ y => y.val = (a.val * b.val) % 8380417 ∧ y.val < 8380417 ⦄
  ```
  plus `field_add_total` (`(a+b) % q`), `field_sub_total` (`(a + q - b) % q`), `field_neg_total` (`(q - a) % q`),
  `shift_value : BARRETT_SHIFT = ok 46#usize`, `multiplier_value : BARRETT_MULTIPLIER = ok 8396807#u128`,
  `truncate_total`.
- Depends on: Aeneas `Std` (`WP.spec`, `WP.spec_bind`, `WP.spec_mono`, `WP.spec_imp_exists`, `UScalar.mul_spec`,
  `step*`, `scalar_tac`, `global_simps`), `CoreModels` adapters. No Mathlib tactics beyond `omega`/`norm_num`.
  Built with Lean 4.31.0, Aeneas build-183e4f0.
- Status: tied to extracted code (module-lattice 0.2.3 macro bodies), but the Rust expressions are the same as this
  repo's `src/field.rs`: `small_reduce` = `mask = 0.wrapping_sub((x >= Q) as u32); x - (Q & mask)`; `barrett_reduce` =
  u128 multiply, `>> 46`, subtract, `Truncate`, `small_reduce`. The proof scripts should port after re-extraction.
- Concrete changes:
  - `BARRETT_MULTIPLIER`/`BARRETT_SHIFT` were globals computed from `ilog2(Q)`. Here `BARRETT_SHIFT` is a literal
    46 and the multiplier is `(1u128 << 46) / Q`. `shift_value` can be dropped; `multiplier_value` stays (expect
    `8396807`); keep the `simp only [global_simps]` unfolding pattern.
  - Campaign used 4 hand-written `FunsExternal.lean` adapters (u32 -> u64, u64 -> u128 widening, `U32.ilog2`,
    `U32.wrapping_neg`) delegating to `CoreModels`. New code needs `wrapping_sub` instead of `wrapping_neg`
    and `as` casts instead of `Into`; whether Aeneas build-183e4f0 has a `wrapping_sub` model: not checked.
  - The campaign's `Truncate` step (`U128 -> U32`) becomes `remainder as u32` (a cast); `truncate_total` becomes a
    cast lemma, `UScalar.cast_val_eq`-style.
  - Free functions `field::{add,sub,neg,mul}` replace `Elem<BaseField>` trait impls; wrapper theorems
    `elem_*_total` collapse into the `field_*_total` ones.
- Axioms: standard 3 only (per report and `#print axioms` lines in the file). No `sorry`/`native_decide`/`axiom`
  (grepped the file: none).
- Size/cost: 206 lines; individual theorem cost not recorded; settings `maxRecDepth 8192`, `maxHeartbeats 4000000`.
- Independent evidence: a generated-Lean mutation (`rhs` -> `self` in add) is rejected by the unchanged theorem
  (`campaign/bridge/field-reduction/negative-control/`). Worth copying as a pattern.

## 2. Pure-Nat reduction/division lemmas (ARITH-01)

- Files: `campaign/../theory/Arithmetic.lean` (184 lines), `campaign/native-use-hint-integer-lemmas-v1/Reciprocal.lean`
  (63 lines, ten lemmas, independently replayed in `campaign/native-use-hint-integer-review-v1/REVIEW.md`).
- Key statements (all pure Nat, `omega`-proved):
  ```lean
  theorem one_correction {x modulus estimate : Nat} (lower : estimate * modulus ≤ x)
      (upper : x < (estimate + 2) * modulus) :
      (if x - estimate * modulus < modulus then x - estimate * modulus
       else x - estimate * modulus - modulus) = x % modulus
  theorem barrett_field_product (x : Nat) (hx : x < 8380417 ^ 2) : barrett x 8380417 46 = x % 8380417
  theorem barrett_power2round (x : Nat) (_hx : x < 2 ^ 32) : barrett x 8192 28 = x % 8192
  theorem barrett_44 (x : Nat) (_hx : x < 2 ^ 32) : barrett x 190464 36 = x % 190464
  theorem barrett_65_87 (x : Nat) (_hx : x < 2 ^ 32) : barrett x 523776 38 = x % 523776
  theorem reciprocal_div_44 (x : Nat) (hx : x < 8380417) : reciprocalDiv x 190464 = x / 190464
  ```
  and in `Reciprocal.lean`: `quotient44 : x * 1477838210 / 281474976710656 = x / 190464` (and `quotient65` with
  537395713 / 523776), `estimate44/65` (the `* 360800 / 2^36` and `* 524800 / 2^38` estimates under-count by at most
  one), `remainder*`, `reduced*`, `products*` (all products < 2^64).
- Depends on: `Std.Tactic` (theory) or `Lean.Elab.Tactic.Omega` (Reciprocal). No Aeneas, no Mathlib.
- Pure math; ports almost verbatim. Check: this repo's `src/params.rs` constants equal the campaign's (36/360800,
  38/524800, div mult 1477838210 and 537395713) and `power2round` uses `(28, 32768)`. Note the new `reduce_mod` is
  stated for `x < q` but the campaign lemmas cover all `x < 2^32`, which is stronger.
- Axioms: standard (`Classical.choice`/`propext`/`Quot.sound`; theory reported only `propext`/`Quot.sound`).
  No `native_decide`.
- Cost: trivial for `omega` (per report: the `Reciprocal` module under a 2,000,000 heartbeat setting). Lean version
  mismatch risk for `theory/` (4.35.0 vs 4.31.0): not checked.

## 3. Rounding: mod±, Power2Round, Decompose, HighBits/LowBits, UseHint, MakeHint, infinity norm (HINT-01, ARITH-01)

What exists in Lean:

- Decompose/UseHint integer layer: `campaign/native-use-hint-decompose-integer-v1/Decompose.lean` (122 lines; defs
  `rounded`, `balanced`, `difference`, `high`, `low`, `oracleHigh`, `oracleLow`, `actualHint`, `oracleHint`; ten
  lemmas incl. `edge44`, `difference_formula44`, `high_oracle44`), `campaign/native-use-hint-low-coercion-bridge-v3/
  ResidueBridge.lean` (36), `campaign/native-use-hint-integer-composition-v4/{CanonicalLow,HintSteps,HintComposition}
  .lean` (151 + 31 + 62). Final statement:
  ```lean
  theorem use_hint44 (x : Nat) (hx : x < 8380417) (h : Bool) :
      actualHint 190464 x h = oracleHint 190464 x h ∧ actualHint 190464 x h < 44
  ```
  (and `use_hint65` with 523776 and 16). `oracleHint` matches FIPS 204 Alg 40: `r1 +/- 1 mod m` by `r0 > 0`;
  `actualHint` mirrors the Rust (`high`/`low` with the `q-1` edge case). Replay status: the ten Decompose/Reciprocal
  lemmas were independently replayed; v4 composition says "fresh independent replay remains required"; I did not find
  a review of it (not checked further).
- Mathematical decomposition uniqueness: `campaign/../theory/Decomposition.lean` (91 lines): `Valid` relation,
  `unique_44`, `unique_65_87`, `decompose_valid_44`, `decompose_valid_65_87`, over `Int`.
- Power2Round and mod±: `campaign/skencode-20261029/lean/Keygen/Spec.lean` (171 lines): `modpm`, `p2rHi`, `p2rLoRep`,
  `p2r_decomp : p2rHi x < 1024 ∧ (x:Int) = 8192 * p2rHi x + modpm x`, `p2rLoRep_spec`, `modpm_range`.
- Kani-only (no Lean): scalar MakeHint, infinity norm (`campaign/ntt/RESULTS-v16.md`, `campaign/../hints/`), HighBits/
  LowBits as Rust properties. No Lean theorem for MakeHint or the infinity norm; HighBits/LowBits exist only as the integer-level `high`/`low` of `Decompose.lean`.

Port notes:

- Statement shapes use `Nat` with `% q` and a "balanced" residue defined by hand. For a ZMod-based spec, restate
  `Decompose` via `ZMod.val` and an `Int` centered remainder, then prove the campaign lemmas as the bridge
  (`decompose_valid_*`, `unique_*` are the real content: existence plus uniqueness of the decomposition).
- `balanced`/`difference` correspond to `mod_plus_minus`/`diff` in `rounding.rs`; the `diff = q-1` edge is
  `is_edge` in the new code. The proof scripts (`split <;> omega`) port; expect to redo the lines mentioning
  `rounded` since the new code uses `diff * div_mult >> 48` instead of a rounded quotient (campaign's
  `unconditional_division44` in `native-use-hint-decompose-integer-v1/UseHint.lean:94` covers exactly this).
- That `UseHint.lean` file is an excluded prototype (timeouts); use the `integer-composition-v4` version.
- The new code is constant-time (`ct_select`/`ct_lt_mask`); `ChoiceBridge` lemmas for ctutils
  (`campaign/ctutils-rust-bridge-v1/lean/ChoiceBridge.lean`) are about the ctutils crate and do not apply. Each
  `ct_*` mask function needs a one-line lemma in this repo.
- Axioms: standard 3 only per `THEOREM-AXIOM-INVENTORY-v1.json`. No `native_decide`, `sorry`, `axiom`, `opaque`
  in the files above (grepped).
- Cost: v4 modules: 5 Lean invocations, 62.0 s total subprocess time, 3 passed, 2 hit the 30 s cap. The successful
  version replaced "definitional-change proof steps" with checked literal division equalities, restricted
  `unfold`, and explicit branch rewrites (per `REPORT.md`; root cause of the earlier timeouts not identified).
  Settings used: `maxRecDepth 100000`, `maxHeartbeats 200000` (HintComposition), `2000000` (Decompose).

## 4. NTT: twiddle table, layer schedule, forward/inverse, pointwise, vector/matrix (NTT-01..04, ARITH-04)

### 4a. Table (NTT-01)

- File: `campaign/ntt/lean-forward-v4/NttForward/Table.lean` (210 lines) and `TableValues.lean` (104).
- Key statements:
  ```lean
  theorem tableNat_fips : tableNat = fipsTableNat := by decide +kernel
  theorem computedTable_fips (i : Std.Usize) (hi : i.val < 256) :
      computedTable[i]!.val = (if i.val = 0 then 0 else 1753^(reverseNat i.val) % 8380417)
  theorem actual_table_correct : ∃ table : Vec, ml_dsa.ntt.ZETA_POW_BITREV = ok table ∧ Canonical table ∧
      ∀ (i : Std.Usize), i.val < 256 → table[i]!.val = (if i.val = 0 then 0 else 1753^(reverseNat i.val) % 8380417)
  ```
  with `reverseNat n = (BitVec.ofNat 8 n).reverse.toNat` and `fipsTableNat = List.ofFn (fun i : Fin 256 => ...)`.
- Campaign computed the table at runtime (a `powerFill`/`reorderFill` loop, with `power_loop_total`,
  `reorder_loop_total`); this repo has a literal `ZETAS: [u32; 256]` (`src/ntt.rs:7`). Only the last step ports:
  `decide +kernel` against `fipsTableNat`. For the literal, the proof is `extracted constant = literal list` by
  `rfl`/`decide +kernel`, then `tableNat_fips`'s RHS. The loop proofs are not needed.
- Pure-math companion: `campaign/../theory/NttKernel.lean` (79 lines): `inverse_256 : 256 * 8347681 % 8380417 = 1`,
  `zeta_order_divides_512`, `zeta_no_shorter_period`, `paired_twiddle_inverse` (negated reverse-table twiddle is the
  modular inverse of the forward twiddle), `butterfly_inverse`. Uses plain `decide` on exponents (needs
  `set_option exponentiation.threshold 512`). Not needed if the spec only claims schedule equality; needed for any
  NTT-inverse-roundtrip proof.
- No `native_decide` (grepped; explicitly absent per file comment). Standard axioms; `first_twiddle_fips` shows
  `propext` only.

### 4b. Layer schedule and loop invariants (NTT-02/03)

- Files (forward): `campaign/ntt/lean-forward-v4/NttWholeForward/{GenericInner,GenericOuter,LayerModel,ForwardCorrect,
  Bridge,Geometry}.lean` (164 + 192 + 133 + 186 + 59 + 75 lines) and `NttForward/{FirstInner,Schedule,FieldBridge,
  Verification}.lean` (129 + 178 + 65 + 94). Inverse adds `campaign/ntt/lean-inverse-v5/NttWholeInverse/{GenericInner,
  GenericOuter,LayerModel,InverseCorrect,Scaling,Bridge}.lean` (178 + 204 + 143 + 204 + 130 + 81).
- Key statements:
  ```lean
  def mathButterfly (w : Vec) (z : Std.U32) (j partner : Std.Usize) : Vec :=
    let t := (z.val * w[partner]!.val) % 8380417
    let upper := modElem (w[j]!.val + 8380417 - t)
    let lower := modElem (w[j]!.val + t)
    (w.set partner upper).set j lower
  theorem inner_loop_total (len stop : Std.Usize) (hb : stop.val+len.val ≤ 256) (hlen : 0 < len.val)
      (remaining : Nat) (hrem : remaining ≤ stop.val) (w : Vec) (hw : Canonical w) (z : Std.U32) (hz : z.val < 8380417) :
      innerLoop len {start := smallIndex (stop.val-remaining) _, «end» := stop} w z =
        ok (blockMath len.val stop.val hb remaining hrem w z) ∧ Canonical (blockMath len.val stop.val hb remaining hrem w z)
  theorem layer_total (len iter : Std.Usize) (hp : len.val*iter.val=128) (m : Std.Usize) (hm : m.val=iter.val-1)
      (w : Vec) (hw : Canonical w) :
      layer len iter w m = ok (layerMath len.val iter.val hp iter.val _ w, smallIndex (2*iter.val-1) _) ∧ Canonical (...)
  theorem actual_forward_fips41 (w : Vec) (hw : Canonical w) :
      NttWholeForward.ntt.proof_whole_entrypoints.forward w = ok (fips41 w) ∧ Canonical (fips41 w)
  theorem actual_inverse_fips42 (w : Vec) (hw : Canonical w) :
      NttWholeInverse.ntt.proof_whole_entrypoints.inverse w = ok (fips42 w) ∧ Canonical (fips42 w)
  ```
  `fips41` is eight `layerMath len iter` applications (128,1), (64,2), ..., (1,128); `fips42` is the reverse order
  plus `scaleMath 256`, final multiplier 8347681.
- Technique (see also Performance):
  1. No unrolling. A pure recursive model on a decreasing counter (`blockMath ... remaining`, `layerMath ...
     remaining`) mirrors the loop; the theorem is proved by induction on `remaining` with the loop cursor written
     `smallIndex (stop - remaining)`.
  2. Single step lemma per loop body (`inner_step_math`) with explicit successful-call equations for `mul/sub/add`,
     then "equality to the pure butterfly preserving failure and divergence" (`inner_butterfly_equivalence` is proved
     by `cases` on each `RustM` outcome, so no field-success hypothesis is left).
  3. The eight Rust monomorphic layers `ntt_layer<128,1>` ... are proved kernel-equal (`rfl`) to one parameterized
     control skeleton (`layer_128_1_equal` ... `layer_1_128_equal`), so the generic proof runs once.
  4. Field operations reused by kernel equality (`mul_equal`, `add_equal`, `sub_equal`, `table_equal` in `Bridge.lean`)
     rather than re-proved.
  5. Geometry (`parameters_bounded`, `butterfly_indices`, `twiddle_indices`, `final_twiddle_cursor`) is a separate
     pure-Nat bounds file proved by `omega`/`nlinarith`.
- Depends on: Aeneas `Std` (`Array.index_usize`, `Array.update`, `Array.getElem!_Usize_set_ne`, `UScalar.tryMk_eq`,
  `loop.eq_def`, `bind_tc_ok/fail/div`, `scalar_tac`), campaign helper files above. Lean 4.31.0.
- Tied to extracted code (names like `ml_dsa.ntt.ntt_layer1281_loop0_loop0.body`, Range iterator). The extracted `Range`
  struct and `Concrete3...Iterator.next` unfolding disappear with `while` loops; expect the loop body to be a
  `loop` over a state tuple `(i, m, w)` or similar, and re-derive `inner_exit`/`inner_step`. Mathematical part
  (`mathButterfly`, `blockMath`, `layerMath`, `fips41/42`, `Geometry`, `smallIndex`, `Canonical`) is Aeneas-light and
  ports with small edits.
- Differences to handle: this repo's `ntt_layer` pre-increments `*m` and reads `ZETAS[*m]` inside the outer loop;
  campaign's `layer len iter w m` threads `m` the same way (start `iter-1`, table index `iter + block`). Inverse here
  uses `z = sub(0, ZETAS[*m])` after `*m -= 1`; campaign proves "negative of table[2*block_count-1-i]".
  The scaling loop (`ScaleSemantics.final_scaling_pointwise`, multiply every coefficient by 8347681) is here a
  `while j < 256` loop in `ntt_inverse`; the campaign's was also restated as an indexed loop.
- The spec is `Vec`-based with `Nat %`, i.e. a *schedule* spec, not a ring-theoretic one. The relation to FIPS 204 text
  is by an independent spec review (`campaign/ntt/INDEPENDENT-SPEC-REVIEW-v4.md`, `-v5.md`), not a theorem.
- Axioms: `actual_forward_fips41` etc. use `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`,
  `native_decide`, `axiom`, `opaque` in proof files (the grep hits are the generated, unimported
  `FunsExternal_Template.lean`, see Pitfalls).
- Cost: see Performance.

### 4c. Pointwise multiply, vector/matrix (ARITH-04, NTT-04)

- `campaign/ntt/lean-pointwise-factored-v7/` has the Lean statement `PointwiseProof.indexed_fips45` (extracted indexed
  helper returns `(left[i] * right[i]) % 8380417` at every index for canonical inputs). Same restating story as 4b.
- Vector/matrix lifting was done in Kani with stubs plus a "cross-tool composition" argument
  (`campaign/ntt/RESULTS-v6.md`, 10 runs of 118 to 551 s each); nothing to port. Keygen's `matvec`/`dot`/`vadd` Lean
  spec (`KeygenSpec`, see 9) is the reusable part. For this repo the loops `matrix_vector_ntt`/`scalar_vector_ntt_
  inverse` are plain nested `while` loops: prove them with the same remaining-counter induction, no ADAPTER.

## 5. FIPS 202 Keccak/SHAKE spec and sponge model (HASH-01/02)

Requested item (1).

- Spec: `campaign/skencode-20261029/lean/HashShake/Fips202.lean` (144 lines; identical copy in
  `campaign/hash-shake-20261028/lean/HashShake/`). Bit-level transcription of FIPS 202: `Str := Fin 1600 → Bool`,
  `SA := Fin 5 → Fin 5 → Fin 64 → Bool`, `theta`, `rho` (literal Algorithm 2 walk), `pi`, `chi`, `rc`, `RC`, `iota`,
  `Rnd`, `keccakP`, `keccakF`, `pad101`, `sponge` (Alg 8, fuel `d+1`), `keccakC`, `SHAKE128`, `SHAKE256`, `h2b`, `b2h`,
  `shake128Bytes`, `shake256Bytes`, and the stream views
  `xof128 M j = (shake128Bytes M (j+1)).getD j 0` (and `xof256`). Independent of Rust and Aeneas.
- Lane/limb level: `HashShake/KeccakLanes.lean` (199 lines): lanes as `List (BitVec 64)`, `lPerm`, and
  ```lean
  theorem lPerm_fips (L : Lanes) : ofA (bits (lPerm L)) = keccakF (ofA (bits L))
  ```
  built from `theta_bits`, `rho_bits`, `pi_bits`, `chi_bits`, `iota_bits`, `RC_table`, `round_bits`, `fold_bits`.
  This is the natural target for `keccak_f1600(&mut [u64; 25])` in `src/keccak.rs`: prove the Rust loops equal `lRound`,
  then compose. (The campaign did not extract Keccak; its Rust-to-Lean link for the round was Kani plus a manual
  transcription of `reference_p`. Here the Rust is in-crate, so extraction replaces both.)
- Sponge: `HashShake/Sponge.lean` (435 lines), generic in the permutation `f` and rate `R`:
  ```lean
  theorem absorb_pad_read_eq_sponge (hR : 1 < R) (hR8 : 8 * R ≤ 1600) (M : List Nat) (n : Nat) :
      (read f R n (0, pad R (absorb f R (0, zero) M))).1 =
        b2h (sponge f (8 * R) (h2b M ++ [true, true, true, true]) (8 * n))
  ```
  and `HashShake/Shake.lean` (42): `shake256_model`, `shake128_model`, `xof256_eq`, `xof128_eq`
  (`xof256 M j = stream keccakF 136 (padded 136 M) j`). Also `squeeze_closed`, `read_from` (reading from an arbitrary
  offset: `readerAt Sp o`), `absorb_within`, `absorb_pad_spec`, `stream f R Sp j = byteOf (f^[j/R+1] Sp) (j % R)`.
- Other pieces: `Transport.lean` (193) and `ReadTransport.lean` (140) connect the RustCrypto `shake 0.1.0` /
  `sponge-cursor` extracted controllers (u64-lane absorb/read) to the byte model; `Interface.lean` (271),
  `SamplingInst.lean` (138), `KeygenInst.lean` (81) instantiate hypothesis interfaces. These are RustCrypto-specific.
- Dependencies: Mathlib (`Mathlib.Tactic`) for `Fips202.lean`; Lean core for the rest. Built under the
  campaign's SamplingLean project (8,980 jobs for `lake build HashShake`, 0 errors, per report).
- Axioms: 41 theorems audited in `campaign/hash-shake-20261028/logs/axioms.log`; standard axioms only (`RC_table`,
  `squeeze_closed`: `propext` and `Quot.sound` only). `run.sh` greps for `sorry`, `admit`, `native_decide`, `axiom`.
- Porting changes:
  - The model's `absorbStep`: XOR byte at cursor, permute and reset when the cursor reaches the rate, matches this
    repo's `Shake::absorb` (eager permute at `pos == rate`).
  - The model's `pad` + lazy `readStep` (permute when cursor is 0) differs from this repo's `finalize` (xor 0x1F at
    `pos`, xor 0x80 at `rate-1`, permute immediately, `pos = 0`) and `squeeze` (permute only when `pos == rate`).
    The observable stream is the same (`stream f R Sp j = byteOf (f^[j/R+1] Sp) (j % R)`), so state a new lemma
    "finalize then squeeze n bytes = `read` from `padded`" using `stream`/`read_from`. One-block lemma, not a redo.
  - Two-slice absorb (M′ = prefix ‖ m): the model's `absorb` is `bytes.foldl (absorbStep f R) s`, so
    `absorb s (a ++ b) = absorb (absorb s a) b` is `List.foldl_append` (not stated as a campaign lemma; I did not find
    one by that name).
  - The model does not track "absorbing vs squeezing". The new `Shake` has no phase flag, so absorb-after-finalize is
    silently wrong rather than a panic; callers must be shown to respect the order (see 6).
- Executability: `Fips202.keccakF` as written (closures over `Fin 1600 → Bool`) is not efficient to kernel-evaluate;
  the campaign evaluated SHAKE only through `campaign/termination-witness-20261029/lean/TermWit/Stream.lean`
  (143 lines), which materializes lanes as lists and proves `xof128 M j = (cBlocks 168 n (cPad 168 M)).getD j 0`.
  Whether `#eval Fips202.shake128Bytes` works for ACVP cross-checks: not checked. If FORK-DESIGN §6(e)'s
  `#eval`-on-ACVP check is wanted, plan on `TermWit/Stream.lean`'s approach or a lane-level `def` with a
  `lPerm_fips` bridge.
- Not covered by anything in Lean: padding of an exactly-rate-sized message (the proof covers all lengths via
  `absorb_pad_spec`, per report), and SHAKE KATs. The campaign used Python hashlib cross-checks
  (`campaign/termination-witness-20261029/crosscheck.py`, per report) as evidence only.

## 6. XofSim / ShakeSim interface and satisfiability witness

Requested item (3). See ERR-15 in Pitfalls.

- Definition: `campaign/skencode-20261029/lean/XofFix/Interface.lean` (80 lines):
  ```lean
  structure XofSim {S : Type} (init : RustM S) (absorb : S → Slice Std.U8 → RustM S)
      (squeeze : S → Slice Std.U8 → RustM (S × (S → S) × Slice Std.U8))
      (xof : List Nat → Nat → Nat) (V : S → List Nat → Nat → Prop) (fresh : S → Prop) : Prop where
    init : ∃ s, init = ok s ∧ V s [] 0 ∧ fresh s
    absorb : ∀ s m (b : Slice Std.U8), V s m 0 → fresh s →
      ∃ s', absorb s b = ok s' ∧ V s' (m ++ b.val.map (·.val)) 0 ∧ fresh s'
    squeeze : ∀ s m o (buf : Slice Std.U8), V s m o →
      ∃ c back out, squeeze s buf = ok (c, back, out) ∧
        out.val.map (·.val) = (List.range buf.val.length).map (fun j => xof m (o + j)) ∧
        V (back c) m (o + buf.val.length)
  ```
  `V s m o` means "squeezing from `s` yields `xof m` from offset `o`"; `fresh s` means "still absorbing". `ShakeSim`
  is the same shape with `squeeze32`/`squeeze64`. `XofSim.of_xofHyp` / `ShakeSim.of_shakeHyp` show the new
  interfaces are implied by the old ones.
- Satisfiability witnesses (Rust-faithful, finite, ghost-free): `campaign/skencode-20261029/lean/XofFix/Model.lean`
  (368 lines): state `FS R = {absorbing : Bool, pos : Nat, S : Fips202.Str}` with `pos < R`, `fsAbsorb` (panics when not
  absorbing), `fsSqueezeRaw`, `fs_xofSim`, and
  ```lean
  theorem g_sim : letI := fsSamplingBackend; GSim Fips202.xof128 (FV 168) FFresh := fs_xofSim 168 (by decide) _ xof128_eq
  theorem h_sim : ... HSim Fips202.xof256 (FV 136) FFresh
  theorem keygen_sim : ... ShakeSim Fips202.xof256 (FV 136) FFresh
  ```
  plus `fst_finite`, `xofHyp'_infinite` (the intermediate repair also had no finite model), `g_not_xofHyp`,
  `keygen_not_shakeHyp`, `fs_absorb_after_squeeze_fails`. Generic-transcript witnesses and joint-satisfiability
  theorems are in `XofFix/Sat.lean` (377 lines), e.g. `gx_xofSim`, `nonvacuous_{44,65,87}`, `closed_*_premises_sat`.
- Porting changes: the interface is parameterized by RustCrypto's `Sampling.Backend` / `Keygen.Backend` type classes.
  In this repo `Shake` is a concrete struct with `absorb/finalize/squeeze`, so a direct refinement
  (`Impl.keccak.Shake.absorb s b = ok s'` with an invariant `V`) works without the class indirection; keep the
  relational `V` + `fresh` idea and the satisfiability theorem as the checklist item. State `fresh` as "finalize
  not yet called". Because `finalize` is an explicit call here, the stream phase can be modeled directly
  instead of a `fresh` predicate.
- Axioms: 91 theorems audited in `XofFix/Axioms.lean`; standard axioms only. No `native_decide`.
- Cost: `XofFix` 15 modules cold-rebuild about 60 s (per `campaign/xof-interface-fix-20261028/RESULTS.md`).
- Rule adopted by the campaign: every hypothesis interface in a credited chain needs a satisfiability theorem.

## 7. Samplers: RejNTTPoly, RejBoundedPoly, SampleInBall, ExpandA/S (SAMPLE-01..04)

- Spec (pure, over an abstract stream `x : Nat → Nat`): `campaign/skencode-20261029/lean/Sampling/Spec.lean`
  (136 lines): `coeffFromThreeBytes` (Alg 14), `coeffFromHalfByte` (Alg 15), `rejNTTRun` (Alg 30), `rejBoundedRun`
  (Alg 31), `ballRun`/`ballSearch`/`sampleInBallRun` (Alg 29), `bytesToBits` (Alg 13), `integerToBytes` (Alg 11),
  `expandA` (Alg 32), `expandSHalf` (Alg 33). Loops carry explicit `fuel`; the total functions
  `rejNTTPoly`/`rejBoundedPoly`/`sampleInBall` are `noncomputable`, using `Nat.find` on a termination predicate
  (`RejNTTTerminates`, `RejBoundedTerminates`, `SampleInBallTerminates`) and return the zero polynomial otherwise.
  Termination is never assumed by a definition; theorems carry it as a premise. This matches FORK-DESIGN's `RejTerm`.
- Spec facts: `Sampling/SpecFacts.lean` (366 lines): fuel monotonicity (`rejNTTRun_mono_le`, `rejBoundedRun_mono_le`,
  `ballRun_mono_le`), `rejNTTPoly_eq` (any witness fuel gives the poly), `rejNTTPoly_out` (length 256, all `< Q`),
  `rejBoundedPoly_out`, `sampleInBallRun_out`, `sampleInBall_out` (ternary entries, weight = tau for tau <= 256),
  `weight_set`, `ballRun_out`. Pure, no Aeneas, ports nearly verbatim (the lane imports `Keygen.Spec` for `Q`).
- Extracted-code theorems (restate):
  ```lean
  theorem rej_ntt_poly_spec ... (hG : GSim xof V fresh) (hD : DefaultHyp) (rho : Slice Std.U8) (r s : Std.U8)
      (hterm : RejNTTTerminates (xof (rho.val.map (·.val) ++ [s.val, r.val]))) :
      ∃ p, sampling.rej_ntt_poly rho r s = ok p ∧
        p.val.map (·.val) = rejNTTPoly (xof (rho.val.map (·.val) ++ [s.val, r.val]))
  theorem sample_in_ball_spec ... (hH : HSim xof V fresh) (tau : Usize) (htau : tau.val ≤ 64)
      (hterm : SampleInBallTerminates (xof (rho.val.map (·.val))) tau.val) :
      ∃ p, sampling.sample_in_ball rho tau = ok p ∧ p.val.map (·.val) = sampleInBall ... ∧
        (∀ v ∈ p.val.map (·.val), Ternary v) ∧ weight (p.val.map (·.val)) = tau.val
  ```
  in `XofFix/Sampling/{RejNtt,RejBounded,InBall,Expand}.lean` (212 + 330 + 298 + 504 lines).
- What changes for this repo: RustCrypto's loop reads an 840-byte batch (G) / 272 bytes (H) and loops over the
  buffer; `src/sampling.rs` (read: `rej_ntt_poly`, `rej_bounded_poly`) squeezes 3 bytes (RejNTT) or 1 byte (RejBounded) per loop iteration into a fresh stack array. The step lemma is simpler but must be
  redone; the spec above uses the one-byte-offset `x c` form so both loop shapes map to it. The reduction from
  `GSim` squeeze equations to `x`-indexed bytes (`squeeze_array`, `absorb_array` in `XofFix/Sampling/Basic.lean`) may
  reduce to single `squeeze` equations.
- Original-vs-factored sampler loops (F-NTT, F-BND, F-BALL, F-EXA, F-EXS, `OrigNttIter`, `Cleanup.*_orig_callee`):
  not needed here (no refactor bridge, since the Rust is plain `while`).
- Satisfiability of termination: for the all-zero stream by `decide +kernel` (`rejNTT_zero` etc.); for real SHAKE only at
  a specific seed (see 11). No witness for all seeds, and none is claimed possible.
- Axioms: standard 3 (some use none or only `propext`). No `native_decide`. Size: Spec 136 + SpecFacts 366 + sampler
  proofs about 1,350.

## 8. Bit packing, skEncode, pk/sig codecs, hint pack/unpack (PARSE-01..05, KEYGEN-01 line 10)

- Pure spec fragments (Lean): `campaign/skencode-20261029/lean/Keygen/Spec.lean`: `intToBits` (Alg 9, LSB first),
  `bitsToBytes` (Alg 12), `simpleBitPack10` and `pkEncode` (Algs 16, 22, `bitlen(q-1)-d = 10` only).
  `campaign/skencode-20261029/lean/SkEnc/Spec.lean` (168 lines): `bitlen`, `bitPack a b w` (Alg 17:
  `z_i = b - w_i`, written with `bitlen(a+b)` bits), `skEncode eta rho K tr s1 s2 t0` (Alg 24, d = 13), `signed`,
  `sub_signed`, `signed_p2rLoRep`, and byte-formula lemmas about little-endian windows:
  ```lean
  theorem pack_byte (D : Nat) (hD : 0 < D) (l : List Nat) (m : Nat) (hm : 8 * m + 8 ≤ D * l.length) :
      (bitsToBytes (l.flatMap fun c => intToBits c D)).getD m 0 =
        ((List.range 8).map fun j => if (l.getD ((8 * m + j) / D) 0).testBit ((8 * m + j) % D) then 2 ^ j else 0).sum
  ```
  plus `sum_bits`, `psum`, `psum_lt`, `testBit_psum`, `flatMap_bits_length`, `flatMap_bits_getD`. These are what a
  bit-accumulator loop proof (`src/encode.rs:9 bit_pack`, `:28 bit_unpack`) needs; pure Nat/List, `omega`-based.
- Hint pack/unpack spec shape: `fipsWellFormed (bytes) k omega` in `campaign/parsing/hint-pack-v27/lean-acceptance-65/
  HintPackOuter65/Segments.lean:122` (a parameter-generic list predicate with `cutAt`, `byteSegment`, strictly
  increasing segments, zero padding), with `columns`/`writeValues`/`packList` lemmas (`packed_byte_segment`) and
  all-input acceptance `all_input_acceptance_65` (`accepted ↔ fipsWellFormed`). The list-level lemmas are generic in
  `k`, `omega`; the rest (`Output`, `Row`, `OuterCursor.*`) is bound to the extracted RustCrypto cursor parser and
  hybrid-array types. Reuse `fipsWellFormed` and its segment lemmas as the spec of HintBitUnpack (Alg 21).
- Not in Lean: BitUnpack/SimpleBitUnpack, pkDecode, sigEncode/sigDecode, skDecode, w1Encode. The campaign proved
  those with Kani, or not at all (public-key decode Aeneas extraction was excluded because of TOOL-7 region warnings).
- skEncode on extracted code (`SkEnc/{PolyPack,VecPack,VecInst,Top}.lean`) and `SkEnc/ByteEncode.lean` (322 lines) are
  about RustCrypto's `to_expanded` and hybrid arrays: do not port, but see `ByteEncode.lean` for a worked bit-packing
  proof structure (not read in detail).
- The `Q - a ≤ c` "mod q representative" trick (`InRange`, `sub_signed`): the campaign stored negatives as `c mod q`.
  This repo does the same: `pack_signed` (`encode.rs:50`) computes `sub(b, w[i])` (that is `(b + q - w) mod q`) and calls
  `bit_pack(&t, c, out)`, which takes values `< 2^c` and uses a `u64` accumulator (`acc`, `nbits`) with an inner
  `while nbits >= 8` flush. So `sub_signed` (`(b + Q - c) % Q ≤ a + b`) is the lemma for the first step and
  `pack_byte` for the accumulator step.
- Axioms: standard; `SkEnc` lane: 49 theorems, standard axioms (per report). Size: Spec fragments about 340 lines
  excluding the extracted-code proofs.

## 9. FIPS 204 spec transcription that already exists, and top-level algorithms

Requested item (4). Nothing near a complete spec exists. Inventory of what is in Lean:

| FIPS 204 item | Lean def | File |
|---|---|---|
| Alg 9 IntegerToBits, Alg 12 BitsToBytes | `intToBits`, `bitsToBytes` | `campaign/skencode-20261029/lean/Keygen/Spec.lean` |
| Alg 11 IntegerToBytes, Alg 13 BytesToBits | `integerToBytes`, `bytesToBits` | `.../Sampling/Spec.lean` |
| Alg 14, 15 CoeffFromThreeBytes/HalfByte | `coeffFromThreeBytes`, `coeffFromHalfByte` | `.../Sampling/Spec.lean` |
| Alg 16 SimpleBitPack (10 bits only), Alg 22 pkEncode | `simpleBitPack10`, `pkEncode` | `.../Keygen/Spec.lean` |
| Alg 17 BitPack, Alg 24 skEncode | `bitPack`, `skEncode` | `.../SkEnc/Spec.lean` |
| Alg 29 SampleInBall, 30 RejNTTPoly, 31 RejBoundedPoly, 32 ExpandA, 33 ExpandS (not ExpandMask 34) | see 7 | `.../Sampling/Spec.lean` |
| Alg 35 Power2Round (d = 13) | `modpm`, `p2rHi`, `p2rLoRep` | `.../Keygen/Spec.lean` |
| Alg 36 Decompose, 40 UseHint (integer level) | `rounded`/`balanced`/`high`/`low`/`oracleHint` | `campaign/native-use-hint-decompose-integer-v1/Decompose.lean` |
| Alg 41 NTT, 42 NTT⁻¹ | `fips41`, `fips42` (over `Vec`) | `campaign/ntt/lean-{forward-v4,inverse-v5}/...` |
| Alg 45 MultiplyNTT, AddNTT, matrix-vector product | `mulq`, `addq`, `dot`, `matvec`, `vadd` | `.../Keygen/Spec.lean` |
| Alg 6 ML-DSA.KeyGen_internal lines 1-9 (line 10 = skEncode) | `alg6 : Prims k l -> List Nat -> Alg6Out k l` | `.../Keygen/Spec.lean` |
| SHAKE128/256 (FIPS 202 Algs 1-9) | see 5 | `.../HashShake/Fips202.lean` |

`Keygen/Spec.lean`'s `alg6`, with SHAKE, ExpandA, ExpandS as parameters in a `Prims` structure:
```lean
def alg6 {k l : Usize} (P : Prims k l) (xi : List Nat) : Alg6Out k l :=
  let hb := H P.xof (xi ++ [k.val, l.val]) 128          -- line 1
  let rho := hb.take 32; let rhop := (hb.drop 32).take 64; let K := (hb.drop 96).take 32
  let A := P.expandA rho                                 -- line 3
  let s1 := P.expandSL rhop 0; let s2 := P.expandSK rhop l.val
  let t := vadd (vmap fips42 (matvec A (vmap fips41 s1))) s2   -- line 5
  let t1 := vmap p2rHiPoly t; let t0 := vmap p2rLoPoly t
  let pk := pkEncode rho t1.val; let tr := H P.xof pk 64 ...
```
Not in Lean anywhere (write fresh): Alg 1-5 (API layer, ctx handling, M′), Alg 2/7 Sign_internal and `Sign_internal_bounded`,
Alg 3/8 Verify_internal, Alg 18-20 BitUnpack family, Alg 21 HintBitUnpack (only as `fipsWellFormed`), Alg 23 pkDecode,
Alg 25-28 skDecode/sigEncode/sigDecode/w1Encode, Alg 34 ExpandMask, Alg 39 MakeHint, a FIPS-shaped Alg 37/38 HighBits/LowBits (only the integer-level `high`/`low` of `Decompose.lean` exist), norm checks.

Existing signing/verification theorems (`campaign/signing-candidate-v1/`, `signing-original-closure-v2/`,
`signing-h-connection-v3/`, `verifying/composed-v3/`): about the extracted RustCrypto `sign`/`raw_verify_mu` bodies,
conditional on many individual helper-success equations; they do not contain a FIPS 204 Sign/Verify spec to lift.
They are templates for the shape of a "one attempt" refinement only (SIGN-01: 54 conditional audits, partial).

Errata to apply when transcribing (source: `campaign/spec/FIPS204.txt`, `campaign/spec/errata-cells.json`,
NIST potential updates dated 2026-07-31, "not official"):
- Sec 6.2/6.3 text: M should be M′. Sec 3.3: c~ is mu ‖ w1 (as in Alg 7), not w1 ‖ mu.
- Alg 6 pseudocode should use Power2Round; Alg 3 step 2 should return `false`, not ⊥; Alg 1/2/4 NULL means ⊥.
- Alg 40 UseHint output bound is `0 <= r1 <= (q-1)/(2γ2) - 1`.
- Table 1 repetitions become 4.36, 5.14, 3.91; Table 3 minimum iteration limit for internal signing becomes 821
  (relevant to the κ budget B in STATUS.md; FORK-DESIGN's B = ⌊(2^16 - L)/L⌋ + 1 is unaffected).
- Appendix A (Montgomery) rewritten; not used by this repo's Barrett code.

Correctness argument (stretch goal): nothing exists. Needed and absent: NTT as ring homomorphism (or NTT-free algebra
for the spec), `t = t1*2^d + t0` use, `‖ct0‖∞ < γ2`, hint soundness, `UseHint(MakeHint(...)) = HighBits`.
`KeygenSpec.p2r_decomp` (`x = 8192 * p2rHi x + modpm x`) is the only related lemma.

## 10. Where the campaign's spec style conflicts with the planned one

- Planned: `ZMod q`, `Vector (ZMod q) 256`, `Fin k →` vectors. Campaign: `Nat % q` on `Array U32 256` with
  `Canonical`/`Can`. Two options: (a) keep the campaign's `Nat`-with-`%` spec and add one `ZMod` view lemma
  (`Nat.cast`, `ZMod.val_natCast`) at the top; (b) restate everything over `ZMod q` and prove the Nat lemmas as the
  bridge at the leaves. All campaign pure-Nat lemmas (sections 2, 3, 4a, 8) are needed either way.
- The campaign's NTT spec (`fips41` over `Vec`) is a *program* spec. A readable FIPS spec would define Alg 41 over
  `Vector (ZMod q) 256` with the same layer loop; `layerMath`/`blockMath` already have the right recursion and can be
  transcribed 1:1.
- `Aeneas.Std.Array`/`List` indexing (`w[i]!`, `.set`) leaks into the campaign's specs; use `Vector.get`/`Vector.set`
  or `Fin 256 → _` in the new spec and one projection lemma at the refinement boundary
  (campaign analogue: `coefficients_set`, `coefficients_get` in `TableValues.lean`).

## 11. Real-SHAKE termination witnesses (technique, not a lemma family to port)

`campaign/termination-witness-20261029/` shows how to kernel-check that a rejection loop terminates at a concrete seed:
`decide +kernel` for `cBlocks 168 5 (cPad 168 M) = [literal bytes]`, then `rejNTTRun_lit` rewrites the FIPS loop
onto the literal and `decide +kernel` runs the loop on 840 bytes. Cost and memory are in Performance. It matters for
ACVP-vector-level sanity (e.g., prove `RejTerm` at a given test seed) but not for the general theorem, which keeps
`RejTerm` as a named premise. Per-call statements establish both `isSome` at fuel F and `isSome = false` at F-1.

## Pitfalls (from TOOL-* / ERR-*)

Copied or summarized from `campaign/ISSUES-AND-FIXES.md`. Kani-specific items (TOOL-1, 2, 8, 9, 10) are listed only
briefly because this project's plan relies on Lean/Aeneas plus BINSEC; they matter if Kani is added later.

- **TOOL-3 Charon `reuses_default` (fixed upstream, not in our pin).** Charon labels explicit impls of *required*
  trait methods as `reuses_default = true`, which relaxes type checking for them. Filed as AeneasVerif/charon#1573,
  closed as completed 2026-10-28 (maintainer: an oversight). Our pin is Charon `nightly-2026.09.02` (FORK-DESIGN §6
  already records it). The new code has no trait impls to speak of (free functions), so exposure is low; a
  one-hunk candidate patch exists (`campaign/native-charon-default-reuse-remediation-plan-v1/candidate.patch`,
  unbuilt).
- **TOOL-4 Aeneas ignores `Drop` (default and `-eval-drops`).** The interpreter discards the destructor callee
  (`src/interp/InterpStatements.ml:805-810`); `-eval-drops` produced a byte-identical `Funs.lean`. Extracted models
  assume destructors are no-ops, so totality and secret-erasure claims do not follow for types with non-trivial
  `Drop`. FORK-DESIGN already scopes zeroize out; keep any `Drop`/`Zeroize` type out of the extraction closure.
- **TOOL-5 Aeneas crash on instantiated ADT names.** `ctx_compute_var_basename` raises `Failure "Unexpected"` on an
  unnamed local of type like `Elem<BaseField>`, leaving a truncated `Funs.lean` (check the exit status). Also four
  declaration-name collisions were reported in that (monomorphized) export; this repo uses generic Charon (STATUS.md
  decision), and whether the collisions arise there: not checked.
- **TOOL-6 hax `-core-models-lib` exit 0 with missing definitions.** Run pinned Aeneas directly on untouched LLBC,
  without that flag (campaign mitigation); a truncated project shows up only at `lake build` ("Unknown identifier
  `typenum...`"). Filed as pereq-dev/aeneas#92. The scripts here already run Aeneas directly (per STATUS.md gate);
  keep the "exit 0, no `[Error]`/`[Warning]`" gate.
- **TOOL-7 "extracted code may be incorrect" (unknown region mutability) and erased-region internal errors.** Appears on
  iterators over `&mut` chunks (hybrid-array). Treat any such warning as High: the campaign excluded every
  translation containing it. Not expected for index-based `while` loops; keep it in the gate.
- **TOOL-11 Aeneas items.** A type-name printer crash on concrete types in names, worked around by metadata-only
  renames with an exact inverse (195 renames in one lane); `Not_found` on a higher-order signing driver; unsupported
  FnOnce adapters; unused dictionaries that break the Lean build. Common-subexpression elimination (e.g., `w - cs2`
  computed once) means the extracted model is only a value relation, call counts and effects are not modeled.
- **TOOL-12 Aeneas cannot extract `Iterator::map`/`zip`/`fold` or operator impls on references.** Forced seven
  lane-copy factorings, each needing an ADAPTER bridge. The reason this repo uses plain `while` loops and arrays.
  Do not reintroduce iterator chains, closures, `impl Add for &T`, or `chunks_exact` in extracted code.
- **Generated `FunsExternal_Template.lean` contains `opaque`/`axiom`-like declarations.** grep for `opaque`/`axiom`
  in the campaign hits only these unimported templates. The real `FunsExternal.lean` replaces them with explicit
  definitions delegating to `CoreModels`/Aeneas `Std`. The project gate "no local opaque function" must be checked
  on the imported file, not by grepping the whole `lean/` tree. Which core functions this repo's code needs models
  for (`wrapping_sub`, `<<`, casts): not checked.
- **ERR-15 unsatisfiable hypothesis interfaces (read this before writing `XofSim`).**
  - `SamplingLean.XofHyp` allowed `absorb` after `squeeze`; in `crypto.rs` that is `unreachable!()`, so no faithful
    SHAKE model satisfies it (`g_not_xofHyp`, `h_not_xofHyp`). Every "conditional" sampler theorem was vacuous.
  - `KeygenLean.ShakeHyp` had `view : State → List Nat × Nat`; any such function forces an infinite state
    (`shakeHyp_infinite`, `shakeHyp_unsat_of_finite`), while the Rust state is finite (200 bytes plus cursor).
  - The first repair `XofHyp'` (adds a `fresh` premise) still forced an infinite state (`xofHyp'_infinite`).
  - The fix: relate state to stream position by a *relation* `V s m o` plus a phase predicate `fresh`; require
    `absorb` only on fresh states; prove a finite model satisfies it (`fst_finite`, `g_sim`).
  - Process rule: every hypothesis interface needs a satisfiability theorem, ideally with a Rust-faithful finite model,
    and a "not vacuous" theorem that instantiates all premises of the top theorem at once (`nonvacuous_*`).
  - Termination premises (`ATerm`/`STerm`) were first witnessed only by an all-zero stream. Real-SHAKE witnesses were
    added later for one seed (section 11). For this repo's `RejTerm`, do the same: witness at ξ = 0^32 at minimum.
- **ERR-16 ledger misattribution** (XOF interface work was filed under the wrong obligation). Only a bookkeeping
  lesson: name the obligation each lemma discharges and check against `obligations.json`.
- **ERR-17 hidden dependency.** A transfer theorem stated over factored code silently also depended on the loop
  bridges. Lesson: when a theorem about function F is derived through a replaced callee, say so in the statement.
- **ERR-18 Keccak backend selection on Apple silicon is compile-time.** RustCrypto `keccak` takes the AArch64 SHA3
  path always on `aarch64-apple-darwin`; the soft-backend proofs did not cover the host. Not applicable to the in-crate
  Keccak, but any differential test must run the same binary the proof is about.
- **Axiom-printing parser bug (listed under "Reviewed and excluded", not an ERR).** The campaign's own
  `#print axioms` parser falsely rejected universe-suffixed names such as `Classical.choice.{u}`; check that
  `scripts/check-axioms.sh` here accepts them. (ERR-13 is a different parser bug: an incomplete text parser reported
  passing axiom checks as failing.)
- **Kani-related (only if added):** TOOL-1/TOOL-2 (mutable ghost statics alias constants, reads of atomics' `Ordering`
  from mutable cells; use non-zero initial values for ghost statics and audit models); TOOL-8 (function contracts
  drop the write-set argument); TOOL-9 (stubs not applied to inlined calls, kani#5094); TOOL-10 (CBMC 16-bit object
  model bounds "every length" claims).
- **FIPS 204 spec subtleties already hit:** hint-array acceptance must reject non-increasing indices within a row,
  decreasing/over-ω cuts and nonzero padding; the campaign's hint spec is `fipsWellFormed`. Also ExpandMask nonce
  overflow at u16 on the last ML-DSA-87 attempt (ML-2) and contexts of 256 bytes aliasing (ML-1) are upstream bugs
  that motivate the explicit `ctx ≤ 255` and bounded-κ statements in STATUS.md.

## Performance notes

Numbers are from campaign reports/logs; hardware differs per lane ("this machine" in the reports is an Apple-silicon
Mac, 64 GB where stated).

- **NTT forward lane (`campaign/ntt/lean-forward-v4`).** Cold `lake build`: 40.2 s for 1,749 jobs
  (`campaign/ntt/logs/lean-forward-checkpoint-v4-first-build.json`); warm rebuild 4.9 s. Last three modules:
  `Bridge` 5.4 s, `LayerModel` 2.2 s, `NttWholeForward` 1.8 s. v3 (table plus first layer): 12.4 s then 1.5 s warm. Inverse
  v5: 6.7 s on a warm cache. Per-module times for the heavy modules (`GenericOuter`, `ForwardCorrect`): not extracted.
  Settings seen: `maxHeartbeats 4000000` + `maxRecDepth 8192` (`TableValues`, field proofs), `2000000` + `8192`
  (`GenericOuter`). No file needed more.
- **What made 256-element loops tractable.** (1) No unrolling; counter-indexed induction. (2) Arrays treated as
  Aeneas `Array U32 256` with `.set` and `[i]!`, with `Array.getElem!_Usize_set_ne/_eq` as the only frame lemmas.
  (3) Eight layers proven equal to one parameterized layer by `rfl`. (4) `Canonical` as a universally quantified
  predicate with `canonical_set`, not a `decide` over 256 values. (5) Failure/divergence preserved by explicit
  `cases` on the three `RustM` constructors, not `step*` automation. (6) `decide +kernel` is used only on closed
  Nat/List data (table, 3 uses in the NTT lanes).
- **Where it was slow:** (a) Kani, not Lean: whole forward NTT and first-layer Kani comparisons timed out at 180 s; the
  campaign moved those to Lean. Vector lifting took 118 to 551 s per run. (b) Lean elaboration of definitional-change
  steps in the UseHint integer composition (see 3). (c) Kernel evaluation of Keccak, below.
- **Kernel-evaluated SHAKE** (`campaign/termination-witness-20261029/RESULTS.md` §6): one Keccak-f[1600] by
  `decide +kernel` 2.7 s; four chained 12.8 s; one ExpandA call (5 permutations plus loop over 840 bytes) 32 s kernel,
  peak RSS about 9.8 GB; one ExpandS call about 26 s. 136 witness modules took 68 CPU-minutes, 29 min wall, in batches of
  3. Running 18 in parallel pushed a 64 GB machine into swap. Memory is the constraint, not time; limit parallel
  `lake build` jobs. On the closure-heavy bit-level `Fips202.xof` the kernel is "hopeless" without the lane
  materialization in `TermWit/Stream.lean` (each round is a closure over the previous one).
- **Whole-chain build costs.** `lake build HashShake`: 8,980 jobs. `XofFix`: 15 modules, about 60 s cold. `lean-cleanup-20261029` from an empty
  `lean/.lake/build` (shared package builds): 2 min 56 s. `skencode-20261029/run.sh`: about 15 s warm.
  Adapter/ShakeStateX/ShakeMulti/Cleanup on a cloned witness build: 80 s first build.
- **Fuel/measure pattern for rejection loops:** explicit `fuel : Nat` in the spec (`rejNTTRun x fuel c a`),
  monotonicity lemma (`*_mono_le`), `Nat.find` for the total function. Avoids well-founded recursion on a loop that
  may not terminate.
- **Tooling for large replays:** the campaign hashed all inputs and lake dependency snapshots before/after each run
  and kept `logs/` per lane (`run.sh` pattern); `lake build` has no job cap by default, so batch heavy modules.

## Suggested port order (for the NTT refinement prototype and the Spec)

1. `campaign/ntt/lean-forward-v4` machinery (Geometry, `smallIndex`, `Canonical`, `mathButterfly`, `blockMath`,
   `layerMath`) into `lean/Proofs/` over the new extraction; this is the "main proof-performance risk" from
   STATUS.md and has a measured baseline (about 40 s cold for the polynomial NTT, forward).
2. `campaign/bridge/field-reduction/completed-operations/MlDsa/Proof.lean` for `small_reduce`/`barrett_reduce`/
   `add`/`sub`/`neg`/`mul`.
3. `Fips202.lean`, `KeccakLanes.lean`, `Sponge.lean`, `Shake.lean` (copy; re-point at the in-crate sponge).
4. Sampler spec and facts; `XofSim`-style relation for the in-crate `Shake`.
5. Pure-Nat lemma files (sections 2, 3, 8) as `Spec/Lemmas/*.lean`.
6. Write the FIPS 204 spec fresh in the chosen representation, using the section 9 table as the checklist and the
   errata list.
