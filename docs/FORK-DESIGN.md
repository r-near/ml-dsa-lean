# Proof-first ML-DSA fork: design

Goal: one end-to-end Lean proof a reader can follow, of a Rust ML-DSA whose functions are FIPS 204's algorithms. The
fork is based on upstream master `a3690c4`, which already carries the upstream fixes #1481, #1483, #1488 and #1489.
Everything here is backed by `fork-skeleton/`:

- **Differential test:** `Sign_internal` for all three parameter sets is byte-identical to upstream master
  `ExpandedSigningKey::sign_internal(..).encode()` on 75 cases (`fork-skeleton/tests/diff.rs`).
- **Extraction:** the crate extracts with the campaign's pinned Charon and Aeneas with no errors, warnings, name clashes
  or opaque local functions.
- **Lean build:** the extracted Lean builds with `lake` against Aeneas `build-183e4f0`. All 180 extracted definitions
  depend only on `propext`, `Classical.choice` and `Quot.sound` (`logs/master-fork-generic/lake.log`; the extracted
  files are in `fork-skeleton/extracted-lean/`).

## 1. Code shape

Each FIPS 204 algorithm gets one Rust function with the algorithm's name. It follows the algorithm's step order, and
its comments cite the step numbers. The core follows the rules in BLOCKERS.md, each one backed by a failure seen in this
lane:

1. **Loops.** Use `while i < N { …; i += 1 }` over fixed-size arrays. No `for`, ranges, iterator adapters or closures:
   iterator adapters and closures fail in TOOL-12 (BLOCKERS §A, §C), and `for` pulls in `Step` axioms (B-F2).
2. **Arithmetic.** Use free functions (`field::add/sub/mul/neg`, `ntt::multiply_ntt`, `ntt::matrix_vector_ntt`).
   Operator-trait impls on references fail (BLOCKERS §B). Scalar `Elem` impls extract, but plain functions read better
   in Lean.
3. **Types.** Use native `[u32; 256]` (canonical `0 ≤ x < q`), `[[u32; 256]; K]`, `[[[u32; 256]; L]; K]`, `[u8; N]`, and
   `&[u8]` for variable-length input. No `hybrid-array`, `typenum`, `module-lattice` or `MaybeBox`. This retires
   BLOCKERS §B, §C and B-O4: the trusted `hybrid_array` index/deref models go away, because Aeneas has a model for
   native array indexing (`Array.index_usize`, `Array.update`).
4. **Nested loops.** Lift a per-coefficient inner loop into its own function when it reads data the outer body just
   wrote (B-F1). `poly_high_bits` and `poly_low_bits` exist for this reason, and they also read as "HighBits applied
   coefficient-wise".
5. **Core library.** Avoid `copy_from_slice`, `to_le_bytes`, `chunks_exact`, `windows`, `rotate_left` and `u16 + u16`
   near the nonce limit. Write the byte loops and shifts out (e.g. `[nonce as u8, (nonce >> 8) as u8]` is
   IntegerToBytes(·, 2)).
6. **Constant time.** Keep upstream's mask idioms for secret-dependent selects (`ct_lt_mask`, `ct_select`, Barrett
   division, the `small_reduce` mask). Branch only on public data: rejection decisions and the encoding of the final
   hint, as upstream does.

What the extracted Lean looks like (from `fork-skeleton/extracted-lean/Survey/Funs.lean`, unedited):

```lean
def rounding.power2round (r : Std.U32) : RustM (Std.U32 × Std.U32) := do
  let i ← 1#u32 <<< 13#i32
  let r0 ← rounding.mod_plus_minus r i 28#u32 32768#u64
  let i1 ← field.sub r r0
  let r1 ← i1 >>> 13#i32
  ok (r1, r0)

def sampling.rej_ntt_poly (rho : Array Std.U8 34#usize) : RustM (Array Std.U32 256#usize) := do
  let a := Array.repeat 256#usize 0#u32
  let ctx ← keccak.Shake.shake128
  let s ← lift (Array.to_slice rho)
  let ctx1 ← keccak.Shake.absorb ctx s
  let ctx2 ← keccak.Shake.finalize ctx1
  sampling.rej_ntt_poly_loop a ctx2 0#usize

def sign.sign_internal_loop.body {K L : Std.Usize} (p : params.Params) (sig : Slice Std.U8) … (kappa : Std.U32) :
    RustM (ControlFlow Std.U32 (Bool × (Slice Std.U8))) := do
  let i ← lift (UScalar.cast .U32 L)
  let i1 ← kappa + i
  let i2 ← i1 - 1#u32
  if i2 <= 65535#u32 then
    let i3 ← lift (UScalar.cast .U16 kappa)
    let o ← sign.attempt p a_hat s1_hat s2_hat t0_hat mu rho_pp i3
    match o with
    | none => let kappa1 ← kappa + (← lift (UScalar.cast .U32 L)); ok (cont kappa1)
    | some (c_tilde, z, hint) => … ok (done (true, sig1))
  else ok (done (false, sig))
```

(The last block's `match` arms are condensed here for space; the file has them in full.) Every loop becomes a
`*_loop.body` function plus a `loop` combinator. `K` and `L` stay generic, so there is one Lean definition, and one
proof, per algorithm for all three parameter sets. `Params` is a plain Lean `structure`. The extraction has 3,128 lines
of `Funs.lean` for the whole signing path, including Keccak.

### Algorithm map (fork module → FIPS 204)

"Skeleton" means the function exists in `fork-skeleton/` and is covered by the differential test or extraction.

| FIPS 204 | Fork function | Status |
|---|---|---|
| Alg 1 ML-DSA.KeyGen | `api::keygen_{44,65,87}` (rnd from the caller's RNG, wrapper only) | planned |
| Alg 2 ML-DSA.Sign / Alg 3 ML-DSA.Verify | `api::sign`, `api::verify` (build M′ = 0‖|ctx|‖ctx‖M, reject |ctx| > 255) | planned |
| Alg 4/5 HashML-DSA | out of scope (upstream does not implement it either) | — |
| Alg 6 KeyGen_internal | `keygen::keygen_internal<K,L>` | planned |
| Alg 7 Sign_internal | `sign::sign_internal<K,L>` (loop body steps 11–29 in `sign::attempt`) | **skeleton** |
| Alg 8 Verify_internal | `verify::verify_internal<K,L>` (includes sigDecode and the ‖z‖∞ check) | planned |
| Alg 9–13 bit/byte conversions | spec-only in Lean. Rust packs with a bit accumulator (`encode::bit_pack/bit_unpack`), and a lemma relates the two | skeleton (pack/unpack) |
| Alg 14 CoeffFromThreeBytes | `sampling::coeff_from_three_bytes` | **skeleton** |
| Alg 15 CoeffFromHalfByte | `sampling::coeff_from_half_byte` | planned |
| Alg 16–19 (Simple)BitPack/Unpack | `encode::bit_pack`, `bit_unpack`, `pack_signed`, `unpack_signed` | **skeleton** |
| Alg 20 HintBitPack | `encode::hint_bit_pack` | **skeleton** |
| Alg 21 HintBitUnpack | `encode::hint_bit_unpack` (explicit index loops, replaces B-A14) | planned |
| Alg 22/23 pkEncode/pkDecode | `encode::pk_encode/pk_decode` | planned |
| Alg 24/25 skEncode/skDecode | `encode::sk_encode`, `encode::sk_decode` | skDecode **skeleton** |
| Alg 26/27 sigEncode/sigDecode | `encode::sig_encode`, `encode::sig_decode` | sigEncode **skeleton** |
| Alg 28 w1Encode | `encode::w1_encode` | **skeleton** |
| Alg 29 SampleInBall | `sampling::sample_in_ball` | **skeleton** |
| Alg 30 RejNTTPoly | `sampling::rej_ntt_poly` | **skeleton** |
| Alg 31 RejBoundedPoly | `sampling::rej_bounded_poly` | planned |
| Alg 32 ExpandA / 33 ExpandS / 34 ExpandMask | `sampling::expand_a`, `expand_s`, `expand_mask` | A, Mask **skeleton** |
| Alg 35 Power2Round … 38 LowBits | `rounding::power2round`, `decompose`, `high_bits`, `low_bits` | **skeleton** |
| Alg 39 MakeHint / 40 UseHint | `rounding::make_hint`, `use_hint` | MakeHint **skeleton** |
| Alg 41 NTT / 42 NTT⁻¹ | `ntt::ntt`, `ntt_inverse` (upstream's `ntt_layer` structure) | **skeleton** |
| Alg 43 BitRev8 | spec-only. `ntt::ZETAS` is a literal table, and Lean checks it against ζ^BitRev8(k) | skeleton (table) |
| Alg 44–48 AddNTT … MatrixVectorNTT | `ntt::add_poly`, `multiply_ntt`, `scalar_vector_ntt_inverse`, `matrix_vector_ntt` | **skeleton** |
| Alg 49 MontgomeryReduce | not used. The fork reduces with Barrett, as upstream does; FIPS 204 allows any equivalent reduction | — |
| FIPS 202 Keccak-f[1600], SHAKE128/256 | `keccak::keccak_f1600`, `keccak::Shake` | **skeleton** |

## 2. Structure

- **Parameter sets.** Use `const K: usize, const L: usize` on every vector function, plus a `&Params` value
  (`params::ML_DSA_{44,65,87}`) with η, τ, β, γ1, γ2, ω, λ/4 and the derived bit widths and Barrett constants.
  - *Why not a params trait with associated consts:* array lengths like `[T; P::K]` need the unstable
    `generic_const_exprs`, and the typenum route is what produced §B and §C.
  - *Why not one monomorphic copy per set:* three copies would mean three proofs.
  - *Why Charon runs without `--monomorphize`:* the generic run has 0 referenced external axioms, while monomorphized
    slice and range indexing adds 9 (B-X3).
  - The thin API asserts `K = p.k` and `L = p.l` (planned: one `debug_assert` per entry point, and a Lean lemma
    instantiating the three cases).
  - Byte lengths come from `params::{sk_len, sig_len}`. The core takes `&[u8]` / `&mut [u8]` of exactly that length,
    and the API exposes fixed arrays (`[u8; 2560]` and so on).
- **SHAKE.** It lives in the crate, in `keccak.rs`: a plain-loop Keccak-f[1600] and a byte-wise sponge. It replaces
  `ml_dsa::crypto` and the `shake`/`keccak` crates, so the accepted opaque SHAKE boundary disappears. **It is new code
  text.** The campaign's HASH-01 is about `keccak` 0.2.0's soft backend, and master now locks `keccak` 0.2.2, which
  rewrote round-constant handling (`diff/keccak-0.2.0-to-0.2.2.diff`). So the proved permutation does not carry by
  identity. What carries is the campaign's FIPS 202 Lean spec and the ERR-15 `XofSim`/`ShakeSim` interface. The fork
  needs its own small permutation proof: 24 rounds of θρπχι over a 25-lane array, about 130 lines of Rust. The proof
  can be by computation per round on symbolic lanes, or by bit-blasting (`bv_decide`) one round. Backing evidence:
  the NIST SHAKE KATs, and the differential test already covers SHAKE through every signature.
  - *Performance:* a byte-wise sponge is slower than upstream's lane-wise one. Even so, Sign is within 1.07× (§7).
- **Public API.** A thin `api` module (or a second crate, `ml-dsa-fork`) holds the per-set fixed-array entry points.
  Above it sit, outside the proof boundary, `signature::{Signer, Verifier, Multipart*, Digest*}`, rand_core, PKCS#8
  and the `KeyInit`/`KeyExport` traits. These only delegate. The proof covers `api::*` and everything below it.
- **Key caching.** Upstream's `ExpandedSigningKey` (precomputed ŝ1, ŝ2, t̂0, Â) and `VerifyingKey` precompute become
  plain structs of arrays, built by a function whose Lean postcondition is "fields = NTT(skDecode(sk))". This also
  closes most of the measured performance gap (§7).

## 3. What to keep

- **checkct / BINSEC** (`upstream-master/ml-dsa/checkct/`, nightly-2026-10-06, `-Zbuild-std`, targets
  riscv32imac, thumbv7em and x86_64).
  - *How upstream does it:* the driver includes production modules through `#[path = "../../../src/…"]` and probes
    straight-line steps with every input secret: `signing_steps::response` (FIPS steps 18–21 plus both norms),
    `hint_polynomials` (25 and the w − cs2 + ct0 sum), `Hint::new` with `hamming_weight` (26), `expand_mask_xof`, and
    `Gamma1::unpack`.
  - *What the fork does:* the fork is `no_std` with no dependencies, so the same `#[path]` trick works unchanged. The
    fork exposes the same step boundaries as `pub(crate)` functions. Concretely, split `sign::attempt` into `response`
    (steps 18–21, returning z, w − cs2, r0) and `hint_step` (steps 25–26), and keep the two rejection `if`s in
    `attempt`. Its probes are then one-line ports.
  - *The fork's own CT surface:* its mask primitives (`ct_select`, `ct_lt_mask`, `small_reduce`) replace ctutils. They
    are exactly what BINSEC checks, at assembly level. The campaign's ctutils proofs (BACKEND-01, portable cmov)
    become unnecessary.
  - Add one probe for `keccak_f1600` with a secret state.
- **zeroize.** Keep it as a feature of the wrapper: `Zeroize`/`ZeroizeOnDrop` on the key structs, and an explicit
  zeroize of `rho_pp`, `y` and the other secrets at the end of `sign_internal`. TOOL-4: Aeneas does not model `Drop`,
  so erasure stays outside the Lean proof. It joins the trusted base, as SECRET-01 does today, and can be checked by a
  Kani or test harness on the concrete key types.

## 4. Lean target

- **`FIPS204/Spec.lean`** (estimated 700–900 lines). It transcribes FIPS 204 Algorithms 1–3 and 6–48:
  - Values: ZMod q coefficients, `Vector (ZMod q) 256` polynomials and `Fin k →` vectors, with bytes and bits as lists.
  - Hashing: `H`/`G` as FIPS 202 SHAKE from the campaign's Keccak spec.
  - Each algorithm is one `def` with the same name, and the step numbers appear in comments, so a reviewer can read
    it side by side with the PDF.
  - Alg 7's unbounded `while` becomes `Sign_internal_bounded B` (B attempts, `Option` result). Appendix C permits
    this, and a lemma relates it to the unbounded loop: if the first accepting κ comes within B attempts, the two agree.
  - Spec fidelity is reviewed independently, once.
- **Per-algorithm refinement theorems.** Each one has the form `Fork.f args = ok (Spec.f (⟦args⟧))` under
  representation invariants: canonical coefficients, and slice lengths `= sk_len p`.
  - *Loops:* each loop gets an invariant lemma on its `_loop.body`.
  - *Rejection loops:* RejNTTPoly, RejBoundedPoly and SampleInBall's inner draw are stated as partial correctness,
    "returns ⇒ equals the spec". Termination is a named premise, `RejTerm ρ`: the stream yields enough accepted
    samples. That cannot be proved for SHAKE; it is a probabilistic fact.
- **Top theorems** (premises named):
  - `keygen_internal_correct : RejTerm(ExpandA ρ) → RejTerm(ExpandS ρ′) → Fork.keygen_internal p ξ = ok (Spec.KeyGen_internal p ξ)`.
    Corollary for Alg 1/6: `api::keygen` with RNG output ξ equals ML-DSA.KeyGen.
  - `sign_internal_correct : sk = Spec.skEncode … (well-formed) → RejTerm(ExpandA ρ) →`
    `Fork.sign_internal p sk M′ rnd = ok (true, σ) ↔ Spec.Sign_internal_bounded p B sk M′ rnd = some σ`,
    and `= ok (false, _) ↔ … = none`, with B = ⌊(2¹⁶ − L)/L⌋ + 1 (16384, 13107 and 9362).
    SampleInBall's draw needs `RejTerm` as well. Corollary for Alg 2: the ctx check and M′ construction.
  - `verify_internal_correct : RejTerm(ExpandA ρ) → RejTerm(SampleInBall c̃) → Fork.verify_internal p pk M′ σ = ok (Spec.Verify_internal p pk M′ σ)`
    for every byte string pk and σ. Because the fork's Alg 8 contains sigDecode, HintBitUnpack and the ‖z‖∞ < γ1 − β
    check, the theorem needs **no signature-invariant premise**. Compare upstream, where `Signature::decode` and
    `raw_verify_mu` are split and VERIFY-01 needed decoded-signature invariants. Corollary for Alg 3.
- **Stretch: correctness.**
  - Statement: for every ξ, M, ctx with |ctx| ≤ 255 and rnd, with `(pk, sk) = KeyGen_internal ξ`: if `Sign` returns σ,
    then `Verify pk M σ ctx = true`.
  - The proof works only on `Spec` (FIPS 204 §3.4 / the Dilithium argument). It needs:
    - the identity w − cs2 + ct0 = Az − ct1·2^d, since t = t1·2^d + t0;
    - ‖ct0‖∞ < γ2, so UseHint(h, w − cs2 + ct0) = HighBits(w − cs2);
    - ‖cs2‖∞ ≤ β with ‖r0‖∞ < γ2 − β, so HighBits(w − cs2) = HighBits(w) = w1;
    - the encode/decode round trips for pk and σ.
  - It is independent of Rust, and it then transfers to the fork through the three top theorems.

## 5. Reuse of campaign proofs (when the fork keeps the code text)

| Component | Campaign evidence | Fork text vs proved text | Reuse |
|---|---|---|---|
| Field add/sub/neg/mul, small and Barrett reduce | ARITH-02/03 (module-lattice 0.2.3 macro bodies) | same expressions with macro parameters substituted; `wrapping_neg` is now `0.wrapping_sub` | lemmas port almost verbatim. Re-extract and re-run the proof scripts |
| mod±, Decompose, HighBits/LowBits, ct_div, Power2Round, infinity norm | ARITH-01, HINT-01, keygen P2R (portable ctutils) | same arithmetic. `ctutils` calls become in-crate masks (one-line lemmas) | light adaptation. The ctutils 0.4.7 bump no longer matters |
| MakeHint/UseHint scalar | HINT-01 | same formula | light adaptation |
| NTT layers and twiddle table | NTT-01/02/03 | the `ntt_layer<LEN, ITERATIONS>` shape is kept. `for` becomes `while`, Elem becomes `u32` with `field::*`, and the table is a literal | the math (layer schedule = FIPS 41/42) is reused. Loop-invariant scripts are redone for the `loop` form. The table needs a new `decide` check against ζ^brv |
| Vector/matrix NTT products | NTT-04, ARITH-04, keygen addFwd/matFwd (ADAPTER) | new plain functions | redo, but simpler: no ADAPTER, no Kani join |
| CoeffFromThreeBytes / HalfByte | SAMPLE-01 | same logic | light adaptation |
| RejNTTPoly, RejBoundedPoly, SampleInBall | SAMPLE-02/03 (with F-NTT/F-BND/F-BALL bridges) | different loop shape: 3 bytes per squeeze, not an 840-byte buffer | `XofSim` framework and output specs reused. Loop proofs redone, with no refactor bridge |
| ExpandA/S/Mask | SAMPLE-04 (F-EXA/F-EXS) | index loops | spec lemmas reused. No bridge |
| Encodings (BitPack, skEncode, pk/sig codecs, HintBitPack/Unpack) | PARSE-01..05, skEncode lane (F-PPACK/F-VPACK/F-BENC) | new bit-accumulator code | the spec-level BitPack lemmas carry. The Rust side is redone around one accumulator lemma |
| SHAKE / Keccak | HASH-01/02/03 | new text (see §2) | FIPS 202 spec and XOF interface reused. Permutation and sponge proofs are new, but small |
| KeyGen, skEncode, Sign attempt, Verify | KEYGEN-01, skEncode lane, SIGN-01, VERIFY-01 | new composition code | spec-side statements reused as templates. Every ADAPTER hypothesis and Kani-to-Lean join disappears |

Net: no campaign theorem carries **as-is** to the fork, because none of its extracted Lean is byte-identical. The math
lemmas carry for arithmetic, rounding, hint and NTT, plus the FIPS 202/XOF specs and the sampler output specs, and the
ADAPTER and Kani bridges are gone. Section 4 of SURVEY.md has the carry-over map onto master itself.

## 6. Trusted base

1. **Spec fidelity.** `FIPS204/Spec.lean` and the FIPS 202 spec are faithful transcriptions. This needs one
   independent review, plus executable cross-checks: run the Spec on ACVP vectors via `#eval`/`native_decide`, outside
   the trusted proof.
2. **Translation.** Charon nightly-2026.09.02 and Aeneas build-183e4f0 translate Rust semantics faithfully: their
   machine-integer models, `loop`, arrays and slices. TOOL-3 is fixed upstream but not in this pin. TOOL-4 (`Drop`
   ignored) is irrelevant to the core, which has no `Drop`, but relevant to zeroize.
3. **Compilation.** rustc/LLVM compile the extracted MIR's meaning. The CT property is checked separately, on binaries,
   by BINSEC.
4. **Lean.** The Lean 4.31 kernel, plus the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
5. **Termination.** The rejection loops terminate (`RejTerm`). This is probabilistic: for honest seeds a loop runs past
   its budget with probability below 2⁻¹²⁸ (FIPS 204 App. C). Sign's κ budget turns non-termination into an explicit
   `false`. ExpandA, ExpandS and SampleInBall need the premise.
6. **Outside the proof.** The wrapper layer (traits, PKCS#8, RNG plumbing) and zeroize.

**Differential testing plan.**

- *(a) Fork vs upstream master,* through the deprecated expanded-key API. This is done for Sign_internal: 25 cases per
  set (`fork-skeleton/tests/diff.rs`). Extend it to KeyGen (`from_seed` vs `keygen_internal`), Verify (accept and
  reject, including mutated σ, malformed hints and |ctx| = 256), and many-iteration rejection cases.
- *(b) NIST ACVP ML-DSA vectors* (keyGen, sigGen deterministic/hedged with internal and external interface, sigVer),
  vendored as JSON test data.
- *(c) Wycheproof ML-DSA vectors,* for decode edge cases.
- *(d) A fuzz target* comparing fork and upstream on random seeds, messages and contexts.
- *(e) The Lean Spec* evaluated on a few ACVP vectors, as a fidelity check.

## 7. Cost

- **Size.**
  - Skeleton: 1,022 lines of Rust (about 865 non-blank, non-comment) covering Sign_internal end to end, with
    skDecode, sigEncode, samplers, NTT, rounding and Keccak.
  - Full core (adding KeyGen_internal, Verify_internal, pk/sk/sig codecs, HintBitUnpack, ExpandS, RejBoundedPoly,
    UseHint and the key-cache structs): about 1,500–1,800 lines.
  - API and wrapper with traits and PKCS#8: about 500 more.
  - For comparison, upstream ml-dsa `src/` is 2,854 non-blank lines (tests included) plus module-lattice's 677, on top
    of hybrid-array, typenum and the shake/keccak crates.
- **Performance** (box, x86_64, `--release`, 300 signatures, `logs/fork-bench.log`):

  | Set | Upstream sign_internal | Fork sign_internal | Ratio |
  |---|---|---|---|
  | ML-DSA-44 | 380 µs | 385 µs | 1.01× |
  | ML-DSA-65 | 653 µs | 651 µs | 1.00× |
  | ML-DSA-87 | 734 µs | 785 µs | 1.07× |

  The fork's number **includes skDecode, three vector NTTs and ExpandA on every call**, which upstream precomputes in
  `ExpandedSigningKey`. A cached-key struct should therefore come in under upstream. Only this one hot path was
  measured; Verify and KeyGen were not.
- **Effort** (person-weeks, for someone fluent with this campaign's Aeneas and Lean setup):

  | Phase | Work | Estimate |
  |---|---|---|
  | 0 | Finish fork code (KeyGen, Verify, codecs, key cache, wrapper, checkct probes); differential, ACVP and fuzz tests | 1.5–2 |
  | 1 | `Spec.lean` for FIPS 204 plus the FIPS 202 reuse; independent spec review | 2–3 |
  | 2 | Leaf refinements: field and rounding (ports), NTT (port the math, redo invariants), Keccak permutation and sponge (new, small), encodings (new accumulator lemma), samplers (port XofSim) | 4–6 |
  | 3 | Composition: ExpandA/S/Mask, KeyGen_internal, the Sign attempt and loop, Verify_internal | 2–3 |
  | 4 | External Alg 1–3 and the API wrappers | 0.5–1 |
  | **Total** | **through the three top theorems** | **10–15** |
  | 5 (stretch) | Spec-level correctness, verify(sign) = true | 3–5 |

  The biggest risk is Lean proof performance on 256-element arrays inside `loop` bodies; NTT is the worst case. The
  campaign has already paid that cost once, for upstream's layer shape.
