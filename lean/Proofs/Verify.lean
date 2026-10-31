import Spec.MLDSA
import Proofs.StdParams
import Proofs.Bridge
import Proofs.EncodeKeys
import Proofs.KeyGen
import Proofs.SampleA
import Proofs.SampleBall
import Proofs.SigCodec
import Proofs.NTTOps
import Proofs.NTTInverse
import Proofs.NTT
import Proofs.Rounding
import Proofs.Steps
import Proofs.ExpandMask
import Proofs.Keccak

/-!
# Verify_internal (Algorithm 8)

`verify_internal_spec`: the extracted `verify.verify_internal K L ip pk m_prefix m σ` returns `b` whenever
`Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F = some b`, for every byte string `pk`,
`σ` of the encoded lengths (`sp.pkLen`, `sp.sigLen`). No premise on their contents (`pkDecode` and `sigDecode`
accept every byte string of the right length; `sigDecode` may return `⊥`, in which case both sides return
`false`), and none on `|m_prefix|`, `|m|`.

Premises: `Params.Std ip K L sp` (the parameter bundle of `StdParams.lean`), the two lengths, the `RejTerm`
premise (here: the spec returns `some`). `Params.Std` includes `sp.k ≤ 8` (`StdParams.k_le_8`): the Rust code keeps
`w1Encode(w′₁)` in a fixed buffer of `8 * 192 = 1536` bytes (`let mut w1_enc = [0u8; 8 * 192]` in `src/verify.rs`)
and indexes `K * 32 * w1_bits` bytes of it, so it panics for `k ≥ 9` (`32 k bitlen(m − 1) ≤ 1536` is exactly
`k ≤ 8` for `m ∈ {16, 44}`). It holds for ML-DSA-44/65/87 (`k = 4, 6, 8`: `k_le_8_44`, `k_le_8_65`, `k_le_8_87`).

## What the `some` premise means

`Verify.verify_isSome_iff`: for inputs of the right lengths, `Verify_internal … = some _` iff, whenever
`sigDecode σ = some (c̃, z, h)`, both `ExpandA(ρ)` (with `ρ` the first component of `pkDecode pk`) and
`SampleInBall(c̃)` return `some` at the fuel `F`. Other inputs never reach a sampler: a malformed hint gives
`some false` before `ExpandA` runs (`Verify.verify_of_sigDecode_none`), wrong lengths give `some false`
(`Verify.verify_of_length_ne`, step 0). When both samplers succeed, the result is
`‖z‖∞ < γ₁ − β ∧ c̃ = c̃′` (`Verify.verify_some`), with the accept, norm-too-large and `c̃`-mismatch branches
all covered by the single `Bool` `b`.

## Composition

Leaf specs: `pk_decode_spec_range`, `sig_decode_spec`, `expand_a_spec`, `shake256_spec`, `absorb_spec`,
`finalize_spec`, `squeeze_spec` (three hashes; `M′ = m_prefix ‖ m` is absorbed by two `absorb_spec` steps, so the
concatenation needs no extra lemma), `sample_in_ball_spec`, `ntt_vec_spec`, `matrix_vector_ntt_spec`, `ntt_spec`,
`scale_vec_by_2d_pk_decode`, `multiply_ntt_spec`, `sub_poly_spec`, `ntt_inverse_spec`, `poly_use_hint_spec`
(the loop of steps 10-11 is `Verify.verify_loop_spec`), `w1_encode_spec_long` (the `EncodeKeys` spec for a buffer
longer than the encoding, proved here), `vec_infinity_norm_spec`, `prefix_eq_spec`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

namespace Verify

/-- `w′_Approx = NTT⁻¹(Â ∘ NTT(z) − NTT(c) ∘ NTT(t₁ · 2^d))` (Algorithm 8, step 9). -/
def wApprox (sp : Spec.Params) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (z : Vector RPoly sp.ℓ)
    (t₁ : Vector RPoly sp.k) (c : RPoly) : Vector Spec.Poly sp.k :=
  NTTInvVec (MatrixVectorNTT A (NTTVec (z.map RPoly.toZq)) -
    ScalarVectorNTT (NTT c.toZq) (NTTVec ((t₁.map RPoly.toZq).map (·.map (· * (2 ^ sp.d : Zq))))))

/-- `c̃′ = H(μ ‖ w1Encode(w′₁), λ/4)` with `μ = H(tr ‖ M′, 64)`, `tr = H(pk, 64)` (steps 6, 7, 12). -/
def cTildePrime (sp : Spec.Params) (pk M' : List UInt8) (w₁ : Vector RPoly sp.k) : List UInt8 :=
  H (H (H pk 64 ++ M') 64 ++ w1Encode sp w₁) (sp.lam / 4)

theorem verify_some (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8) (b : Bool)
    (hpk : pk.length = sp.pkLen) (hσ : σ.length = sp.sigLen)
    (c' : List UInt8) (z : Vector RPoly sp.ℓ) (h : Vector HintPoly sp.k)
    (hsd : Spec.sigDecode sp σ = some (c', z, h))
    (hs : Spec.Verify_internal sp pk M' σ F = some b) :
    ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (c : RPoly),
      Spec.ExpandA sp F.rejNTT (Spec.pkDecode sp pk).1 = some A ∧
      Spec.SampleInBall sp F.sampleInBall c' = some c ∧
      b = (decide (‖z‖∞ < sp.γ₁ - sp.β) &&
        c' == cTildePrime sp pk M' (UseHintVec sp h (wApprox sp A z (Spec.pkDecode sp pk).2 c))) := by
  unfold Spec.Verify_internal at hs
  simp [Id.run, hpk, hσ, hsd] at hs
  rcases hA : Spec.ExpandA sp F.rejNTT (Spec.pkDecode sp pk).1 with _ | A
  · simp [hA] at hs
  rcases hC : Spec.SampleInBall sp F.sampleInBall c' with _ | c
  · simp [hA, hC] at hs
  simp [hA, hC] at hs
  refine ⟨A, c, rfl, rfl, ?_⟩
  have h2 := Option.some.inj (show some _ = some b from hs)
  rw [← h2]
  simp [wApprox, cTildePrime, Vector.map_map]

/-- Wrong lengths: `Verify_internal` returns `some false` (step 0). -/
theorem verify_of_length_ne (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (hl : pk.length ≠ sp.pkLen ∨ σ.length ≠ sp.sigLen) :
    Spec.Verify_internal sp pk M' σ F = some false := by
  unfold Spec.Verify_internal
  simp [Id.run, hl]
  rfl

/-- A malformed hint (`sigDecode = ⊥`): `Verify_internal` returns `some false` before `ExpandA` runs. -/
theorem verify_of_sigDecode_none (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (hsd : Spec.sigDecode sp σ = none) :
    Spec.Verify_internal sp pk M' σ F = some false := by
  unfold Spec.Verify_internal
  simp [Id.run, hsd]
  rfl

/-- **When does `Verify_internal` return `some`?** For inputs of the right lengths, exactly when, if `sigDecode`
succeeds with `c̃`, both `ExpandA(ρ)` (`ρ` from `pk`) and `SampleInBall(c̃)` return `some` at the fuel. A
malformed hint returns `some false` without running either sampler; wrong lengths always return `some false`. -/
theorem verify_isSome_iff (sp : Spec.Params) (F : Spec.Fuel) (pk M' σ : List UInt8)
    (hpk : pk.length = sp.pkLen) (hσ : σ.length = sp.sigLen) :
    (Spec.Verify_internal sp pk M' σ F).isSome = true ↔
      ∀ (c' : List UInt8) (z : Vector RPoly sp.ℓ) (h : Vector HintPoly sp.k),
        Spec.sigDecode sp σ = some (c', z, h) →
          (Spec.ExpandA sp F.rejNTT (Spec.pkDecode sp pk).1).isSome = true ∧
          (Spec.SampleInBall sp F.sampleInBall c').isSome = true := by
  constructor
  · intro hs c' z h hsd
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨A, c, hA, hC, -⟩ := verify_some sp F pk M' σ b hpk hσ c' z h hsd hb
    simp [hA, hC]
  · intro H
    rcases hsd : Spec.sigDecode sp σ with _ | ⟨c', z, h⟩
    · rw [verify_of_sigDecode_none sp F pk M' σ hsd]; rfl
    · obtain ⟨hA, hC⟩ := H c' z h hsd
      obtain ⟨A, hA'⟩ := Option.isSome_iff_exists.mp hA
      obtain ⟨c, hC'⟩ := Option.isSome_iff_exists.mp hC
      unfold Spec.Verify_internal
      simp [Id.run, hpk, hσ, hsd, hA', hC']
      rfl

/-! ## Rust-side helpers -/

theorem scalarVectorNTT_getElem! {ℓ : Nat} (C : Spec.Poly) (V : Vector Spec.Poly ℓ) (i : Nat) (hi : i < ℓ) :
    (ScalarVectorNTT C V)[i]! = MultiplyNTT C V[i]! := by
  have h1 : ScalarVectorNTT C V =
      (List.range' 0 ℓ).foldl (fun (c : Vector Spec.Poly ℓ) j => c.set! j (MultiplyNTT C V[j]!))
        (Vector.replicate ℓ Poly.zero) := by
    simp [Spec.ScalarVectorNTT, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [h1, foldl_set_replicate_full ℓ Poly.zero (fun j => MultiplyNTT C V[j]!), vget! _ i hi]
  simp [vget! V i hi]

theorem useHintVec_getElem! (sp : Spec.Params) {n : Nat} (H : Vector HintPoly n) (W : Vector Spec.Poly n)
    (i : Nat) (hi : i < n) :
    (UseHintVec sp H W)[i]! = Vector.zipWith (Spec.UseHint sp) H[i] W[i] := by
  rw [vget! _ i hi]
  simp [Spec.UseHintVec]

/-- Rows of an array satisfying `P` also satisfy any consequence of `P`. -/
theorem Rows.mono {α : Type} {n : Usize} {a : Array α n} {P Q : Nat → α → Prop} {i : Nat}
    (h : Rows a P i) (hPQ : ∀ r x, P r x → Q r x) : Rows a Q i :=
  fun r hr => let ⟨x, hx, hp⟩ := h r hr; ⟨x, hx, hPQ r x hp⟩

/-- `w1_encode_loop` on a buffer that may be longer than the encoding: the first `k·n` bytes are the
encoding (`EncodeKeys.w1_encode_loop_spec` needs the buffer to have exactly `k·n` bytes). -/
theorem w1_encode_loop_spec_long {K : Usize} (c n : Usize) (hn : n.val = 32 * c.val) (b : Nat) (hb : b < Spec.q)
    (hc : c.val = bitlen b) (k : Nat) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256, 0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (b : Int))
    (out : Slice U8) (hL : k * n.val ≤ out.val.length) (i1 : Usize) (hi1 : i1.val ≤ k)
    (hinv : (bytes out).take (i1.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) i1.val) :
    encode.w1_encode_loop c w1 out n i1 ⦃ out' =>
      (bytes out').take (k * n.val) = flat (fun t => SimpleBitPack v[t]! b) k ∧
        out'.val.length = out.val.length ⦄ := by
  have hKk := hv.len
  unfold encode.w1_encode_loop
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => k - p.2.val)
    (fun p => p.1.val.length = out.val.length ∧ p.2.val ≤ k ∧
      (bytes p.1).take (p.2.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) p.2.val)
  · rintro ⟨out1, i1⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.w1_encode_loop.body]
    split
    · rename_i hi
      have hik : i1.val < k := by scalar_tac
      have hm1 : (i1.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have hm2 : i1.val * n.val ≤ k * n.val := Nat.mul_le_mul_right _ (by omega)
      have hlen := out1.property
      step*
      have hFlen : ∀ t : Nat, (SimpleBitPack v[t]! b).length = n.val := fun t => by
        rw [SimpleBitPack_length, ← hc, hn]
      refine WP.spec_bind (bit_pack_spec_repr _ (v[i1.val]'hik) ?_ b hb (hrng _ hik) c hc s ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i4.val - i2.val := s_post2
        have e : (i1.val + 1) * n.val = i1.val * n.val + n.val := by ring
        rw [this, i4_post, i2_post, i3_post, e]; omega
      · intro s1 hs1
        simp only [WP.spec_ok]
        have hs1' : bytes s1 = SimpleBitPack v[i1.val]! b := by rw [hs1, vec_getElem!_eq v _ hik]
        obtain ⟨b1, b2⟩ := block_write_step out1 s1 index_mut_back i2 i4 0 n.val i1.val []
          (fun (t : Nat) => SimpleBitPack v[t]! b) hFlen rfl (by rw [i2_post]; ring)
          (by rw [i4_post, i3_post]; ring) s_post3 hs1' (by simpa using h3) (by rw [h1]; simpa using hm1.trans hL)
        refine ⟨by rw [b1]; exact h1, by omega, ?_, by omega⟩
        show List.take (i3.val * n.val) (bytes (index_mut_back s1)) = flat _ i3.val
        rw [i3_post]
        simpa using b2
    · rename_i hi
      have hi' : i1.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      exact ⟨h3, h1⟩
  · exact ⟨rfl, hi1, hinv⟩

theorem w1_encode_spec_long {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly sp.k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int))
    (out : Slice U8) (hL : 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ out.val.length) :
    encode.w1_encode ip w1 out ⦃ out' =>
      (bytes out').take (32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) = Spec.w1Encode sp v ∧
      out'.val.length = out.val.length ⦄ := by
  have hc : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hp.w1_bits
  have hb := hp.w1_b_lt
  have h23 := bitlen_lt_q hb
  unfold encode.w1_encode
  step*
  rw [w1Encode_eq]
  refine WP.spec_mono (w1_encode_loop_spec_long ip.w1_bits n (by rw [n_post]) _ hb hc sp.k w1 v hv hrng out
    (by
      have e : sp.k * (32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) =
          32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by ring
      rw [n_post, hc, e]; exact hL) 0#usize (by simp) (by simp [flat_zero])) ?_
  intro out' h
  have e : sp.k * (32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) =
      32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by ring
  rw [n_post, hc, e] at h
  exact h

theorem bitlen_m_le (sp : Spec.Params) (hg : StdGamma2 sp) :
    bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ 6 := by
  rcases hg with h | h <;> rw [h] <;> decide +kernel

/-! ## The loop of steps 9-10 -/

/-- The row-`r` invariant of `w1`: the stored polynomial is `UseHint` of `w′_Approx`'s row, with values `< m`. -/
def W1Row (sp : Spec.Params) {k : Nat} (U : Vector RPoly k) (r : Nat) (x : Array U32 256#usize) : Prop :=
  ReprInt x U[r]! ∧ ∀ (c : Nat) (hc : c < 256), 0 ≤ (U[r]!)[c]'hc ∧ (U[r]!)[c]'hc < sp.m

/-- Steps 10-11, row by row: `w′_Approx[r] = NTT⁻¹(Â z[r] − ĉ ∘ t̂₁[r])` and `w₁[r] = UseHint(h[r], w′_Approx[r])`. -/
theorem verify_loop_spec {K L : Usize} {k : Nat} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp)
    (h : Array (Array Bool 256#usize) K) (H : Vector HintPoly k) (hh : ReprHintVec h H)
    (az_hat : Array (Array U32 256#usize) K) (AZ : Vector Spec.Poly k) (haz : ReprVec az_hat AZ)
    (c_hat : Array U32 256#usize) (C : Spec.Poly) (hc : Repr c_hat C)
    (t1_2d_hat : Array (Array U32 256#usize) K) (T : Vector Spec.Poly k) (ht : ReprVec t1_2d_hat T)
    (w_approx w1 : Array (Array U32 256#usize) K) (i : Usize) (hi : i.val ≤ K.val)
    (h1 : Rows w_approx (fun r x => Repr x (NTTInvVec (AZ - ScalarVectorNTT C T))[r]!) i.val)
    (h2 : Rows w1 (W1Row sp (UseHintVec sp H (NTTInvVec (AZ - ScalarVectorNTT C T)))) i.val) :
    verify.verify_core_loop ip t1_2d_hat h az_hat c_hat w_approx w1 i ⦃ o =>
      Rows o (W1Row sp (UseHintVec sp H (NTTInvVec (AZ - ScalarVectorNTT C T)))) K.val ⦄ := by
  have hN : K.val = k := hh.len
  unfold verify.verify_core_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Array (Array U32 256#usize) K × Usize) => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧
      Rows p.1 (fun r x => Repr x (NTTInvVec (AZ - ScalarVectorNTT C T))[r]!) p.2.2.val ∧
      Rows p.2.1 (W1Row sp (UseHintVec sp H (NTTInvVec (AZ - ScalarVectorNTT C T)))) p.2.2.val)
  · rintro ⟨wa, w1', i⟩ ⟨hi1, hw1, hw2⟩
    dsimp only at hi1 hw1 hw2
    simp only [verify.verify_core_loop.body]
    split
    · rename_i hi
      have hi' : i.val < K.val := hi
      have hik : i.val < k := by omega
      have hl : i.val < wa.val.length := by rw [wa.property]; exact hi'
      have hl2 : i.val < w1'.val.length := by rw [w1'.property]; exact hi'
      step with ht.index_spec i hik as ⟨a, ha⟩
      step with multiply_ntt_spec c_hat a C _ hc ha as ⟨ct1, hct1⟩
      step with haz.index_spec i hik as ⟨a1, ha1⟩
      step with sub_poly_spec a1 ct1 _ _ ha1 hct1 as ⟨a2, ha2⟩
      step with ntt_inverse_spec a2 ha2.canon as ⟨a3, ha3, ha3'⟩
      step as ⟨wa1, hwa1⟩
      step with hh.index_spec' i hik as ⟨a4, ha4⟩
      step as ⟨hlt5, a5, ha5⟩
      have e5 : a5 = a3 := by rw [ha5]; simp [hwa1, Array.set_val_eq]
      subst e5
      have hW : (NTTInvVec (AZ - ScalarVectorNTT C T))[i.val]! =
          NTTInv (AZ[i.val] - MultiplyNTT C T[i.val]) := by
        rw [nttInvVec_getElem! _ _ hik, vsub_getElem! _ _ _ hik, scalarVectorNTT_getElem! _ _ _ hik,
          vget! AZ _ hik, vget! T _ hik]
      have hrW : Repr a5 (NTTInvVec (AZ - ScalarVectorNTT C T))[i.val]! := by
        rw [hW]; exact ⟨ha3, by rw [ha3', ha2.eq]⟩
      have hrW' : Repr a5 ((NTTInvVec (AZ - ScalarVectorNTT C T))[i.val]'hik) := by
        rw [← vget! _ _ hik]; exact hrW
      step with poly_use_hint_spec hp hg a4 H[i.val] ha4 a5 _ hrW' as ⟨a6, ha6, ha6'⟩
      step*
      have hrow : W1Row sp (UseHintVec sp H (NTTInvVec (AZ - ScalarVectorNTT C T))) i.val a6 := by
        refine ⟨?_, fun c hc => ?_⟩
        · rw [useHintVec_getElem! _ _ _ _ hik]; exact ha6
        · have := ha6' c hc
          simp only [useHintVec_getElem! _ _ _ _ hik, Vector.getElem_zipWith]
          omega
      have e16 : i1.val = i.val + 1 := i1_post
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [e16, hwa1]; exact hw1.set i rfl hl a5 hrW
      · rw [e16, a8_post]; exact hw2.set i rfl hl2 a6 hrow
    · rename_i hi
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at hw2
      exact hw2
  · exact ⟨hi, h1, h2⟩

/-- The length guard's comparison `s.len() != n`. -/
theorem len_bne_iff (s : Slice U8) (i : Usize) : (Slice.len s != i) = true ↔ s.val.length ≠ i.val := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h e
    apply h
    exact UScalar.eq_of_val_eq (by simpa using e)
  · intro h e
    apply h
    have := congrArg UScalar.val e
    simpa using this

/-- The Rust `pk_len` computes `32 + 320·k`, which is the spec's `pkLen` (no `usize` overflow for `k ≤ 8`). -/
theorem pk_len_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) :
    params.pk_len ip ⦃ r => r.val = sp.pkLen ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hk8 : sp.k ≤ 8 := hstd.k_le_8
  have hkv : ip.k.val = sp.k := hv.k_eq
  have hpl := KeyGen.pkLen_eq sp hstd.d_eq
  unfold params.pk_len
  step as ⟨i, hi⟩
  step as ⟨r, hr⟩
  rw [hpl]; omega

/-- The Rust `sig_len` computes `λ/4 + ℓ·32·(1 + bitlen(γ₁ − 1)) + ω + k`, which is the spec's `sigLen` (no `usize`
overflow: `ℓ < 256`, `1 + bitlen(γ₁ − 1) ≤ 20`, `λ/4 ≤ 64`, `ω ≤ 255`, `k ≤ 8`). -/
theorem sig_len_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) :
    params.sig_len ip ⦃ r => r.val = sp.sigLen ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  obtain ⟨hbl, hlt, hc2, hpow⟩ := hstd.stdSig.bitlen_eq
  have hkl := hstd.kl_lt
  have hk8 : sp.k ≤ 8 := hstd.k_le_8
  have hl : ip.l.val = sp.ℓ := hv.l_eq
  have hkv : ip.k.val = sp.k := hv.k_eq
  have hgb : ip.gamma1_bits.val = 1 + bitlen (sp.γ₁ - 1) := hv.gamma1_bits
  have hgb20 : ip.gamma1_bits.val ≤ 20 := by omega
  have hct : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
  have hct64 : ip.c_tilde_len.val ≤ 64 := by rw [hct]; exact hstd.lam_le
  have hom : ip.omega.val = sp.ω := hv.omega
  have hom255 : ip.omega.val ≤ 255 := by rw [hom]; exact hstd.omega_le
  unfold params.sig_len
  step as ⟨i, hi⟩
  have hprod : i.val * ip.gamma1_bits.val ≤ 8160 * 20 := Nat.mul_le_mul (by omega) hgb20
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step as ⟨r, hr⟩
  have e : r.val = sp.lam / 4 + sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1))) + (sp.ω + sp.k) := by
    have h1 : i1.val = sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1))) := by
      rw [hi1, hi, hl, hgb]; ring
    omega
  rw [e]; unfold Spec.Params.sigLen; ring

/-! ## The per-key / per-signature split

`verify_internal` is `prepare_vk` (steps 1, 6, 7 and the key half of step 10) followed by `verify_decoded`
(steps 8-13: `hash_mu`, SampleInBall, then `verify_core`). The pieces are proved once here and composed in
`verify_internal_spec`; `PartialVerify.lean` and `PreparedVerify.lean` reuse them. -/

/-- `tr = H(pk, 64)` (step 7). -/
theorem hash_pk_spec (pk : Slice U8) :
    verify.hash_pk pk ⦃ tr => bytesA tr = H (bytes pk) 64 ⦄ := by
  unfold verify.hash_pk
  step*
  have hs1len : s.val.length = 64 := by rw [s_post1]; simp
  have hs1b : bytes s1 = H (bytes pk) 64 := by
    rw [__post2, List.drop_zero, Nat.zero_add, hs1len, List.nil_append]; rfl
  have hs1l : s1.val.length = 64 := by
    have h := congrArg List.length hs1b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  rw [s_post2, bytesA_from_slice _ _ hs1l, hs1b]

/-- `μ = H(tr ‖ M′, 64)` (step 8), for `tr = H(pk, 64)`. -/
theorem hash_mu_spec (tr : Array U8 64#usize) (m_prefix m : Slice U8) (pkb : List UInt8)
    (htr : bytesA tr = H pkb 64) :
    verify.hash_mu tr m_prefix m ⦃ mu =>
      bytesA mu = H (H pkb 64 ++ (bytes m_prefix ++ bytes m)) 64 ⦄ := by
  unfold verify.hash_mu
  step*
  have hsb : bytes s = H pkb 64 := by rw [s_post, bytes_to_slice]; exact htr
  have hs1len : s1.val.length = 64 := by rw [s1_post1]; simp
  have hmu : bytes s2 = H (H pkb 64 ++ (bytes m_prefix ++ bytes m)) 64 := by
    have e : ([] ++ H pkb 64 ++ bytes m_prefix ++ bytes m : List UInt8) =
        H pkb 64 ++ (bytes m_prefix ++ bytes m) := by simp
    rw [__post2, List.drop_zero, Nat.zero_add, hs1len, hsb, e]; rfl
  have hs2l : s2.val.length = 64 := by
    have h := congrArg List.length hmu
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  rw [s1_post2, bytesA_from_slice _ _ hs2l, hmu]

/-- The key half of Verify: `prepare_vk` returns Â (= ExpandA(ρ), for any fuel at which the spec samples),
NTT(t₁ · 2^d) and tr = H(pk, 64). -/
theorem prepare_vk_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk : Slice U8) (hpkLen : pk.val.length = 32 + 320 * sp.k)
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (F1 : Nat)
    (hA : Spec.ExpandA sp F1 (Spec.pkDecode sp (bytes pk)).1 = some A) :
    verify.prepare_vk K L pk ⦃ vk =>
      ReprMat vk.a_hat A ∧
      ReprVec vk.t1_2d_hat (NTTVec (((Spec.pkDecode sp (bytes pk)).2.map RPoly.toZq).map
        (·.map (· * (2 ^ sp.d : Zq))))) ∧
      bytesA vk.tr = H (bytes pk) 64 ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hd := hstd.d_eq
  unfold verify.prepare_vk
  refine WP.spec_bind (pk_decode_spec_range ip sp hv pk hpkLen) ?_
  rintro ⟨rho, t1⟩ ⟨hrho, ht1, ht1rng⟩
  refine WP.spec_bind (expand_a_spec sp K L hK hL rho A F1 (by rw [hrho]; exact hA)) ?_
  intro a_hat hahat
  refine WP.spec_bind (hash_pk_spec pk) ?_
  intro tr htr
  refine WP.spec_bind (scale_vec_by_2d_pk_decode sp hd (bytes pk) t1 ht1) ?_
  intro a1 ha1
  refine WP.spec_bind (ntt_vec_spec a1 _ ha1) ?_
  intro t1_2d_hat ht2d
  simp only [WP.spec_ok]
  exact ⟨hahat, ht2d, htr⟩

/-- The slice `c_tilde[..n]` of the 64-byte buffer. -/
theorem c_tilde_prefix_spec (c_tilde : Array U8 64#usize) (n : Usize) (hn : n.val ≤ 64) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) c_tilde { «end» := n } ⦃ t =>
      bytes t = (bytesA c_tilde).take n.val ⦄ := by
  rw [Array.index_SliceIndexRangeToUsizeSlice]
  apply WP.spec_mono (slice_to_bytes c_tilde.to_slice { «end» := n } (by
    have := c_tilde.property
    simp [Array.to_slice]
    omega))
  intro t ht
  rw [ht, bytes_to_slice]

/-- Steps 10-13 once `c = SampleInBall(c̃)` is known: the verdict `‖z‖∞ < γ₁ − β ∧ c̃ = c̃′`. The key enters
through Â (`hA`), NTT(t₁ · 2^d) (`ht`) and μ (`hmu`, from `tr = H(pk, 64)`). -/
theorem verify_core_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (vk : verify.PreparedVk K L) (mu c_tilde : Array U8 64#usize)
    (cp : Array U32 256#usize) (z : Array (Array U32 256#usize) L) (h : Array (Array Bool 256#usize) K)
    (pkb M' : List UInt8) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (hA : ReprMat vk.a_hat A)
    (ht : ReprVec vk.t1_2d_hat (NTTVec (((Spec.pkDecode sp pkb).2.map RPoly.toZq).map
      (·.map (· * (2 ^ sp.d : Zq))))))
    (hmu : bytesA mu = H (H pkb 64 ++ M') 64)
    (c' : List UInt8) (z' : Vector RPoly sp.ℓ) (h' : Vector HintPoly sp.k)
    (hc1 : (bytesA c_tilde).take (sp.lam / 4) = c') (hz : ReprIntVec z z')
    (hzr : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.γ₁ : Int) + 1 ≤ (z'[i]'hi)[j]'hj ∧ (z'[i]'hi)[j]'hj ≤ (sp.γ₁ : Int))
    (hhh : ReprHintVec h h') (c : RPoly) (hcp : ReprInt cp c) :
    verify.verify_core ip vk mu c_tilde cp z h ⦃ r =>
      r = (decide (‖z'‖∞ < sp.γ₁ - sp.β) &&
        c' == cTildePrime sp pkb M' (UseHintVec sp h' (wApprox sp A z' (Spec.pkDecode sp pkb).2 c))) ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hk8 : sp.k ≤ 8 := hstd.k_le_8
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hd := hstd.d_eq
  have hg := hstd.stdGamma2
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
  have h64 : sp.lam / 4 ≤ 64 := hstd.lam_le
  have hK8 : K.val ≤ 8 := by omega
  have hw1b : ip.w1_bits.val ≤ 6 := by rw [hv.w1_bits]; exact bitlen_m_le sp hg
  have hβ : ip.beta.val ≤ ip.gamma1.val := by
    rw [hv.beta, hv.gamma1]
    have : sp.β ≤ 256 := by
      have := hstd.tau_le
      rcases hstd.eta with e | e <;> simp only [Spec.Params.β, e] <;> omega
    rcases hstd.gamma1 with e | e <;> rw [e] <;> omega
  unfold verify.verify_core
  refine WP.spec_bind (ntt_vec_spec z _ hz.repr) ?_
  intro az0 haz0
  refine WP.spec_bind (matrix_vector_ntt_spec vk.a_hat A hA az0 _ haz0) ?_
  intro az_hat haz
  refine WP.spec_bind (ntt_spec cp hcp.canon) ?_
  rintro c_hat ⟨hch1, hch2⟩
  have hchat : Repr c_hat (NTT c.toZq) := ⟨hch1, by rw [hch2, hcp.2]⟩
  refine WP.spec_bind (verify_loop_spec hv hg h h' hhh az_hat _ haz c_hat _ hchat vk.t1_2d_hat _ ht
    (Array.repeat K (Array.repeat 256#usize 0#u32)) (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize
    (by simp) (Rows.zero _ _) (Rows.zero _ _)) ?_
  intro w11 hw11
  rw [hK] at hw11
  have hw11' : Rows w11 (W1Row sp (UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c))) sp.k :=
    hw11
  have hw11r : ReprIntVec w11 (UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c)) :=
    Rows.reprIntVec (Rows.mono hw11' fun r x hx => hx.1) hK
  have hrng : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256),
      0 ≤ ((UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c))[i]'hi)[j]'hj ∧
      ((UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c))[i]'hi)[j]'hj ≤
        (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int) := by
    intro i hi j hj
    obtain ⟨x, -, -, hr⟩ := hw11' i hi
    have := hr j hj
    rw [vget! _ i hi] at this
    have hpos : 0 < sp.m := hg.m_pos
    have hm' : (Spec.q - 1) / (2 * sp.γ₂) = sp.m := rfl
    rw [hm']
    omega
  step*
  have hslen : s.val.length = 1536 := by rw [s_post1]; simp
  have hbitsle : bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ 6 := bitlen_m_le sp hg
  have hL1 : 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ s.val.length := by
    rw [hslen]
    calc 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ 32 * 8 * 6 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hk8) hbitsle
      _ ≤ 1536 := by norm_num
  refine WP.spec_bind (w1_encode_spec_long ip sp hv w11 _ hw11r hrng s hL1) ?_
  intro s1 hs1
  obtain ⟨hs1a, hs1len⟩ := hs1
  step*
  case h_fail =>
    have h1 : i.val ≤ 256 := by scalar_tac
    have h2 : i.val * ip.w1_bits.val ≤ 256 * 6 := Nat.mul_le_mul h1 hw1b
    scalar_tac
  case h =>
    show i1.val ≤ (to_slice_mut_back s1).to_slice.length
    have h1 : i.val ≤ 256 := by scalar_tac
    have h2 : i1.val = i.val * ip.w1_bits.val := i1_post
    have h3 : i.val * ip.w1_bits.val ≤ 256 * 6 := Nat.mul_le_mul h1 hw1b
    have h4 : (to_slice_mut_back s1).to_slice.length = 1536 := by simp [Array.to_slice, Slice.length]
    omega
  have hs2b : bytes s2 = H (H pkb 64 ++ M') 64 := by
    rw [s2_post, bytes_to_slice]; exact hmu
  have hwb : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hv.w1_bits
  have hi1v : i1.val = 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by
    rw [i1_post, i_post, hK, hwb]; ring
  have he1 : bytesA (to_slice_mut_back s1) = bytes s1 := by
    rw [s_post2, bytesA_from_slice _ _ (by simp [hs1len, hslen])]
  have hs3b : bytes s3 = (bytes s1).take i1.val := by
    rw [← he1]
    simp [bytes, bytesA, s3_post1, List.slice, Array.to_slice, List.map_take]
  have hs3 : bytes s3 = w1Encode sp (UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c)) := by
    rw [hs3b, hi1v, hs1a]
  have hs4len : s4.val.length = sp.lam / 4 := by
    have h := s4_post2
    simp only [Slice.length] at h
    rw [h, hcl]
  have hs5b : bytes s5 = cTildePrime sp pkb M'
      (UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c)) := by
    rw [__post2, List.drop_zero, Nat.zero_add, hs4len, hs2b, hs3]
    unfold cTildePrime
    rw [List.append_assoc, List.nil_append]
    rfl
  have hs5len : s5.val.length = sp.lam / 4 := by
    have h := congrArg List.length hs5b
    simp only [bytes, List.length_map, cTildePrime] at h
    rw [h]; exact SHAKE256_length _ _
  have hctp : (bytesA (index_mut_back s5)).take (sp.lam / 4) = bytes s5 := by
    have hn : s5.val.length ≤ (Array.repeat 64#usize 0#u8).val.length := by
      simp [hs5len]; omega
    have e := setSlice_zero (Array.repeat 64#usize 0#u8).val s5.val hn
    have hmap : bytesA (index_mut_back s5) =
        ((s5.val ++ (Array.repeat 64#usize 0#u8).val.drop s5.val.length).map
          fun x => UInt8.ofNat x.val) := by
      simp only [bytesA, s4_post3, e]
    rw [hmap, List.map_append, List.take_left' (by simp [hs5len])]
    rfl
  have hnorm : ‖z'‖∞ ≤ 4190208 := by
    rw [infNorm_le_iff]
    intro i hi
    rw [infNorm_le_iff]
    intro j hj
    have := hzr i hi j hj
    rw [infNorm_int]
    rcases hstd.gamma1 with e | e <;> rw [e] at this <;> norm_num at this <;> omega
  step with vec_infinity_norm_spec z z' hz hnorm as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  step with prefix_eq_spec c_tilde (index_mut_back s5) ip.c_tilde_len (by omega) as ⟨hok, hhok⟩
  have hi3' : i3.val = sp.γ₁ - sp.β := by rw [hi3, hv.gamma1, hv.beta]
  have hhok' : hok = decide (c' = cTildePrime sp pkb M'
      (UseHintVec sp h' (wApprox sp A z' (pkDecode sp pkb).2 c))) := by
    rw [hhok, hcl, hc1, hctp, hs5b]
  by_cases hlt : i2 < i3
  · have hlt' : ‖z'‖∞ < sp.γ₁ - sp.β := by
      have : i2.val < i3.val := by scalar_tac
      rw [hi2, hi3'] at this
      exact this
    rw [if_pos hlt]
    simp only [WP.spec_ok]
    rw [hhok']
    simp [hlt']
    rw [Bool.eq_iff_iff]
    simp
  · have hlt' : ¬ ‖z'‖∞ < sp.γ₁ - sp.β := by
      intro h
      apply hlt
      have : i2.val < i3.val := by rw [hi2, hi3']; exact h
      scalar_tac
    rw [if_neg hlt]
    simp only [WP.spec_ok]
    simp [hlt']

/-- Steps 8-13 for a decoded signature `(c̃, z, h)`: μ, SampleInBall (at fuel `F2`), then `verify_core`. -/
theorem verify_decoded_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (vk : verify.PreparedVk K L) (m_prefix m : Slice U8)
    (c_tilde : Array U8 64#usize) (z : Array (Array U32 256#usize) L) (h : Array (Array Bool 256#usize) K)
    (pkb : List UInt8) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (hA : ReprMat vk.a_hat A)
    (ht : ReprVec vk.t1_2d_hat (NTTVec (((Spec.pkDecode sp pkb).2.map RPoly.toZq).map
      (·.map (· * (2 ^ sp.d : Zq))))))
    (htr : bytesA vk.tr = H pkb 64)
    (c' : List UInt8) (z' : Vector RPoly sp.ℓ) (h' : Vector HintPoly sp.k)
    (hc1 : (bytesA c_tilde).take (sp.lam / 4) = c') (hz : ReprIntVec z z')
    (hzr : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.γ₁ : Int) + 1 ≤ (z'[i]'hi)[j]'hj ∧ (z'[i]'hi)[j]'hj ≤ (sp.γ₁ : Int))
    (hhh : ReprHintVec h h') (c : RPoly) (F2 : Nat) (hC : Spec.SampleInBall sp F2 c' = some c) :
    verify.verify_decoded ip vk m_prefix m c_tilde z h ⦃ r =>
      r = (decide (‖z'‖∞ < sp.γ₁ - sp.β) &&
        c' == cTildePrime sp pkb (bytes m_prefix ++ bytes m)
          (UseHintVec sp h' (wApprox sp A z' (Spec.pkDecode sp pkb).2 c))) ⦄ := by
  have hv := hp.valid
  have hstd := hp.params
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
  have h64 : sp.lam / 4 ≤ 64 := hstd.lam_le
  unfold verify.verify_decoded
  refine WP.spec_bind (hash_mu_spec vk.tr m_prefix m pkb htr) ?_
  intro mu hmu
  refine WP.spec_bind (c_tilde_prefix_spec c_tilde ip.c_tilde_len (by omega)) ?_
  intro s hs
  have hs' : bytes s = c' := by rw [hs, hcl, hc1]
  refine WP.spec_bind (sample_in_ball_spec hv hstd.tau s c F2 (by rw [hs']; exact hC)) ?_
  intro cp hcp
  exact verify_core_spec hp vk mu c_tilde cp z h pkb _ A hA ht hmu c' z' h' hc1 hz hzr hhh c hcp

end Verify

open Verify

theorem verify_internal_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk σ m_prefix m : Slice U8)
    (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F = some b) :
    verify.verify_internal K L ip pk m_prefix m σ ⦃ r => r = b ⦄ := by
  have hpkS := pk_len_spec hp
  have hsgS := sig_len_spec hp
  have hp' := hp
  obtain ⟨hv, hstd⟩ := hp
  have hd := hstd.d_eq
  unfold verify.verify_internal
  dsimp only
  -- Length guard (Rust: `pk.len() != pk_len(p) || sig.len() != sig_len(p)` returns false, as in FIPS 204 Verify)
  refine WP.spec_bind hpkS ?_
  intro gk hgk
  by_cases hpk : pk.length = sp.pkLen
  swap
  · rw [if_pos ((len_bne_iff pk gk).2 (fun e => hpk (by show pk.val.length = _; omega)))]
    have hl : (bytes pk).length ≠ sp.pkLen ∨ (bytes σ).length ≠ sp.sigLen :=
      Or.inl (by rw [bytes_length]; exact hpk)
    rw [verify_of_length_ne sp F _ _ _ hl] at hs
    have hbf : b = false := (Option.some.inj hs).symm
    subst hbf
    exact (WP.spec_ok _).mpr rfl
  rw [if_neg (fun h => ((len_bne_iff pk gk).1 h) (by
    have : pk.val.length = sp.pkLen := hpk
    omega))]
  refine WP.spec_bind hsgS ?_
  intro gs hgs
  by_cases hσ : σ.length = sp.sigLen
  swap
  · rw [if_pos ((len_bne_iff σ gs).2 (fun e => hσ (by show σ.val.length = _; omega)))]
    have hl : (bytes pk).length ≠ sp.pkLen ∨ (bytes σ).length ≠ sp.sigLen :=
      Or.inr (by rw [bytes_length]; exact hσ)
    rw [verify_of_length_ne sp F _ _ _ hl] at hs
    have hbf : b = false := (Option.some.inj hs).symm
    subst hbf
    exact (WP.spec_ok _).mpr rfl
  rw [if_neg (fun h => ((len_bne_iff σ gs).1 h) (by
    have : σ.val.length = sp.sigLen := hσ
    omega))]
  have hpkLen : pk.val.length = 32 + 320 * sp.k := by
    have : pk.val.length = sp.pkLen := hpk
    rw [this, KeyGen.pkLen_eq sp hd]
  refine WP.spec_bind (sig_decode_spec ip sp hv hstd.stdSig σ hσ) ?_
  intro o ho
  rcases o with _ | ⟨c_tilde, z, h⟩
  · rcases hsd : Spec.sigDecode sp (bytes σ) with _ | ⟨c', z', h'⟩
    · rw [verify_of_sigDecode_none sp F _ _ _ hsd] at hs
      have : b = false := (Option.some.inj hs).symm
      subst this
      simp only [WP.spec_ok]
    · rw [hsd] at ho
      exact ho.elim
  · rcases hsd : Spec.sigDecode sp (bytes σ) with _ | ⟨c', z', h'⟩
    · rw [hsd] at ho
      exact ho.elim
    · rw [hsd] at ho
      obtain ⟨hc1, hc2, hz, hzr, hhh⟩ := ho
      have hpkb : (bytes pk).length = sp.pkLen := by rw [bytes_length]; exact hpk
      have hσb : (bytes σ).length = sp.sigLen := by rw [bytes_length]; exact hσ
      obtain ⟨A, c, hA, hC, hb⟩ := verify_some sp F _ _ _ b hpkb hσb c' z' h' hsd hs
      dsimp only
      refine WP.spec_bind (prepare_vk_spec hp' pk hpkLen A F.rejNTT hA) ?_
      rintro vk ⟨hvA, hvt, hvtr⟩
      apply WP.spec_mono (verify_decoded_spec hp' vk m_prefix m c_tilde z h (bytes pk) A hvA hvt hvtr
        c' z' h' hc1 hz hzr hhh c F.sampleInBall hC)
      intro r hr
      rw [hr, hb]

/-- Headline form: the extracted `verify_internal` returns `ok` of the spec's verdict. -/
theorem verify_internal_correct {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk σ m_prefix m : Slice U8)
    (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F = some b) :
    ∃ r, verify.verify_internal K L ip pk m_prefix m σ = ok r ∧ r = b :=
  WP.spec_imp_exists (verify_internal_spec hp pk σ m_prefix m F b hs)

/-- The premise in terms of `isSome` (what `RejTerm` is about): if the spec returns `some`, the Rust code returns
its verdict. -/
theorem verify_internal_correct_of_isSome {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk σ m_prefix m : Slice U8)
    (F : Spec.Fuel)
    (hs : (Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F).isSome = true) :
    ∃ b r, Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F = some b ∧
      verify.verify_internal K L ip pk m_prefix m σ = ok r ∧ r = b := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨r, hr, hrb⟩ := verify_internal_correct hp pk σ m_prefix m F b hb
  exact ⟨b, r, hb, hr, hrb⟩

/-- Satisfiability of the `k ≤ 8` premise: ML-DSA-44/65/87 have `k = 4, 6, 8`. -/
theorem k_le_8_44 : Spec.ML_DSA_44.k ≤ 8 := by decide +kernel
theorem k_le_8_65 : Spec.ML_DSA_65.k ≤ 8 := by decide +kernel
theorem k_le_8_87 : Spec.ML_DSA_87.k ≤ 8 := by decide +kernel

end Proofs
