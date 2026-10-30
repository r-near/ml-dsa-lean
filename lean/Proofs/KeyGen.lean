import Spec.MLDSA
import Proofs.StdParams
import Proofs.EncodeKeys
import Proofs.SampleA
import Proofs.SampleS
import Proofs.NTTOps
import Proofs.Steps
import Proofs.Keccak

/-!
# KeyGen_internal (Algorithm 6)

`keygen_internal_spec`: the extracted `keygen.keygen_internal K L ip ξ pk sk` returns buffers holding the pair
`(pk', sk')` whenever `Spec.KeyGen_internal sp (bytesA ξ) F = some (pk', sk')`.

Premises: `Params.Std ip K L sp` (the parameter bundle of `StdParams.lean`), `pk.len = pkLen`, `sk.len = skLen`
(the extracted code writes into these buffers and indexes them directly), and the `RejTerm` premise, here the
statement that the spec returns `some`. By `KeyGen.keygen_isSome_iff` that premise is equivalent to `ExpandA` and
`ExpandS` returning `some` on the seeds `ρ`, `ρ′` that the first `H` call derives from `ξ`; nothing else about
`ξ` is assumed.

Composition (leaf specs): `shake256_spec`, `absorb_spec`, `finalize_spec`, `squeeze_spec` (Keccak), two copy loops
proved here (`loop0_spec`, `loop1_spec`: `ρ`, `K`, `ρ′` out of the 128 SHAKE bytes), `expand_a_spec`,
`expand_s_spec` (with `|s| ≤ η`), `ntt_vec_spec`, `compute_t_spec`, `vec_power2round_spec`,
`power2roundVec_range`, `pk_encode_spec`, `sk_encode_spec`. The spec side is unfolded once by `keygen_some`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

namespace KeyGen

theorem integerToBytes_one (x : Nat) : IntegerToBytes x 1 = [(x % 256).toUInt8] := by
  unfold IntegerToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ]

/-- The vector `t = NTT⁻¹(Â ∘ NTT(s₁)) + s₂` of Algorithm 6, step 5. -/
def tVec (sp : Spec.Params) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ)
    (s₂ : Vector RPoly sp.k) : Vector Spec.Poly sp.k :=
  NTTInvVec (MatrixVectorNTT A (NTTVec (s₁.map RPoly.toZq))) + s₂.map RPoly.toZq

theorem keygen_some (sp : Spec.Params) (F : Spec.Fuel) (ξ pk' sk' : List UInt8)
    (hs : Spec.KeyGen_internal sp ξ F = some (pk', sk')) :
    ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k),
      Spec.ExpandA sp F.rejNTT (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 0 32) = some A ∧
      Spec.ExpandS sp F.rejBounded (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 32 64)
        = some (s₁, s₂) ∧
      pk' = pkEncode sp (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 0 32)
        (Power2RoundVec sp (tVec sp A s₁ s₂)).1 ∧
      sk' = skEncode sp (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 0 32)
        (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 96 32)
        (H (pkEncode sp (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 0 32)
          (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64)
        s₁ s₂ (Power2RoundVec sp (tVec sp A s₁ s₂)).2 := by
  unfold Spec.KeyGen_internal at hs
  generalize H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hs ⊢
  cases hA : Spec.ExpandA sp F.rejNTT (slice out 0 32) with
  | none => simp [hA] at hs
  | some A =>
    cases hS : Spec.ExpandS sp F.rejBounded (slice out 32 64) with
    | none => simp [hA, hS] at hs
    | some r =>
      obtain ⟨s₁, s₂⟩ := r
      simp [hA, hS] at hs
      exact ⟨A, s₁, s₂, rfl, rfl, hs.1.symm, hs.2.symm⟩

theorem pkLen_eq (sp : Spec.Params) (hd : sp.d = 13) : sp.pkLen = 32 + 320 * sp.k := by
  unfold Spec.Params.pkLen
  rw [hd, bitlen_q_sub_one]
  ring

theorem pkEncode_length (sp : Spec.Params) (hd : sp.d = 13) (ρ : List UInt8) (hρ : ρ.length = 32)
    (v : Vector RPoly sp.k) : (pkEncode sp ρ v).length = 32 + 320 * sp.k := by
  have hc10 : bitlen (2 ^ 10 - 1) = 10 := by decide +kernel
  rw [pkEncode_eq, t1Bits_eq sp hd]
  have := flat_length (fun t => SimpleBitPack v[t]! (2 ^ 10 - 1)) 320
    (fun t => by rw [SimpleBitPack_length, hc10]) sp.k
  rw [List.length_append, hρ]
  show 32 + (flat (fun t => SimpleBitPack v[t]! (2 ^ 10 - 1)) sp.k).length = _
  rw [this]; ring

theorem loop0_spec (expanded : Array U8 128#usize) (rho0 key0 : Array U8 32#usize) :
    keygen.keygen_internal_loop0 expanded rho0 key0 0#usize ⦃ r =>
      bytesA r.1 = (bytesA expanded).take 32 ∧ bytesA r.2 = ((bytesA expanded).drop 96).take 32 ⦄ := by
  unfold keygen.keygen_internal_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 32#usize × Array U8 32#usize × Usize) => 32 - p.2.2.val)
    (fun p => p.2.2.val ≤ 32 ∧
      (∀ k, (bytesA p.1)[k]? = if k < p.2.2.val then (bytesA expanded)[k]? else (bytesA rho0)[k]?) ∧
      (∀ k, (bytesA p.2.1)[k]? = if k < p.2.2.val then (bytesA expanded)[96 + k]? else (bytesA key0)[k]?))
  · rintro ⟨rho, key, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [keygen.keygen_internal_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 32 := by scalar_tac
      step*
      subst i1_post2 i3_post2 a_post a1_post
      have e1 := bytesA_getElem? expanded i.val (by simp; omega)
      have e2 := bytesA_getElem? expanded i2.val (by simp; omega)
      have hl1 : i.val < (bytesA rho).length := by simp; omega
      have hl2 : i.val < (bytesA key).length := by simp; omega
      refine ⟨by omega, fun k => ?_, fun k => ?_, by omega⟩
      · rw [bytesA_set, List.getElem?_set, h2 k, i4_post]
        by_cases hk : i.val = k
        · subst hk; simp [hi', e1]
        · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
      · rw [bytesA_set, List.getElem?_set, h3 k, i4_post]
        by_cases hk : i.val = k
        · subst hk; rw [← i2_post]; simp [hi', e2]
        · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · apply List.ext_getElem?
        intro k
        rw [h2 k, hi', List.getElem?_take]
        by_cases hk : k < 32
        · simp [hk]
        · simp only [hk, if_false]
          rw [List.getElem?_eq_none (by simp; omega)]
      · apply List.ext_getElem?
        intro k
        rw [h3 k, hi', List.getElem?_take, List.getElem?_drop]
        by_cases hk : k < 32
        · simp [hk, Nat.add_comm]
        · simp only [hk, if_false]
          rw [List.getElem?_eq_none (by simp; omega)]
  · exact ⟨by simp, fun k => by simp, fun k => by simp⟩

theorem loop1_spec (expanded : Array U8 128#usize) (rp0 : Array U8 64#usize) :
    keygen.keygen_internal_loop1 expanded rp0 0#usize ⦃ r =>
      bytesA r = ((bytesA expanded).drop 32).take 64 ⦄ := by
  unfold keygen.keygen_internal_loop1
  apply loop.spec_decr_nat
    (fun (p : Array U8 64#usize × Usize) => 64 - p.2.val)
    (fun p => p.2.val ≤ 64 ∧
      (∀ k, (bytesA p.1)[k]? = if k < p.2.val then (bytesA expanded)[32 + k]? else (bytesA rp0)[k]?))
  · rintro ⟨rp, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keygen.keygen_internal_loop1.body]
    split
    · rename_i hi
      have hi' : i.val < 64 := by scalar_tac
      step*
      subst i2_post2 a_post
      have e2 := bytesA_getElem? expanded i1.val (by simp; omega)
      have hl1 : i.val < (bytesA rp).length := by simp; omega
      refine ⟨by omega, fun k => ?_, by omega⟩
      rw [bytesA_set, List.getElem?_set, h2 k, i3_post]
      by_cases hk : i.val = k
      · subst hk; rw [← i1_post]; simp [hi', e2]
      · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      apply List.ext_getElem?
      intro k
      rw [h2 k, hi', List.getElem?_take, List.getElem?_drop]
      by_cases hk : k < 64
      · simp [hk, Nat.add_comm]
      · simp only [hk, if_false]
        rw [List.getElem?_eq_none (by simp; omega)]
  · exact ⟨by simp, fun k => by simp⟩

/-- Satisfiability reduction for the `RejTerm` premise of `keygen_internal_spec`: the spec returns `some`
exactly when `ExpandA` (on `ρ`) and `ExpandS` (on `ρ′`) return `some` on the seeds derived from `ξ`. -/
theorem keygen_isSome_iff (sp : Spec.Params) (F : Spec.Fuel) (ξ : List UInt8) :
    (Spec.KeyGen_internal sp ξ F).isSome = true ↔
      (Spec.ExpandA sp F.rejNTT (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 0 32)).isSome
          = true ∧
      (Spec.ExpandS sp F.rejBounded (slice (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128) 32 64)).isSome
          = true := by
  unfold Spec.KeyGen_internal
  generalize H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out
  rcases hA : Spec.ExpandA sp F.rejNTT (slice out 0 32) with _ | A
  · simp [hA]
  · rcases hS : Spec.ExpandS sp F.rejBounded (slice out 32 64) with _ | ⟨s₁, s₂⟩
    · simp [hA, hS]
    · simp [hA, hS]

end KeyGen

open KeyGen

theorem keygen_internal_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (ξ : Array U8 32#usize) (pk sk : Slice U8)
    (hpk : pk.val.length = sp.pkLen) (hsk : sk.val.length = sp.skLen)
    (F : Spec.Fuel) (pk' sk' : List UInt8)
    (hs : Spec.KeyGen_internal sp (bytesA ξ) F = some (pk', sk')) :
    keygen.keygen_internal K L ip ξ pk sk ⦃ r => bytes r.1 = pk' ∧ bytes r.2 = sk' ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hkl := hstd.kl_lt
  have hd := hstd.d_eq
  have hpkLen : sp.pkLen = 32 + 320 * sp.k := pkLen_eq sp hd
  obtain ⟨A, s₁, s₂, hA, hS, hpk', hsk'⟩ := keygen_some sp F _ _ _ hs
  unfold keygen.keygen_internal
  step*
  -- the bytes absorbed by the first hash
  have hiv : i.val = sp.k % 256 := by rw [i_post, UScalar.cast_val_eq, hK]; rfl
  have hi1v : i1.val = sp.ℓ % 256 := by rw [i1_post, UScalar.cast_val_eq, hL]; rfl
  have hbs : bytes s = bytesA ξ := by rw [s_post, bytes_to_slice]
  have hbs1 : bytes s1 = IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1 := by
    rw [s1_post, bytes_to_slice, integerToBytes_one, integerToBytes_one]
    simp only [bytesA, Array.make, List.map_cons, List.map_nil]
    have e1 : UInt8.ofNat i.val = (sp.k % 256).toUInt8 := by rw [hiv]
    have e2 : UInt8.ofNat i1.val = (sp.ℓ % 256).toUInt8 := by rw [hi1v]
    rw [e1, e2]; rfl
  have hM : ([] ++ bytes s ++ bytes s1 : List UInt8) =
      bytesA ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1 := by
    rw [List.nil_append, hbs, hbs1, ← List.append_assoc]
  have hs2len : s2.val.length = 128 := by rw [s2_post1]; simp
  have hs3b : bytes s3 = H (bytesA ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 := by
    rw [__post2, List.drop_zero, Nat.zero_add, hs2len, hM]; rfl
  have hs3len : s3.val.length = 128 := by
    have h := congrArg List.length hs3b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  generalize H (bytesA ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hs3b hA hS hpk' hsk'
  have hE : bytesA (to_slice_mut_back s3) = out := by
    rw [s2_post2, bytesA_from_slice _ _ hs3len, hs3b]
  generalize to_slice_mut_back s3 = E at hE ⊢
  refine WP.spec_bind (loop0_spec E _ _) ?_
  rintro ⟨rho1, key1⟩ ⟨hrho, hkey⟩
  refine WP.spec_bind (loop1_spec E _) ?_
  intro rp hrp
  have hrho' : bytesA rho1 = slice out 0 32 := by rw [hrho, hE]; simp [slice]
  have hkey' : bytesA key1 = slice out 96 32 := by rw [hkey, hE]; rfl
  have hrp' : bytesA rp = slice out 32 64 := by rw [hrp, hE]; rfl
  refine WP.spec_bind (expand_a_spec sp K L hK hL rho1 A F.rejNTT (by rw [hrho']; exact hA)) ?_
  intro ahat hahat
  refine WP.spec_bind (expand_s_spec hv hstd.eta hkl rp s₁ s₂ F.rejBounded (by rw [hrp']; exact hS)) ?_
  rintro ⟨s11, s21⟩ ⟨hs1r, hs2r, hb1, hb2⟩
  refine WP.spec_bind (ntt_vec_spec s11 _ hs1r.repr) ?_
  intro sh hsh
  refine WP.spec_bind (compute_t_spec ahat A hahat sh _ hsh s21 s₂ hs2r) ?_
  intro t ht
  refine WP.spec_bind (vec_power2round_spec sp hd t (tVec sp A s₁ s₂) ht) ?_
  rintro ⟨t1, t0⟩ ⟨ht1, ht0⟩
  have hrange := power2roundVec_range sp hd (tVec sp A s₁ s₂)
  refine WP.spec_bind (pk_encode_spec ip sp hv rho1 t1 _ ht1 ?_ pk (by rw [hpk, hpkLen])) ?_
  · intro i hi j hj
    have := hrange.1 i hi j hj
    rw [t1Bits_eq sp hd]
    constructor <;> omega
  intro pk1 hpk1
  have hpk1len : pk1.val.length = 32 + 320 * sp.k := by
    have h := congrArg List.length hpk1
    rw [bytes_length, pkEncode_length sp hd _ (by simp)] at h
    exact h
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hidx : core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨i3⟩ pk1 ⦃ s4 =>
      bytes s4 = (bytes pk1).take i3.val ⦄ :=
    slice_to_bytes pk1 ⟨i3⟩ (by simp only []; omega)
  refine WP.spec_bind hidx ?_
  intro s4 hs4
  step*
  have hs5len : s5.val.length = 64 := by rw [s5_post1]; simp
  have hs4' : bytes s4 = bytes pk1 := by
    rw [hs4]
    apply List.take_of_length_le
    simp only [bytes_length]
    omega
  have hs6 : bytes s6 = H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64 := by
    rw [__post2, List.drop_zero, Nat.zero_add, hs5len, List.nil_append, hs4', hpk1, hrho']; rfl
  have hs6len : s6.val.length = 64 := by
    have h := congrArg List.length hs6
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  have htr : bytesA (to_slice_mut_back1 s6) =
      H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64 := by
    rw [s5_post2, bytesA_from_slice _ _ hs6len, hs6]
  refine WP.spec_bind (sk_encode_spec ip sp hv hstd.eta_lt rho1 key1 (to_slice_mut_back1 s6) s11 s21 t0
    s₁ s₂ _ hs1r hs2r ht0 ?_ ?_ hrange.2 sk hsk) ?_
  · intro i hi j hj
    have := hb1 i hi j hj
    omega
  · intro i hi j hj
    have := hb2 i hi j hj
    omega
  intro sk1 hsk1
  simp only [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · rw [hpk1, hpk', hrho']
  · rw [hsk1, hsk', htr, hrho', hkey']

/-- Headline form: the extracted `keygen_internal` returns `ok` and the buffers hold the spec's `(pk, sk)`. -/
theorem keygen_internal_correct {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (ξ : Array U8 32#usize) (pk sk : Slice U8)
    (hpk : pk.val.length = sp.pkLen) (hsk : sk.val.length = sp.skLen)
    (F : Spec.Fuel) (pk' sk' : List UInt8)
    (hs : Spec.KeyGen_internal sp (bytesA ξ) F = some (pk', sk')) :
    ∃ r, keygen.keygen_internal K L ip ξ pk sk = ok r ∧ bytes r.1 = pk' ∧ bytes r.2 = sk' :=
  WP.spec_imp_exists (keygen_internal_spec hp ξ pk sk hpk hsk F pk' sk' hs)

end Proofs
