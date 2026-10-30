import Proofs.PartialSampleS
import Proofs.API
import Proofs.PartialAPI

/-!
# Partial correctness and panic-freedom of KeyGen (FIPS 204 Algorithms 6 and 1)

See `Proofs/Partial.lean` for the technique. For every seed `ξ` (and, for `keygen_internal`, output buffers of the
lengths the code writes into):

* the Rust never panics, and
* if it returns `(pk, sk)`, then there is a fuel `F` with `Spec.KeyGen_internal … F = some (pk, sk)`.

The fuels of ExpandA and ExpandS are independent fields of `Spec.Fuel`, so the two sampler fuels are installed in
the two fields. No premise other than the argument types (plus the buffer lengths for `keygen_internal`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open KeyGen

/-- The converse of `keygen_some`: if both samplers succeed (at their own fuels) on the seeds the spec derives,
then `KeyGen_internal` is `some` of the encoded keys. -/
theorem keygen_of_samplers (sp : Spec.Params) (F1 F2 : Nat) (ξ out : List UInt8)
    (hout : out = H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128)
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k)
    (hA : Spec.ExpandA sp F1 (slice out 0 32) = some A)
    (hS : Spec.ExpandS sp F2 (slice out 32 64) = some (s₁, s₂)) :
    Spec.KeyGen_internal sp ξ { rejNTT := F1, rejBounded := F2 } =
      some (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1,
        skEncode sp (slice out 0 32) (slice out 96 32)
          (H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64)
          s₁ s₂ (Power2RoundVec sp (tVec sp A s₁ s₂)).2) := by
  subst hout
  unfold Spec.KeyGen_internal
  generalize H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hA hS ⊢
  simp [hA, hS, tVec]

theorem keygen_internal_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (ξ : Array U8 32#usize) (pk sk : Slice U8)
    (hpk : pk.val.length = sp.pkLen) (hsk : sk.val.length = sp.skLen) :
    keygen.keygen_internal K L ip ξ pk sk ⦃ r =>
      ∃ F, Spec.KeyGen_internal sp (bytesA ξ) F = some (bytes r.1, bytes r.2) ⦄div := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hkl := hstd.kl_lt
  have hd := hstd.d_eq
  have hpkLen : sp.pkLen = 32 + 320 * sp.k := pkLen_eq sp hd
  unfold keygen.keygen_internal
  step*
  obtain ⟨s2, tsmb⟩ := s2
  rename' to_slice_mut_back => s2_post1
  try dsimp only
  step*
  rename' s3 => s3_sq
  split_pair
  rename_i hx3 s3
  try dsimp only
  rename' __post2 => hs3raw
  step*
  dsimp only at s2_post1 s2_post2 s3_sq hs3raw
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
    rw [hs3raw, List.drop_zero, Nat.zero_add, hs2len, hM]; rfl
  have hs3len : s3.val.length = 128 := by
    have h := congrArg List.length hs3b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  obtain ⟨out, hout⟩ : ∃ out, out = H (bytesA ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 :=
    ⟨_, rfl⟩
  rw [← hout] at hs3b
  have hE : bytesA (tsmb s3) = out := by
    rw [s2_post2, bytesA_from_slice _ _ hs3len, hs3b]
  generalize tsmb s3 = E at hE ⊢
  refine dspec_bind_of_spec (loop0_spec E _ _) ?_
  rintro ⟨rho1, key1⟩ ⟨hrho, hkey⟩
  refine dspec_bind_of_spec (loop1_spec E _) ?_
  intro rp hrp
  have hrho' : bytesA rho1 = slice out 0 32 := by rw [hrho, hE]; simp [slice]
  have hkey' : bytesA key1 = slice out 96 32 := by rw [hkey, hE]; rfl
  have hrp' : bytesA rp = slice out 32 64 := by rw [hrp, hE]; rfl
  refine WP.dspec_bind' (expand_a_partial sp K L hK hL rho1) ?_
  rintro ahat ⟨A, F1, hA, hahat⟩
  refine WP.dspec_bind' (expand_s_partial hv hstd.eta hkl rp) ?_
  rintro ⟨s11, s21⟩ ⟨s₁, s₂, F2, hS, hs1r, hs2r⟩
  obtain ⟨hr1, hr2⟩ := ExpandS_some sp F2 _ s₁ s₂ hS
  have hb1 : ∀ (i : Nat) (hi : i < sp.ℓ) (j : Nat) (hj : j < 256), ((s₁[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp F2 _ _ (hr1 i hi)
  have hb2 : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256), ((s₂[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp F2 _ _ (hr2 i hi)
  rw [hrho'] at hA
  rw [hrp'] at hS
  refine dspec_bind_of_spec (ntt_vec_spec s11 _ hs1r.repr) ?_
  intro sh hsh
  refine dspec_bind_of_spec (compute_t_spec ahat A hahat sh _ hsh s21 s₂ hs2r) ?_
  intro t ht
  refine dspec_bind_of_spec (vec_power2round_spec sp hd t (tVec sp A s₁ s₂) ht) ?_
  rintro ⟨t1, t0⟩ ⟨ht1, ht0⟩
  have hrange := power2roundVec_range sp hd (tVec sp A s₁ s₂)
  refine dspec_bind_of_spec (pk_encode_spec ip sp hv rho1 t1 _ ht1 ?_ pk (by rw [hpk, hpkLen])) ?_
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
  refine dspec_bind_of_spec hidx ?_
  intro s4 hs4
  step*
  obtain ⟨s5, tsmb1⟩ := s5
  rename' to_slice_mut_back1 => s5_post1
  try dsimp only
  step*
  rename' s6 => s6_sq
  split_pair
  rename_i hx6 s6
  try dsimp only
  rename' __post2 => hs6raw
  dsimp only at s5_post1 s5_post2 s6_sq hs6raw
  have hs5len : s5.val.length = 64 := by rw [s5_post1]; simp
  have hs4' : bytes s4 = bytes pk1 := by
    rw [hs4]
    apply List.take_of_length_le
    simp only [bytes_length]
    omega
  have hs6 : bytes s6 = H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64 := by
    rw [hs6raw, List.drop_zero, Nat.zero_add, hs5len, List.nil_append, hs4', hpk1, hrho']; rfl
  have hs6len : s6.val.length = 64 := by
    have h := congrArg List.length hs6
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  have htr : bytesA (tsmb1 s6) =
      H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64 := by
    rw [s5_post2, bytesA_from_slice _ _ hs6len, hs6]
  refine dspec_bind_of_spec (sk_encode_spec ip sp hv hstd.eta_lt rho1 key1 (tsmb1 s6) s11 s21 t0
    s₁ s₂ _ hs1r hs2r ht0 ?_ ?_ hrange.2 sk hsk) ?_
  · intro i hi j hj
    have := hb1 i hi j hj
    omega
  · intro i hi j hj
    have := hb2 i hi j hj
    omega
  intro sk1 hsk1
  simp only [WP.dspec_ok]
  refine ⟨{ rejNTT := F1, rejBounded := F2 }, ?_⟩
  rw [keygen_of_samplers sp F1 F2 (bytesA ξ) out hout A s₁ s₂ hA hS]
  show some _ = some (bytes pk1, bytes sk1)
  rw [hpk1, hsk1, htr, hrho', hkey']

namespace API
open Proofs.API

theorem keygenAPI_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.pkLen) (hN : N.val = sp.skLen)
    (ξ : Array U8 32#usize) :
    keygenAPI n N K L (ok ip) ξ ⦃ r =>
      ∃ F, Spec.KeyGen sp (bytesA ξ) F = some (bytesA r.1, bytesA r.2) ⦄div := by
  unfold keygenAPI
  simp only [Std.bind_tc_ok]
  step*
  obtain ⟨s, tsmb⟩ := s
  rename' to_slice_mut_back => s_post1
  try dsimp only
  step*
  obtain ⟨s1, tsmb1⟩ := s1
  rename' to_slice_mut_back1 => s1_post1
  dsimp only at s_post1 s_post2 s1_post1 s1_post2
  have hsl : s.val.length = sp.pkLen := by rw [s_post1]; simp [Array.repeat_val, hn]
  have hsl1 : s1.val.length = sp.skLen := by rw [s1_post1]; simp [Array.repeat_val, hN]
  refine WP.dspec_bind' (keygen_internal_partial hp ξ s s1 hsl hsl1) ?_
  rintro ⟨s2, s3⟩ ⟨F, hF⟩
  have hF' : Spec.KeyGen_internal sp (bytesA ξ) F = some (bytes s2, bytes s3) := hF
  obtain ⟨hlpk, hlsk⟩ := keygen_lens sp hp.2.d_eq F _ _ _ hF'
  have hl2 : s2.val.length = n.val := by
    simp only [bytes_length] at hlpk
    omega
  have hl3 : s3.val.length = N.val := by
    simp only [bytes_length] at hlsk
    omega
  refine (WP.dspec_ok _).2 ?_
  refine ⟨F, ?_⟩
  show Spec.KeyGen_internal sp (bytesA ξ) F = some (bytesA (tsmb s2), bytesA (tsmb1 s3))
  rw [s_post2, s1_post2, bytesA_from_slice _ _ hl2, bytesA_from_slice _ _ hl3]
  exact hF'

end API

open API

/-! ## The three public functions -/

theorem keygen_44_dspec (ξ : Array U8 32#usize) :
    api.keygen_44 ξ ⦃ r =>
      ∃ F, Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (bytesA r.1, bytesA r.2) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [keygen_44_eq, hip]
  exact keygenAPI_partial hp _ _ (by rw [show Spec.ML_DSA_44.pkLen = 1312 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl) ξ

theorem keygen_65_dspec (ξ : Array U8 32#usize) :
    api.keygen_65 ξ ⦃ r =>
      ∃ F, Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (bytesA r.1, bytesA r.2) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [keygen_65_eq, hip]
  exact keygenAPI_partial hp _ _ (by rw [show Spec.ML_DSA_65.pkLen = 1952 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl) ξ

theorem keygen_87_dspec (ξ : Array U8 32#usize) :
    api.keygen_87 ξ ⦃ r =>
      ∃ F, Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (bytesA r.1, bytesA r.2) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [keygen_87_eq, hip]
  exact keygenAPI_partial hp _ _ (by rw [show Spec.ML_DSA_87.pkLen = 2592 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl) ξ

/-! ## Headline statements -/

/-- **ML-DSA-44 `keygen`, partial correctness and panic-freedom.** For every seed the Rust never returns `fail`
(never panics), and if it returns `ok (pk, sk)` then the spec returns `some (pk, sk)` at some fuel. -/
theorem keygen_44_partial (ξ : Array U8 32#usize) :
    (∀ e, api.keygen_44 ξ ≠ .fail e) ∧
    ∀ pk sk, api.keygen_44 ξ = ok (pk, sk) →
      ∃ F, Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (bytesA pk, bytesA sk) :=
  ⟨dspec_not_fail (keygen_44_dspec ξ),
    fun pk sk h => WP.dspec_imp_forall (keygen_44_dspec ξ) (pk, sk) h⟩

/-- **ML-DSA-65 `keygen`, partial correctness and panic-freedom.** For every seed the Rust never returns `fail`
(never panics), and if it returns `ok (pk, sk)` then the spec returns `some (pk, sk)` at some fuel. -/
theorem keygen_65_partial (ξ : Array U8 32#usize) :
    (∀ e, api.keygen_65 ξ ≠ .fail e) ∧
    ∀ pk sk, api.keygen_65 ξ = ok (pk, sk) →
      ∃ F, Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (bytesA pk, bytesA sk) :=
  ⟨dspec_not_fail (keygen_65_dspec ξ),
    fun pk sk h => WP.dspec_imp_forall (keygen_65_dspec ξ) (pk, sk) h⟩

/-- **ML-DSA-87 `keygen`, partial correctness and panic-freedom.** For every seed the Rust never returns `fail`
(never panics), and if it returns `ok (pk, sk)` then the spec returns `some (pk, sk)` at some fuel. -/
theorem keygen_87_partial (ξ : Array U8 32#usize) :
    (∀ e, api.keygen_87 ξ ≠ .fail e) ∧
    ∀ pk sk, api.keygen_87 ξ = ok (pk, sk) →
      ∃ F, Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (bytesA pk, bytesA sk) :=
  ⟨dspec_not_fail (keygen_87_dspec ξ),
    fun pk sk h => WP.dspec_imp_forall (keygen_87_dspec ξ) (pk, sk) h⟩

/-! ## Exactness: the Rust agrees with the unbounded FIPS 204 algorithm -/

/-- **ML-DSA-44 `keygen` is exactly the unbounded FIPS 204 Algorithm 1.** For all `F`, `pk`, `sk`:
`Spec … F = some (pk, sk) → Rust = ok (arrays holding pk, sk)`; `Rust = ok (pk, sk) → ∃ F, Spec … F = some …`;
and the Rust is never `fail`. (So the Rust diverges exactly when the spec returns `none` at every fuel.) -/
theorem keygen_44_exact (ξ : Array U8 32#usize) :
    (∀ e, api.keygen_44 ξ ≠ .fail e) ∧
    (∀ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (pk, sk) →
      ∃ r, api.keygen_44 ξ = ok r ∧ bytesA r.1 = pk ∧ bytesA r.2 = sk) ∧
    (∀ pk sk, api.keygen_44 ξ = ok (pk, sk) →
      ∃ F, Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (bytesA pk, bytesA sk)) :=
  ⟨(keygen_44_partial ξ).1,
    fun F pk sk hs => WP.spec_imp_exists (keygen_44_correct ξ F pk sk hs),
    (keygen_44_partial ξ).2⟩

/-- **ML-DSA-65 `keygen` is exactly the unbounded FIPS 204 Algorithm 1.** For all `F`, `pk`, `sk`:
`Spec … F = some (pk, sk) → Rust = ok (arrays holding pk, sk)`; `Rust = ok (pk, sk) → ∃ F, Spec … F = some …`;
and the Rust is never `fail`. (So the Rust diverges exactly when the spec returns `none` at every fuel.) -/
theorem keygen_65_exact (ξ : Array U8 32#usize) :
    (∀ e, api.keygen_65 ξ ≠ .fail e) ∧
    (∀ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (pk, sk) →
      ∃ r, api.keygen_65 ξ = ok r ∧ bytesA r.1 = pk ∧ bytesA r.2 = sk) ∧
    (∀ pk sk, api.keygen_65 ξ = ok (pk, sk) →
      ∃ F, Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (bytesA pk, bytesA sk)) :=
  ⟨(keygen_65_partial ξ).1,
    fun F pk sk hs => WP.spec_imp_exists (keygen_65_correct ξ F pk sk hs),
    (keygen_65_partial ξ).2⟩

/-- **ML-DSA-87 `keygen` is exactly the unbounded FIPS 204 Algorithm 1.** For all `F`, `pk`, `sk`:
`Spec … F = some (pk, sk) → Rust = ok (arrays holding pk, sk)`; `Rust = ok (pk, sk) → ∃ F, Spec … F = some …`;
and the Rust is never `fail`. (So the Rust diverges exactly when the spec returns `none` at every fuel.) -/
theorem keygen_87_exact (ξ : Array U8 32#usize) :
    (∀ e, api.keygen_87 ξ ≠ .fail e) ∧
    (∀ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (pk, sk) →
      ∃ r, api.keygen_87 ξ = ok r ∧ bytesA r.1 = pk ∧ bytesA r.2 = sk) ∧
    (∀ pk sk, api.keygen_87 ξ = ok (pk, sk) →
      ∃ F, Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (bytesA pk, bytesA sk)) :=
  ⟨(keygen_87_partial ξ).1,
    fun F pk sk hs => WP.spec_imp_exists (keygen_87_correct ξ F pk sk hs),
    (keygen_87_partial ξ).2⟩

end Proofs
