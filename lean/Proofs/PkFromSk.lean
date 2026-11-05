import Proofs.PartialKeyGen
import Proofs.SkWellFormed

/-!
# The key-consistency check `pk_from_sk_NN`

`api.pk_from_sk_NN sk` is not a FIPS 204 step. It returns `some pk` exactly when the expanded secret key `sk` is
internally consistent, and then `pk` is the public key of `sk`:

1. every coefficient of `s₁` and `s₂` that `skDecode` returns lies in `[−η, η]` (`skWellFormed`), and
2. recomputing from `(ρ, s₁, s₂)` as in `KeyGen_internal` steps 5–9 (`Â ← ExpandA(ρ)`;
   `t ← NTT⁻¹(Â ∘ NTT(s₁)) + s₂`; `(t₁, t₀) ← Power2Round(t)`; `pk ← pkEncode(ρ, t₁)`; `tr ← H(pk, 64)`) gives
   the stored `t₀` and the stored `tr`.

The key `K` (bytes 32..64) is not checked: it is a free seed. `Sign` does not call this function.

## The spec side

`skConsistentR sp sk F` is the fuel-bounded specification, defined in `Proofs` from the `Spec` functions
`skDecode`, `ExpandA`, `NTT`, `Power2Round`, `pkEncode` and `H`; it is not a FIPS algorithm, so it does not
belong in `Spec`. Like the spec samplers it takes a fuel `F` for `ExpandA`. Its value has three cases:

* `none`: `ExpandA` ran out of fuel (the Rust loop would keep sampling),
* `some none`: the key is not consistent (range check failed, or the recomputed `t₀` or `tr` differs),
* `some (some pk)`: the key is consistent and `pk` is its public key.

`skConsistent sp sk F : Option (List UInt8)` is the flattened `Option`: `some pk` iff consistent and `ExpandA`
finishes within `F`.

## Results

* `pk_from_sk_NN_exact`: `api.pk_from_sk_NN` never fails; `skConsistentR … F = some o` at any fuel gives
  `ok r` with `r.map bytesA = o`; and `ok r` gives some fuel `F` with `skConsistentR … F = some (r.map bytesA)`.
  No premise other than the array type. So the Rust diverges exactly when `skConsistentR` is `none` at every
  fuel (`Divergence.lean`).
* `skConsistent_keygen` (completeness): the secret key of every `Spec.KeyGen_internal` result is accepted and
  gives back that result's public key.
* `skConsistent_sound` (soundness): if `skConsistent` returns `some pk`, then `s₁`, `s₂` are in range and,
  with `(ρ, K, tr, s₁, s₂, t₀) = skDecode sk`, `pk = pkEncode ρ t₁` for the `(t₁, t₀)` that `Power2Round` gives
  from `ExpandA(ρ)`, `s₁`, `s₂`, the stored `t₀` is that `t₀`, and the stored `tr` is `H(pk, 64)`.
* `skConsistent_bad_44`: a kernel witness that the check can fail (a key with an out-of-range `s₁`). That it
  can succeed is `skConsistent_keygen`: no concrete witness exists in the kernel because KeyGen needs SHAKE and
  `ExpandA`/`ExpandS` on a derived seed (the same reason as for the top-level KeyGen premises, docs/assurance.md).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open KeyGen

/-! ## The specification -/

/-- The fuel-bounded key-consistency check. `none`: `ExpandA` out of fuel. `some none`: not consistent.
`some (some pk)`: consistent, `pk` is the public key. -/
def skConsistentR (sp : Spec.Params) (sk : List UInt8) (F : Nat) : Option (Option (List UInt8)) :=
  if skWellFormed sp sk = true then                          -- s₁, s₂ within [−η, η]
    let (ρ, _K, tr, s₁, s₂, t₀) := Spec.skDecode sp sk       -- 1: skDecode (K is not checked)
    match Spec.ExpandA sp F ρ with                           -- 3: Â ← ExpandA(ρ)
    | none => none
    | some Â =>
      let t := NTTInvVec (MatrixVectorNTT Â (NTTVec (s₁.map RPoly.toZq))) + s₂.map RPoly.toZq    -- 5
      let (t₁, t₀') := Power2RoundVec sp t                   -- 6
      let pk := pkEncode sp ρ t₁                             -- 8
      if t₀' = t₀ ∧ H pk 64 = tr then some (some pk) else some none    -- 9: tr = H(pk, 64), and t₀
  else some none

/-- `some pk` iff the key is consistent (and `ExpandA` finishes within `F`); `none` otherwise. -/
def skConsistent (sp : Spec.Params) (sk : List UInt8) (F : Nat) : Option (List UInt8) :=
  (skConsistentR sp sk F).getD none

theorem skConsistent_eq_some_iff (sp : Spec.Params) (sk : List UInt8) (F : Nat) (pk : List UInt8) :
    skConsistent sp sk F = some pk ↔ skConsistentR sp sk F = some (some pk) := by
  unfold skConsistent
  cases h : skConsistentR sp sk F with
  | none => simp
  | some o => simp

theorem tVec_eq (sp : Spec.Params) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ)
    (s₂ : Vector RPoly sp.k) :
    tVec sp A s₁ s₂ = NTTInvVec (MatrixVectorNTT A (NTTVec (s₁.map RPoly.toZq))) + s₂.map RPoly.toZq := rfl

theorem skConsistentR_not_wf (sp : Spec.Params) (sk : List UInt8) (F : Nat)
    (h : skWellFormed sp sk = false) : skConsistentR sp sk F = some none := by
  unfold skConsistentR
  simp [h]

theorem skConsistentR_exhausted (sp : Spec.Params) (sk : List UInt8) (F : Nat)
    (ρ K tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hwf : skWellFormed sp sk = true) (hd : Spec.skDecode sp sk = (ρ, K, tr, s₁, s₂, t₀))
    (hA : Spec.ExpandA sp F ρ = none) : skConsistentR sp sk F = none := by
  unfold skConsistentR
  rw [if_pos hwf, hd]
  simp only [hA]

theorem skConsistentR_some (sp : Spec.Params) (sk : List UInt8) (F : Nat)
    (ρ K tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k)
    (hwf : skWellFormed sp sk = true) (hd : Spec.skDecode sp sk = (ρ, K, tr, s₁, s₂, t₀))
    (hA : Spec.ExpandA sp F ρ = some A) :
    skConsistentR sp sk F =
      if (Power2RoundVec sp (tVec sp A s₁ s₂)).2 = t₀ ∧
          H (pkEncode sp ρ (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64 = tr
      then some (some (pkEncode sp ρ (Power2RoundVec sp (tVec sp A s₁ s₂)).1)) else some none := by
  unfold skConsistentR
  rw [if_pos hwf, hd]
  simp only [hA, tVec]

/-! ## The Rust side: comparing arrays -/

theorem u32_val_zero_iff (w : U32) : w.val = 0 ↔ w.bv = 0#_ := by
  show w.bv.toNat = 0 ↔ _
  rw [BitVec.toNat_eq]
  simp

theorem u32_bv_eq (x y : U32) : x.bv = y.bv ↔ x = y :=
  ⟨fun h => by cases x; cases y; simp_all, fun h => by rw [h]⟩

theorem u32_or_xor_zero (d x y z w : U32) (h1' : z.val = (d ||| w).val) (h2' : w.val = (x ^^^ y).val) :
    z.val = 0 ↔ d.val = 0 ∧ x = y := by
  have h1 : z.bv = d.bv ||| w.bv := by
    rw [UScalar.eq_of_val_eq h1']; exact UScalar.bv_or d w
  have h2 : w.bv = x.bv ^^^ y.bv := by
    rw [UScalar.eq_of_val_eq h2']; exact UScalar.bv_xor x y
  constructor
  · intro h
    have h0 := (u32_val_zero_iff z).1 h
    obtain ⟨hd0, hw0⟩ := BitVec.or_eq_zero_iff.1 (h1.symm.trans h0)
    exact ⟨(u32_val_zero_iff d).2 hd0,
      (u32_bv_eq x y).1 (BitVec.xor_eq_zero_iff.1 (h2.symm.trans hw0))⟩
  · rintro ⟨hd, rfl⟩
    apply (u32_val_zero_iff z).2
    have hd0 := (u32_val_zero_iff d).1 hd
    rw [h1, h2, BitVec.xor_self, hd0]
    simp

theorem u32_or_zero (d x z : U32) (h1' : z.val = (d ||| x).val) : z.val = 0 ↔ d.val = 0 ∧ x.val = 0 := by
  have h1 : z.bv = d.bv ||| x.bv := by
    rw [UScalar.eq_of_val_eq h1']; exact UScalar.bv_or d x
  rw [u32_val_zero_iff, h1, BitVec.or_eq_zero_iff, u32_val_zero_iff, u32_val_zero_iff]

/-- Two fixed-size arrays are equal iff they agree at every index below the size. -/
theorem arr_eq_iff_get {α : Type} {n : Usize} (a b : Array α n) :
    a = b ↔ ∀ c, c < n.val → a.val[c]? = b.val[c]? := by
  constructor
  · rintro rfl c _
    rfl
  · intro h
    apply Subtype.ext
    apply List.ext_getElem?
    intro c
    by_cases hc : c < n.val
    · exact h c hc
    · rw [List.getElem?_eq_none (by rw [a.property]; omega), List.getElem?_eq_none (by rw [b.property]; omega)]

theorem poly_diff_loop_spec (a b : Array U32 256#usize) (diff : U32) (i : Usize) (hi : i.val ≤ 256)
    (hinv : diff.val = 0 ↔ ∀ c, c < i.val → a.val[c]? = b.val[c]?) :
    keygen.poly_diff_loop a b diff i ⦃ d => d.val = 0 ↔ ∀ c, c < 256 → a.val[c]? = b.val[c]? ⦄ := by
  unfold keygen.poly_diff_loop
  apply loop.spec_decr_nat
    (fun (p : U32 × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (p.1.val = 0 ↔ ∀ c, c < p.2.val → a.val[c]? = b.val[c]?))
  · rintro ⟨d, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keygen.poly_diff_loop.body]
    split
    · rename_i hj
      have hj' : i.val < 256 := by scalar_tac
      have hla : i.val < a.val.length := by rw [len256 a]; exact hj'
      have hlb : i.val < b.val.length := by rw [len256 b]; exact hj'
      step with arr_index_spec a i hla as ⟨x1, hx1⟩
      step with arr_index_spec b i hlb as ⟨x2, hx2⟩
      step as ⟨i3, hi3⟩
      step as ⟨diff1, hdiff1⟩
      step as ⟨i4, hi4⟩
      have hx : diff1.val = 0 ↔ d.val = 0 ∧ x1 = x2 := u32_or_xor_zero d x1 x2 diff1 i3 hdiff1 hi3
      have hcc : (∀ c, c < i.val + 1 → a.val[c]? = b.val[c]?) ↔
          (∀ c, c < i.val → a.val[c]? = b.val[c]?) ∧ a.val[i.val]? = b.val[i.val]? :=
        ⟨fun h => ⟨fun c hc => h c (by omega), h _ (by omega)⟩, fun ⟨h, h'⟩ c hc => by
          by_cases e : c = i.val
          · subst e; exact h'
          · exact h c (by omega)⟩
      have hai : a.val[i.val]? = some a.val[i.val] := List.getElem?_eq_getElem hla
      have hbi : b.val[i.val]? = some b.val[i.val] := List.getElem?_eq_getElem hlb
      refine ⟨by omega, ?_, by omega⟩
      have hi4v : i4.val = i.val + 1 := by scalar_tac
      rw [hi4v, hcc, hai, hbi, ← h2, hx, hx1, hx2]
      simp
    · rename_i hj
      simp only [WP.spec_ok]
      have : i.val = 256 := by scalar_tac
      rw [this] at h2
      exact h2
  · exact ⟨hi, hinv⟩

theorem poly_diff_spec (a b : Array U32 256#usize) :
    keygen.poly_diff a b ⦃ d => d.val = 0 ↔ a = b ⦄ := by
  unfold keygen.poly_diff
  refine WP.spec_mono (poly_diff_loop_spec a b 0#u32 0#usize (by simp) (by simp)) ?_
  intro d hd
  rw [hd]
  exact (arr_eq_iff_get a b).symm

theorem vec_diff_loop_spec {K : Usize} (a b : Array (Array U32 256#usize) K) (diff : U32) (i : Usize)
    (hi : i.val ≤ K.val) (hinv : diff.val = 0 ↔ ∀ c, c < i.val → a.val[c]? = b.val[c]?) :
    keygen.vec_diff_loop a b diff i ⦃ d => d.val = 0 ↔ ∀ c, c < K.val → a.val[c]? = b.val[c]? ⦄ := by
  unfold keygen.vec_diff_loop
  apply loop.spec_decr_nat
    (fun (p : U32 × Usize) => K.val - p.2.val)
    (fun p => p.2.val ≤ K.val ∧ (p.1.val = 0 ↔ ∀ c, c < p.2.val → a.val[c]? = b.val[c]?))
  · rintro ⟨d, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keygen.vec_diff_loop.body]
    split
    · rename_i hj
      have hj' : i.val < K.val := by scalar_tac
      have hla : i.val < a.val.length := by rw [a.property]; exact hj'
      have hlb : i.val < b.val.length := by rw [b.property]; exact hj'
      step with arr_index_spec a i hla as ⟨x1, hx1⟩
      step with arr_index_spec b i hlb as ⟨x2, hx2⟩
      step with poly_diff_spec x1 x2 as ⟨e, he⟩
      step as ⟨diff1, hdiff1⟩
      step as ⟨i4, hi4⟩
      have hx : diff1.val = 0 ↔ d.val = 0 ∧ x1 = x2 := by
        rw [u32_or_zero d e diff1 hdiff1, he]
      have hcc : (∀ c, c < i.val + 1 → a.val[c]? = b.val[c]?) ↔
          (∀ c, c < i.val → a.val[c]? = b.val[c]?) ∧ a.val[i.val]? = b.val[i.val]? :=
        ⟨fun h => ⟨fun c hc => h c (by omega), h _ (by omega)⟩, fun ⟨h, h'⟩ c hc => by
          by_cases e : c = i.val
          · subst e; exact h'
          · exact h c (by omega)⟩
      have hai : a.val[i.val]? = some a.val[i.val] := List.getElem?_eq_getElem hla
      have hbi : b.val[i.val]? = some b.val[i.val] := List.getElem?_eq_getElem hlb
      refine ⟨by omega, ?_, by omega⟩
      have hi4v : i4.val = i.val + 1 := by scalar_tac
      rw [hi4v, hcc, hai, hbi, ← h2, hx, hx1, hx2]
      simp
    · rename_i hj
      simp only [WP.spec_ok]
      have : i.val = K.val := by scalar_tac
      rw [this] at h2
      exact h2
  · exact ⟨hi, hinv⟩

theorem vec_diff_spec {K : Usize} (a b : Array (Array U32 256#usize) K) :
    keygen.vec_diff a b ⦃ d => d.val = 0 ↔ a = b ⦄ := by
  unfold keygen.vec_diff
  refine WP.spec_mono (vec_diff_loop_spec a b 0#u32 0#usize (by simp) (by simp)) ?_
  intro d hd
  rw [hd]
  exact (arr_eq_iff_get a b).symm

theorem u32_eq_zero_iff (d : U32) : d = 0#u32 ↔ d.val = 0 :=
  ⟨fun h => by subst h; rfl, fun h => UScalar.eq_of_val_eq (by simpa using h)⟩

/-- Two stored integer vectors are equal as arrays iff the integer vectors are equal, when all coefficients are
small (`|x| ≤ 4096 < q / 2`). -/
theorem reprIntVec_eq_iff {K : Usize} {k : Nat} {a b : Array (Array U32 256#usize) K} {V W : Vector RPoly k}
    (ha : ReprIntVec a V) (hb : ReprIntVec b W)
    (hV : ∀ (i : Nat) (hi : i < k) (j : Nat) (hj : j < 256), -4095 ≤ (V[i]'hi)[j]'hj ∧ (V[i]'hi)[j]'hj ≤ 4096)
    (hW : ∀ (i : Nat) (hi : i < k) (j : Nat) (hj : j < 256), -4095 ≤ (W[i]'hi)[j]'hj ∧ (W[i]'hi)[j]'hj ≤ 4096) :
    a = b ↔ V = W := by
  constructor
  · intro hab
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    have h1 := (ha.elt i hi).coeff j hj
    have h2 := (hb.elt i hi).coeff j hj
    subst hab
    have hq : Spec.q = 8380417 := rfl
    rw [hq] at h1 h2
    have e1 := hV i hi j hj
    have e2 := hW i hi j hj
    omega
  · intro hVW
    subst hVW
    exact ha.unique hb

/-- The range of the stored `t₀` that `skDecode` returns: its 13-bit field decodes to `4096 − z`, `z < 2¹³`. -/
theorem skDecode_t0_range (sp : Spec.Params) (hd : sp.d = 13) (sk : List UInt8) (i : Nat) (hi : i < sp.k)
    (j : Nat) (hj : j < 256) :
    -4095 ≤ (Spec.skDecode sp sk).2.2.2.2.2[i][j] ∧ (Spec.skDecode sp sk).2.2.2.2.2[i][j] ≤ 4096 := by
  have h := BitUnpack_range
    (slice sk (128 + (sp.ℓ + sp.k) * (32 * bitlen (2 * sp.η)) + i * (32 * sp.d)) (32 * sp.d))
    (2 ^ (sp.d - 1) - 1) (2 ^ (sp.d - 1)) j hj
  have hb : (2 : Int) ^ bitlen (2 ^ (sp.d - 1) - 1 + 2 ^ (sp.d - 1)) = 8192 := by
    rw [hd]; decide +kernel
  have h2 : (((2 ^ (sp.d - 1) : Nat)) : Int) = 4096 := by rw [hd]; norm_num
  rw [hb, h2] at h
  rw [skDecode_t0 sp sk i hi]
  omega

/-! ## `pk_check` -/

/-- The `Option` a call of `pk_from_sk` stands for: `some pk` if it returned `true`, `none` otherwise. -/
def pkOut (r : Bool × Slice U8) : Option (List UInt8) := if r.1 = true then some (bytes r.2) else none

theorem pk_check_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp)
    (a_hat : Array (Array (Array U32 256#usize) L) K) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k)
    (hA : ReprMat a_hat A) (dec : encode.SecretKey K L)
    (S₁ : Vector RPoly sp.ℓ) (S₂ T₀ : Vector RPoly sp.k)
    (hS₁ : ReprIntVec dec.s1 S₁) (hS₂ : ReprIntVec dec.s2 S₂) (hT₀ : ReprIntVec dec.t0 T₀)
    (hT₀r : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256),
      -4095 ≤ (T₀[i]'hi)[j]'hj ∧ (T₀[i]'hi)[j]'hj ≤ 4096)
    (pk : Slice U8) (hpk : pk.val.length = sp.pkLen) :
    keygen.pk_check a_hat dec pk ⦃ r =>
      r.2.val.length = pk.val.length ∧
      bytes r.2 = pkEncode sp (bytesA dec.rho) (Power2RoundVec sp (tVec sp A S₁ S₂)).1 ∧
      (r.1 = true ↔ (Power2RoundVec sp (tVec sp A S₁ S₂)).2 = T₀ ∧
        H (pkEncode sp (bytesA dec.rho) (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64 = bytesA dec.tr) ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hkl := hstd.kl_lt
  have hd := hstd.d_eq
  have hpkLen : sp.pkLen = 32 + 320 * sp.k := pkLen_eq sp hd
  unfold keygen.pk_check
  refine WP.spec_bind (ntt_vec_spec dec.s1 _ hS₁.repr) ?_
  intro sh hsh
  refine WP.spec_bind (compute_t_spec a_hat A hA sh _ hsh dec.s2 S₂ hS₂) ?_
  intro t ht
  refine WP.spec_bind (vec_power2round_spec sp hd t (tVec sp A S₁ S₂) ht) ?_
  rintro ⟨t1, t0n⟩ ⟨ht1, ht0⟩
  have hrange := power2roundVec_range sp hd (tVec sp A S₁ S₂)
  refine WP.spec_bind (pk_encode_spec ip sp hv dec.rho t1 _ ht1 ?_ pk (by rw [hpk, hpkLen])) ?_
  · intro i hi j hj
    have := hrange.1 i hi j hj
    rw [t1Bits_eq sp hd]
    constructor <;> omega
  intro pk1 hpk1
  have hpk1len : pk1.val.length = 32 + 320 * sp.k := by
    have h := congrArg List.length hpk1
    rw [bytes_length, pkEncode_length sp hd _ (by simp)] at h
    exact h
  step as ⟨h, hh⟩
  step as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hidx : core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨i3⟩ pk1 ⦃ s4 =>
      bytes s4 = (bytes pk1).take i3.val ⦄ :=
    slice_to_bytes pk1 ⟨i3⟩ (by simp only []; omega)
  refine WP.spec_bind hidx ?_
  intro s4 hs4
  step*
  have hs1len : s1.val.length = 64 := by rw [s1_post1]; simp [Array.repeat_val]
  have hbs2 : bytes s2 = H (bytes s4) 64 := by
    rw [__post2]
    simp [hs1len, H, SHAKE256]
  have hs2len : s2.val.length = 64 := by
    rw [← bytes_length, hbs2]; exact SHAKE256_length _ _
  have hi3v : i3.val = 32 + 320 * sp.k := by rw [hi3, hi2, hK]
  have hs4' : bytes s4 = bytes pk1 := by
    rw [hs4, hi3v]; exact List.take_of_length_le (by rw [bytes_length]; omega)
  have hH : bytesA (to_slice_mut_back s2) =
      H (pkEncode sp (bytesA dec.rho) (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64 := by
    rw [s1_post2, bytesA_from_slice _ _ hs2len, hbs2, hs4', hpk1]
  refine WP.spec_bind (vec_diff_spec t0n dec.t0) ?_
  intro d2 hd2
  step with prefix_eq_spec (to_slice_mut_back s2) dec.tr 64#usize (by scalar_tac) as ⟨ts, hts⟩
  have hl1 : (H (pkEncode sp (bytesA dec.rho) (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64).length = 64 :=
    SHAKE256_length _ _
  have hl2 : (bytesA dec.tr).length = 64 := by simp
  have hts' : ts = true ↔ H (pkEncode sp (bytesA dec.rho) (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64 =
      bytesA dec.tr := by
    rw [hts, hH]
    have e1 := List.take_of_length_le (i := 64)
      (l := H (pkEncode sp (bytesA dec.rho) (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64) (by omega)
    have e2 := List.take_of_length_le (i := 64) (l := bytesA dec.tr) (by omega)
    rw [e1, e2]
    simp
  have heq : t0n = dec.t0 ↔ (Power2RoundVec sp (tVec sp A S₁ S₂)).2 = T₀ :=
    reprIntVec_eq_iff ht0 hT₀ hrange.2 hT₀r
  have hz : d2 = 0#u32 ↔ (Power2RoundVec sp (tVec sp A S₁ S₂)).2 = T₀ := by
    rw [u32_eq_zero_iff, hd2, heq]
  have hlen : pk1.val.length = pk.val.length := by rw [hpk1len, hpk, hpkLen]
  by_cases hzz : d2 = 0#u32
  · rw [if_pos hzz]
    simp only [WP.spec_ok]
    refine ⟨hlen, hpk1, ?_⟩
    rw [hts']
    exact ⟨fun h => ⟨hz.1 hzz, h⟩, fun h => h.2⟩
  · rw [if_neg hzz]
    simp only [WP.spec_ok]
    refine ⟨hlen, hpk1, ?_⟩
    constructor
    · intro h; cases h
    · rintro ⟨h1, _⟩; exact absurd (hz.2 h1) hzz

/-! ## `pk_from_sk` -/

/-- The common first steps: `skDecode` as a tuple, with the facts the later steps need. -/
theorem skDecode_tuple (sp : Spec.Params) (sk : List UInt8) :
    ∃ (ρ K tr : List UInt8) (S₁ : Vector RPoly sp.ℓ) (S₂ T₀ : Vector RPoly sp.k),
      Spec.skDecode sp sk = (ρ, K, tr, S₁, S₂, T₀) :=
  ⟨(Spec.skDecode sp sk).1, (Spec.skDecode sp sk).2.1, (Spec.skDecode sp sk).2.2.1,
    (Spec.skDecode sp sk).2.2.2.1, (Spec.skDecode sp sk).2.2.2.2.1, (Spec.skDecode sp sk).2.2.2.2.2, rfl⟩

/-- **`pk_from_sk` against `skConsistentR`, total form**: if the spec returns `some o` at fuel `F`, the Rust returns
`ok r` with `pkOut r = o` (and the output buffer keeps its length). -/
theorem pk_from_sk_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk pk : Slice U8)
    (hsk : sk.val.length = sp.skLen) (hpk : pk.val.length = sp.pkLen) (F : Nat) (o : Option (List UInt8))
    (hs : skConsistentR sp (bytes sk) F = some o) :
    keygen.pk_from_sk K L ip sk pk ⦃ r => pkOut r = o ∧ r.2.val.length = pk.val.length ⦄ := by
  have hv := hp.valid
  have hstd := hp.params
  have hd := hstd.d_eq
  unfold keygen.pk_from_sk
  refine WP.spec_bind (sk_is_well_formed_spec hp sk hsk) ?_
  intro b hb
  by_cases hwf : b = true
  · try dsimp only
    rw [if_pos hwf]
    have hwf' : skWellFormed sp (bytes sk) = true := by rw [← hb]; exact hwf
    refine WP.spec_bind (sk_decode_into_spec ip sp hv hstd.eta_lt sk hsk _) ?_
    intro dec hdec
    obtain ⟨hρ, hK, htr, hs1, hs2, ht0⟩ := hdec
    obtain ⟨ρ, Kk, trs, S₁, S₂, T₀, hdd⟩ := skDecode_tuple sp (bytes sk)
    have hT0r : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256),
        -4095 ≤ (T₀[i]'hi)[j]'hj ∧ (T₀[i]'hi)[j]'hj ≤ 4096 := by
      intro i hi j hj
      have := skDecode_t0_range sp hd (bytes sk) i hi j hj
      rw [hdd] at this
      exact this
    rw [hdd] at hρ htr hs1 hs2 ht0
    simp only at hρ htr hs1 hs2 ht0
    rcases hE : Spec.ExpandA sp F ρ with _ | A
    · exfalso
      rw [skConsistentR_exhausted sp (bytes sk) F ρ Kk trs S₁ S₂ T₀ hwf' hdd hE] at hs
      cases hs
    · rw [skConsistentR_some sp (bytes sk) F ρ Kk trs S₁ S₂ T₀ A hwf' hdd hE] at hs
      refine WP.spec_bind (expand_a_spec sp K L hv.K_eq hv.L_eq dec.rho A F (by rw [hρ]; exact hE)) ?_
      intro ahat hahat
      refine WP.spec_mono (pk_check_spec hp ahat A hahat dec S₁ S₂ T₀ hs1 hs2 ht0 hT0r pk hpk) ?_
      rintro r ⟨hr0, hr1, hr2⟩
      rw [hρ] at hr1 hr2
      rw [htr] at hr2
      refine ⟨?_, hr0⟩
      unfold pkOut
      by_cases hc : (Power2RoundVec sp (tVec sp A S₁ S₂)).2 = T₀ ∧
          H (pkEncode sp ρ (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64 = trs
      · rw [if_pos hc] at hs
        have ho : some (pkEncode sp ρ (Power2RoundVec sp (tVec sp A S₁ S₂)).1) = o :=
          Option.some.inj hs
        have hrt : r.1 = true := hr2.mpr hc
        rw [if_pos hrt, hr1]
        exact ho
      · rw [if_neg hc] at hs
        have ho : none = o := Option.some.inj hs
        have hrf : ¬ r.1 = true := fun h => hc (hr2.mp h)
        rw [if_neg hrf]
        exact ho
  · try dsimp only
    rw [if_neg hwf]
    have hnwf : skWellFormed sp (bytes sk) = false := by rw [← hb]; simpa using hwf
    rw [skConsistentR_not_wf sp (bytes sk) F hnwf] at hs
    simp only [WP.spec_ok]
    cases hs
    refine ⟨?_, ?_⟩ <;> trivial

/-- **`pk_from_sk`, partial form**: it never fails, and if it returns `r` then `skConsistentR` is `some (pkOut r)`
at some fuel. -/
theorem pk_from_sk_dspec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk pk : Slice U8)
    (hsk : sk.val.length = sp.skLen) (hpk : pk.val.length = sp.pkLen) :
    keygen.pk_from_sk K L ip sk pk ⦃ r =>
      (∃ F, skConsistentR sp (bytes sk) F = some (pkOut r)) ∧ r.2.val.length = pk.val.length ⦄div := by
  have hv := hp.valid
  have hstd := hp.params
  have hd := hstd.d_eq
  unfold keygen.pk_from_sk
  refine dspec_bind_of_spec (sk_is_well_formed_spec hp sk hsk) ?_
  intro b hb
  by_cases hwf : b = true
  · try dsimp only
    rw [if_pos hwf]
    have hwf' : skWellFormed sp (bytes sk) = true := by rw [← hb]; exact hwf
    refine dspec_bind_of_spec (sk_decode_into_spec ip sp hv hstd.eta_lt sk hsk _) ?_
    intro dec hdec
    obtain ⟨hρ, hK, htr, hs1, hs2, ht0⟩ := hdec
    obtain ⟨ρ, Kk, trs, S₁, S₂, T₀, hdd⟩ := skDecode_tuple sp (bytes sk)
    have hT0r : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256),
        -4095 ≤ (T₀[i]'hi)[j]'hj ∧ (T₀[i]'hi)[j]'hj ≤ 4096 := by
      intro i hi j hj
      have := skDecode_t0_range sp hd (bytes sk) i hi j hj
      rw [hdd] at this
      exact this
    rw [hdd] at hρ htr hs1 hs2 ht0
    simp only at hρ htr hs1 hs2 ht0
    refine WP.dspec_bind' (expand_a_partial sp K L hv.K_eq hv.L_eq dec.rho) ?_
    rintro ahat ⟨A, F, hE, hahat⟩
    rw [hρ] at hE
    refine WP.dspec_mono' (WP.spec_dspec _ _ _
      (pk_check_spec hp ahat A hahat dec S₁ S₂ T₀ hs1 hs2 ht0 hT0r pk hpk)) ?_
    rintro r ⟨hr0, hr1, hr2⟩
    rw [hρ] at hr1 hr2
    rw [htr] at hr2
    refine ⟨⟨F, ?_⟩, hr0⟩
    rw [skConsistentR_some sp (bytes sk) F ρ Kk trs S₁ S₂ T₀ A hwf' hdd hE]
    unfold pkOut
    by_cases hc : (Power2RoundVec sp (tVec sp A S₁ S₂)).2 = T₀ ∧
        H (pkEncode sp ρ (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64 = trs
    · have hrt : r.1 = true := hr2.mpr hc
      rw [if_pos hc, if_pos hrt, hr1]
    · have hrf : ¬ r.1 = true := fun h => hc (hr2.mp h)
      rw [if_neg hc, if_neg hrf]
  · try dsimp only
    rw [if_neg hwf]
    have hnwf : skWellFormed sp (bytes sk) = false := by rw [← hb]; simpa using hwf
    simp only [WP.dspec_ok]
    refine ⟨⟨0, ?_⟩, ?_⟩
    swap
    · trivial
    rw [skConsistentR_not_wf sp (bytes sk) 0 hnwf]
    simp [pkOut]

/-! ## The API wrappers -/

/-- The body of `api.pk_from_sk_NN`, generic in the array sizes and the parameter record. -/
def pkFromSkAPI (n N : Usize) (K L : Usize) (P : RustM params.Params) (sk : Array U8 n) :
    RustM (Option (Array U8 N)) := do
  let p ← P
  let pk := Array.repeat N 0#u8
  let s ← lift (Array.to_slice sk)
  let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut pk)
  let (b, s2) ← keygen.pk_from_sk K L p s s1
  if b
  then let pk1 := to_slice_mut_back s2
       ok (some pk1)
  else ok none

theorem pk_from_sk_44_eq :
    api.pk_from_sk_44 = pkFromSkAPI 2560#usize 1312#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem pk_from_sk_65_eq :
    api.pk_from_sk_65 = pkFromSkAPI 4032#usize 1952#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem pk_from_sk_87_eq :
    api.pk_from_sk_87 = pkFromSkAPI 4896#usize 2592#usize 8#usize 7#usize params.ML_DSA_87 := rfl

theorem pkFromSkAPI_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.pkLen)
    (sk : Array U8 n) (F : Nat) (o : Option (List UInt8))
    (hs : skConsistentR sp (bytesA sk) F = some o) :
    pkFromSkAPI n N K L (ok ip) sk ⦃ r => r.map bytesA = o ⦄ := by
  unfold pkFromSkAPI
  simp only [Std.bind_tc_ok]
  step*
  have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
  have hls : s.val.length = sp.skLen := by
    have := congrArg List.length hbs
    simp only [bytes_length, bytesA_length] at this
    omega
  have hls1 : s1.val.length = sp.pkLen := by rw [s1_post1]; simp [Array.repeat_val, hN]
  rw [← hbs] at hs
  refine WP.spec_bind (pk_from_sk_spec hp s s1 hls hls1 F o hs) ?_
  rintro ⟨b, s2⟩ ⟨hb, hl2⟩
  cases b with
  | false =>
    have h0 : (ok (none : Option (Array U8 N))) ⦃ r => r.map bytesA = o ⦄ := by
      simp only [WP.spec_ok]
      simp only [pkOut, Bool.false_eq_true, if_false] at hb
      subst hb
      rfl
    exact h0
  | true =>
    have hl3 : s2.val.length = N.val := by
      have : s2.val.length = s1.val.length := hl2
      rw [this, hls1, hN]
    have h1 : (ok (some (to_slice_mut_back s2))) ⦃ r => r.map bytesA = o ⦄ := by
      simp only [WP.spec_ok]
      simp only [pkOut, if_true] at hb
      subst hb
      show some (bytesA _) = some (bytes s2)
      rw [s1_post2, bytesA_from_slice _ _ hl3]
    exact h1

theorem pkFromSkAPI_dspec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.pkLen)
    (sk : Array U8 n) :
    pkFromSkAPI n N K L (ok ip) sk ⦃ r => ∃ F, skConsistentR sp (bytesA sk) F = some (r.map bytesA) ⦄div := by
  unfold pkFromSkAPI
  simp only [Std.bind_tc_ok]
  step*
  rcases s1 with ⟨s1, tmb⟩
  have e1 : s1.val = (Array.repeat N 0#u8).val := to_slice_mut_back
  have e2 : tmb = (Array.repeat N 0#u8).from_slice := s1_post2
  have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
  have hls : s.val.length = sp.skLen := by
    have := congrArg List.length hbs
    simp only [bytes_length, bytesA_length] at this
    omega
  have hls1 : s1.val.length = sp.pkLen := by rw [e1]; simp [Array.repeat_val, hN]
  refine WP.dspec_bind' (pk_from_sk_dspec hp s s1 hls hls1) ?_
  rintro ⟨b, s2⟩ ⟨⟨F, hF⟩, hl2⟩
  rw [hbs] at hF
  cases b with
  | false =>
    have h0 : (ok (none : Option (Array U8 N)))
        ⦃ r => ∃ F, skConsistentR sp (bytesA sk) F = some (r.map bytesA) ⦄div := by
      simp only [WP.dspec_ok]
      refine ⟨F, ?_⟩
      simpa [pkOut] using hF
    exact h0
  | true =>
    have hl3 : s2.val.length = N.val := by
      have : s2.val.length = s1.val.length := hl2
      rw [this, hls1, hN]
    have h1 : (ok (some (tmb s2)))
        ⦃ r => ∃ F, skConsistentR sp (bytesA sk) F = some (r.map bytesA) ⦄div := by
      simp only [WP.dspec_ok]
      refine ⟨F, ?_⟩
      have e : bytesA (tmb s2) = bytes s2 := by
        rw [e2, bytesA_from_slice _ _ hl3]
      simp only [pkOut, if_true] at hF
      simpa [e] using hF
    exact h1

theorem pk_from_sk_44_dspec (sk : Array U8 2560#usize) :
    api.pk_from_sk_44 sk ⦃ r => ∃ F, skConsistentR Spec.ML_DSA_44 (bytesA sk) F = some (r.map bytesA) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [pk_from_sk_44_eq, hip]
  exact pkFromSkAPI_dspec hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.pkLen = 1312 by decide +kernel]; rfl) sk

theorem pk_from_sk_44_total (sk : Array U8 2560#usize) (F : Nat) (o : Option (List UInt8))
    (hs : skConsistentR Spec.ML_DSA_44 (bytesA sk) F = some o) :
    api.pk_from_sk_44 sk ⦃ r => r.map bytesA = o ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [pk_from_sk_44_eq, hip]
  exact pkFromSkAPI_spec hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.pkLen = 1312 by decide +kernel]; rfl) sk F o hs

/-- **`api.pk_from_sk_44` is exactly `skConsistentR Spec.ML_DSA_44`.** It never returns `fail` (never panics); if
`skConsistentR … F = some o` at any fuel `F`, it returns `ok r` with `r.map bytesA = o` (`some pk` iff the key is
consistent, `none` iff it is not); and if it returns `ok r`, then `skConsistentR … F = some (r.map bytesA)` for some
fuel `F`. No premise other than the array type. -/
theorem pk_from_sk_44_exact (sk : Array U8 2560#usize) :
    (∀ e, api.pk_from_sk_44 sk ≠ .fail e) ∧
    (∀ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_44 (bytesA sk) F = some o →
      ∃ r, api.pk_from_sk_44 sk = ok r ∧ r.map bytesA = o) ∧
    (∀ r, api.pk_from_sk_44 sk = ok r → ∃ F, skConsistentR Spec.ML_DSA_44 (bytesA sk) F = some (r.map bytesA)) :=
  ⟨dspec_not_fail (pk_from_sk_44_dspec sk),
    fun F o hs => WP.spec_imp_exists (pk_from_sk_44_total sk F o hs),
    fun r hr => WP.dspec_imp_forall (pk_from_sk_44_dspec sk) r hr⟩

/-- The same in terms of `skConsistent` (`some pk` only for a consistent key): a consistent key at any fuel gives
`ok (some pk')` with `pk'` holding the bytes, and `ok (some pk')` gives a consistent key at some fuel. -/
theorem pk_from_sk_44_consistent (sk : Array U8 2560#usize) :
    (∀ (F : Nat) (pk : List UInt8), skConsistent Spec.ML_DSA_44 (bytesA sk) F = some pk →
      ∃ pk', api.pk_from_sk_44 sk = ok (some pk') ∧ bytesA pk' = pk) ∧
    (∀ pk', api.pk_from_sk_44 sk = ok (some pk') →
      ∃ F, skConsistent Spec.ML_DSA_44 (bytesA sk) F = some (bytesA pk')) := by
  constructor
  · intro F pk h
    rw [skConsistent_eq_some_iff] at h
    obtain ⟨r, hr, hmap⟩ := (pk_from_sk_44_exact sk).2.1 F _ h
    cases r with
    | none => cases hmap
    | some pk' => exact ⟨pk', hr, Option.some.inj hmap⟩
  · intro pk' h
    obtain ⟨F, hF⟩ := (pk_from_sk_44_exact sk).2.2 _ h
    exact ⟨F, (skConsistent_eq_some_iff _ _ _ _).mpr hF⟩

theorem pk_from_sk_65_dspec (sk : Array U8 4032#usize) :
    api.pk_from_sk_65 sk ⦃ r => ∃ F, skConsistentR Spec.ML_DSA_65 (bytesA sk) F = some (r.map bytesA) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [pk_from_sk_65_eq, hip]
  exact pkFromSkAPI_dspec hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.pkLen = 1952 by decide +kernel]; rfl) sk

theorem pk_from_sk_65_total (sk : Array U8 4032#usize) (F : Nat) (o : Option (List UInt8))
    (hs : skConsistentR Spec.ML_DSA_65 (bytesA sk) F = some o) :
    api.pk_from_sk_65 sk ⦃ r => r.map bytesA = o ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [pk_from_sk_65_eq, hip]
  exact pkFromSkAPI_spec hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.pkLen = 1952 by decide +kernel]; rfl) sk F o hs

/-- **`api.pk_from_sk_65` is exactly `skConsistentR Spec.ML_DSA_65`.** It never returns `fail` (never panics); if
`skConsistentR … F = some o` at any fuel `F`, it returns `ok r` with `r.map bytesA = o` (`some pk` iff the key is
consistent, `none` iff it is not); and if it returns `ok r`, then `skConsistentR … F = some (r.map bytesA)` for some
fuel `F`. No premise other than the array type. -/
theorem pk_from_sk_65_exact (sk : Array U8 4032#usize) :
    (∀ e, api.pk_from_sk_65 sk ≠ .fail e) ∧
    (∀ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_65 (bytesA sk) F = some o →
      ∃ r, api.pk_from_sk_65 sk = ok r ∧ r.map bytesA = o) ∧
    (∀ r, api.pk_from_sk_65 sk = ok r → ∃ F, skConsistentR Spec.ML_DSA_65 (bytesA sk) F = some (r.map bytesA)) :=
  ⟨dspec_not_fail (pk_from_sk_65_dspec sk),
    fun F o hs => WP.spec_imp_exists (pk_from_sk_65_total sk F o hs),
    fun r hr => WP.dspec_imp_forall (pk_from_sk_65_dspec sk) r hr⟩

/-- The same in terms of `skConsistent` (`some pk` only for a consistent key): a consistent key at any fuel gives
`ok (some pk')` with `pk'` holding the bytes, and `ok (some pk')` gives a consistent key at some fuel. -/
theorem pk_from_sk_65_consistent (sk : Array U8 4032#usize) :
    (∀ (F : Nat) (pk : List UInt8), skConsistent Spec.ML_DSA_65 (bytesA sk) F = some pk →
      ∃ pk', api.pk_from_sk_65 sk = ok (some pk') ∧ bytesA pk' = pk) ∧
    (∀ pk', api.pk_from_sk_65 sk = ok (some pk') →
      ∃ F, skConsistent Spec.ML_DSA_65 (bytesA sk) F = some (bytesA pk')) := by
  constructor
  · intro F pk h
    rw [skConsistent_eq_some_iff] at h
    obtain ⟨r, hr, hmap⟩ := (pk_from_sk_65_exact sk).2.1 F _ h
    cases r with
    | none => cases hmap
    | some pk' => exact ⟨pk', hr, Option.some.inj hmap⟩
  · intro pk' h
    obtain ⟨F, hF⟩ := (pk_from_sk_65_exact sk).2.2 _ h
    exact ⟨F, (skConsistent_eq_some_iff _ _ _ _).mpr hF⟩

theorem pk_from_sk_87_dspec (sk : Array U8 4896#usize) :
    api.pk_from_sk_87 sk ⦃ r => ∃ F, skConsistentR Spec.ML_DSA_87 (bytesA sk) F = some (r.map bytesA) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [pk_from_sk_87_eq, hip]
  exact pkFromSkAPI_dspec hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.pkLen = 2592 by decide +kernel]; rfl) sk

theorem pk_from_sk_87_total (sk : Array U8 4896#usize) (F : Nat) (o : Option (List UInt8))
    (hs : skConsistentR Spec.ML_DSA_87 (bytesA sk) F = some o) :
    api.pk_from_sk_87 sk ⦃ r => r.map bytesA = o ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [pk_from_sk_87_eq, hip]
  exact pkFromSkAPI_spec hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.pkLen = 2592 by decide +kernel]; rfl) sk F o hs

/-- **`api.pk_from_sk_87` is exactly `skConsistentR Spec.ML_DSA_87`.** It never returns `fail` (never panics); if
`skConsistentR … F = some o` at any fuel `F`, it returns `ok r` with `r.map bytesA = o` (`some pk` iff the key is
consistent, `none` iff it is not); and if it returns `ok r`, then `skConsistentR … F = some (r.map bytesA)` for some
fuel `F`. No premise other than the array type. -/
theorem pk_from_sk_87_exact (sk : Array U8 4896#usize) :
    (∀ e, api.pk_from_sk_87 sk ≠ .fail e) ∧
    (∀ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_87 (bytesA sk) F = some o →
      ∃ r, api.pk_from_sk_87 sk = ok r ∧ r.map bytesA = o) ∧
    (∀ r, api.pk_from_sk_87 sk = ok r → ∃ F, skConsistentR Spec.ML_DSA_87 (bytesA sk) F = some (r.map bytesA)) :=
  ⟨dspec_not_fail (pk_from_sk_87_dspec sk),
    fun F o hs => WP.spec_imp_exists (pk_from_sk_87_total sk F o hs),
    fun r hr => WP.dspec_imp_forall (pk_from_sk_87_dspec sk) r hr⟩

/-- The same in terms of `skConsistent` (`some pk` only for a consistent key): a consistent key at any fuel gives
`ok (some pk')` with `pk'` holding the bytes, and `ok (some pk')` gives a consistent key at some fuel. -/
theorem pk_from_sk_87_consistent (sk : Array U8 4896#usize) :
    (∀ (F : Nat) (pk : List UInt8), skConsistent Spec.ML_DSA_87 (bytesA sk) F = some pk →
      ∃ pk', api.pk_from_sk_87 sk = ok (some pk') ∧ bytesA pk' = pk) ∧
    (∀ pk', api.pk_from_sk_87 sk = ok (some pk') →
      ∃ F, skConsistent Spec.ML_DSA_87 (bytesA sk) F = some (bytesA pk')) := by
  constructor
  · intro F pk h
    rw [skConsistent_eq_some_iff] at h
    obtain ⟨r, hr, hmap⟩ := (pk_from_sk_87_exact sk).2.1 F _ h
    cases r with
    | none => cases hmap
    | some pk' => exact ⟨pk', hr, Option.some.inj hmap⟩
  · intro pk' h
    obtain ⟨F, hF⟩ := (pk_from_sk_87_exact sk).2.2 _ h
    exact ⟨F, (skConsistent_eq_some_iff _ _ _ _).mpr hF⟩

/-! ## Meaning: completeness, soundness, falsifiability -/

/-- **Completeness.** The secret key of every `Spec.KeyGen_internal` result is accepted, at the fuel that
`KeyGen_internal` used for `ExpandA`, and gives back that result's public key. -/
theorem skConsistent_keygen {sp : Spec.Params} (hp : StdParams sp) (F : Spec.Fuel) (ξ pk sk : List UInt8)
    (hk : Spec.KeyGen_internal sp ξ F = some (pk, sk)) : skConsistent sp sk F.rejNTT = some pk := by
  have hwf := skWellFormed_keygen hp F ξ pk sk hk
  obtain ⟨A, s₁, s₂, hA, hS, hpk, hsk⟩ := keygen_some sp F ξ pk sk hk
  have hH : (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128).length = 128 := SHAKE256_length _ _
  generalize H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hH hA hS hpk hsk
  have hd := hp.d_eq
  have h32 : (slice out 0 32).length = 32 := by simp [slice, hH]
  have h32' : (slice out 96 32).length = 32 := by simp [slice, hH]
  obtain ⟨hr1, hr2⟩ := ExpandS_some sp F.rejBounded _ s₁ s₂ hS
  have hb1 : ∀ (i : Nat) (hi : i < sp.ℓ) (j : Nat) (hj : j < 256), ((s₁[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp F.rejBounded _ _ (hr1 i hi)
  have hb2 : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256), ((s₂[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp F.rejBounded _ _ (hr2 i hi)
  have hdec : Spec.skDecode sp sk =
      (slice out 0 32, slice out 96 32,
        H (pkEncode sp (slice out 0 32) (Power2RoundVec sp (tVec sp A s₁ s₂)).1) 64, s₁, s₂,
        (Power2RoundVec sp (tVec sp A s₁ s₂)).2) := by
    rw [hsk]
    apply Corr.skDecode_skEncode sp hd _ _ _ h32 h32' (SHAKE256_length _ _)
    · intro i hi j hj
      have := hb1 i hi j hj
      have := Int.natAbs_eq (s₁[i][j])
      omega
    · intro i hi j hj
      have := hb2 i hi j hj
      have := Int.natAbs_eq (s₂[i][j])
      omega
    · intro i hi j hj
      have := Corr.power2RoundVec_range sp hd (tVec sp A s₁ s₂) i hi j hj
      omega
  rw [skConsistent_eq_some_iff, skConsistentR_some sp sk F.rejNTT _ _ _ s₁ s₂ _ A hwf hdec hA,
    if_pos ⟨rfl, rfl⟩, hpk]

/-- **Soundness.** If `skConsistent` returns `some pk`, then `s₁` and `s₂` are in range and, writing
`(ρ, K, tr, s₁, s₂, t₀) = skDecode sk`, there is an `Â = ExpandA(ρ)` (at fuel `F`) with
`pk = pkEncode ρ t₁` where `(t₁, t₀') = Power2Round(NTT⁻¹(Â ∘ NTT(s₁)) + s₂)`; the stored `t₀` is that `t₀'`, and the
stored `tr` is `H(pk, 64)`. (`K` is unconstrained.) -/
theorem skConsistent_sound {sp : Spec.Params} {sk : List UInt8} {F : Nat} {pk : List UInt8}
    (h : skConsistent sp sk F = some pk) :
    SkWF sp sk ∧ ∃ A, Spec.ExpandA sp F (Spec.skDecode sp sk).1 = some A ∧
      pk = pkEncode sp (Spec.skDecode sp sk).1
        (Power2RoundVec sp (tVec sp A (Spec.skDecode sp sk).2.2.2.1 (Spec.skDecode sp sk).2.2.2.2.1)).1 ∧
      (Power2RoundVec sp (tVec sp A (Spec.skDecode sp sk).2.2.2.1 (Spec.skDecode sp sk).2.2.2.2.1)).2 =
        (Spec.skDecode sp sk).2.2.2.2.2 ∧
      H pk 64 = (Spec.skDecode sp sk).2.2.1 := by
  rw [skConsistent_eq_some_iff] at h
  by_cases hwf : skWellFormed sp sk = true
  · obtain ⟨ρ, Kk, trs, S₁, S₂, T₀, hdd⟩ := skDecode_tuple sp sk
    rcases hE : Spec.ExpandA sp F ρ with _ | A
    · rw [skConsistentR_exhausted sp sk F ρ Kk trs S₁ S₂ T₀ hwf hdd hE] at h
      cases h
    · rw [skConsistentR_some sp sk F ρ Kk trs S₁ S₂ T₀ A hwf hdd hE] at h
      by_cases hc : (Power2RoundVec sp (tVec sp A S₁ S₂)).2 = T₀ ∧
          H (pkEncode sp ρ (Power2RoundVec sp (tVec sp A S₁ S₂)).1) 64 = trs
      · rw [if_pos hc] at h
        have hpk : pkEncode sp ρ (Power2RoundVec sp (tVec sp A S₁ S₂)).1 = pk :=
          Option.some.inj (Option.some.inj h)
        rw [hdd]
        refine ⟨(skWellFormed_eq_true_iff sp sk).mp hwf, A, hE, hpk.symm, hc.1, ?_⟩
        rw [← hpk]
        exact hc.2
      · rw [if_neg hc] at h
        cases h
  · have hnwf : skWellFormed sp sk = false := by simpa using hwf
    rw [skConsistentR_not_wf sp sk F hnwf] at h
    cases h

/-- Falsifiable: a key whose first `s₁` field is out of range (coefficient `−5`) is rejected at every fuel. -/
theorem skConsistent_bad_44 (F : Nat) :
    skConsistent Spec.ML_DSA_44 (List.replicate 128 0 ++ [7] ++ List.replicate 2431 0) F = none := by
  unfold skConsistent
  rw [skConsistentR_not_wf _ _ F skWellFormed_bad_44]
  rfl

end Proofs
