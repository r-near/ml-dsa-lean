import Spec.Sampling
import Proofs.Keccak
import Proofs.Encode

/-!
# ExpandMask (FIPS 204 Algorithm 34): the extracted `expand_mask` equals the spec

`expand_mask L ip ρ κ` loops over the `L` rows. Row `r` absorbs `ρ ‖ IntegerToBytes (κ + r, 2)` into a fresh
SHAKE256, squeezes `32 c` bytes (`c = gamma1_bits = 1 + bitlen (γ₁ - 1)`) into the prefix of a 640-byte buffer,
runs `bit_unpack` and stores `γ₁ - z[i]` (`field.sub`). The spec's `BitUnpack` is exactly `b - (unsigned value)`
with `(a, b) = (γ₁ - 1, γ₁)`.

## Hypotheses

* `Params.Valid ip K L sp` (as everywhere).
* `hγ : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19`. Needed, and satisfied by all three standard parameter sets
  (`ML_DSA_44_gamma1`, ...): the Rust buffer is 640 bytes (`c ≤ 20`), `field.sub γ₁ _` needs `γ₁ < q`, and the
  spec's `BitUnpack` uses the width `bitlen (2 γ₁ - 1)`, which equals `1 + bitlen (γ₁ - 1)` (the width the
  Rust code and the spec's `ExpandMask` use) exactly when `γ₁` is a power of two.
* `hκ : κ + ℓ ≤ 2 ^ 16`: no `u16` overflow of `mu + r` and no wrap in `IntegerToBytes (κ + r, 2)`;
  this is what Sign's `κ` budget guarantees.

## Range

`expand_mask_range`: every coefficient of the spec's `ExpandMask` lies in `[-γ₁ + 1, γ₁]`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## The spec side -/

/-- Row `j` of `ExpandMask`. -/
def maskPoly (sp : Spec.Params) (ρ : List UInt8) (μ j : Nat) : RPoly :=
  BitUnpack (H (ρ ++ IntegerToBytes (μ + j) 2) (32 * (1 + bitlen (sp.γ₁ - 1)))) (sp.γ₁ - 1) sp.γ₁

theorem foldl_set!_range {α : Type} {n : Nat} (U : Nat → α) (init : Vector α n) :
    ∀ m, m ≤ n → ∀ i (hi : i < n),
      ((List.range' 0 m).foldl (fun (y : Vector α n) r => y.set! r (U r)) init)[i] =
        if i < m then U i else init[i] := by
  intro m
  induction m with
  | zero => intro _ i hi; simp
  | succ m ih =>
    intro hm i hi
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add, Nat.one_mul]
    have key : ∀ xs : Vector α n, (xs.set! m (U m))[i] = if m = i then U m else xs[i] := fun xs => by
      rw [set!_eq']; exact Vector.getElem_setIfInBounds hi
    rw [key, ih (by omega) i hi]
    by_cases h : m = i
    · subst h; simp
    · have h' : ¬ i = m := fun e => h e.symm
      by_cases h2 : i < m
      · simp [h, h2, show i < m + 1 by omega]
      · simp [h, h2, show ¬ i < m + 1 by omega]

theorem ExpandMask_get (sp : Spec.Params) (ρ : List UInt8) (μ : Nat) (i : Nat) (hi : i < sp.ℓ) :
    (Spec.ExpandMask sp ρ μ)[i] = maskPoly sp ρ μ i := by
  unfold Spec.ExpandMask
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (foldl_set!_range (fun r => maskPoly sp ρ μ r) _ sp.ℓ le_rfl i hi).trans ?_
  rw [if_pos hi]

theorem gamma1_cases (sp : Spec.Params) (h : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19) :
    (sp.γ₁ = 2 ^ 17 ∧ 1 + bitlen (sp.γ₁ - 1) = 18 ∧ bitlen ((sp.γ₁ - 1) + sp.γ₁) = 18) ∨
    (sp.γ₁ = 2 ^ 19 ∧ 1 + bitlen (sp.γ₁ - 1) = 20 ∧ bitlen ((sp.γ₁ - 1) + sp.γ₁) = 20) := by
  rcases h with h | h
  · left; refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> decide +kernel
  · right; refine ⟨h, ?_, ?_⟩ <;> rw [h] <;> decide +kernel

theorem ML_DSA_44_gamma1 : Spec.ML_DSA_44.γ₁ = 2 ^ 17 ∨ Spec.ML_DSA_44.γ₁ = 2 ^ 19 := Or.inl rfl

theorem IntegerToBytes_two (x : Nat) :
    IntegerToBytes x 2 = [(x % 256).toUInt8, (x / 256 % 256).toUInt8] := by
  unfold IntegerToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range'_succ]

theorem ofNat_mod_u8 (a : Nat) (i : U8) (h : i.val = a % 256) : UInt8.ofNat i.val = (a % 256).toUInt8 := by
  rw [h]

/-- Coefficients of `BitUnpack` with `γ₁ = 2^e`: in `[-γ₁ + 1, γ₁]`. -/
theorem expand_mask_range (sp : Spec.Params) (hγ : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19) (ρ : List UInt8) (μ : Nat)
    (i : Nat) (hi : i < sp.ℓ) (k : Nat) (hk : k < 256) :
    -(sp.γ₁ : Int) + 1 ≤ ((Spec.ExpandMask sp ρ μ)[i])[k] ∧ ((Spec.ExpandMask sp ρ μ)[i])[k] ≤ sp.γ₁ := by
  rw [ExpandMask_get sp ρ μ i hi]
  unfold maskPoly
  rw [BitUnpack_get _ _ _ k hk]
  have hlt := BV_lt (byteBit (H (ρ ++ IntegerToBytes (μ + i) 2) (32 * (1 + bitlen (sp.γ₁ - 1)))))
    (byteBit_le _) (bitlen (sp.γ₁ - 1 + sp.γ₁) * k) (bitlen (sp.γ₁ - 1 + sp.γ₁))
  rcases gamma1_cases sp hγ with ⟨h1, _, h3⟩ | ⟨h1, _, h3⟩
  · rw [h3] at hlt ⊢
    rw [h1] at hlt ⊢
    omega
  · rw [h3] at hlt ⊢
    rw [h1] at hlt ⊢
    omega

/-! ## The Rust side -/

theorem setSlice_zero {α : Type} (v t : List α) (hn : t.length ≤ v.length) :
    v.setSlice! 0 t = t ++ v.drop t.length := by
  simp only [List.setSlice!]
  have e : min t.length (v.length - 0) = t.length := by omega
  rw [e, List.take_of_length_le (le_refl _)]
  simp

/-- `w[k] = b - z[k]` in `Z_q`, canonical, for `k < n`. -/
def SubRow (b : U32) (z w : Array U32 256#usize) (n : Nat) : Prop :=
  ∀ k (hk : k < 256), k < n →
    (w.val[k]'(by rw [len256 w]; exact hk)).val < Spec.q ∧
    (((w.val[k]'(by rw [len256 w]; exact hk)).val : Nat) : Zq) =
      ((b.val : Nat) : Zq) - (((z.val[k]'(by rw [len256 z]; exact hk)).val : Nat) : Zq)

theorem reprInt_of_sub (v : Slice U8) (b : U32) (a : Nat) (c : Usize) (hc : c.val = bitlen (a + b.val))
    (z w : Array U32 256#usize)
    (hz : ∀ i (hi : i < 256), (z.val[i]'(by rw [len256 z]; exact hi)).val =
      BV (byteBit (bytes v)) (c.val * i) c.val)
    (hw : SubRow b z w 256) : ReprInt w (BitUnpack (bytes v) a b.val) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 256 := by simpa [len256 w] using hi
    exact (hw i hi' hi').1
  · apply Vector.ext
    intro k hk
    rw [toZq_get w k hk]
    simp only [RPoly.toZq, Vector.getElem_map]
    rw [(hw k hk hk).2]
    have hzk := hz k hk
    have hbu : (BitUnpack (bytes v) a b.val)[k] = (b.val : Int) -
        ((BV (byteBit (bytes v)) (bitlen (a + b.val) * k) (bitlen (a + b.val)) : Nat) : Int) :=
      BitUnpack_get _ _ _ _ hk
    rw [hbu, ← hc, hzk]
    push_cast
    ring

theorem mask_row_loop {L : Usize} (b : U32) (hb : b.val < Spec.q) (z : Array U32 256#usize)
    (hz : Canonical z) (y0 : Array (Array U32 256#usize) L) (r : Usize) (hr : r.val < L.val) :
    sampling.expand_mask_loop0_loop0 b y0 r z 0#usize ⦃ y =>
      (∀ j, j ≠ r.val → y.val[j]? = y0.val[j]?) ∧
      ∃ row, y.val[r.val]? = some row ∧ SubRow b z row 256 ⦄ := by
  unfold sampling.expand_mask_loop0_loop0
  have hr0 : r.val < y0.val.length := by have := y0.property; omega
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) L × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ j, j ≠ r.val → p.1.val[j]? = y0.val[j]?) ∧
      ∃ row, p.1.val[r.val]? = some row ∧ SubRow b z row p.2.val)
  · rintro ⟨y, i⟩ ⟨h1, h2, row, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simp only [sampling.expand_mask_loop0_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := by scalar_tac
      step*
      · rw [i2_post2]; exact hz _ (List.getElem_mem _)
      · subst a_post3 a1_post
        have hrow : a = row := by
          have h := List.getElem?_eq_getElem (l := y.val) (show r.val < y.val.length from a_post1)
          rw [h3] at h
          rw [a_post2]; exact (Option.some.inj h).symm
        subst hrow
        refine ⟨by omega, ?_, ⟨a.set i i3, ?_, ?_⟩, by omega⟩
        · intro j hj
          rw [Array.set_val_eq, List.getElem?_set_ne (Ne.symm hj)]
          exact h2 j hj
        · rw [Array.set_val_eq]
          exact List.getElem?_set_self a_post1
        · intro k hk hk'
          simp only [Array.set_val_eq, List.getElem_set]
          split
          · rename_i hki
            subst hki
            refine ⟨i3_post1, ?_⟩
            rw [i3_post2, i2_post2]
          · rename_i hki
            exact h4 k hk (by omega)
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨h2, row, h3, by rw [hi'] at h4; exact h4⟩
  · refine ⟨by simp, fun j _ => rfl, y0.val[r.val], List.getElem?_eq_getElem hr0, ?_⟩
    intro k hk hk'
    exact absurd hk' (by simp)

theorem mask_loop {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params} (hp : Params.Valid ip K L sp)
    (hγ : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19) (ρ : Array U8 64#usize) (κ : U16)
    (hκ : κ.val + sp.ℓ ≤ 2 ^ 16) (y0 : Array (Array U32 256#usize) L) (v0 : Array U8 640#usize) :
    sampling.expand_mask_loop0 ip ip.gamma1 ρ κ y0 v0 0#usize ⦃ y =>
      ∀ j (_hj : j < sp.ℓ), ∃ row, y.val[j]? = some row ∧
        ReprInt row (maskPoly sp (bytesA ρ) κ.val j) ⦄ := by
  unfold sampling.expand_mask_loop0
  have hcases := gamma1_cases sp hγ
  have hc : ip.gamma1_bits.val = 18 ∨ ip.gamma1_bits.val = 20 := by
    rw [hp.gamma1_bits]; omega
  have hb : ip.gamma1.val < Spec.q := by
    rw [hp.gamma1]; rcases hγ with h | h <;> rw [h] <;> decide +kernel
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) L × Array U8 640#usize × Usize) => L.val - p.2.2.val)
    (fun p => p.2.2.val ≤ L.val ∧ ∀ j (hj : j < p.2.2.val), ∃ row, p.1.val[j]? = some row ∧
      ReprInt row (maskPoly sp (bytesA ρ) κ.val j))
  · rintro ⟨y, v, r⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [sampling.expand_mask_loop0.body]
    split
    · rename_i hr
      have hr' : r.val < L.val := hr
      have hLℓ : L.val = sp.ℓ := hp.L_eq
      step*
      all_goals try scalar_tac
      -- the bytes absorbed
      have hr16 : r.val < 2 ^ 16 := by omega
      have hi1 : i1.val = r.val := by
        rw [i1_post, UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (by simpa using hr16)
      have hnon : nonce.val = κ.val + r.val := by rw [nonce_post, hi1]
      have hi2 : i2.val = (κ.val + r.val) % 256 := by
        rw [i2_post, UScalar.cast_val_eq, ← hnon]; rfl
      have hi4 : i4.val = (κ.val + r.val) / 256 % 256 := by
        rw [i4_post, UScalar.cast_val_eq]
        show i3.val % 256 = _
        rw [i3_post1, Nat.shiftRight_eq_div_pow, hnon]
      have hbs : bytes s = bytesA ρ := by rw [s_post, bytes_to_slice]
      have hbs1 : bytes s1 = IntegerToBytes (κ.val + r.val) 2 := by
        rw [s1_post, bytes_to_slice, IntegerToBytes_two]
        simp only [bytesA, Array.make, List.map_cons, List.map_nil]
        rw [ofNat_mod_u8 _ i2 hi2, ofNat_mod_u8 _ i4 hi4]
      have hM : ([] ++ bytes s ++ bytes s1 : List UInt8) =
          bytesA ρ ++ IntegerToBytes (κ.val + r.val) 2 := by
        rw [List.nil_append, hbs, hbs1]
      have hs2len : s2.val.length = 32 * (1 + bitlen (sp.γ₁ - 1)) := by
        have h := s2_post2
        simp only [Slice.length] at h
        rw [h, i5_post, hp.gamma1_bits]
      have hs3b : bytes s3 =
          H (bytesA ρ ++ IntegerToBytes (κ.val + r.val) 2) (32 * (1 + bitlen (sp.γ₁ - 1))) := by
        rw [__post2, List.drop_zero, Nat.zero_add, hs2len, hM]; rfl
      have hs3len : s3.val.length = 32 * (1 + bitlen (sp.γ₁ - 1)) := by
        have h := congrArg List.length hs3b
        simp only [bytes, List.length_map] at h
        rw [h]; exact SHAKE256_length _ _
      have hs4 : s4.val = s3.val := by
        have hi5 : i5.val = s3.val.length := by rw [hs3len, i5_post, hp.gamma1_bits]
        have hv : v.val.length = 640 := by simp
        have hle : s3.val.length ≤ v.val.length := by
          rw [hv, hs3len]; rcases hcases with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> omega
        rw [s4_post1]
        show List.slice 0 i5.val (index_mut_back s3).val = _
        rw [s2_post3 s3, setSlice_zero _ _ hle, hi5]
        simp [List.slice]
      have hlen4 : s4.val.length = 32 * ip.gamma1_bits.val := by
        have h := s4_post2
        simp only [Slice.length] at h
        rw [h, i5_post]
      have hbs4 : bytes s4 =
          H (bytesA ρ ++ IntegerToBytes (κ.val + r.val) 2) (32 * (1 + bitlen (sp.γ₁ - 1))) := by
        rw [← hs3b]; simp only [bytes, hs4]
      have hcb : ip.gamma1_bits.val = bitlen ((sp.γ₁ - 1) + ip.gamma1.val) := by
        rw [hp.gamma1, hp.gamma1_bits]
        rcases hcases with ⟨_, h2, h3⟩ | ⟨_, h2, h3⟩ <;> omega
      refine WP.spec_bind (bit_unpack_core (byteBit (bytes s4)) (byteBit_le _) s4 ip.gamma1_bits
        (by omega) hlen4 (bytes_BV s4)) ?_
      intro z hz
      have hzc : Canonical z := by
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        have hi' : i < 256 := by simpa [len256 z] using hi
        rw [hz i hi']
        have := BV_lt (byteBit (bytes s4)) (byteBit_le _) (ip.gamma1_bits.val * i) ip.gamma1_bits.val
        have : (2:Nat) ^ ip.gamma1_bits.val ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h22 : (2:Nat) ^ 22 < Spec.q := by decide +kernel
        omega
      refine WP.spec_bind (mask_row_loop ip.gamma1 hb z hzc y r hr') ?_
      rintro y1 ⟨hy1a, row, hy1r, hrow⟩
      step*
      refine ⟨by omega, ?_, by omega⟩
      intro j hj
      by_cases hjr : j = r.val
      · subst hjr
        refine ⟨row, hy1r, ?_⟩
        have h := reprInt_of_sub s4 ip.gamma1 (sp.γ₁ - 1) ip.gamma1_bits hcb z row hz hrow
        rw [hbs4, hp.gamma1] at h
        exact h
      · obtain ⟨row', hrow', hrep⟩ := h2 j (by omega)
        exact ⟨row', by rw [hy1a j hjr]; exact hrow', hrep⟩
    · rename_i hr
      have hr' : r.val = L.val := by scalar_tac
      have hLℓ : L.val = sp.ℓ := hp.L_eq
      simp only [WP.spec_ok]
      intro j hj
      exact h2 j (by omega)
  · refine ⟨by simp, fun j hj => absurd hj (by simp)⟩

/-- **`expand_mask` is `ExpandMask`** (Algorithm 34). -/
theorem expand_mask_spec {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hγ : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19) (ρ : Array U8 64#usize) (κ : U16)
    (hκ : κ.val + sp.ℓ ≤ 2 ^ 16) :
    sampling.expand_mask L ip ρ κ ⦃ y => ReprIntVec y (Spec.ExpandMask sp (bytesA ρ) κ.val) ⦄ := by
  unfold sampling.expand_mask
  simp only []
  apply WP.spec_mono (mask_loop hp hγ ρ κ hκ _ _)
  intro y hy
  refine ⟨hp.L_eq, fun i hi => ?_⟩
  obtain ⟨row, hrow, hrep⟩ := hy i hi
  have hi' : i < y.val.length := by have h1 : y.val.length = L.val := y.property; have h2 := hp.L_eq; omega
  have e : y.val[i] = row := by
    rw [List.getElem?_eq_getElem hi'] at hrow
    exact Option.some.inj hrow
  rw [e, ExpandMask_get sp _ _ i hi]
  exact hrep

/-- Satisfiability: the preconditions hold for ML-DSA-44 with `κ = 0` (and likewise for the other sets). -/
theorem expand_mask_exists :
    ∃ ip : Impl.params.Params, Params.Valid ip 4#usize 4#usize Spec.ML_DSA_44 ∧
      ∃ y, sampling.expand_mask 4#usize ip (Array.repeat 64#usize 0#u8) 0#u16 = ok y ∧
        ReprIntVec y (Spec.ExpandMask Spec.ML_DSA_44 (bytesA (Array.repeat 64#usize 0#u8)) 0) := by
  obtain ⟨ip, _, hv⟩ := ML_DSA_44_valid
  obtain ⟨y, hy, h⟩ := WP.spec_imp_exists (expand_mask_spec (K := 4#usize) hv ML_DSA_44_gamma1
    (Array.repeat 64#usize 0#u8) 0#u16 (by decide +kernel))
  exact ⟨ip, hv, y, hy, h⟩

end Proofs
