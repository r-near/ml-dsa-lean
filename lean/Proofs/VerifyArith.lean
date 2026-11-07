import Proofs.NTTPub
import Proofs.MatrixVector
import Proofs.EncodeKeys

/-!
# The verify-only arithmetic equals the shared functions it replaces on verify's path

* `mac_row_pub` (one row of `Â ∘ NTT(z) − NTT(c) ∘ NTT(t₁·2^d)`, accumulated in 64 bits and reduced by two Montgomery
  steps) computes the coefficients `∑_l Â[i][l][κ]·ẑ[l][κ] − ĉ[κ]·t̂[κ]` of FIPS 204 Algorithm 8 step 9.
* `vec_norm_lt_pub` decides `‖z‖∞ < bound` for canonical `z`.
* `bit_pack_pub` equals `bit_pack` for values below `2^c` (c = 4, 6).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## The fused multiply-accumulate row -/

theorem QQ_val : verify_arith.QQ ⦃ r => r.val = 8380417 * 8380417 ⦄ := by
  unfold verify_arith.QQ
  simp only [global_simps, lift, bind_tc_ok]
  have hq : (UScalar.cast UScalarTy.U64 8380417#u32).val = 8380417 := by simp
  obtain ⟨z, hz, hv⟩ := mul64_ok (UScalar.cast UScalarTy.U64 8380417#u32) (UScalar.cast UScalarTy.U64 8380417#u32)
    (by rw [hq]; norm_num)
  rw [hz]
  simp only [WP.spec_ok]
  rw [hv, hq]

attribute [step] QQ_val

theorem reprvec_coeff {L : Usize} {ℓ : Nat} {a : Array (Array U32 256#usize) L} {A : Vector Poly ℓ}
    (h : ReprVec a A) (l : Nat) (hl : l < ℓ) (j : Nat) (hj : j < 256) :
    ((((a.val[l]'(by have := a.property; have := h.len; omega)).val[j]'(by rw [len256]; exact hj)).val : Nat) : Zq)
      = (A[l]!)[j]! ∧
    (((a.val[l]'(by have := a.property; have := h.len; omega)).val[j]'(by rw [len256]; exact hj)).val < 8380417) := by
  have hr := h.elt l hl
  refine ⟨?_, canon_get hr.canon _⟩
  rw [hr.coeff j hj, vget! A l hl, vget! _ j hj]

theorem mac_step_nat (s : U64) (X Y : U32) (hX : X.val < 8380417) (hY : Y.val < 8380417)
    (h : s.val + 8380417 * 8380417 < 18446744073709551616) :
    (core.num.U64.wrapping_add s (core.num.U64.wrapping_mul (UScalar.cast UScalarTy.U64 X)
        (UScalar.cast UScalarTy.U64 Y))).val = s.val + X.val * Y.val := by
  have hcX : (UScalar.cast UScalarTy.U64 X).val = X.val := by simp
  have hcY : (UScalar.cast UScalarTy.U64 Y).val = Y.val := by simp
  have hXY : X.val * Y.val ≤ 8380417 * 8380417 := Nat.mul_le_mul (by omega) (by omega)
  have hlt : X.val * Y.val < 2 ^ 64 := lt_of_le_of_lt hXY (by norm_num)
  rw [wrapping_add_val_u64, wrapping_mul_val_u64, hcX, hcY, Nat.mod_eq_of_lt hlt]
  exact Nat.mod_eq_of_lt (by omega)

theorem mac_inner_loop {L : Usize} {ℓ : Nat} (a z : Array (Array U32 256#usize) L)
    (Arow Zv : Vector Poly ℓ) (ha : ReprVec a Arow) (hz : ReprVec z Zv) (j : Usize) (hj : j.val < 256)
    (s0 : U64) (hs0 : s0.val + L.val * (8380417 * 8380417) < 18446744073709551616) :
    verify_arith.mac_row_pub_loop0_loop0 a z j s0 0#usize ⦃ r =>
      r.val ≤ s0.val + L.val * (8380417 * 8380417) ∧
      ((r.val : Nat) : Zq) = (s0.val : Zq) + ∑ l ∈ Finset.range ℓ, (Arow[l]!)[j.val]! * (Zv[l]!)[j.val]! ⦄ := by
  have hL : L.val = ℓ := ha.len
  unfold verify_arith.mac_row_pub_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : U64 × Usize) => L.val - p.2.val)
    (fun p => p.2.val ≤ L.val ∧ p.1.val ≤ s0.val + p.2.val * (8380417 * 8380417) ∧
       ((p.1.val : Nat) : Zq) = (s0.val : Zq) + ∑ l ∈ Finset.range p.2.val, (Arow[l]!)[j.val]! * (Zv[l]!)[j.val]!)
  · rintro ⟨s, l⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [verify_arith.mac_row_pub_loop0_loop0.body]
    split
    · rename_i hl
      have hl' : l.val < L.val := by scalar_tac
      step*
      subst_vars
      have hlℓ : l.val < L.val := hl'
      obtain ⟨hAc, hAq⟩ := reprvec_coeff ha l.val hlℓ j.val hj
      obtain ⟨hZc, hZq⟩ := reprvec_coeff hz l.val hlℓ j.val hj
      have hs1 := mac_step_nat s _ _ hAq hZq (by omega)
      have hXY := Nat.mul_le_mul (le_of_lt hAq) (le_of_lt hZq)
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hs1]; omega
      · rw [hs1, l1_post, Finset.sum_range_succ, Nat.cast_add, h3, Nat.cast_mul, hAc, hZc]; ring
    · rename_i hl
      have hl' : l.val = L.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨by rw [← hl']; exact h2, ?_⟩
      rw [h3, hl', hL]
  · refine ⟨by simp, by simp, by simp⟩

theorem mul_cast_nat (X Y : U32) (hX : X.val < 8380417) (hY : Y.val < 8380417) :
    (core.num.U64.wrapping_mul (UScalar.cast UScalarTy.U64 X) (UScalar.cast UScalarTy.U64 Y)).val =
      X.val * Y.val := by
  have hcX : (UScalar.cast UScalarTy.U64 X).val = X.val := by simp
  have hcY : (UScalar.cast UScalarTy.U64 Y).val = Y.val := by simp
  have hXY : X.val * Y.val ≤ 8380417 * 8380417 := Nat.mul_le_mul (by omega) (by omega)
  have hlt : X.val * Y.val < 2 ^ 64 := lt_of_le_of_lt hXY (by norm_num)
  rw [wrapping_mul_val_u64, hcX, hcY, Nat.mod_eq_of_lt hlt]

theorem r2_mul_nat (p : U32) (hp : p.val < 2 * 8380417) (i6 i7 : U64)
    (h6 : i6 = UScalar.cast UScalarTy.U64 p) (h7 : i7 = core.num.U64.wrapping_mul i6 verify_arith.R2) :
    i7.val = p.val * 2365951 := by
  have hR : verify_arith.R2.val = 2365951 := by unfold verify_arith.R2; rfl
  have hc : (UScalar.cast UScalarTy.U64 p).val = p.val := by simp
  rw [h7, wrapping_mul_val_u64, h6, hc, hR]
  exact Nat.mod_eq_of_lt (by omega)

theorem mac_row_loop {L : Usize} {ℓ : Nat} (a z : Array (Array U32 256#usize) L)
    (Arow Zv : Vector Poly ℓ) (ha : ReprVec a Arow) (hz : ReprVec z Zv)
    (c t : Array U32 256#usize) (C T : Poly) (hc : Repr c C) (ht : Repr t T) (hL : L.val ≤ 255)
    (P : Poly) (hP : ∀ κ, κ < 256 → P[κ]! =
      ∑ l ∈ Finset.range ℓ, (Arow[l]!)[κ]! * (Zv[l]!)[κ]! - C[κ]! * T[κ]!)
    (out0 : Array U32 256#usize) :
    verify_arith.mac_row_pub_loop0 a z c t out0 0#usize ⦃ r => Canonical r ∧ toZq r = P ⦄ := by
  unfold verify_arith.mac_row_pub_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ (∀ k x, k < p.2.val → p.1.val[k]? = some x → x.val < 8380417) ∧
       (∀ k, k < p.2.val → (toZq p.1)[k]! = P[k]!))
  · rintro ⟨out, j⟩ ⟨h1, hq, hk⟩
    dsimp only at h1 hq hk
    simp only [verify_arith.mac_row_pub_loop0.body]
    split
    · rename_i hj
      have hj' : j.val < 256 := by scalar_tac
      step*
      subst i_post2 i2_post2
      have hcq := canon_get hc.canon (show j.val < c.val.length by rw [len256]; exact hj')
      have htq := canon_get ht.canon (show j.val < t.val.length by rw [len256]; exact hj')
      have hcc := hc.coeff j.val hj'
      have htc := ht.coeff j.val hj'
      have hi4 : i4.val = (c.val[j.val]).val * (t.val[j.val]).val := by
        rw [i4_post, i1_post, i3_post]; exact mul_cast_nat _ _ hcq htq
      have hXY := Nat.mul_le_mul hcq.le htq.le
      have hsv : s.val = 8380417 * 8380417 - (c.val[j.val]).val * (t.val[j.val]).val := by
        rw [s_post, wrapping_sub_val_u64, i5_post, hi4]; omega
      step with mac_inner_loop a z Arow Zv ha hz j hj' s (by omega) as ⟨s1, hs1, hs1'⟩
      step*
      · have := r2_mul_nat p p_post1 i6 i7 i6_post i7_post
        omega
      have hi7 := r2_mul_nat p p_post1 i6 i7 i6_post i7_post
      have hmod : i8.val % 8380417 = s1.val % 8380417 :=
        mont2_nat s1.val p.val i8.val p_post2 (by rw [i8_post2, hi7])
      have hq0 : ((8380417 : Nat) : ZMod 8380417) = 0 := ZMod.natCast_self _
      have hscast : ((s.val : Nat) : Zq) = -(C[j.val]! * T[j.val]!) := by
        rw [hsv, Nat.cast_sub hXY, Nat.cast_mul, Nat.cast_mul, hq0, hcc, htc,
          vget! C _ hj', vget! T _ hj']
        ring
      have hfin : ((i9.val : Nat) : Zq) = P[j.val]! := by
        rw [hP j.val hj', i9_post1, hmod, ZMod.natCast_mod, hs1', hscast]
        ring
      refine ⟨by omega, ?_, ?_, by omega⟩
      · intro k x hk' hkx
        rw [a1_post, get?_set _ _ _ _ hj'] at hkx
        by_cases hkj : j.val = k
        · rw [if_pos hkj] at hkx; cases hkx; exact i9_post2
        · rw [if_neg hkj] at hkx; exact hq k x (by omega) hkx
      · intro k hk'
        rw [a1_post, toZq_set _ _ _ hj', Corr.vget!_set! _ _ _ (by omega : k < 256)]
        by_cases hkj : k = j.val
        · rw [if_pos hkj, hkj]; exact hfin
        · rw [if_neg hkj]; exact hk k (by omega)
    · rename_i hj
      have hj' : j.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · intro x hx
        obtain ⟨k, hk'⟩ := List.mem_iff_getElem?.mp hx
        have hkl := (List.getElem?_eq_some_iff.mp hk').1
        rw [len256 out] at hkl
        exact hq k x (by omega) hk'
      · exact Corr.poly_ext _ _ (fun k hk' => hk k (by omega))
  · refine ⟨by simp, by intro k x hk; simp at hk, by intro k hk; simp at hk⟩

theorem mac_row_pub_spec {L : Usize} {ℓ : Nat} (a z : Array (Array U32 256#usize) L)
    (Arow Zv : Vector Poly ℓ) (ha : ReprVec a Arow) (hz : ReprVec z Zv)
    (c t : Array U32 256#usize) (C T : Poly) (hc : Repr c C) (ht : Repr t T) (hL : L.val ≤ 255)
    (P : Poly) (hP : ∀ κ, κ < 256 → P[κ]! =
      ∑ l ∈ Finset.range ℓ, (Arow[l]!)[κ]! * (Zv[l]!)[κ]! - C[κ]! * T[κ]!) :
    verify_arith.mac_row_pub a z c t ⦃ r => Repr r P ⦄ := by
  unfold verify_arith.mac_row_pub
  apply WP.spec_mono (mac_row_loop a z Arow Zv ha hz c t C T hc ht hL P hP _)
  intro r hr
  exact ⟨hr.1, hr.2⟩

/-- Row `i` of `Â ∘ ẑ − ĉ ∘ t̂`: the fused row computes `(Â ∘ ẑ)[i] − ĉ ∘ t̂` (Algorithm 8, step 9, before NTT⁻¹). -/
theorem mac_row_pub_spec_mv {L : Usize} {k ℓ : Nat} (ar : Array (Array U32 256#usize) L)
    (M : Vector (Vector Poly ℓ) k) (i : Nat) (hi : i < k) (hrow : ReprVec ar M[i])
    (z : Array (Array U32 256#usize) L) (V : Vector Poly ℓ) (hz : ReprVec z V)
    (c t : Array U32 256#usize) (C T : Poly) (hc : Repr c C) (ht : Repr t T) (hL : L.val ≤ 255) :
    verify_arith.mac_row_pub ar z c t ⦃ r =>
      Repr r ((MatrixVectorNTT M V)[i]! - MultiplyNTT C T) ⦄ := by
  apply mac_row_pub_spec ar z M[i] V hrow hz c t C T hc ht hL
  intro κ hκ
  rw [Corr.get!_sub, Corr.MVN2! M V hi hκ, Corr.MultiplyNTT_get _ _ κ hκ, vget! M i hi]

/-! ## The norm check -/

/-- `x < b` or `x > q - b`: the canonical `x` is within `b` of `0` modulo `q` (strictly). -/
def NGood (b x : Nat) : Prop := x < b ∨ 8380417 - b < x

theorem nat_lor_eq_zero (a b : Nat) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · apply Nat.eq_of_testBit_eq; intro i
      have := congrArg (fun n => Nat.testBit n i) h
      simp [Nat.testBit_or] at this ⊢
      exact this.1
    · apply Nat.eq_of_testBit_eq; intro i
      have := congrArg (fun n => Nat.testBit n i) h
      simp [Nat.testBit_or] at this ⊢
      exact this.2
  · rintro ⟨rfl, rfl⟩; simp

theorem bit_good (x bound i1 : U32) (hi1 : i1.val = 8380417 - bound.val) (_hb : bound.val < 8380417) :
    (decide ¬(decide (x < bound) || decide (x > i1)) = true).toNat = 0 ↔ NGood bound.val x.val := by
  have h1 : (x < bound) ↔ x.val < bound.val := by
    constructor <;> intro h <;> scalar_tac
  have h2 : (x > i1) ↔ i1.val < x.val := by
    constructor <;> intro h <;> scalar_tac
  unfold NGood
  by_cases c1 : x < bound
  · have := h1.mp c1
    simp [c1, this]
  · by_cases c2 : x > i1
    · have := h2.mp c2
      simp [c1, c2]
      omega
    · have a1 : ¬ x.val < bound.val := fun h => c1 (h1.mpr h)
      have a2 : ¬ i1.val < x.val := fun h => c2 (h2.mpr h)
      simp [c1, c2, a1]
      omega

theorem norm_row_loop {N : Usize} (w : Array (Array U32 256#usize) N) (bound : U32)
    (hbq : bound.val < 8380417) (i : Usize) (row : Array U32 256#usize) (hrow : w.val[i.val]? = some row)
    (bad0 : U32) (j0 : Usize) (hj0 : j0.val ≤ 256) :
    rounding.vec_norm_lt_pub_loop0_loop0 w bound bad0 i j0 ⦃ r =>
      (r.val = 0 ↔ bad0.val = 0 ∧ ∀ (k : Nat) (hk : k < 256), j0.val ≤ k →
        NGood bound.val (row.val[k]'(by rw [len256]; exact hk)).val) ⦄ := by
  obtain ⟨hi, hrowe⟩ := List.getElem?_eq_some_iff.mp hrow
  subst hrowe
  unfold rounding.vec_norm_lt_pub_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : U32 × Usize) => 256 - p.2.val)
    (fun p => j0.val ≤ p.2.val ∧ p.2.val ≤ 256 ∧
      (p.1.val = 0 ↔ bad0.val = 0 ∧ ∀ (k : Nat) (hk : k < 256), j0.val ≤ k → k < p.2.val →
        NGood bound.val ((w.val[i.val]'hi).val[k]'(by rw [len256]; exact hk)).val))
  · rintro ⟨bad, j⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [rounding.vec_norm_lt_pub_loop0_loop0.body]
    split
    · rename_i hj
      have hj' : j.val < 256 := by scalar_tac
      step*
      · rw [Q_eq]; simp; omega
      subst_vars
      have hi1 : i1.val = 8380417 - bound.val := by rw [i1_post1, Q_eq]; simp
      have hor : bad1.val = 0 ↔ bad.val = 0 ∧ i2.val = 0 := by
        rw [bad1_post1, UScalar.val_or, nat_lor_eq_zero]
      rw [i2_post, bit_good _ bound i1 hi1 hbq] at hor
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [hor, h3]
      constructor
      · rintro ⟨⟨hb0, hg⟩, hgj⟩
        refine ⟨hb0, fun k hk hjk hlt => ?_⟩
        by_cases hkj : k = j.val
        · subst hkj; exact hgj
        · exact hg k hk hjk (by omega)
      · rintro ⟨hb0, hg⟩
        exact ⟨⟨hb0, fun k hk hjk hlt => hg k hk hjk (by omega)⟩, hg j.val hj' h1 (by omega)⟩
    · rename_i hj
      have hj' : j.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      rw [h3]
      constructor
      · rintro ⟨hb, hg⟩
        exact ⟨hb, fun k hk hjk => hg k hk hjk (by omega)⟩
      · rintro ⟨hb, hg⟩
        exact ⟨hb, fun k hk hjk _ => hg k hk hjk⟩
  · refine ⟨le_refl _, hj0, ?_⟩
    constructor
    · intro h; exact ⟨h, fun k hk hjk hlt => by simp at hlt; omega⟩
    · intro h; exact h.1

theorem norm_loop {N : Usize} (w : Array (Array U32 256#usize) N) (bound : U32)
    (hbq : bound.val < 8380417) (bad0 : U32) (i0 : Usize) (hi0 : i0.val ≤ N.val) :
    rounding.vec_norm_lt_pub_loop0 w bound bad0 i0 ⦃ r =>
      (r.val = 0 ↔ bad0.val = 0 ∧ ∀ (r : Nat) (hr : r < w.val.length), i0.val ≤ r → ∀ (k : Nat) (hk : k < 256),
        NGood bound.val ((w.val[r]'hr).val[k]'(by rw [len256]; exact hk)).val) ⦄ := by
  have hlen : w.val.length = N.val := w.property
  unfold rounding.vec_norm_lt_pub_loop0
  apply loop.spec_decr_nat
    (fun (p : U32 × Usize) => N.val - p.2.val)
    (fun p => i0.val ≤ p.2.val ∧ p.2.val ≤ N.val ∧
      (p.1.val = 0 ↔ bad0.val = 0 ∧ ∀ (r : Nat) (hr : r < w.val.length), i0.val ≤ r → r < p.2.val →
        ∀ (k : Nat) (hk : k < 256), NGood bound.val ((w.val[r]'hr).val[k]'(by rw [len256]; exact hk)).val))
  · rintro ⟨bad, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [rounding.vec_norm_lt_pub_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < N.val := hi
      have hrow := norm_row_loop w bound hbq i (w.val[i.val]'(by omega)) (List.getElem?_eq_getElem _) bad 0#usize
        (by simp)
      step with hrow
      step*
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [bad1_post]
      rw [h3]
      constructor
      · rintro ⟨⟨hb0, hg⟩, hgi⟩
        refine ⟨hb0, fun r hr h0 hlt k hk => ?_⟩
        by_cases hri : r = i.val
        · subst hri; exact hgi k hk (Nat.zero_le _)
        · exact hg r hr h0 (by omega) k hk
      · rintro ⟨hb0, hg⟩
        exact ⟨⟨hb0, fun r hr h0 hlt k hk => hg r hr h0 (by omega) k hk⟩,
          fun k hk _ => hg i.val (by omega) h1 (by omega) k hk⟩
    · rename_i hi
      have hi' : i.val = N.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [h3]
      constructor
      · rintro ⟨hb, hg⟩
        exact ⟨hb, fun r hr hr0 k hk => hg r hr hr0 (by omega) k hk⟩
      · rintro ⟨hb, hg⟩
        exact ⟨hb, fun r hr hr0 _ k hk => hg r hr hr0 k hk⟩
  · refine ⟨le_refl _, hi0, ?_⟩
    constructor
    · intro h; exact ⟨h, fun r hr h0 hlt => by simp at hlt; omega⟩
    · intro h; exact h.1

/-- A residue `x` (storing `c mod q`, `|c| ≤ (q−1)/2`) passes the test `x < bound ∨ q − bound < x` iff `|c| < bound`. -/
theorem good_iff (x : Nat) (c : Int) (bound : Nat) (hx : (x : Int) = c % 8380417) (hc : c.natAbs ≤ 4190208)
    (hb0 : 0 < bound) (hbq : bound < 8380417) : NGood bound x ↔ c.natAbs < bound := by
  unfold NGood
  omega

theorem vec_norm_lt_pub_spec {N : Usize} (w : Array (Array U32 256#usize) N) {n : Nat}
    (v : Vector RPoly n) (hw : ReprIntVec w v) (hb : ‖v‖∞ ≤ 4190208) (bound : U32)
    (hb0 : 0 < bound.val) (hbq : bound.val < 8380417) :
    rounding.vec_norm_lt_pub w bound ⦃ r => r = decide (‖v‖∞ < bound.val) ⦄ := by
  have hbi := (infNorm_le_iff v 4190208).1 hb
  have hlen : w.val.length = N.val := w.property
  have key : ‖v‖∞ < bound.val ↔ ∀ (r : Nat) (hr : r < w.val.length) (k : Nat) (hk : k < 256),
      NGood bound.val ((w.val[r]'hr).val[k]'(by rw [len256]; exact hk)).val := by
    have e : ‖v‖∞ < bound.val ↔ ‖v‖∞ ≤ bound.val - 1 := by omega
    rw [e, infNorm_le_iff]
    constructor
    · intro h r hr k hk
      have hrn : r < n := by have := hw.len; omega
      have h1 := (infNorm_le_iff v[r] (bound.val - 1)).1 (h r hrn) k hk
      have h2 := (infNorm_le_iff v[r] 4190208).1 (hbi r hrn) k hk
      have hc := (hw.elt r hrn).coeff k hk
      rw [infNorm_int] at h1 h2
      simp only [Spec.q] at hc
      exact (good_iff _ _ _ hc h2 hb0 hbq).2 (by omega)
    · intro h r hrn
      rw [infNorm_le_iff]
      intro k hk
      have h2 := (infNorm_le_iff v[r] 4190208).1 (hbi r hrn) k hk
      have hc := (hw.elt r hrn).coeff k hk
      rw [infNorm_int] at h2 ⊢
      simp only [Spec.q] at hc
      have := (good_iff _ _ _ hc h2 hb0 hbq).1 (h r (by have := hw.len; omega) k hk)
      omega
  unfold rounding.vec_norm_lt_pub
  have h := norm_loop w bound hbq 0#u32 0#usize (by simp)
  step with h
  rw [decide_eq_decide, key]
  have hz : bad = 0#u32 ↔ bad.val = 0 := by
    constructor
    · intro e; subst e; rfl
    · intro e; exact UScalar.eq_of_val_eq (by simpa using e)
  rw [hz, bad_post]
  constructor
  · intro hb; exact fun r hr k hk => (hb.2 r hr (Nat.zero_le _) k hk)
  · intro hg; exact ⟨trivial, fun r hr _ k hk => hg r hr k hk⟩

/-! ## `bit_pack_pub` -/

theorem pack4_bytes (f : Nat → Nat) (_hf : ∀ t, f t ≤ 1) (g w0 w1 : Nat) (h0 : w0 = BV f (8 * g) 4)
    (h1 : w1 = BV f (8 * g + 4) 4) : w0 + w1 * 16 = BV f (8 * g) 8 := by
  have := BV_add f (8 * g) 4 4
  norm_num at this
  omega

theorem pack4_step (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (g : Nat) (X0 X1 i4 i5 : U32) (i6 : U8)
    (hX0 : X0.val = BV f (8 * g) 4) (hX1 : X1.val = BV f (8 * g + 4) 4)
    (h4 : i4.val = X1.val <<< 4 % U32.size) (h5 : i5.val = (X0 ||| i4).val)
    (h6 : i6 = UScalar.cast UScalarTy.U8 i5) : i6.val = BV f (8 * g) 8 := by
  have l0 := BV_lt f hf (8 * g) 4
  have l1 := BV_lt f hf (8 * g + 4) 4
  have l8 := BV_lt f hf (8 * g) 8
  have hsz : U32.size = 4294967296 := by simp [U32.size, U32.numBits]
  have hi4 : i4.val = X1.val * 2 ^ 4 := by
    rw [h4, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    rw [hsz]; omega
  have hi5 : i5.val = X0.val + X1.val * 2 ^ 4 := by
    rw [h5, UScalar.val_or, hi4, or_shift _ _ _ (by omega)]
  have hb := pack4_bytes f hf g X0.val X1.val hX0 hX1
  have hb' : X0.val + X1.val * 2 ^ 4 = BV f (8 * g) 8 := by omega
  rw [h6, UScalar.cast_val_eq, hi5, hb']
  (try simp); omega

theorem pack4_loop (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (w : Array U32 256#usize)
    (hw : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val = BV f (4 * i) 4)
    (out : Slice U8) (hL : out.val.length = 128) :
    encode.bit_pack_pub_loop0 w out 0#usize ⦃ out' => out'.val.length = 128 ∧
      ∀ k (hk : k < out'.val.length), (out'.val[k]).val = BV f (8 * k) 8 ⦄ := by
  unfold encode.bit_pack_pub_loop0
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => 128 - p.2.val)
    (fun p => p.1.val.length = 128 ∧ p.2.val ≤ 128 ∧
      ∀ k (hk : k < p.1.val.length), k < p.2.val → (p.1.val[k]).val = BV f (8 * k) 8)
  · rintro ⟨o, g⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.bit_pack_pub_loop0.body]
    split
    · rename_i hg
      have hg' : g.val < 128 := by scalar_tac
      step*
      have hi2 : i2.val = 2 * g.val + 1 := by omega
      have a0 : ((w.val[i.val]'(by rw [len256 w]; omega)).val) = BV f (8 * g.val) 4 := by
        rw [hw i.val (by omega), show 4 * i.val = 8 * g.val by omega]
      have a1 : ((w.val[i2.val]'(by rw [len256 w]; omega)).val) = BV f (8 * g.val + 4) 4 := by
        rw [hw i2.val (by omega), show 4 * i2.val = 8 * g.val + 4 by omega]
      have hi6 := pack4_step f hf g.val _ _ _ _ _ (by rw [i1_post2]; exact a0) (by rw [i3_post2]; exact a1)
        i4_post1 i5_post1 i6_post
      subst s_post2
      refine ⟨by simp [h1], by omega, ?_, by omega⟩
      intro k hk hlt
      simp only [Slice.set_val_eq, List.getElem_set]
      split
      · rename_i hko
        subst hko
        exact hi6
      · rename_i hko
        exact h3 k (by simpa [h1] using hk) (by omega)
    · rename_i hg
      have hg' : g.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨h1, fun k hk => h3 k hk (by omega)⟩
  · exact ⟨hL, by simp, fun k hk h => by simp at h⟩

theorem BV_cut (f : Nat → Nat) (s a b c s' : Nat) (hc : a + b = c) (hs : s + a = s') :
    BV f s c = BV f s a + 2 ^ a * BV f s' b := by
  subst hc hs; exact BV_add f s a b

theorem u32_size : U32.size = 4294967296 := by simp [U32.size, U32.numBits]

/-- The first byte of a group of four 6-bit values. -/
theorem pack6_b0 (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (g : Nat) (X0 X1 i4 i5 : U32) (i7 : U8)
    (hX0 : X0.val = BV f (24 * g) 6) (hX1 : X1.val = BV f (24 * g + 6) 6)
    (h4 : i4.val = X1.val <<< 6 % U32.size) (h5 : i5.val = (X0 ||| i4).val)
    (h7 : i7 = UScalar.cast UScalarTy.U8 i5) : i7.val = BV f (24 * g) 8 := by
  have l0 := BV_lt f hf (24 * g) 6
  have l1 := BV_lt f hf (24 * g + 6) 6
  have l8 := BV_lt f hf (24 * g) 8
  have s1 := BV_lt f hf (24 * g + 6) 2
  have a1 := BV_add f (24 * g) 6 2
  have a2 := BV_add f (24 * g + 6) 2 4
  norm_num at a1 a2
  have hi4 : i4.val = X1.val * 2 ^ 6 := by
    rw [h4, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    rw [u32_size]; omega
  have hi5 : i5.val = X0.val + X1.val * 2 ^ 6 := by
    rw [h5, UScalar.val_or, hi4, or_shift _ _ _ (by omega)]
  rw [h7, UScalar.cast_val_eq, hi5]
  (try simp); omega

/-- The second byte. -/
theorem pack6_b1 (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (g : Nat) (X1 X2 i8 i9 i10 : U32) (i12 : U8)
    (hX1 : X1.val = BV f (24 * g + 6) 6) (hX2 : X2.val = BV f (24 * g + 12) 6)
    (h8 : i8.val = X1.val >>> 2) (h9 : i9.val = X2.val <<< 4 % U32.size)
    (h10 : i10.val = (i8 ||| i9).val)
    (h12 : i12 = UScalar.cast UScalarTy.U8 i10) : i12.val = BV f (24 * g + 8) 8 := by
  have l1 := BV_lt f hf (24 * g + 6) 6
  have l2 := BV_lt f hf (24 * g + 12) 6
  have l8 := BV_lt f hf (24 * g + 8) 8
  have s2 := BV_lt f hf (24 * g + 6) 2
  have t4 := BV_lt f hf (24 * g + 8) 4
  have t5 := BV_lt f hf (24 * g + 12) 4
  have a1 := BV_cut f (24 * g + 6) 2 4 6 (24 * g + 8) rfl (by omega)
  have a2 := BV_cut f (24 * g + 8) 4 4 8 (24 * g + 12) rfl (by omega)
  have a3 := BV_cut f (24 * g + 12) 4 2 6 (24 * g + 16) rfl (by omega)
  have hi8 : i8.val = X1.val / 2 ^ 2 := by rw [h8, Nat.shiftRight_eq_div_pow]
  have hi9 : i9.val = X2.val * 2 ^ 4 := by
    rw [h9, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    rw [u32_size]; omega
  have hi10 : i10.val = i8.val + X2.val * 2 ^ 4 := by
    rw [h10, UScalar.val_or, hi9, or_shift _ _ _ (by omega)]
  rw [h12, UScalar.cast_val_eq, hi10, hi8]
  (try simp); omega

/-- The third byte. -/
theorem pack6_b2 (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (g : Nat) (X2 X3 i13 i14 i15 : U32) (i17 : U8)
    (hX2 : X2.val = BV f (24 * g + 12) 6) (hX3 : X3.val = BV f (24 * g + 18) 6)
    (h13 : i13.val = X2.val >>> 4) (h14 : i14.val = X3.val <<< 2 % U32.size)
    (h15 : i15.val = (i13 ||| i14).val)
    (h17 : i17 = UScalar.cast UScalarTy.U8 i15) : i17.val = BV f (24 * g + 16) 8 := by
  have l2 := BV_lt f hf (24 * g + 12) 6
  have l3 := BV_lt f hf (24 * g + 18) 6
  have l8 := BV_lt f hf (24 * g + 16) 8
  have s2 := BV_lt f hf (24 * g + 16) 2
  have t5 := BV_lt f hf (24 * g + 12) 4
  have a3 := BV_cut f (24 * g + 12) 4 2 6 (24 * g + 16) rfl (by omega)
  have a4 := BV_cut f (24 * g + 16) 2 6 8 (24 * g + 18) rfl (by omega)
  have hi13 : i13.val = X2.val / 2 ^ 4 := by rw [h13, Nat.shiftRight_eq_div_pow]
  have hi14 : i14.val = X3.val * 2 ^ 2 := by
    rw [h14, Nat.shiftLeft_eq]
    apply Nat.mod_eq_of_lt
    rw [u32_size]; omega
  have hi15 : i15.val = i13.val + X3.val * 2 ^ 2 := by
    rw [h15, UScalar.val_or, hi14, or_shift _ _ _ (by omega)]
  rw [h17, UScalar.cast_val_eq, hi15, hi13]
  (try simp); omega

theorem pack6_loop (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (w : Array U32 256#usize)
    (hw : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val = BV f (6 * i) 6)
    (out : Slice U8) (hL : out.val.length = 192) :
    encode.bit_pack_pub_loop1 w out 0#usize ⦃ out' => out'.val.length = 192 ∧
      ∀ k (hk : k < out'.val.length), (out'.val[k]).val = BV f (8 * k) 8 ⦄ := by
  unfold encode.bit_pack_pub_loop1
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => 64 - p.2.val)
    (fun p => p.1.val.length = 192 ∧ p.2.val ≤ 64 ∧
      ∀ k (hk : k < p.1.val.length), k < 3 * p.2.val → (p.1.val[k]).val = BV f (8 * k) 8)
  · rintro ⟨o, g⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.bit_pack_pub_loop1.body]
    split
    · rename_i hg
      have hg' : g.val < 64 := by scalar_tac
      step*
      have hwi : ∀ (j : Nat) (hj : j < 256) (s : Nat), 6 * j = s →
          (w.val[j]'(by rw [len256 w]; exact hj)).val = BV f s 6 := fun j hj s e => by rw [hw j hj, e]
      have hb0 := pack6_b0 f hf g.val _ _ _ _ _ (by rw [w0_post2]; exact hwi i.val (by omega) (24 * g.val) (by omega))
        (by rw [w1_post2]; exact hwi i1.val (by omega) (24 * g.val + 6) (by omega)) i4_post1 i5_post1 i7_post
      have hb1 := pack6_b1 f hf g.val _ _ _ _ _ _
        (by rw [w1_post2]; exact hwi i1.val (by omega) (24 * g.val + 6) (by omega))
        (by rw [w2_post2]; exact hwi i2.val (by omega) (24 * g.val + 12) (by omega))
        i8_post1 i9_post1 i10_post1 i12_post
      have hb2 := pack6_b2 f hf g.val _ _ _ _ _ _
        (by rw [w2_post2]; exact hwi i2.val (by omega) (24 * g.val + 12) (by omega))
        (by rw [w3_post2]; exact hwi i3.val (by omega) (24 * g.val + 18) (by omega))
        i13_post1 i14_post1 i15_post1 i17_post
      have e11 : i11.val = 3 * g.val + 1 := by omega
      have e16 : i16.val = 3 * g.val + 2 := by omega
      subst out1_post2 out2_post2 s_post2
      refine ⟨by simp [h1], by omega, ?_, by omega⟩
      intro k hk hlt
      simp only [Slice.set_val_eq, List.getElem_set]
      split
      · rename_i hko
        subst hko
        rw [e16, show 8 * (3 * g.val + 2) = 24 * g.val + 16 by ring]
        exact hb2
      · split
        · rename_i hko
          subst hko
          rw [e11, show 8 * (3 * g.val + 1) = 24 * g.val + 8 by ring]
          exact hb1
        · split
          · rename_i hko
            subst hko
            rw [i6_post, show 8 * (3 * g.val) = 24 * g.val by ring]
            exact hb0
          · rename_i hk1 hk2 hk3
            exact h3 k (by simpa [h1] using hk) (by omega)
    · rename_i hg
      have hg' : g.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨h1, fun k hk => h3 k hk (by omega)⟩
  · exact ⟨hL, by simp, fun k hk h => by simp at h⟩

/-- `&mut s[..e]`: the sub-slice is `take e`, and writing a sub-slice of the same length back gives `t ++ drop e`. -/
theorem slice_to_mut_spec {T : Type} (s : Slice T) (r : core.ops.range.RangeTo Usize)
    (h : r.end.val ≤ s.val.length) :
    core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice T) s r ⦃ p =>
      p.1.val = s.val.take r.end.val ∧
      ∀ t : Slice T, t.val.length = r.end.val → (p.2 t).val = t.val ++ s.val.drop r.end.val ⦄ := by
  simp only [core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice.index_mut]
  split
  · simp only [WP.spec_ok]
    refine ⟨by simp, fun t ht => ?_⟩
    simp only [List.setSlice!]
    have e : min t.val.length (s.val.length - 0) = t.val.length := by omega
    rw [e]
    simp [ht]
  · rename_i h'
    exfalso; apply h'
    simpa [Slice.length] using h

/-- `bit_pack_pub` on packed windows `w[i] = BV f (c·i) c` (the same hypotheses as `bit_pack_core`) gives the same
bytes `BV f (8k) 8`; for `c` other than 4 and 6 it is `bit_pack`. -/
theorem bit_pack_pub_core (f : Nat → Nat) (hf : ∀ t, f t ≤ 1) (w : Array U32 256#usize) (c : Usize)
    (hc : c.val ≤ 32) (out : Slice U8) (hL : out.val.length = 32 * c.val)
    (hw : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val = BV f (c.val * i) c.val) :
    encode.bit_pack_pub w c out ⦃ out' => out'.val.length = 32 * c.val ∧
      ∀ k (hk : k < out'.val.length), (out'.val[k]).val = BV f (8 * k) 8 ⦄ := by
  unfold encode.bit_pack_pub
  split
  · rename_i h4
    have hc4 : c.val = 4 := by rw [h4]; rfl
    rw [hc4] at hL hw
    refine WP.spec_bind (slice_to_mut_spec out { «end» := 128#usize } (by simp; omega)) ?_
    rintro ⟨s1, back⟩ ⟨hs1, hback⟩
    dsimp only at hs1 hback
    have hl1 : s1.val.length = 128 := by rw [hs1]; simp; omega
    refine WP.spec_bind (pack4_loop f hf w hw s1 hl1) ?_
    rintro out2 ⟨hl2, hk2⟩
    have hb : (back out2).val = out2.val := by
      rw [hback out2 (by simpa using hl2)]
      have hd : out.val.drop (128#usize).val = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [hd, List.append_nil]
    refine (WP.spec_ok _).2 ?_
    refine ⟨by rw [hb, hl2, hc4], fun k hk => ?_⟩
    have hk' : k < out2.val.length := by rw [hb] at hk; exact hk
    rw [List.getElem_of_eq hb hk]
    exact hk2 k hk'
  · split
    · rename_i h6
      have hc6 : c.val = 6 := by rw [h6]; rfl
      rw [hc6] at hL hw
      refine WP.spec_bind (slice_to_mut_spec out { «end» := 192#usize } (by simp; omega)) ?_
      rintro ⟨s1, back⟩ ⟨hs1, hback⟩
      dsimp only at hs1 hback
      have hl1 : s1.val.length = 192 := by rw [hs1]; simp; omega
      refine WP.spec_bind (pack6_loop f hf w hw s1 hl1) ?_
      rintro out2 ⟨hl2, hk2⟩
      have hb : (back out2).val = out2.val := by
        rw [hback out2 (by simpa using hl2)]
        have hd : out.val.drop (192#usize).val = [] := List.drop_eq_nil_of_le (by simp; omega)
        rw [hd, List.append_nil]
      refine (WP.spec_ok _).2 ?_
      refine ⟨by rw [hb, hl2, hc6], fun k hk => ?_⟩
      have hk' : k < out2.val.length := by rw [hb] at hk; exact hk
      rw [List.getElem_of_eq hb hk]
      exact hk2 k hk'
    · exact bit_pack_core f hf w c hc out hL hw

/-- **`bit_pack_pub` is `SimpleBitPack`.** `out` has `32·c` bytes, `c = bitlen b ≤ 32`, and the 256 coefficients
`w[i]` are the (nonnegative) integers `v[i]`, each below `2^c`. -/
theorem bit_pack_pub_spec (w : Array U32 256#usize) (c : Usize) (out : Slice U8) (v : RPoly) (b : Nat)
    (hc : c.val = bitlen b) (hc32 : c.val ≤ 32) (hL : out.val.length = 32 * c.val)
    (hwv : ∀ i (hi : i < 256), ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) = v[i])
    (hlt : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val < 2 ^ c.val) :
    encode.bit_pack_pub w c out ⦃ out' => bytes out' = Spec.SimpleBitPack v b ⦄ := by
  obtain ⟨g, hg, hwin, hSBP⟩ := SimpleBitPack_model v b
  have hcore := bit_pack_pub_core g hg w c hc32 out hL (fun i hi => by
    have h := hwin i hi
    rw [← hc, v_getElem!_eq v i hi] at h
    rw [h, ← hwv i hi]
    simp only [Int.toNat_natCast]
    exact (Nat.mod_eq_of_lt (hlt i hi)).symm)
  apply WP.spec_mono hcore
  rintro out' ⟨hlen, hk⟩
  rw [hSBP, ← hc]
  exact bytes_eq_map out' (fun k => BV g (8 * k) 8) _ hlen hk

/-- **`bit_pack_pub` on a `ReprInt` polynomial with coefficients in `[0, b]`** (the shape used by `w1_encode` and
`pk_encode`): the output is `SimpleBitPack v b`. -/
theorem bit_pack_pub_spec_repr (w : Array U32 256#usize) (v : RPoly) (hw : ReprInt w v) (b : Nat)
    (hb : b < Spec.q) (hv : ∀ j : Nat, ∀ hj : j < 256, 0 ≤ v[j]'hj ∧ v[j]'hj ≤ (b : Int))
    (c : Usize) (hc : c.val = bitlen b) (out : Slice U8) (hL : out.val.length = 32 * c.val) :
    encode.bit_pack_pub w c out ⦃ out' => bytes out' = Spec.SimpleBitPack v b ⦄ := by
  have hc23 := bitlen_lt_q hb
  have hcoef : ∀ i (hi : i < 256), ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) = v[i] := by
    intro i hi
    rw [hw.coeff i hi]
    exact Int.emod_eq_of_lt (hv i hi).1 (by have := (hv i hi).2; have hqv : Spec.q = 8380417 := rfl; rw [hqv]; omega)
  refine bit_pack_pub_spec w c out v b hc (by omega) hL hcoef (fun i hi => ?_)
  have hle : ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) ≤ b := by
    rw [hcoef i hi]; exact (hv i hi).2
  rw [hc]
  exact lt_pow_of_bitlen (by exact_mod_cast hle)


/-- `w1_encode_pub_loop` on a buffer that may be longer than the encoding: the first `k·n` bytes are the
encoding (`EncodeKeys.w1_encode_loop_spec` needs the buffer to have exactly `k·n` bytes). -/
theorem w1_encode_pub_loop_spec_long {K : Usize} (c n : Usize) (hn : n.val = 32 * c.val) (b : Nat) (hb : b < Spec.q)
    (hc : c.val = bitlen b) (k : Nat) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256, 0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (b : Int))
    (out : Slice U8) (hL : k * n.val ≤ out.val.length) (i1 : Usize) (hi1 : i1.val ≤ k)
    (hinv : (bytes out).take (i1.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) i1.val) :
    encode.w1_encode_pub_loop c w1 out n i1 ⦃ out' =>
      (bytes out').take (k * n.val) = flat (fun t => SimpleBitPack v[t]! b) k ∧
        out'.val.length = out.val.length ⦄ := by
  have hKk := hv.len
  unfold encode.w1_encode_pub_loop
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => k - p.2.val)
    (fun p => p.1.val.length = out.val.length ∧ p.2.val ≤ k ∧
      (bytes p.1).take (p.2.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) p.2.val)
  · rintro ⟨out1, i1⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.w1_encode_pub_loop.body]
    split
    · rename_i hi
      have hik : i1.val < k := by scalar_tac
      have hm1 : (i1.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have hm2 : i1.val * n.val ≤ k * n.val := Nat.mul_le_mul_right _ (by omega)
      have hlen := out1.property
      step*
      have hFlen : ∀ t : Nat, (SimpleBitPack v[t]! b).length = n.val := fun t => by
        rw [SimpleBitPack_length, ← hc, hn]
      refine WP.spec_bind (bit_pack_pub_spec_repr _ (v[i1.val]'hik) ?_ b hb (hrng _ hik) c hc s ?_) ?_
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

theorem w1_encode_pub_spec_long {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly sp.k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int))
    (out : Slice U8) (hL : 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ out.val.length) :
    encode.w1_encode_pub ip w1 out ⦃ out' =>
      (bytes out').take (32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) = Spec.w1Encode sp v ∧
      out'.val.length = out.val.length ⦄ := by
  have hc : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hp.w1_bits
  have hb := hp.w1_b_lt
  have h23 := bitlen_lt_q hb
  unfold encode.w1_encode_pub
  step*
  rw [w1Encode_eq]
  refine WP.spec_mono (w1_encode_pub_loop_spec_long ip.w1_bits n (by rw [n_post]) _ hb hc sp.k w1 v hv hrng out
    (by
      have e : sp.k * (32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) =
          32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by ring
      rw [n_post, hc, e]; exact hL) 0#usize (by simp) (by simp [flat_zero])) ?_
  intro out' h
  have e : sp.k * (32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) =
      32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by ring
  rw [n_post, hc, e] at h
  exact h


end Proofs
