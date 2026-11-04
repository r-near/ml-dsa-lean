import Proofs.Field

/-!
# The vectorizable products of the NTT: Shoup and two-step Montgomery

`field.mul_shoup z zp x` multiplies by a fixed twiddle `z` with its companion `zp = ⌊z·2³²/q⌋`
(forward and inverse NTT butterflies, the 256⁻¹ scaling); `field.mul_mont a b` multiplies two variable
canonical operands with two Montgomery reductions (pointwise product). Both use only 32 × 32 → 64 bit
multiplies, which is what lets LLVM vectorize them.

For canonical inputs they return the same canonical value as `field.mul`, so the statements below have the
shape of `Field.lean`'s `mul_spec`/`mul_zmod`, and everything built on those continues to hold.
The Shoup companion is a hypothesis here (`zp = z·2³²/q`); `Proofs/NTT.lean` discharges it from the tables
by `decide +kernel`.
-/

open Aeneas Aeneas.Std RustM
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Shoup multiplication -/

/-- Shoup's lemma over the naturals: with `zp = ⌊z·M/q⌋` and `hi = ⌊x·zp/M⌋`, `z·x − hi·q` is in `[0, 2q)`. -/
theorem shoup_abs (M q z zp x hi : Nat) (hM : 0 < M) (hq : 0 < q)
    (h1 : zp * q ≤ z * M) (h2 : z * M < zp * q + q)
    (h3 : hi * M ≤ x * zp) (h4 : x * zp < hi * M + M) (hx : x < M) :
    hi * q ≤ z * x ∧ z * x < hi * q + 2 * q := by
  constructor
  · apply Nat.le_of_mul_le_mul_right _ hM
    calc hi * q * M = (hi * M) * q := by ring
      _ ≤ (x * zp) * q := Nat.mul_le_mul_right q h3
      _ = x * (zp * q) := by ring
      _ ≤ x * (z * M) := Nat.mul_le_mul_left x h1
      _ = z * x * M := by ring
  · apply Nat.lt_of_mul_lt_mul_right (a := M)
    have a1 : x * zp * q < (hi * M + M) * q := Nat.mul_lt_mul_of_pos_right h4 hq
    have a2 : x * q ≤ M * q := Nat.mul_le_mul_right q hx.le
    calc z * x * M = x * (z * M) := by ring
      _ ≤ x * (zp * q + q) := Nat.mul_le_mul_left x h2.le
      _ = (x * zp) * q + x * q := by ring
      _ < (hi * M + M) * q + M * q := by omega
      _ = (hi * q + 2 * q) * M := by ring

theorem mul_shoup_nat (z zp x : Nat) (hzp : zp = z * 4294967296 / 8380417) (hx : x < 4294967296) :
    x * zp / 4294967296 * 8380417 ≤ z * x ∧ z * x < x * zp / 4294967296 * 8380417 + 2 * 8380417 := by
  have h1 : zp * 8380417 ≤ z * 4294967296 := by rw [hzp]; exact Nat.div_mul_le_self _ _
  have h2 : z * 4294967296 < zp * 8380417 + 8380417 := by
    rw [hzp]; have := Nat.lt_div_mul_add (a := z * 4294967296) (b := 8380417) (by norm_num); omega
  have h3 : x * zp / 4294967296 * 4294967296 ≤ x * zp := Nat.div_mul_le_self _ _
  have h4 : x * zp < x * zp / 4294967296 * 4294967296 + 4294967296 := by
    have := Nat.lt_div_mul_add (a := x * zp) (b := 4294967296) (by norm_num); omega
  exact shoup_abs 4294967296 8380417 z zp x _ (by norm_num) (by norm_num) h1 h2 h3 h4 hx

/-- `field.mul_shoup z zp x = z·x mod q` for a twiddle `z` with companion `zp = ⌊z·2³²/q⌋` and any `x : U32`
(the NTT calls it with canonical `z` and `x`, but canonicity is not needed: `z·x − hi·q ∈ [0, 2q)` regardless). -/
theorem mul_shoup_spec (z zp x : U32) (hzp : zp.val = z.val * 4294967296 / 8380417) :
    field.mul_shoup z zp x ⦃ y => y.val = (z.val * x.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  have hx32 : x.val < 4294967296 := x.hBounds
  have hzp32 : zp.val < 4294967296 := zp.hBounds
  have hn := mul_shoup_nat z.val zp.val x.val hzp hx32
  have hxm : x.val % 18446744073709551616 = x.val := Nat.mod_eq_of_lt (by omega)
  have hzpm : zp.val % 18446744073709551616 = zp.val := Nat.mod_eq_of_lt (by omega)
  have hprod : x.val * zp.val < 4294967296 * 4294967296 := Nat.mul_lt_mul'' hx32 hzp32
  unfold field.mul_shoup
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_sub_val_u32, wrapping_mul_val_u32, UScalar.cast_val_eq,
    Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U64.numBits, U32.numBits, UScalarTy.numBits] at *
  all_goals rw [Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hzpm] at i2_post
  all_goals generalize hzx : z.val * x.val = P at *
  all_goals generalize hxz : x.val * zp.val = A at *
  all_goals omega

/-! ## Two-step Montgomery product -/

/-- `QNEG = −q⁻¹ mod 2³²`: `a + (a·QNEG mod 2³²)·q` is divisible by `2³²`. -/
theorem mont_div (a : Nat) : (a + (a * 4236238847 % 4294967296) * 8380417) % 4294967296 = 0 := by
  omega

theorem mont_core (a m r : Nat) (hm : m < 4294967296) (hr : r * 4294967296 = a + m * 8380417)
    (ha : a < 4294967296 * 8380417) : r < 2 * 8380417 ∧ r * 4294967296 % 8380417 = a % 8380417 := by
  omega

/-- One unsigned Montgomery reduction (R = 2³²): `r·2³² = a + m·q` for the quotient `m`, so `r ≡ a·2⁻³²` and `r < 2q`. -/
theorem mont_reduce_spec (a : U64) (ha : a.val < 4294967296 * 8380417) :
    field.mont_reduce a ⦃ r => r.val < 2 * 8380417 ∧ r.val * 4294967296 % 8380417 = a.val % 8380417 ⦄ := by
  unfold field.mont_reduce
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_mul_val_u32, wrapping_mul_val_u64, wrapping_add_val_u64, UScalar.cast_val_eq,
    Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U64.numBits, U32.numBits, UScalarTy.numBits] at *
  have hd := mont_div a.val
  have hm : a.val * 4236238847 % 4294967296 < 4294967296 := Nat.mod_lt _ (by norm_num)
  have hsum : a.val + a.val * 4236238847 % 4294967296 * 8380417 < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hsum] at i5_post1
  have hsplit : i5.val * 4294967296 = a.val + (a.val * 4236238847 % 4294967296) * 8380417 := by omega
  have hc := mont_core a.val _ i5.val hm hsplit ha
  have h32 : i5.val % 4294967296 = i5.val := Nat.mod_eq_of_lt (by omega)
  rw [h32]
  omega

attribute [step] mont_reduce_spec

/-- The two Montgomery steps compose to the product: `r·2³² ≡ p·R2` and `p·2³² ≡ a·b` with `R2 = 2⁶⁴ mod q`
give `r·2⁶⁴ ≡ a·b·2⁶⁴`, and `2⁶⁴` is invertible mod the prime `q`. -/
theorem mont2_nat (ab p r : Nat) (h1 : p * 4294967296 % 8380417 = ab % 8380417)
    (h2 : r * 4294967296 % 8380417 = (p * 2365951) % 8380417) : r % 8380417 = ab % 8380417 := by
  have c1 : p * 4294967296 ≡ ab [MOD 8380417] := h1
  have c2 : r * 4294967296 ≡ p * 2365951 [MOD 8380417] := h2
  have hR2 : 2365951 ≡ 4294967296 * 4294967296 [MOD 8380417] := by
    unfold Nat.ModEq; norm_num
  have c3 : r * (4294967296 * 4294967296) ≡ ab * (4294967296 * 4294967296) [MOD 8380417] := by
    calc r * (4294967296 * 4294967296) = r * 4294967296 * 4294967296 := by ring
      _ ≡ p * 2365951 * 4294967296 [MOD 8380417] := c2.mul_right _
      _ = (p * 4294967296) * 2365951 := by ring
      _ ≡ ab * 2365951 [MOD 8380417] := c1.mul_right _
      _ ≡ ab * (4294967296 * 4294967296) [MOD 8380417] := hR2.mul_left _
  exact Nat.ModEq.cancel_right_of_coprime (by decide +kernel) c3

theorem mul64_ok (x y : U64) (h : x.val * y.val < 18446744073709551616) :
    ∃ z : U64, x * y = ok z ∧ z.val = x.val * y.val := by
  have hm : x.val * y.val ≤ UScalar.max UScalarTy.U64 := by
    simp only [UScalar.max, UScalarTy.numBits]
    norm_num
    omega
  exact WP.spec_imp_exists (UScalar.mul_spec hm)

theorem mul_mont_spec (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.mul_mont a b ⦃ y => y.val = (a.val * b.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  have hab : a.val * b.val < 4294967296 * 8380417 := by
    have := Nat.mul_le_mul (show a.val ≤ 8380416 by omega) (show b.val ≤ 8380416 by omega)
    omega
  unfold field.mul_mont
  simp only [global_simps, lift, bind_tc_ok]
  have hA : (UScalar.cast UScalarTy.U64 a).val = a.val := by simp
  have hB : (UScalar.cast UScalarTy.U64 b).val = b.val := by simp
  obtain ⟨i2, h2, hv2⟩ := mul64_ok (UScalar.cast UScalarTy.U64 a) (UScalar.cast UScalarTy.U64 b)
    (by rw [hA, hB]; omega)
  rw [h2]
  simp only [bind_tc_ok]
  have hi2 : i2.val < 4294967296 * 8380417 := by rw [hv2, hA, hB]; exact hab
  step as ⟨p, hp1, hp2⟩
  have hC : (UScalar.cast UScalarTy.U64 p).val = p.val := by simp
  have hR : (2365951#u64).val = 2365951 := rfl
  obtain ⟨i4, h4, hv4⟩ := mul64_ok (UScalar.cast UScalarTy.U64 p) 2365951#u64
    (by rw [hC, hR]; omega)
  rw [h4]
  simp only [bind_tc_ok]
  have hi4 : i4.val < 4294967296 * 8380417 := by rw [hv4, hC, hR]; omega
  step as ⟨r, hr1, hr2⟩
  step as ⟨y, hy1, hy2⟩
  refine ⟨?_, hy2⟩
  rw [hy1]
  have hp2' : p.val * 4294967296 % 8380417 = (a.val * b.val) % 8380417 := by
    rw [hp2, hv2, hA, hB]
  have hr2' : r.val * 4294967296 % 8380417 = (p.val * 2365951) % 8380417 := by
    rw [hr2, hv4, hC, hR]
  exact mont2_nat _ _ _ hp2' hr2'

/-! ## The same, stated in `ZMod 8380417` (the shape the NTT layer proofs use) -/

theorem mul_shoup_zmod (z zp x : U32) (hzp : zp.val = z.val * 4294967296 / 8380417) :
    field.mul_shoup z zp x ⦃ y => y.val < 8380417 ∧
      ((y.val : Nat) : ZMod 8380417) = (z.val : ZMod 8380417) * (x.val : ZMod 8380417) ⦄ := by
  apply WP.spec_mono (mul_shoup_spec z zp x hzp)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  rw [h1, ZMod.natCast_mod, Nat.cast_mul]

theorem mul_mont_zmod (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.mul_mont a b ⦃ y => y.val < 8380417 ∧
      ((y.val : Nat) : ZMod 8380417) = (a.val : ZMod 8380417) * (b.val : ZMod 8380417) ⦄ := by
  apply WP.spec_mono (mul_mont_spec a b ha hb)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  rw [h1, ZMod.natCast_mod, Nat.cast_mul]

attribute [step] mul_shoup_zmod mul_mont_zmod

end Proofs
