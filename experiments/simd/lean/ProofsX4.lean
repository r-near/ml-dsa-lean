import Impl.Funs

/-!
# Cost probe: field-level specs for the rewrites in `experiments/simd/x4_ntt`

Same style and statement shape as `lean/Proofs/Field.lean` (`small_reduce_spec`, `barrett_reduce_spec`, `mul_spec`),
proved against the Aeneas-extracted `fold.*`, `shoup.*` and `mont2.*` functions of the x4_ntt crate.
Each theorem replaces one lemma of the existing proof stack with an unchanged statement, which is the point:
everything above `Field.lean` only uses "mul returns the canonical product".
-/

open Aeneas Aeneas.Std RustM
set_option maxRecDepth 8192

namespace ProofsX4
open Impl

theorem small_reduce_spec (x : U32) (hx : x.val < 2 * 8380417) :
    fold.small_reduce x ⦃ y => y.val = x.val % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold fold.small_reduce
  simp only [global_simps, lift, bind_tc_ok]
  by_cases h : x ≥ 8380417#u32
  · simp only [h, decide_true]
    have hm : core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 true) = 4294967295#u32 := by rfl
    rw [hm]
    have ha : (8380417#u32 &&& 4294967295#u32) = 8380417#u32 := by rfl
    rw [ha]
    step*
  · simp only [h, decide_false]
    have hm : core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 false) = 0#u32 := by rfl
    rw [hm]
    have ha : (8380417#u32 &&& 0#u32) = 0#u32 := by rfl
    rw [ha]
    step*

attribute [step] small_reduce_spec

/-- The arithmetic core of `fold_reduce`: three folds with 2^23 = q + 8191, linear in `x` with literal coefficients. -/
theorem fold_nat (x y1 y2 y3 : Nat) (hx : x < 8380417 ^ 2)
    (h1 : y1 = x % 8388608 + x / 8388608 * 8191)
    (h2 : y2 = y1 % 8388608 + y1 / 8388608 * 8191)
    (h3 : y3 = y2 % 8388608 + y2 / 8388608 * 8191) :
    y3 % 8380417 = x % 8380417 ∧ y3 < 2 * 8380417 := by
  omega

/-! ### Shoup multiplication -/

theorem wrapping_mul_val_u32 (a b : U32) :
    (core.num.U32.wrapping_mul a b).val = (a.val * b.val) % 2 ^ 32 := by
  show (a.bv * b.bv).toNat = _
  rw [BitVec.toNat_mul, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_sub_val_u32 (a b : U32) :
    (core.num.U32.wrapping_sub a b).val = (2 ^ 32 - b.val + a.val) % 2 ^ 32 := by
  show (a.bv - b.bv).toNat = _
  rw [BitVec.toNat_sub, UScalar.bv_toNat, UScalar.bv_toNat]

/-- Shoup's lemma over the naturals: with `zp = floor(z*M/q)` and `hi = floor(x*zp/M)`, `z*x - hi*q` is in `[0, 2q)`. -/
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

theorem mul_shoup_nat (z zp x : Nat) (hz : z < 8380417) (hzp : zp = z * 4294967296 / 8380417) (hx : x < 4294967296) :
    x * zp / 4294967296 * 8380417 ≤ z * x ∧ z * x < x * zp / 4294967296 * 8380417 + 2 * 8380417 := by
  have h1 : zp * 8380417 ≤ z * 4294967296 := by rw [hzp]; exact Nat.div_mul_le_self _ _
  have h2 : z * 4294967296 < zp * 8380417 + 8380417 := by
    rw [hzp]; have := Nat.lt_div_mul_add (a := z * 4294967296) (b := 8380417) (by norm_num); omega
  have h3 : x * zp / 4294967296 * 4294967296 ≤ x * zp := Nat.div_mul_le_self _ _
  have h4 : x * zp < x * zp / 4294967296 * 4294967296 + 4294967296 := by
    have := Nat.lt_div_mul_add (a := x * zp) (b := 4294967296) (by norm_num); omega
  exact shoup_abs 4294967296 8380417 z zp x _ (by norm_num) (by norm_num) h1 h2 h3 h4 hx

theorem mul_shoup_spec (z zp x : U32) (hz : z.val < 8380417) (hzp : zp.val = z.val * 4294967296 / 8380417) :
    shoup.mul_shoup z zp x ⦃ y => y.val = (z.val * x.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  have hx32 : x.val < 4294967296 := x.hBounds
  have hzp32 : zp.val < 4294967296 := zp.hBounds
  have hn := mul_shoup_nat z.val zp.val x.val hz hzp hx32
  have hxm : x.val % 18446744073709551616 = x.val := Nat.mod_eq_of_lt (by omega)
  have hzpm : zp.val % 18446744073709551616 = zp.val := Nat.mod_eq_of_lt (by omega)
  have hprod : x.val * zp.val < 4294967296 * 4294967296 := Nat.mul_lt_mul'' hx32 hzp32
  unfold shoup.mul_shoup
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_sub_val_u32, wrapping_mul_val_u32, UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U64.numBits, U32.numBits, UScalarTy.numBits] at *
  all_goals rw [Nat.mod_eq_of_lt hxm, Nat.mod_eq_of_lt hzpm] at i2_post
  all_goals generalize hzx : z.val * x.val = P at *
  all_goals generalize hxz : x.val * zp.val = A at *
  all_goals omega

/-! ### Two-reduction Montgomery product (canonical pointwise multiply) -/

/-- `QNEG = -q^-1 mod 2^32`: `a + (a*QNEG mod 2^32) * q` is divisible by `2^32`. -/
theorem mont_div (a : Nat) : (a + (a * 4236238847 % 4294967296) * 8380417) % 4294967296 = 0 := by
  omega

theorem mont_core (a m r : Nat) (hm : m < 4294967296) (hr : r * 4294967296 = a + m * 8380417)
    (ha : a < 4294967296 * 8380417) : r < 2 * 8380417 ∧ r * 4294967296 % 8380417 = a % 8380417 := by
  omega

/-- One unsigned Montgomery reduction (R = 2^32): `r * 2^32 = a + m*q` for the quotient `m`, so `r = a * 2^-32 mod q`, `r < 2q`. -/
theorem mont_u_spec (a : U64) (ha : a.val < 4294967296 * 8380417) :
    mont2.mont_u a ⦃ r => r.val < 2 * 8380417 ∧ r.val * 4294967296 % 8380417 = a.val % 8380417 ⦄ := by
  unfold mont2.mont_u
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_mul_val_u32, UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U64.numBits, U32.numBits, UScalarTy.numBits] at *
  all_goals have hd := mont_div a.val
  all_goals have hm : a.val * 4236238847 % 4294967296 < 4294967296 := Nat.mod_lt _ (by norm_num)
  all_goals rw [Nat.mod_eq_of_lt (by omega : a.val * 4236238847 % 4294967296 < 18446744073709551616)] at i3_post
  all_goals have hsplit : i5.val * 4294967296 = a.val + (a.val * 4236238847 % 4294967296) * 8380417 := by omega
  all_goals have hc := mont_core a.val _ i5.val hm hsplit ha
  all_goals have h32 : i5.val % 4294967296 = i5.val := Nat.mod_eq_of_lt (by omega)
  all_goals rw [h32]
  all_goals omega

end ProofsX4
