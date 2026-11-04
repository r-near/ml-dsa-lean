import Impl.Funs

/-!
# Field operations on canonical representatives

For canonical inputs (`< q`, q = 8380417), the extracted `field.add/sub/mul/small_reduce/barrett_reduce`
never fail and return the canonical representative of the corresponding `ZMod q` operation.
Statements use Aeneas' `⦃ y => ... ⦄` (`WP.spec`) notation, which excludes both failure and divergence.
-/

open Aeneas Aeneas.Std RustM
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ### Wrapping arithmetic on values

`field.rs` writes `+`, `-` and `*` on secret-dependent operands as `wrapping_*` (an overflow-check guard on a secret
value is a branch that constant-time tools cannot decide, `checkct/README.md`). The proofs below show that the exact
result fits, so the wrapping result is the exact result. -/

theorem wrapping_add_val_u32 (a b : U32) :
    (core.num.U32.wrapping_add a b).val = (a.val + b.val) % 2 ^ 32 := by
  show (a.bv + b.bv).toNat = _
  rw [BitVec.toNat_add, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_mul_val_u32 (a b : U32) :
    (core.num.U32.wrapping_mul a b).val = (a.val * b.val) % 2 ^ 32 := by
  show (a.bv * b.bv).toNat = _
  rw [BitVec.toNat_mul, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_sub_val_u32 (a b : U32) :
    (core.num.U32.wrapping_sub a b).val = (2 ^ 32 - b.val + a.val) % 2 ^ 32 := by
  show (a.bv - b.bv).toNat = _
  rw [BitVec.toNat_sub, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_add_val_u64 (a b : U64) :
    (core.num.U64.wrapping_add a b).val = (a.val + b.val) % 2 ^ 64 := by
  show (a.bv + b.bv).toNat = _
  rw [BitVec.toNat_add, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_mul_val_u64 (a b : U64) :
    (core.num.U64.wrapping_mul a b).val = (a.val * b.val) % 2 ^ 64 := by
  show (a.bv * b.bv).toNat = _
  rw [BitVec.toNat_mul, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_mul_val_u128 (a b : U128) :
    (core.num.U128.wrapping_mul a b).val = (a.val * b.val) % 2 ^ 128 := by
  show (a.bv * b.bv).toNat = _
  rw [BitVec.toNat_mul, UScalar.bv_toNat, UScalar.bv_toNat]

theorem wrapping_sub_val_u128 (a b : U128) :
    (core.num.U128.wrapping_sub a b).val = (2 ^ 128 - b.val + a.val) % 2 ^ 128 := by
  show (a.bv - b.bv).toNat = _
  rw [BitVec.toNat_sub, UScalar.bv_toNat, UScalar.bv_toNat]

theorem multiplier_value : field.BARRETT_MULTIPLIER = ok 8396807#u128 := by
  unfold field.BARRETT_MULTIPLIER
  simp only [global_simps]
  rfl

theorem small_reduce_spec (x : U32) (hx : x.val < 2 * 8380417) :
    field.small_reduce x ⦃ y => y.val = x.val % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.small_reduce
  simp only [global_simps, lift, bind_tc_ok]
  by_cases h : x ≥ 8380417#u32
  · simp only [h, decide_true]
    have hm : core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 true) = 4294967295#u32 := by rfl
    rw [hm]
    have ha : (8380417#u32 &&& 4294967295#u32) = 8380417#u32 := by rfl
    rw [ha]
    step*
    rw [wrapping_sub_val_u32]
    have hq : (8380417#u32).val = 8380417 := rfl
    rw [hq]
    have hge : 8380417 ≤ x.val := by scalar_tac
    omega
  · simp only [h, decide_false]
    have hm : core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 false) = 0#u32 := by rfl
    rw [hm]
    have ha : (8380417#u32 &&& 0#u32) = 0#u32 := by rfl
    rw [ha]
    step*
    rw [wrapping_sub_val_u32]
    have hq : (0#u32).val = 0 := rfl
    rw [hq]
    have hlt : x.val < 8380417 := by scalar_tac
    omega

attribute [step] small_reduce_spec

theorem barrett_nat (x : Nat) (hx : x < 8380417 ^ 2) :
    x * 8396807 / 2 ^ 46 * 8380417 ≤ x ∧ x < x * 8396807 / 2 ^ 46 * 8380417 + 2 * 8380417 := by
  omega

/-- The three wrapping `u128` operations of `barrett_reduce` compute the exact remainder `x - q·Q ∈ [0, 2Q)`. -/
theorem barrett_arith (x q : Nat) (hx : x < 8380417 ^ 2) (hq : q = x * 8396807 % 2 ^ 128 / 2 ^ 46) :
    q * 8380417 ≤ x ∧ x - q * 8380417 < 2 * 8380417 ∧
      (340282366920938463463374607431768211456 - q * 8380417 % 340282366920938463463374607431768211456 + x) %
        4294967296 = x - q * 8380417 := by
  have h1 : x * 8396807 % 2 ^ 128 = x * 8396807 := Nat.mod_eq_of_lt (by omega)
  rw [h1] at hq
  have hb := barrett_nat x hx
  rw [← hq] at hb
  have h2 : q * 8380417 % 2 ^ 128 = q * 8380417 := Nat.mod_eq_of_lt (by omega)
  omega

theorem barrett_reduce_spec (x : U64) (hx : x.val < 8380417 ^ 2) :
    field.barrett_reduce x ⦃ y => y.val = x.val % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.barrett_reduce
  rw [multiplier_value]
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [wrapping_mul_val_u128, wrapping_sub_val_u128, UScalar.cast_val_eq,
    Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U128.max, U128.numBits] at *
  all_goals have ha := barrett_arith x.val quotient.val hx (by omega)
  all_goals (try rw [ha.2.2] at y_post1)
  all_goals (try rw [ha.2.2])
  all_goals omega

attribute [step] barrett_reduce_spec

theorem add_spec (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.add a b ⦃ y => y.val = (a.val + b.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.add
  step*
  all_goals subst_vars
  all_goals simp only [wrapping_add_val_u32] at *
  all_goals omega

theorem sub_spec (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.sub a b ⦃ y => y.val = (a.val + 8380417 - b.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  have hq : (8380417#u32).val = 8380417 := rfl
  have h1 : (core.num.U32.wrapping_add a 8380417#u32).val = a.val + 8380417 := by
    rw [wrapping_add_val_u32, hq]; omega
  have h2 : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add a 8380417#u32) b).val =
      a.val + 8380417 - b.val := by
    rw [wrapping_sub_val_u32, h1]; omega
  unfold field.sub
  simp only [global_simps, lift, bind_tc_ok]
  apply WP.spec_mono (small_reduce_spec _ (by rw [h2]; omega))
  intro y hy
  rw [h2] at hy
  exact hy

theorem mul_spec (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.mul a b ⦃ y => y.val = (a.val * b.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  have hprod : a.val * b.val < 8380417 ^ 2 := by
    have := Nat.mul_le_mul (show a.val ≤ 8380416 by omega) (show b.val ≤ 8380416 by omega)
    omega
  unfold field.mul
  step*

/-! ### The same operations stated in `ZMod 8380417` -/

theorem add_zmod (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.add a b ⦃ y => y.val < 8380417 ∧
      ((y.val : Nat) : ZMod 8380417) = (a.val : ZMod 8380417) + (b.val : ZMod 8380417) ⦄ := by
  apply WP.spec_mono (add_spec a b ha hb)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  rw [h1, ZMod.natCast_mod, Nat.cast_add]

theorem sub_zmod (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.sub a b ⦃ y => y.val < 8380417 ∧
      ((y.val : Nat) : ZMod 8380417) = (a.val : ZMod 8380417) - (b.val : ZMod 8380417) ⦄ := by
  apply WP.spec_mono (sub_spec a b ha hb)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  have hq : ((8380417 : Nat) : ZMod 8380417) = 0 := ZMod.natCast_self _
  rw [h1, ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, hq]
  ring

theorem mul_zmod (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.mul a b ⦃ y => y.val < 8380417 ∧
      ((y.val : Nat) : ZMod 8380417) = (a.val : ZMod 8380417) * (b.val : ZMod 8380417) ⦄ := by
  apply WP.spec_mono (mul_spec a b ha hb)
  rintro y ⟨h1, h2⟩
  refine ⟨h2, ?_⟩
  rw [h1, ZMod.natCast_mod, Nat.cast_mul]

attribute [step] add_zmod sub_zmod mul_zmod

end Proofs
