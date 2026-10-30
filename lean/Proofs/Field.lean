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
  · simp only [h, decide_false]
    have hm : core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 false) = 0#u32 := by rfl
    rw [hm]
    have ha : (8380417#u32 &&& 0#u32) = 0#u32 := by rfl
    rw [ha]
    step*

attribute [step] small_reduce_spec

theorem barrett_nat (x : Nat) (hx : x < 8380417 ^ 2) :
    x * 8396807 / 2 ^ 46 * 8380417 ≤ x ∧ x < x * 8396807 / 2 ^ 46 * 8380417 + 2 * 8380417 := by
  omega

theorem barrett_reduce_spec (x : U64) (hx : x.val < 8380417 ^ 2) :
    field.barrett_reduce x ⦃ y => y.val = x.val % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.barrett_reduce
  rw [multiplier_value]
  simp only [global_simps, lift, bind_tc_ok]
  step*
  all_goals simp only [UScalar.cast_val_eq, Nat.shiftRight_eq_div_pow] at *
  all_goals norm_num [U128.max, U128.numBits] at *
  all_goals have h128 : x.val % 340282366920938463463374607431768211456 = x.val :=
    Nat.mod_eq_of_lt (by omega)
  all_goals simp only [h128] at *
  all_goals have hb := barrett_nat x.val hx
  all_goals try have hk : quotient.val = x.val * 8396807 / 2 ^ 46 := by omega
  all_goals try have hrem : remainder.val < 2 * 8380417 := by omega
  all_goals try have hmod : remainder.val % 4294967296 = remainder.val :=
    Nat.mod_eq_of_lt (by omega)
  all_goals omega

attribute [step] barrett_reduce_spec

theorem add_spec (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.add a b ⦃ y => y.val = (a.val + b.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.add
  step*

theorem sub_spec (a b : U32) (ha : a.val < 8380417) (hb : b.val < 8380417) :
    field.sub a b ⦃ y => y.val = (a.val + 8380417 - b.val) % 8380417 ∧ y.val < 8380417 ⦄ := by
  unfold field.sub
  simp only [global_simps]
  step*

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
