import Spec.Rounding

/-!
# Rounding: the integer arithmetic behind `Proofs.Rounding`

Pure `Nat`/`Int` lemmas about the constants of `src/rounding.rs`: the Barrett reductions modulo `2γ₂` and `2^13`,
the multiply-shift divisions by `2γ₂`, and the unfolding of the specification functions `Decompose`, `Power2Round`
and `UseHint`. Nothing here mentions the extracted code.
-/

set_option maxRecDepth 8192

namespace Proofs
open Spec

/-- The two values of `γ₂` of the standard parameter sets (`(q-1)/88` and `(q-1)/32`). The Barrett constants of the
Rust code are only correct for these two; `Params.Valid` alone does not pin `γ₂`. -/
def StdGamma2 (sp : Spec.Params) : Prop := sp.γ₂ = 95232 ∨ sp.γ₂ = 261888

theorem stdGamma2_44 : StdGamma2 Spec.ML_DSA_44 := Or.inl (by decide +kernel)
theorem stdGamma2_65 : StdGamma2 Spec.ML_DSA_65 := Or.inr (by decide +kernel)
theorem stdGamma2_87 : StdGamma2 Spec.ML_DSA_87 := Or.inr (by decide +kernel)

/-! ## Barrett reduction -/

theorem barrett_p2r (x : Nat) (_hx : x < 8380417) :
    x * 32768 / 2 ^ 28 * 8192 ≤ x ∧ x < x * 32768 / 2 ^ 28 * 8192 + 2 * 8192 := by
  omega

theorem barrett_44 (x : Nat) (hx : x < 8380417) :
    x * 360800 / 2 ^ 36 * 190464 ≤ x ∧ x < x * 360800 / 2 ^ 36 * 190464 + 2 * 190464 := by
  omega

theorem barrett_65 (x : Nat) (hx : x < 8380417) :
    x * 524800 / 2 ^ 38 * 523776 ≤ x ∧ x < x * 524800 / 2 ^ 38 * 523776 + 2 * 523776 := by
  omega

/-! ## Division by `2γ₂` as multiply-shift -/

theorem div48_44 (k : Nat) (hk : k ≤ 44) : k * 190464 * 1477838210 / 2 ^ 48 = k := by
  omega

theorem div48_65 (k : Nat) (hk : k ≤ 16) : k * 523776 * 537395713 / 2 ^ 48 = k := by
  omega

/-! ## mod± -/

theorem modPM_cases (x : Int) (M : Nat) :
    (x % (M : Int) > ((M / 2 : Nat) : Int) ∧ Spec.modPM x M = x % (M : Int) - M) ∨
    (x % (M : Int) ≤ ((M / 2 : Nat) : Int) ∧ Spec.modPM x M = x % (M : Int)) := by
  unfold Spec.modPM
  simp only []
  split
  · left; exact ⟨by assumption, rfl⟩
  · right; exact ⟨by omega, rfl⟩

/-! ## The multiply-shift high parts of `use_hint_g32` / `use_hint_g88` -/

/-- The multiply-shift high part for γ₂ = (q-1)/32. -/
theorem uh65_r1 (r t k : Int) (hk : r = 523776*k + t) (ht1 : -261888 < t)
    (ht2 : t ≤ 261888) (hk0 : 0 ≤ k) (hk16 : k ≤ 16) :
    ((r+127)/128*1025 + 2097152)/4194304 % 16 = if k = 16 then 0 else k := by
  have ha : (r + 127) / 128 = 4092 * k + (t + 127) / 128 := by omega
  rw [ha]
  generalize (t + 127) / 128 = s at *
  have hs1 : -2045 ≤ s := by omega
  have hs2 : s ≤ 2046 := by omega
  have hd : ((4092 * k + s) * 1025 + 2097152) / 4194304 = k := by omega
  rw [hd]
  split <;> omega

/-- The multiply-shift high part for γ₂ = (q-1)/88 (before the edge case is mapped to 0). -/
theorem uh44_r1 (r t k : Int) (hk : r = 190464*k + t) (ht1 : -95232 < t)
    (ht2 : t ≤ 95232) (hk0 : 0 ≤ k) (hk44 : k ≤ 44) :
    ((r+127)/128*11275 + 8388608)/16777216 = k := by
  have ha : (r + 127) / 128 = 1488 * k + (t + 127) / 128 := by omega
  rw [ha]
  generalize (t + 127) / 128 = s at *
  have hs1 : -743 ≤ s := by omega
  have hs2 : s ≤ 744 := by omega
  omega

/-! ## Unfolding the specification -/

theorem Power2Round_eq (sp : Spec.Params) (r : Zq) :
    Spec.Power2Round sp r =
      (((r.val : Int) - Spec.modPM (r.val : Int) (2 ^ sp.d)) / 2 ^ sp.d, Spec.modPM (r.val : Int) (2 ^ sp.d)) := by
  rfl

theorem Decompose_eq (sp : Spec.Params) (r : Zq) :
    Spec.Decompose sp r =
      if (r.val : Int) - Spec.modPM (r.val : Int) (2 * sp.γ₂) = (Spec.q : Int) - 1 then
        (0, Spec.modPM (r.val : Int) (2 * sp.γ₂) - 1)
      else
        (((r.val : Int) - Spec.modPM (r.val : Int) (2 * sp.γ₂)) / (2 * (sp.γ₂ : Int)),
         Spec.modPM (r.val : Int) (2 * sp.γ₂)) := by
  unfold Spec.Decompose
  by_cases h : (r.val : Int) - Spec.modPM (r.val : Int) (2 * sp.γ₂) = (Spec.q : Int) - 1
  · simp only [h, if_true]; rfl
  · simp only [h, if_false]; rfl

theorem UseHint_eq (sp : Spec.Params) (h : Bool) (r : Zq) :
    Spec.UseHint sp h r =
      (if h = true ∧ (Spec.Decompose sp r).2 > 0 then ((Spec.Decompose sp r).1 + 1) % (sp.m : Int)
       else if h = true then ((Spec.Decompose sp r).1 - 1) % (sp.m : Int)
       else (Spec.Decompose sp r).1) := by
  unfold Spec.UseHint Spec.Params.m
  by_cases h1 : h = true <;> by_cases h2 : (Spec.Decompose sp r).2 > 0 <;> simp [h1, h2]

end Proofs
