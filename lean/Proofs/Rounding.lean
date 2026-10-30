import Proofs.Repr
import Proofs.RoundingArith

/-!
# Rounding and hints: the extracted Rust equals FIPS 204 Algorithms 35-40

For canonical inputs (`r.val < q`) the extracted `Impl.rounding.*` functions never fail, never diverge, and compute
the specification functions of `Spec/Rounding.lean`.

## How results are encoded

The spec returns *integers* (`Spec.Power2Round`, `Decompose`, `HighBits`, `LowBits`, `UseHint`) or a `Bool`
(`MakeHint`); the Rust returns `u32` values, with a signed value `r` stored as the canonical residue `r mod q`
(this is `ReprInt`, see `Proofs/Repr.lean`).

* High parts (`r₁` of `power2round` and `decompose`, `high_bits`, `use_hint`) are small and non-negative: the `u32`
  `y` satisfies `(y.val : Int) = <spec value>` exactly, together with the bound (`< 2^10` resp. `< m`).
* Low parts (`r₀`) are signed: `(y.val : Int) = <spec value> % q` with `y.val < q`. For `decompose` the proof also
  gives the signed range `-γ₂ ≤ r₀ ≤ γ₂`, which pins the spec value down from the residue.
* `make_hint` returns exactly `Spec.MakeHint`.
* The polynomial wrappers conclude `ReprInt out (…)` for the spec's coefficientwise map (the per-polynomial body of
  `HighBitsVec`, `LowBitsVec`, `UseHintVec`, `Power2RoundVec`), plus the exact per-coefficient values.

## Premises

* `hp : Params.Valid ip K L sp` as everywhere, and `hg : StdGamma2 sp` (`sp.γ₂ ∈ {95232, 261888}`): `Params.Valid`
  relates the Barrett constants to `γ₂` by their defining equations, but does not pin `γ₂`, and the Rust constants
  (36/360800, 38/524800, `>> 48` with 1477838210 / 537395713) are correct exactly for these two values. The three
  standard parameter sets satisfy it (`stdGamma2_44/65/87`, `rounding_hypotheses_ML_DSA_*`).
* `power2round` and `poly_power2round` do not depend on `ip`: they need only `sp.d = 13` (`Params.Valid.d_eq`).

The arithmetic (Barrett quotient bounds, exactness of the multiply-shift division) is in `Proofs/RoundingArith.lean`
and is discharged by `omega`; no exhaustive check over `r < q` is used.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-- The parameter triples `(m, shift, mult)` the Rust code passes to `reduce_mod`. -/
def BarrettOK (m shift : U32) (mult : U64) : Prop :=
  (m = 190464#u32 ∧ shift = 36#u32 ∧ mult = 360800#u64) ∨
  (m = 523776#u32 ∧ shift = 38#u32 ∧ mult = 524800#u64) ∨
  (m = 8192#u32 ∧ shift = 28#u32 ∧ mult = 32768#u64)

theorem BarrettOK.p2r : BarrettOK 8192#u32 28#u32 32768#u64 := Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

theorem BarrettOK.facts {m shift : U32} {mult : U64} (h : BarrettOK m shift mult) :
    0 < m.val ∧ m.val < 2 ^ 20 ∧ m.val % 2 = 0 ∧ shift.val < 64 ∧ mult.val ≤ 524800 ∧
    (∀ x : Nat, x < 8380417 →
      x * mult.val / 2 ^ shift.val * m.val ≤ x ∧ x < x * mult.val / 2 ^ shift.val * m.val + 2 * m.val) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨by decide, by decide, by decide, by decide, by decide, fun x hx => barrett_44 x hx⟩
  · exact ⟨by decide, by decide, by decide, by decide, by decide, fun x hx => barrett_65 x hx⟩
  · exact ⟨by decide, by decide, by decide, by decide, by decide, fun x hx => barrett_p2r x hx⟩

theorem reduce_mod_spec (x m shift : U32) (mult : U64) (hx : x.val < 8380417)
    (hb : BarrettOK m shift mult) :
    rounding.reduce_mod x m shift mult ⦃ y => y.val = x.val % m.val ∧ y.val < m.val ⦄ := by
  obtain ⟨hm0, hm1, hm2, hs, hmu, hbar⟩ := hb.facts
  have hbx := hbar x.val hx
  have hxm : x.val * mult.val < 2 ^ 63 := by nlinarith
  unfold rounding.reduce_mod
  step*
  all_goals have hm64 : m64.val = m.val := by rw [m64_post]; simp
  all_goals have hx1 : x1.val = x.val := by rw [x1_post]; simp
  all_goals (have hq : quotient.val = x.val * mult.val / 2 ^ shift.val := by
                    rw [quotient_post1, Nat.shiftRight_eq_div_pow, i_post, hx1])
  · rw [hq, hm64]; exact le_trans (hbx.1.trans' (le_refl _)) (by simp [U64.max, U64.numBits]; omega)
  · rw [i1_post, hq, hm64, hx1]; exact hbx.1
  · have hrem : remainder.val = x.val - x.val * mult.val / 2 ^ shift.val * m.val := by
      rw [remainder_post1, i1_post, hq, hm64, hx1]
    have hmod : x.val % m.val = remainder.val % m.val := by
      have h1 : m.val * (x.val * mult.val / 2 ^ shift.val) ≤ x.val := by
        rw [Nat.mul_comm]; exact hbx.1
      have h2 := Nat.sub_mul_mod h1
      rw [Nat.mul_comm m.val] at h2
      rw [hrem]; exact h2.symm
    have hrlt : remainder.val < 2 * m.val := by omega
    have h32 : (2 : Nat) ^ UScalarTy.U32.numBits = 4294967296 := by decide
    have h32' : (2 : Nat) ^ UScalarTy.U64.numBits = 18446744073709551616 := by decide
    by_cases hlt : remainder.val < m.val
    · have h3 := i3_post1 (by omega)
      have h4 := (cast_mask i3 i4 i4_post).2 h3
      have := y_post2 h4
      rw [this, r_small_post]
      simp only [UScalar.cast_val_eq, h32]
      rw [hmod, Nat.mod_eq_of_lt hlt]
      constructor <;> omega
    · have h3 := i3_post2 (by omega)
      have h4 := (cast_mask i3 i4 i4_post).1 h3
      have := y_post1 h4
      rw [this, r_large_post, i2_post]
      simp only [UScalar.cast_val_eq, wrapping_sub_val_u64, hm64, h32]
      rw [hmod, Nat.mod_eq_sub_mod (not_lt.mp hlt), Nat.mod_eq_of_lt (a := remainder.val - m.val) (b := m.val) (by omega)]
      constructor <;> omega

attribute [step] reduce_mod_spec

theorem mod_plus_minus_spec (x m shift : U32) (mult : U64) (hx : x.val < 8380417)
    (hb : BarrettOK m shift mult) :
    rounding.mod_plus_minus x m shift mult ⦃ y => y.val < 8380417 ∧
      y.val = if x.val % m.val ≤ m.val / 2 then x.val % m.val else x.val % m.val + 8380417 - m.val ⦄ := by
  obtain ⟨hm0, hm1, hm2, hs, hmu, hbar⟩ := hb.facts
  unfold rounding.mod_plus_minus
  simp only [global_simps]
  step*
  all_goals have hi1 : i1.val = m.val / 2 := by simp [i1_post, i_post1, Nat.shiftRight_eq_div_pow]
  all_goals have hi2 : i2.val = raw.val := by simp [i2_post]
  all_goals have hmask := lower_of_mask i3 i4 lower i4_post lower_post
  · by_cases h : m.val / 2 < raw.val
    · exact Or.inl (hmask.2 (i3_post1 (by omega)))
    · exact Or.inr (hmask.1 (i3_post2 (by omega)))
  · by_cases h : m.val / 2 < raw.val
    · have hl := (hmask.2 (i3_post1 (by omega)))
      have := y_post1 hl
      rw [this, i7_post1, i6_post1, i5_post, raw_post1.symm]
      have : ¬ (raw.val ≤ m.val / 2) := by omega
      rw [raw_post1] at this ⊢
      simp only [this, if_false]
      omega
    · have hl := (hmask.1 (i3_post2 (by omega)))
      have := y_post2 hl
      rw [this, raw_post1]
      simp only [raw_post1] at h
      simp only [show x.val % m.val ≤ m.val / 2 by omega, if_true]
      exact ⟨by omega, trivial⟩

attribute [step] mod_plus_minus_spec

theorem zq_val (x : Nat) (hx : x < Spec.q) : ((x : Nat) : Zq).val = x := by
  rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hx

theorem mod_plus_minus_p2r (x : U32) (hx : x.val < 8380417) :
    rounding.mod_plus_minus x 8192#u32 28#u32 32768#u64 ⦃ y => y.val < 8380417 ∧
      y.val = if x.val % 8192 ≤ 8192 / 2 then x.val % 8192 else x.val % 8192 + 8380417 - 8192 ⦄ :=
  mod_plus_minus_spec x _ _ _ hx BarrettOK.p2r

attribute [step] mod_plus_minus_p2r

/-- **Algorithm 35.** `power2round r = (r₁, r₀)` with `r₁` the exact `Spec.Power2Round` high part (`< 2^10`) and `r₀`
the canonical residue of the spec's signed low part. -/
theorem power2round_spec (sp : Spec.Params) (hd : sp.d = 13) (r : U32) (hr : r.val < 8380417) :
    rounding.power2round r ⦃ p => p.1.val < 1024 ∧ p.2.val < 8380417 ∧
      (p.1.val : Int) = (Spec.Power2Round sp ((r.val : Nat) : Zq)).1 ∧
      (p.2.val : Int) = (Spec.Power2Round sp ((r.val : Nat) : Zq)).2 % (Spec.q : Int) ⦄ := by
  have e : (1#u32 <<< 13#i32) = ok 8192#u32 := by rfl
  unfold rounding.power2round
  simp only [e, bind_tc_ok]
  step with mod_plus_minus_p2r r hr as ⟨r0, h0a, h0b⟩
  step with sub_spec r r0 hr h0a as ⟨i1, h1a, h1b⟩
  step as ⟨r1, h2a, h2b, h2c⟩
  rw [Power2Round_eq, hd, zq_val _ hr]
  have hc := modPM_cases (r.val : Int) (2 ^ 13)
  generalize Spec.modPM (r.val : Int) (2 ^ 13) = t at hc ⊢
  simp only [Nat.reducePow, Nat.cast_ofNat] at hc ⊢
  rw [Nat.shiftRight_eq_div_pow] at h2a
  split at h0b
  · have e1 : i1.val = r.val - r.val % 8192 := by omega
    have e2 : r1.val = r.val / 8192 := by omega
    have e3 : t = (r.val : Int) % 8192 := by omega
    refine ⟨by omega, h0a, ?_, ?_⟩
    · omega
    · omega
  · have e1 : i1.val = r.val - r.val % 8192 + 8192 := by omega
    have e2 : r1.val = r.val / 8192 + 1 := by omega
    have e3 : t = (r.val : Int) % 8192 - 8192 := by omega
    refine ⟨by omega, h0a, ?_, ?_⟩
    · omega
    · omega

theorem xor_eq_zero_iff (a b : Nat) : a = b ↔ a ^^^ b = 0 := by
  constructor
  · intro h; subst h; exact Nat.xor_self a
  · intro h
    have := congrArg (· ^^^ b) h
    simpa [Nat.xor_assoc] using this

theorem xor_edge (diff i1 i : U32) (hi : i.val = 8380416) (h : i1.val = (diff ^^^ i).val) :
    (diff.val = 8380416 ↔ i1.val = 0) := by
  rw [h, UScalar.val_xor, hi]
  exact (xor_eq_zero_iff diff.val 8380416)

theorem edge_mask (i1 : U32) (i2 i3 i4 : U64) (is_edge : U32) (h2 : i2 = UScalar.cast .U64 i1)
    (h3a : 0 < i2.val → i3.val = 2 ^ 64 - 1) (h3b : i2.val ≤ 0 → i3.val = 0) (h4 : i4 = ~~~i3)
    (h5 : is_edge = UScalar.cast .U32 i4) :
    (i1.val = 0 → is_edge = 4294967295#u32) ∧ (i1.val ≠ 0 → is_edge = 0#u32) := by
  have hi2 : i2.val = i1.val := by simp [h2]
  have hm := lower_of_mask i3 i4 is_edge h4 h5
  constructor
  · intro h; exact hm.1 (h3b (by omega))
  · intro h; exact hm.2 (h3a (by omega))

theorem BarrettOK.g44 : BarrettOK 190464#u32 36#u32 360800#u64 := Or.inl ⟨rfl, rfl, rfl⟩
theorem BarrettOK.g65 : BarrettOK 523776#u32 38#u32 524800#u64 := Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

theorem mod_plus_minus_44 (x : U32) (hx : x.val < 8380417) :
    rounding.mod_plus_minus x 190464#u32 36#u32 360800#u64 ⦃ y => y.val < 8380417 ∧
      y.val = if x.val % 190464 ≤ 190464 / 2 then x.val % 190464 else x.val % 190464 + 8380417 - 190464 ⦄ :=
  mod_plus_minus_spec x _ _ _ hx BarrettOK.g44

theorem mod_plus_minus_65 (x : U32) (hx : x.val < 8380417) :
    rounding.mod_plus_minus x 523776#u32 38#u32 524800#u64 ⦃ y => y.val < 8380417 ∧
      y.val = if x.val % 523776 ≤ 523776 / 2 then x.val % 523776 else x.val % 523776 + 8380417 - 523776 ⦄ :=
  mod_plus_minus_spec x _ _ _ hx BarrettOK.g65

attribute [step] mod_plus_minus_44 mod_plus_minus_65

section
attribute [local step] sub_spec
theorem decompose_44 (sp : Spec.Params) (p : params.Params) (hg : p.gamma2 = 95232#u32)
    (hs : p.two_gamma2_shift = 36#u32) (hm : p.two_gamma2_mult = 360800#u64)
    (hd : p.two_gamma2_div_mult = 1477838210#u64) (hsp : sp.γ₂ = 95232) (r : U32) (hr : r.val < 8380417) :
    rounding.decompose p r ⦃ o => o.1.val < 44 ∧ o.2.val < 8380417 ∧
      (o.1.val : Int) = (Spec.Decompose sp ((r.val : Nat) : Zq)).1 ∧
      (o.2.val : Int) = (Spec.Decompose sp ((r.val : Nat) : Zq)).2 % (Spec.q : Int) ∧
      -(95232 : Int) ≤ (Spec.Decompose sp ((r.val : Nat) : Zq)).2 ∧
      (Spec.Decompose sp ((r.val : Nat) : Zq)).2 ≤ 95232 ⦄ := by
  have e2 : (2#u32 * 95232#u32) = ok 190464#u32 := by rfl
  unfold rounding.decompose
  rw [hg, hs, hm, hd]
  simp only [global_simps, e2, bind_tc_ok]
  step*
  all_goals have hxor := xor_edge diff i1 i (by rw [i_post1]) i1_post1
  all_goals have hedge := edge_mask i1 i2 i3 i4 is_edge i2_post i3_post1 i3_post2 i4_post (by rw [is_edge_post, i5_post])
  · by_cases h : diff.val = 8380416
    · exact Or.inr (hedge.1 (hxor.1 h))
    · exact Or.inl (hedge.2 (fun h' => h (hxor.2 h')))
  · by_cases h : diff.val = 8380416
    · exact Or.inr (hedge.1 (hxor.1 h))
    · exact Or.inl (hedge.2 (fun h' => h (hxor.2 h')))
  · have hmod := modPM_cases (r.val : Int) (2 * 95232)
    rw [Decompose_eq, hsp, zq_val _ hr]
    generalize Spec.modPM (r.val : Int) (2 * 95232) = t at hmod ⊢
    have hr0 : (r0.val : Int) = t % 8380417 := by split at r0_post2 <;> omega
    have hdiff : (diff.val : Int) = r.val - t := by split at r0_post2 <;> omega
    obtain ⟨k, hkd⟩ : ∃ k, diff.val = k * 190464 := ⟨diff.val / 190464, by omega⟩
    have hk44 : k ≤ 44 := by omega
    have hi6 : i6.val = diff.val := by simp [i6_post]
    have hi8 : i8.val = k := by
      rw [i8_post1, Nat.shiftRight_eq_div_pow, i7_post, hi6, hkd]; exact div48_44 k hk44
    have hr1 : r1.val = k := by
      rw [r1_post]; simp only [UScalar.cast_val_eq, hi8]
      have h32 : (2 : Nat) ^ UScalarTy.U32.numBits = 4294967296 := by decide
      rw [h32]; exact Nat.mod_eq_of_lt (by omega)
    simp only [Spec.q] at *
    by_cases hE : diff.val = 8380416
    · have he := hedge.1 (hxor.1 hE)
      have h8 := i9_post2 he
      have h10 := i11_post2 he
      have hS : (r.val : Int) - t = 8380416 := by omega
      push_cast
      rw [if_pos hS]
      rw [h8, h10]
      dsimp only
      have h0 : (0#u32).val = 0 := rfl
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · have he := hedge.2 (fun h' => hE (hxor.2 h'))
      have h8 := i9_post1 he
      have h10 := i11_post1 he
      have hS : ¬ (r.val : Int) - t = 8380416 := by omega
      push_cast
      rw [if_neg hS]
      rw [h8, h10]
      dsimp only
      have h0 : (0#u32).val = 0 := rfl
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem decompose_65 (sp : Spec.Params) (p : params.Params) (hg : p.gamma2 = 261888#u32)
    (hs : p.two_gamma2_shift = 38#u32) (hm : p.two_gamma2_mult = 524800#u64)
    (hd : p.two_gamma2_div_mult = 537395713#u64) (hsp : sp.γ₂ = 261888) (r : U32) (hr : r.val < 8380417) :
    rounding.decompose p r ⦃ o => o.1.val < 16 ∧ o.2.val < 8380417 ∧
      (o.1.val : Int) = (Spec.Decompose sp ((r.val : Nat) : Zq)).1 ∧
      (o.2.val : Int) = (Spec.Decompose sp ((r.val : Nat) : Zq)).2 % (Spec.q : Int) ∧
      -(261888 : Int) ≤ (Spec.Decompose sp ((r.val : Nat) : Zq)).2 ∧
      (Spec.Decompose sp ((r.val : Nat) : Zq)).2 ≤ 261888 ⦄ := by
  have e2 : (2#u32 * 261888#u32) = ok 523776#u32 := by rfl
  unfold rounding.decompose
  rw [hg, hs, hm, hd]
  simp only [global_simps, e2, bind_tc_ok]
  step*
  all_goals have hxor := xor_edge diff i1 i (by rw [i_post1]) i1_post1
  all_goals have hedge := edge_mask i1 i2 i3 i4 is_edge i2_post i3_post1 i3_post2 i4_post (by rw [is_edge_post, i5_post])
  · by_cases h : diff.val = 8380416
    · exact Or.inr (hedge.1 (hxor.1 h))
    · exact Or.inl (hedge.2 (fun h' => h (hxor.2 h')))
  · by_cases h : diff.val = 8380416
    · exact Or.inr (hedge.1 (hxor.1 h))
    · exact Or.inl (hedge.2 (fun h' => h (hxor.2 h')))
  · have hmod := modPM_cases (r.val : Int) (2 * 261888)
    rw [Decompose_eq, hsp, zq_val _ hr]
    generalize Spec.modPM (r.val : Int) (2 * 261888) = t at hmod ⊢
    have hr0 : (r0.val : Int) = t % 8380417 := by split at r0_post2 <;> omega
    have hdiff : (diff.val : Int) = r.val - t := by split at r0_post2 <;> omega
    obtain ⟨k, hkd⟩ : ∃ k, diff.val = k * 523776 := ⟨diff.val / 523776, by omega⟩
    have hk16 : k ≤ 16 := by omega
    have hi6 : i6.val = diff.val := by simp [i6_post]
    have hi8 : i8.val = k := by
      rw [i8_post1, Nat.shiftRight_eq_div_pow, i7_post, hi6, hkd]; exact div48_65 k hk16
    have hr1 : r1.val = k := by
      rw [r1_post]; simp only [UScalar.cast_val_eq, hi8]
      have h32 : (2 : Nat) ^ UScalarTy.U32.numBits = 4294967296 := by decide
      rw [h32]; exact Nat.mod_eq_of_lt (by omega)
    simp only [Spec.q] at *
    by_cases hE : diff.val = 8380416
    · have he := hedge.1 (hxor.1 hE)
      have h8 := i9_post2 he
      have h10 := i11_post2 he
      have hS : (r.val : Int) - t = 8380416 := by omega
      push_cast
      rw [if_pos hS]
      rw [h8, h10]
      dsimp only
      have h0 : (0#u32).val = 0 := rfl
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · have he := hedge.2 (fun h' => hE (hxor.2 h'))
      have h8 := i9_post1 he
      have h10 := i11_post1 he
      have hS : ¬ (r.val : Int) - t = 8380416 := by omega
      push_cast
      rw [if_neg hS]
      rw [h8, h10]
      dsimp only
      have h0 : (0#u32).val = 0 := rfl
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
end

/-! ## `Params.Valid` fixes the Barrett constants (given the standard `γ₂`) -/

theorem gamma2_consts {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) :
    (ip.gamma2 = 95232#u32 ∧ ip.two_gamma2_shift = 36#u32 ∧ ip.two_gamma2_mult = 360800#u64 ∧
      ip.two_gamma2_div_mult = 1477838210#u64 ∧ sp.γ₂ = 95232) ∨
    (ip.gamma2 = 261888#u32 ∧ ip.two_gamma2_shift = 38#u32 ∧ ip.two_gamma2_mult = 524800#u64 ∧
      ip.two_gamma2_div_mult = 537395713#u64 ∧ sp.γ₂ = 261888) := by
  rcases hg with h | h
  · left
    have hs : ip.two_gamma2_shift.val = 36 := by rw [hp.shift, h]; decide +kernel
    refine ⟨UScalar.eq_of_val_eq (by rw [hp.gamma2, h]; rfl), UScalar.eq_of_val_eq (by rw [hs]; rfl),
      UScalar.eq_of_val_eq (by rw [hp.mult, hs, h]; decide +kernel),
      UScalar.eq_of_val_eq (by rw [hp.div_mult, h]; decide +kernel), h⟩
  · right
    have hs : ip.two_gamma2_shift.val = 38 := by rw [hp.shift, h]; decide +kernel
    refine ⟨UScalar.eq_of_val_eq (by rw [hp.gamma2, h]; rfl), UScalar.eq_of_val_eq (by rw [hs]; rfl),
      UScalar.eq_of_val_eq (by rw [hp.mult, hs, h]; decide +kernel),
      UScalar.eq_of_val_eq (by rw [hp.div_mult, h]; decide +kernel), h⟩

/-- **Algorithm 36.** On a canonical input, `decompose` returns the high bits `r₁ < m` as the exact value, and the
low bits `r₀` as the canonical residue (mod `q`) of the specification's signed `r₀`, which lies in `[-γ₂, γ₂]`. -/
theorem decompose_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (r : U32) (hr : r.val < 8380417) :
    rounding.decompose ip r ⦃ o => o.1.val < sp.m ∧ o.2.val < 8380417 ∧
      (o.1.val : Int) = (Spec.Decompose sp ((r.val : Nat) : Zq)).1 ∧
      (o.2.val : Int) = (Spec.Decompose sp ((r.val : Nat) : Zq)).2 % (Spec.q : Int) ∧
      -(sp.γ₂ : Int) ≤ (Spec.Decompose sp ((r.val : Nat) : Zq)).2 ∧
      (Spec.Decompose sp ((r.val : Nat) : Zq)).2 ≤ sp.γ₂ ⦄ := by
  rcases gamma2_consts hp hg with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
  · apply WP.spec_mono (decompose_44 sp ip h1 h2 h3 h4 h5 r hr)
    intro o ho
    simp only [Spec.Params.m, h5, Spec.q] at ho ⊢
    exact ho
  · apply WP.spec_mono (decompose_65 sp ip h1 h2 h3 h4 h5 r hr)
    intro o ho
    simp only [Spec.Params.m, h5, Spec.q] at ho ⊢
    exact ho


theorem HighBits_eq (sp : Spec.Params) (r : Zq) : Spec.HighBits sp r = (Spec.Decompose sp r).1 := rfl
theorem LowBits_eq (sp : Spec.Params) (r : Zq) : Spec.LowBits sp r = (Spec.Decompose sp r).2 := rfl

/-- **Algorithm 37.** `high_bits r` is the exact `Spec.HighBits` (a value `< m`). -/
theorem high_bits_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (r : U32) (hr : r.val < 8380417) :
    rounding.high_bits ip r ⦃ y => y.val < sp.m ∧ (y.val : Int) = Spec.HighBits sp ((r.val : Nat) : Zq) ⦄ := by
  unfold rounding.high_bits
  step with decompose_spec hp hg r hr as ⟨i, j, h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h3⟩


/-- **Algorithm 38.** `low_bits r` is the canonical residue of `Spec.LowBits`, which lies in `[-γ₂, γ₂]`. -/
theorem low_bits_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (r : U32) (hr : r.val < 8380417) :
    rounding.low_bits ip r ⦃ y => y.val < 8380417 ∧
      (y.val : Int) = Spec.LowBits sp ((r.val : Nat) : Zq) % (Spec.q : Int) ∧
      -(sp.γ₂ : Int) ≤ Spec.LowBits sp ((r.val : Nat) : Zq) ∧
      Spec.LowBits sp ((r.val : Nat) : Zq) ≤ sp.γ₂ ⦄ := by
  unfold rounding.low_bits
  step with decompose_spec hp hg r hr as ⟨i, j, h1, h2, h3, h4, h5, h6⟩
  exact ⟨h2, h4, h5, h6⟩

theorem bne_u32_int (a b : U32) (x y : Int) (ha : (a.val : Int) = x) (hb : (b.val : Int) = y) :
    (a != b) = (x != y) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  constructor
  · intro h h'; apply h; apply UScalar.eq_of_val_eq; omega
  · intro h h'; apply h; subst h'; omega

/-- **Algorithm 39.** `make_hint z r` is exactly `Spec.MakeHint z r`. -/
theorem make_hint_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (z r : U32) (hz : z.val < 8380417)
    (hr : r.val < 8380417) :
    rounding.make_hint ip z r ⦃ b => b = Spec.MakeHint sp ((z.val : Nat) : Zq) ((r.val : Nat) : Zq) ⦄ := by
  unfold rounding.make_hint
  step with high_bits_spec hp hg r hr as ⟨r1, hr1a, hr1b⟩
  step with add_zmod r z hr hz as ⟨i, hia, hib⟩
  step with high_bits_spec hp hg i hia as ⟨v1, hv1a, hv1b⟩
  rw [bne_u32_int r1 v1 _ _ hr1b hv1b, Spec.MakeHint]
  have : ((i.val : Nat) : Zq) = ((r.val : Nat) : Zq) + ((z.val : Nat) : Zq) := hib
  simp only [Spec.HighBits, this]


attribute [step] decompose_spec

theorem uh_fin (sp : Spec.Params) (hsm : sp.m = 44 ∨ sp.m = 16) (hγ : (sp.γ₂ : Int) ≤ 261888)
    (h : Bool) (D1 D2 : Int) (r1 r0 y : Nat) (hr1 : r1 < sp.m) (hD1 : (r1 : Int) = D1)
    (hr0 : r0 < 8380417) (hD2 : (r0 : Int) = D2 % 8380417) (hb1 : -(sp.γ₂ : Int) ≤ D2)
    (hb2 : D2 ≤ sp.γ₂)
    (hy : (h = true ∧ r0 ≠ 0 ∧ r0 ≤ 4190208 ∧ y = (r1 + 1) % sp.m) ∨
          (h = true ∧ ¬ (r0 ≠ 0 ∧ r0 ≤ 4190208) ∧ y = (r1 + sp.m - 1) % sp.m) ∨
          (h = false ∧ y = r1)) :
    y < sp.m ∧ (y : Int) = (if h = true ∧ D2 > 0 then (D1 + 1) % (sp.m : Int)
      else if h = true then (D1 - 1) % (sp.m : Int) else D1) := by
  rcases hsm with hs | hs <;> rw [hs] at hr1 hy ⊢ <;> rcases hy with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  all_goals subst_vars
  all_goals simp only [eq_self, true_and, Bool.false_eq_true, false_and, if_false, if_true]
  all_goals (refine ⟨by omega, ?_⟩)
  all_goals (try split)
  all_goals first | omega | trivial

/-- **Algorithm 40.** `use_hint h r` is the exact `Spec.UseHint h r` (a value `< m`). -/
theorem use_hint_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (h : Bool) (r : U32) (hr : r.val < 8380417) :
    rounding.use_hint ip h r ⦃ y => y.val < sp.m ∧
      (y.val : Int) = Spec.UseHint sp h ((r.val : Nat) : Zq) ⦄ := by
  have hgam : 0 < ip.gamma2.val ∧ ip.gamma2.val ≤ 261888 := by
    rw [hp.gamma2]; rcases hg with h | h <;> rw [h] <;> omega
  have hsm : sp.m = 44 ∨ sp.m = 16 := by
    rcases hg with h | h <;> simp [Spec.Params.m, h, Spec.q]
  have hmv : (8380417 - 1) / (2 * ip.gamma2.val) = sp.m := by
    rw [hp.gamma2]; simp [Spec.Params.m, Spec.q]
  have hγ : (sp.γ₂ : Int) ≤ 261888 := by rcases hg with h | h <;> omega
  unfold rounding.use_hint
  simp only [global_simps]
  step*
  all_goals try scalar_tac
  · have hm : m.val = sp.m := by rw [m_post, i_post1, i1_post]; exact hmv
    have hle : r0.val ≤ i2.val := by scalar_tac
    have hne : r0.val ≠ 0 := fun h0 => by
      have : r0 = 0#u32 := UScalar.eq_of_val_eq (by simpa using h0)
      simp [this] at ‹(r0 != 0#u32) = true›
    have hi2 : i2.val = 4190208 := by rw [i2_post1]; rfl
    rw [UseHint_eq]
    exact uh_fin sp hsm hγ true _ _ r1.val r0.val y.val r1_post1 r1_post3 r1_post2 r1_post4 r1_post5 r1_post6
      (Or.inl ⟨rfl, hne, by omega, by rw [y_post, i3_post, hm]⟩)
  · have hm : m.val = sp.m := by rw [m_post, i_post1, i1_post]; exact hmv
    have hle : ¬ r0.val ≤ i2.val := by scalar_tac
    have hi2 : i2.val = 4190208 := by rw [i2_post1]; rfl
    rw [UseHint_eq]
    exact uh_fin sp hsm hγ true _ _ r1.val r0.val y.val r1_post1 r1_post3 r1_post2 r1_post4 r1_post5 r1_post6
      (Or.inr (Or.inl ⟨rfl, by omega, by rw [y_post, i3_post1, i3_post, hm]⟩))
  · have hm : m.val = sp.m := by rw [m_post, i_post1, i1_post]; exact hmv
    rw [UseHint_eq]
    exact uh_fin sp hsm hγ true _ _ r1.val r0.val y.val r1_post1 r1_post3 r1_post2 r1_post4 r1_post5 r1_post6
      (Or.inr (Or.inl ⟨rfl, fun hh => ‹¬(r0 != 0#u32) = true› (bne_iff_ne.mpr (fun e => hh.1 (by rw [e]; rfl))),
        by rw [y_post, i3_post1, i3_post, hm]⟩))
  · rw [UseHint_eq]
    exact uh_fin sp hsm hγ false _ _ r1.val r0.val r1.val r1_post1 r1_post3 r1_post2 r1_post4 r1_post5 r1_post6
      (Or.inr (Or.inr ⟨rfl, rfl⟩))


/-! ## Coefficientwise loops: a pointwise invariant -/

/-- Loop invariant of the 256-element output loops: `out` is canonical with all entries `< B`, and entry `k`
stores `E k` if `k < j` (already written) and `0` otherwise (the `Array.repeat` initialization). -/
def PInv (out : Array U32 256#usize) (E : Nat → Int) (j B : Nat) : Prop :=
  Canonical out ∧ (∀ x ∈ out.val, x.val < B) ∧ ∀ (k : Nat) (hk : k < 256),
    ((out.val[k]'(by rw [len256 out]; exact hk)).val : Int) = if k < j then E k else 0

theorem PInv_zero (E : Nat → Int) (B : Nat) (hB : 0 < B) : PInv (Array.repeat 256#usize 0#u32) E 0 B := by
  refine ⟨canonical_repeat_zero, ?_, fun k hk => ?_⟩
  · intro x hx
    simp [Array.repeat_val] at hx
    subst hx
    simpa using hB
  · simp only [Array.repeat_val, List.getElem_replicate]
    simp

theorem PInv_set {out : Array U32 256#usize} {E : Nat → Int} {B : Nat} (j : Usize) (y : U32)
    (h : PInv out E j.val B) (hy : y.val < Spec.q) (hyB : y.val < B) (hE : (y.val : Int) = E j.val) :
    PInv (out.set j y) E (j.val + 1) B := by
  refine ⟨canonical_set out j y h.1 hy, ?_, fun k hk => ?_⟩
  · intro x hx
    rw [Array.set_val_eq] at hx
    rcases List.mem_or_eq_of_mem_set hx with hx | hx
    · exact h.2.1 x hx
    · subst hx; exact hyB
  · have hk' : k < (out.set j y).val.length := by rw [len256]; exact hk
    simp only [Array.set_val_eq]
    by_cases hkj : j.val = k
    · subst hkj
      simp [hE]
    · rw [List.getElem_set_ne hkj]
      have := h.2.2 k hk
      rw [this]
      by_cases hlt : k < j.val
      · simp [hlt, show k < j.val + 1 by omega]
      · simp [hlt, show ¬ k < j.val + 1 by omega]

theorem PInv_to_repr {out : Array U32 256#usize} {E : Nat → Int} {B : Nat} {v : RPoly}
    (h : PInv out E 256 B) (hv : ∀ k (hk : k < 256), ((E k : Int) : Zq) = ((v[k] : Int) : Zq)) :
    ReprInt out v := by
  refine ⟨h.1, ?_⟩
  apply Vector.ext
  intro k hk
  rw [toZq_get out k hk]
  simp only [RPoly.toZq, Vector.getElem_map]
  rw [← hv k hk, ← Int.cast_natCast, h.2.2 k hk]
  simp [hk]

theorem StdGamma2.m_le {sp : Spec.Params} (hg : StdGamma2 sp) : sp.m ≤ 44 := by
  rcases hg with h | h <;> simp [Spec.Params.m, h, Spec.q]

theorem StdGamma2.m_pos {sp : Spec.Params} (hg : StdGamma2 sp) : 0 < sp.m := by
  rcases hg with h | h <;> simp [Spec.Params.m, h, Spec.q]

/-- The exact stored values, read off a finished invariant. -/
theorem PInv.get {out : Array U32 256#usize} {E : Nat → Int} {B : Nat} (h : PInv out E 256 B) (k : Nat)
    (hk : k < 256) : ((out.val[k]'(by rw [len256 out]; exact hk)).val : Int) = E k ∧
      (out.val[k]'(by rw [len256 out]; exact hk)).val < B := by
  refine ⟨?_, h.2.1 _ (List.getElem_mem _)⟩
  rw [h.2.2 k hk]; simp [hk]

theorem toZq_getElem!_eq (w : Array U32 256#usize) (k : Nat) (hk : k < 256) :
    (toZq w)[k]! = (toZq w)[k] := by
  rw [getElem!_pos _ _ (by simpa using hk)]

attribute [step] high_bits_spec low_bits_spec use_hint_spec

/-! ### `poly_high_bits` -/

theorem poly_high_bits_loop_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (w : Array U32 256#usize) (hw : Canonical w)
    (out : Array U32 256#usize) (j : Usize) (hj : j.val ≤ 256)
    (hinv : PInv out (fun k => Spec.HighBits sp ((toZq w)[k]!)) j.val sp.m) :
    rounding.poly_high_bits_loop ip w out j ⦃ o =>
      PInv o (fun k => Spec.HighBits sp ((toZq w)[k]!)) 256 sp.m ⦄ := by
  unfold rounding.poly_high_bits_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => PInv p.1 (fun k => Spec.HighBits sp ((toZq w)[k]!)) p.2.val sp.m ∧ p.2.val ≤ 256)
  · rintro ⟨o, j⟩ ⟨hI, hj⟩
    dsimp only at hI hj
    simp only [rounding.poly_high_bits_loop.body]
    split
    · rename_i hlt
      step*
      · rw [i_post2]; exact canon_get hw _
      · have hjlt : j.val < 256 := by scalar_tac
        have hm := StdGamma2.m_le hg
        have hE : (i1.val : Int) = Spec.HighBits sp ((toZq w)[j.val]!) := by
          rw [i1_post2, i_post2, toZq_getElem w j.val i]
        have := PInv_set j i1 hI (by simp only [Spec.q]; omega) i1_post1 hE
        refine ⟨?_, by omega, by omega⟩
        rw [a_post, j1_post]; exact this
    · rename_i hlt
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      rw [this] at hI
      exact hI
  · exact ⟨hinv, hj⟩

/-- **`poly_high_bits`** (Algorithm 37, coefficientwise): the output stores, as exact values `< m`, the high bits
of every coefficient, i.e. `HighBitsVec` on one polynomial. -/
theorem poly_high_bits_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (w : Array U32 256#usize) (v : Poly) (hw : Repr w v) :
    rounding.poly_high_bits ip w ⦃ out => ReprInt out (v.map (Spec.HighBits sp)) ∧
      ∀ (k : Nat) (hk : k < 256), ((out.val[k]'(by rw [len256 out]; exact hk)).val : Int) =
        Spec.HighBits sp v[k] ∧ (out.val[k]'(by rw [len256 out]; exact hk)).val < sp.m ⦄ := by
  obtain ⟨hc, hv⟩ := hw
  unfold rounding.poly_high_bits
  apply WP.spec_mono (poly_high_bits_loop_spec hp hg w hc _ 0#usize (by simp)
    (by simpa using PInv_zero _ sp.m (StdGamma2.m_pos hg)))
  intro out hout
  rw [← hv]
  refine ⟨PInv_to_repr hout (fun k hk => ?_), fun k hk => ?_⟩
  · simp only [Vector.getElem_map, toZq_getElem!_eq w k hk]
  · have := hout.get k hk
    rw [toZq_getElem!_eq w k hk] at this
    exact this


/-! ### `poly_low_bits` -/

theorem poly_low_bits_loop_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (w : Array U32 256#usize) (hw : Canonical w)
    (out : Array U32 256#usize) (j : Usize) (hj : j.val ≤ 256)
    (hinv : PInv out (fun k => Spec.LowBits sp ((toZq w)[k]!) % (Spec.q : Int)) j.val Spec.q) :
    rounding.poly_low_bits_loop ip w out j ⦃ o =>
      PInv o (fun k => Spec.LowBits sp ((toZq w)[k]!) % (Spec.q : Int)) 256 Spec.q ⦄ := by
  unfold rounding.poly_low_bits_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => PInv p.1 (fun k => Spec.LowBits sp ((toZq w)[k]!) % (Spec.q : Int)) p.2.val Spec.q ∧
      p.2.val ≤ 256)
  · rintro ⟨o, j⟩ ⟨hI, hj⟩
    dsimp only at hI hj
    simp only [rounding.poly_low_bits_loop.body]
    split
    · rename_i hlt
      step*
      · rw [i_post2]; exact canon_get hw _
      · have hjlt : j.val < 256 := by scalar_tac
        have hE : (i1.val : Int) = Spec.LowBits sp ((toZq w)[j.val]!) % (Spec.q : Int) := by
          rw [i1_post2, i_post2, toZq_getElem w j.val i]
        have := PInv_set j i1 hI i1_post1 i1_post1 hE
        refine ⟨?_, by omega, by omega⟩
        rw [a_post, j1_post]; exact this
    · rename_i hlt
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      rw [this] at hI
      exact hI
  · exact ⟨hinv, hj⟩

/-- **`poly_low_bits`** (Algorithm 38, coefficientwise): the output stores the residue mod `q` of the (signed)
low bits of every coefficient, i.e. `LowBitsVec` on one polynomial. -/
theorem poly_low_bits_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (w : Array U32 256#usize) (v : Poly) (hw : Repr w v) :
    rounding.poly_low_bits ip w ⦃ out => ReprInt out (v.map (Spec.LowBits sp)) ∧
      ∀ (k : Nat) (hk : k < 256), ((out.val[k]'(by rw [len256 out]; exact hk)).val : Int) =
        Spec.LowBits sp v[k] % (Spec.q : Int) ⦄ := by
  obtain ⟨hc, hv⟩ := hw
  unfold rounding.poly_low_bits
  apply WP.spec_mono (poly_low_bits_loop_spec hp hg w hc _ 0#usize (by simp)
    (by simpa using PInv_zero _ Spec.q (by simp [Spec.q])))
  intro out hout
  rw [← hv]
  refine ⟨PInv_to_repr hout (fun k hk => ?_), fun k hk => ?_⟩
  · simp only [Vector.getElem_map, toZq_getElem!_eq w k hk]
    exact ZMod.intCast_mod _ _
  · have := (hout.get k hk).1
    rw [toZq_getElem!_eq w k hk] at this
    exact this

/-! ### `poly_use_hint` -/

theorem toHint_getElem! (a : Array Bool 256#usize) (k : Nat) (hk : k < a.val.length) :
    (toHint a)[k]! = a.val[k] := by
  have h256 : a.val.length = 256 := a.property
  have hk' : k < 256 := by omega
  rw [getElem!_pos _ _ (by simpa using hk')]
  simp [toHint]

theorem poly_use_hint_loop_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (h : Array Bool 256#usize) (r : Array U32 256#usize)
    (hr : Canonical r) (out : Array U32 256#usize) (j : Usize) (hj : j.val ≤ 256)
    (hinv : PInv out (fun k => Spec.UseHint sp ((toHint h)[k]!) ((toZq r)[k]!)) j.val sp.m) :
    rounding.poly_use_hint_loop ip h r out j ⦃ o =>
      PInv o (fun k => Spec.UseHint sp ((toHint h)[k]!) ((toZq r)[k]!)) 256 sp.m ⦄ := by
  unfold rounding.poly_use_hint_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => PInv p.1 (fun k => Spec.UseHint sp ((toHint h)[k]!) ((toZq r)[k]!)) p.2.val sp.m ∧
      p.2.val ≤ 256)
  · rintro ⟨o, j⟩ ⟨hI, hj⟩
    dsimp only at hI hj
    simp only [rounding.poly_use_hint_loop.body]
    split
    · rename_i hlt
      step*
      · rw [i_post2]; exact canon_get hr _
      · have hjlt : j.val < 256 := by scalar_tac
        have hm := StdGamma2.m_le hg
        have hE : (i1.val : Int) =
            Spec.UseHint sp ((toHint h)[j.val]!) ((toZq r)[j.val]!) := by
          rw [i1_post2, i_post2, b_post2, toZq_getElem r j.val i, toHint_getElem! h j.val b]
        have := PInv_set j i1 hI (by simp only [Spec.q]; omega) i1_post1 hE
        refine ⟨?_, by omega, by omega⟩
        rw [a_post, j1_post]; exact this
    · rename_i hlt
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      rw [this] at hI
      exact hI
  · exact ⟨hinv, hj⟩


/-- **`poly_use_hint`** (Algorithm 40, coefficientwise): the output stores, as exact values `< m`, `UseHint(h, r)`
on every coefficient, i.e. `UseHintVec` on one polynomial. -/
theorem poly_use_hint_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp) (h : Array Bool 256#usize) (hv : HintPoly)
    (hh : ReprHint h hv) (r : Array U32 256#usize) (v : Poly) (hr : Repr r v) :
    rounding.poly_use_hint ip h r ⦃ out => ReprInt out (Vector.zipWith (Spec.UseHint sp) hv v) ∧
      ∀ (k : Nat) (hk : k < 256), ((out.val[k]'(by rw [len256 out]; exact hk)).val : Int) =
        Spec.UseHint sp hv[k] v[k] ∧ (out.val[k]'(by rw [len256 out]; exact hk)).val < sp.m ⦄ := by
  obtain ⟨hc, hvr⟩ := hr
  unfold rounding.poly_use_hint
  apply WP.spec_mono (poly_use_hint_loop_spec hp hg h r hc _ 0#usize (by simp)
    (by simpa using PInv_zero _ sp.m (StdGamma2.m_pos hg)))
  intro out hout
  rw [← hvr, ← (hh : toHint h = hv)]
  have key : ∀ k (hk : k < 256), (toHint h)[k]! = (toHint h)[k] ∧ (toZq r)[k]! = (toZq r)[k] :=
    fun k hk => ⟨by rw [getElem!_pos _ _ (by simpa using hk)], toZq_getElem!_eq r k hk⟩
  refine ⟨PInv_to_repr hout (fun k hk => ?_), fun k hk => ?_⟩
  · simp only [Vector.getElem_zipWith, (key k hk).1, (key k hk).2]
  · have := hout.get k hk
    rw [(key k hk).1, (key k hk).2] at this
    simpa only [Vector.getElem_zipWith] using this

/-! ### `poly_power2round` -/

theorem poly_power2round_loop_spec {sp : Spec.Params} (hd : sp.d = 13) (t : Array U32 256#usize)
    (ht : Canonical t) (t1 t0 : Array U32 256#usize) (j : Usize) (hj : j.val ≤ 256)
    (hinv1 : PInv t1 (fun k => (Spec.Power2Round sp ((toZq t)[k]!)).1) j.val 1024)
    (hinv0 : PInv t0 (fun k => (Spec.Power2Round sp ((toZq t)[k]!)).2 % (Spec.q : Int)) j.val Spec.q) :
    rounding.poly_power2round_loop t t1 t0 j ⦃ o =>
      PInv o.1 (fun k => (Spec.Power2Round sp ((toZq t)[k]!)).1) 256 1024 ∧
      PInv o.2 (fun k => (Spec.Power2Round sp ((toZq t)[k]!)).2 % (Spec.q : Int)) 256 Spec.q ⦄ := by
  unfold rounding.poly_power2round_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Array U32 256#usize × Usize) => 256 - p.2.2.val)
    (fun p => PInv p.1 (fun k => (Spec.Power2Round sp ((toZq t)[k]!)).1) p.2.2.val 1024 ∧
      PInv p.2.1 (fun k => (Spec.Power2Round sp ((toZq t)[k]!)).2 % (Spec.q : Int)) p.2.2.val Spec.q ∧
      p.2.2.val ≤ 256)
  · rintro ⟨o1, o0, j⟩ ⟨hI1, hI0, hj⟩
    dsimp only at hI1 hI0 hj
    simp only [rounding.poly_power2round_loop.body]
    split
    · rename_i hlt
      step*
      rename_i x
      have hxq : x.val < 8380417 := by rw [i_post2]; exact canon_get ht _
      step with power2round_spec sp hd x hxq as ⟨a, b, h1, h2, h3, h4⟩
      step*
      have hjlt : j.val < 256 := by scalar_tac
      have hE : (toZq t)[j.val]! = ((x.val : Nat) : Zq) := by rw [i_post2]; exact toZq_getElem t j.val i
      have e1 := PInv_set j a hI1 (by simp only [Spec.q]; omega) h1 (by rw [h3, hE])
      have e0 := PInv_set j b hI0 h2 h2 (by rw [h4, hE])
      refine ⟨?_, ?_, by omega, by omega⟩
      · rw [a1_post, j1_post]; exact e1
      · rw [a2_post, j1_post]; exact e0
    · rename_i hlt
      simp only [WP.spec_ok]
      have : j.val = 256 := by scalar_tac
      rw [this] at hI1 hI0
      exact ⟨hI1, hI0⟩
  · exact ⟨hinv1, hinv0, hj⟩


/-- **`poly_power2round`** (Algorithm 35, coefficientwise): `t1` stores the exact `r₁ < 2^10`, and `t0` the residue
mod `q` of the signed `r₀`; i.e. the two components of `Power2RoundVec` on one polynomial. -/
theorem poly_power2round_spec {sp : Spec.Params} (hd : sp.d = 13) (t : Array U32 256#usize) (v : Poly)
    (ht : Repr t v) :
    rounding.poly_power2round t ⦃ o =>
      ReprInt o.1 (v.map (fun c => (Spec.Power2Round sp c).1)) ∧
      ReprInt o.2 (v.map (fun c => (Spec.Power2Round sp c).2)) ∧
      ∀ (k : Nat) (hk : k < 256),
        ((o.1.val[k]'(by rw [len256 o.1]; exact hk)).val : Int) = (Spec.Power2Round sp v[k]).1 ∧
        (o.1.val[k]'(by rw [len256 o.1]; exact hk)).val < 1024 ∧
        ((o.2.val[k]'(by rw [len256 o.2]; exact hk)).val : Int) = (Spec.Power2Round sp v[k]).2 % (Spec.q : Int) ⦄ := by
  obtain ⟨hc, hv⟩ := ht
  unfold rounding.poly_power2round
  apply WP.spec_mono (poly_power2round_loop_spec hd t hc _ _ 0#usize (by simp)
    (by simpa using PInv_zero _ 1024 (by decide)) (by simpa using PInv_zero _ Spec.q (by simp [Spec.q])))
  rintro ⟨o1, o0⟩ ⟨h1, h0⟩
  rw [← hv]
  refine ⟨PInv_to_repr h1 (fun k hk => ?_), PInv_to_repr h0 (fun k hk => ?_), fun k hk => ?_⟩
  · simp only [Vector.getElem_map, toZq_getElem!_eq t k hk]
  · simp only [Vector.getElem_map, toZq_getElem!_eq t k hk]
    exact ZMod.intCast_mod _ _
  · have a1 := h1.get k hk
    have a0 := h0.get k hk
    rw [toZq_getElem!_eq t k hk] at a1 a0
    exact ⟨a1.1, a1.2, a0.1⟩


/-! ## The hypotheses are satisfiable -/

theorem rounding_hypotheses_ML_DSA_44 :
    ∃ ip, params.ML_DSA_44 = ok ip ∧ Params.Valid ip 4#usize 4#usize Spec.ML_DSA_44 ∧
      StdGamma2 Spec.ML_DSA_44 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_44_valid
  exact ⟨ip, h, hv, stdGamma2_44⟩

theorem rounding_hypotheses_ML_DSA_65 :
    ∃ ip, params.ML_DSA_65 = ok ip ∧ Params.Valid ip 6#usize 5#usize Spec.ML_DSA_65 ∧
      StdGamma2 Spec.ML_DSA_65 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_65_valid
  exact ⟨ip, h, hv, stdGamma2_65⟩

theorem rounding_hypotheses_ML_DSA_87 :
    ∃ ip, params.ML_DSA_87 = ok ip ∧ Params.Valid ip 8#usize 7#usize Spec.ML_DSA_87 ∧
      StdGamma2 Spec.ML_DSA_87 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_87_valid
  exact ⟨ip, h, hv, stdGamma2_87⟩

end Proofs

