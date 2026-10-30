import Proofs.Repr
import Spec.Sampling

/-!
# Coefficient decoders: the extracted Rust equals FIPS 204 Algorithms 14 and 15

* `coeff_from_three_bytes` (Algorithm 14) returns `Option U32`; the spec returns `Option Zq`. The statement
  compares the integer values: `r.map (·.val) = (Spec.CoeffFromThreeBytes …).map ZMod.val`. It is proved
  arithmetically (the bit twiddling `(b₂ & 127) << 16 | b₁ << 8 | b₀` is a sum, see `or3_nat`), not by
  enumerating the 2^24 inputs.
* `coeff_from_half_byte` (Algorithm 15) returns `Option U32` holding the canonical residue mod `q` of a value in
  `{-η, …, η}`; the spec returns `Option Int`. They are related by `OptCoeff`: both `none`, or both `some` with
  `x.val < q` and `x ≡ c (mod q)`.
  Premise: `Spec.Params` does not restrict `η`, and the Rust code treats every `η ≠ 2` as `η = 4`, so the
  statement needs `sp.η = 2 ∨ sp.η = 4` (true for the three standard sets). No bound on `b` is needed
  (`b ≥ 15`, `b ≥ 9` are rejections on both sides).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Algorithm 14 -/

theorem or3_nat (x y w : Nat) (hx : x < 128) (hy : y < 256) (hw : w < 256) :
    ((x <<< 16) ||| (y <<< 8)) ||| w = x * 65536 + y * 256 + w := by
  have h1 := Nat.shiftLeft_add_eq_or_of_lt (i := 8) (b := w) (by omega) y
  have h2 := Nat.shiftLeft_add_eq_or_of_lt (i := 16) (b := (y <<< 8) + w)
    (by rw [Nat.shiftLeft_eq]; omega) x
  rw [Nat.or_assoc, ← h1, ← h2]
  simp only [Nat.shiftLeft_eq]
  omega

/-- The pure form of Algorithm 14. -/
theorem CoeffFromThreeBytes_eq (b0 b1 b2 : UInt8) :
    Spec.CoeffFromThreeBytes b0 b1 b2 =
      if 2 ^ 16 * (b2.toNat % 128) + 2 ^ 8 * b1.toNat + b0.toNat < Spec.q then
        some (((2 ^ 16 * (b2.toNat % 128) + 2 ^ 8 * b1.toNat + b0.toNat : Nat)) : Zq)
      else none := by
  have hb2 : b2.toNat < 256 := b2.toNat_lt
  unfold Spec.CoeffFromThreeBytes
  by_cases h : b2.toNat > 127
  · have e : b2.toNat - 128 = b2.toNat % 128 := by omega
    simp [h, e]
    split <;> rfl
  · have e : b2.toNat = b2.toNat % 128 := by omega
    simp [h, ← e]
    split <;> rfl

theorem three_val (b0 b1 b2 : U8) (i1 i3 : U32)
    (h1 : i1.val = (UScalar.cast UScalarTy.U32 (b2 &&& 127#u8)).val <<< 16 % U32.size)
    (h3 : i3.val = (UScalar.cast UScalarTy.U32 b1).val <<< 8 % U32.size) :
    (i1 ||| i3 ||| UScalar.cast UScalarTy.U32 b0).val = 2 ^ 16 * (b2.val % 128) + 2 ^ 8 * b1.val + b0.val := by
  have hb0 : b0.val < 256 := by scalar_tac
  have hb1 : b1.val < 256 := by scalar_tac
  have hb2 : b2.val < 256 := by scalar_tac
  have hm : b2.val &&& 127 = b2.val % 128 := by
    have := Nat.and_two_pow_sub_one_eq_mod b2.val 7
    simpa using this
  have hA : (UScalar.cast UScalarTy.U32 (b2 &&& 127#u8)).val = b2.val % 128 := by
    simp [UScalar.cast_val_eq, hm]
    omega
  have hB : (UScalar.cast UScalarTy.U32 b1).val = b1.val := by
    simp [UScalar.cast_val_eq]
    omega
  have hC : (UScalar.cast UScalarTy.U32 b0).val = b0.val := by
    simp [UScalar.cast_val_eq]
    omega
  have hsz : U32.size = 4294967296 := by
    first | scalar_tac | simp [U32.size_def, U32.numBits] | norm_num [U32.size_def, U32.numBits]
  have e1 : i1.val = (b2.val % 128) * 65536 := by
    rw [h1, hA, Nat.shiftLeft_eq, hsz]
    omega
  have e3 : i3.val = b1.val * 256 := by
    rw [h3, hB, Nat.shiftLeft_eq, hsz]
    omega
  rw [UScalar.val_or, UScalar.val_or, hC]
  have := or3_nat (b2.val % 128) b1.val b0.val (by omega) hb1 hb0
  have e1' : i1.val = (b2.val % 128) <<< 16 := by rw [e1, Nat.shiftLeft_eq]
  have e3' : i3.val = b1.val <<< 8 := by rw [e3, Nat.shiftLeft_eq]
  rw [e1', e3', this]
  omega

theorem t0 (b : U8) (hb : b.val < 256) : (UInt8.ofNat b.val).toNat = b.val := by
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt hb]

@[step]
theorem coeff_from_three_bytes_spec (b0 b1 b2 : U8) :
    sampling.coeff_from_three_bytes b0 b1 b2 ⦃ r =>
      r.map (·.val) = (Spec.CoeffFromThreeBytes (UInt8.ofNat b0.val) (UInt8.ofNat b1.val)
        (UInt8.ofNat b2.val)).map ZMod.val ⦄ := by
  have hb0 : b0.val < 256 := by scalar_tac
  have hb1 : b1.val < 256 := by scalar_tac
  have hb2 : b2.val < 256 := by scalar_tac
  unfold sampling.coeff_from_three_bytes
  simp only [global_simps, lift, bind_tc_ok]
  step*
  · rename_i hlt
    have hz := three_val b0 b1 b2 _ _ i1_post1 i3_post1
    have hq : 2 ^ 16 * (b2.val % 128) + 2 ^ 8 * b1.val + b0.val < 8380417 := by
      rw [← hz]; scalar_tac
    rw [CoeffFromThreeBytes_eq, t0 b0 hb0, t0 b1 hb1, t0 b2 hb2, if_pos (by unfold Spec.q; omega)]
    simp only [Option.map_some, hz, ZMod.val_natCast, Nat.mod_eq_of_lt (show _ < 8380417 from hq)]
  · rename_i hlt
    have hz := three_val b0 b1 b2 _ _ i1_post1 i3_post1
    have hq : ¬ (2 ^ 16 * (b2.val % 128) + 2 ^ 8 * b1.val + b0.val < 8380417) := by
      rw [← hz]; scalar_tac
    rw [CoeffFromThreeBytes_eq, t0 b0 hb0, t0 b1 hb1, t0 b2 hb2, if_neg (by unfold Spec.q; omega)]
    rfl

/-! ## Algorithm 15 -/

/-- `x` is the canonical residue mod `q` of the integer `c`. -/
def CoeffRel (x : U32) (c : Int) : Prop := x.val < Spec.q ∧ ((x.val : Nat) : Zq) = (c : Zq)

/-- Rust `Option U32` against spec `Option Int`: both `none`, or both `some` and related by `CoeffRel`. -/
def OptCoeff : Option U32 → Option Int → Prop
  | none, none => True
  | some x, some c => CoeffRel x c
  | _, _ => False

@[step]
theorem coeff_from_half_byte_spec {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (b : U8) :
    sampling.coeff_from_half_byte ip b ⦃ r => OptCoeff r (Spec.CoeffFromHalfByte sp.η b.val) ⦄ := by
  have hbv : b.val < 256 := by scalar_tac
  have he := hp.eta
  unfold sampling.coeff_from_half_byte
  by_cases h2 : ip.eta = 2#u32
  · have hs : sp.η = 2 := by rw [h2] at he; simpa using he.symm
    simp only [h2, ↓reduceIte]
    by_cases hb : b < 15#u8
    · have hb' : b.val < 15 := by scalar_tac
      simp only [hb, ↓reduceIte]
      step*
      have hi1 : i1.val = b.val % 5 := by
        rw [i1_post]; simp [UScalar.cast_val_eq, i_post]; omega
      have hc : Spec.CoeffFromHalfByte sp.η b.val = some (2 - ((b.val % 5 : Nat) : Int)) := by
        simp [Spec.CoeffFromHalfByte, hs, hb']
      rw [hc]
      refine ⟨i2_post1, ?_⟩
      rw [i2_post2, hi1]
      simp
      first
        | done
        | rw [show (((b.val : Nat) : Int) % 5) = ((b.val % 5 : Nat) : Int) by omega, Int.cast_natCast]
    · have hb' : ¬ b.val < 15 := by scalar_tac
      simp only [hb, ↓reduceIte, WP.spec_ok]
      simp [OptCoeff, Spec.CoeffFromHalfByte, hs, hb']
  · have hs : sp.η = 4 := by
      rcases hη with h | h
      · exfalso; apply h2; apply UScalar.eq_of_val_eq; rw [he, h]; rfl
      · exact h
    simp only [h2, ↓reduceIte]
    by_cases hb : b < 9#u8
    · have hb' : b.val < 9 := by scalar_tac
      simp only [hb, ↓reduceIte]
      step*
      have hi : i.val = b.val := by
        rw [i_post]; simp [UScalar.cast_val_eq]; omega
      have hc : Spec.CoeffFromHalfByte sp.η b.val = some (4 - (b.val : Int)) := by
        simp [Spec.CoeffFromHalfByte, hs, hb']
      rw [hc]
      refine ⟨i1_post1, ?_⟩
      rw [i1_post2, hi]
      simp
    · have hb' : ¬ b.val < 9 := by scalar_tac
      simp only [hb, ↓reduceIte, WP.spec_ok]
      simp [OptCoeff, Spec.CoeffFromHalfByte, hs, hb']

theorem coeff_from_three_bytes_correct (b0 b1 b2 : U8) :
    ∃ r, sampling.coeff_from_three_bytes b0 b1 b2 = ok r ∧
      r.map (·.val) = (Spec.CoeffFromThreeBytes (UInt8.ofNat b0.val) (UInt8.ofNat b1.val)
        (UInt8.ofNat b2.val)).map ZMod.val :=
  WP.spec_imp_exists (coeff_from_three_bytes_spec b0 b1 b2)

theorem coeff_from_half_byte_correct {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (b : U8) :
    ∃ r, sampling.coeff_from_half_byte ip b = ok r ∧ OptCoeff r (Spec.CoeffFromHalfByte sp.η b.val) :=
  WP.spec_imp_exists (coeff_from_half_byte_spec hp hη b)

end Proofs
