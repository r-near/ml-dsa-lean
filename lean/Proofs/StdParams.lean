import Proofs.Repr
import Proofs.RoundingArith
import Proofs.SigCodec
import Proofs.SampleBall

/-!
# The standard-parameter premises, bundled

The leaf refinement proofs take, besides `Params.Valid ip K L sp`, a handful of premises on the spec parameter
set `sp` that `Params.Valid` does not pin down (they hold for ML-DSA-44/65/87 but not for an arbitrary
`Spec.Params`). `StdParams sp` bundles all of them, one field each, so that a composition proof (KeyGen, Sign,
Verify) carries one hypothesis `hs : StdParams sp` and feeds every leaf theorem with the derived lemma that has
exactly the form the leaf takes (`hs.stdGamma2`, `hs.stdSig`, `hs.eta`, ...).

`Params.Std ip K L sp` is the canonical bundle `Params.Valid ip K L sp ∧ StdParams sp`; the three standard sets
satisfy it (`ML_DSA_44_std`, `ML_DSA_65_std`, `ML_DSA_87_std`), and `stdParams_44/65/87` show the premise
alone.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-- The parameter premises of the leaf theorems, bundled. -/
structure StdParams (sp : Spec.Params) : Prop where
  /-- `d = 13`: `power2round_spec`, `poly_power2round_spec`, `scale_by_2d_spec`, `vec_power2round_spec`,
  `t1Bits_eq`, `skLen_eq` and their loops (Rounding, EncodeKeys, Steps). -/
  d_eq : sp.d = 13
  /-- `γ₂ ∈ {95232, 261888}`: every rounding, `HighBits`, `UseHint`, `MakeHint` step and the Steps module
  (`StdGamma2`, RoundingArith). -/
  gamma2 : sp.γ₂ = 95232 ∨ sp.γ₂ = 261888
  /-- `γ₁ ∈ {2^17, 2^19}`: `expand_mask_range` and `ExpandMask` (ExpandMask), and the first half of `StdSig`. -/
  gamma1 : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19
  /-- `λ/4 ≤ 64`: the `c̃` buffer of `sig_encode` / `sig_decode` is 64 bytes (second half of `StdSig`, SigCodec). -/
  lam_le : sp.lam / 4 ≤ 64
  /-- `η ∈ {2, 4}`: coefficient decoding, `RejBoundedPoly`, `ExpandS` (Coeff, SampleS) and the key codec
  (EncodeKeys). -/
  eta : sp.η = 2 ∨ sp.η = 4
  /-- `τ ≤ 64`: the sign word of `sample_in_ball` is a `u64` (SampleBall). -/
  tau_le : sp.τ ≤ 64
  /-- `k + ℓ < 256`: the nonce `IntegerToBytes (k + ℓ)` of `ExpandS` fits a byte (SampleS). -/
  kl_lt : sp.k + sp.ℓ < 256
  /-- `k ≤ 2^20`: the loop counters of the `Steps` module (compute `t`, `w`, hint steps). -/
  k_le : sp.k ≤ 2 ^ 20
  /-- `k ≤ 8`: Verify keeps `w1Encode(w′₁)` in a fixed `8 · 192`-byte buffer (Verify). -/
  k_le_8 : sp.k ≤ 8
  /-- `ℓ ≥ 1`: Sign's κ loop tests `κ + ℓ − 1 ≤ 2¹⁶ − 1` and must advance (Sign). -/
  ell_pos : 1 ≤ sp.ℓ

namespace StdParams
variable {sp : Spec.Params}

/-- `d = 13`, in the form of `power2round_spec`, `scale_by_2d_spec`, `t1Bits_eq`, ... -/
theorem d (h : StdParams sp) : sp.d = 13 := h.d_eq

/-- In the form of the `hg` hypothesis of the rounding and Steps theorems. -/
theorem stdGamma2 (h : StdParams sp) : StdGamma2 sp := h.gamma2

/-- In the form of the `hs` hypothesis of the `SigCodec` theorems. -/
theorem stdSig (h : StdParams sp) : StdSig sp := ⟨h.gamma1, h.lam_le⟩

/-- In the form of the `hγ` hypothesis of `expand_mask_range` and `expand_mask_spec`. -/
theorem gamma₁ (h : StdParams sp) : sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19 := h.gamma1

/-- In the form of the `hη` hypothesis of Coeff and SampleS. -/
theorem eta' (h : StdParams sp) : sp.η = 2 ∨ sp.η = 4 := h.eta

/-- In the form of the `hη` hypothesis of EncodeKeys (`skEncode` / `skDecode`). -/
theorem eta_lt (h : StdParams sp) : 2 * sp.η < 2 ^ 22 := by
  rcases h.eta with e | e <;> rw [e] <;> norm_num

/-- In the form of the `hτ` hypothesis of `sample_in_ball_spec`. -/
theorem tau (h : StdParams sp) : sp.τ ≤ 64 := h.tau_le

/-- In the form of the `hKL` hypothesis of SampleS. -/
theorem kl (h : StdParams sp) : sp.k + sp.ℓ < 256 := h.kl_lt

/-- In the form of the `hK` hypothesis of the Steps theorems. -/
theorem k_le' (h : StdParams sp) : sp.k ≤ 2 ^ 20 := h.k_le

/-- `τ ≤ 256`, the hypothesis of the pure `SampleInBall_*` lemmas. -/
theorem tau_le_256 (h : StdParams sp) : sp.τ ≤ 256 := by have := h.tau_le; omega

/-- The `c̃` length bound in the Rust side's terms: `ip.c_tilde_len ≤ 64` (`sig_decode` loops). -/
theorem c_tilde_len_le {ip : Impl.params.Params} {K L : Usize} (h : StdParams sp)
    (hp : Params.Valid ip K L sp) : ip.c_tilde_len.val ≤ 64 := by
  rw [hp.c_tilde_len]; exact h.lam_le

end StdParams

/-! ## The three standard sets -/

theorem stdParams_44 : StdParams Spec.ML_DSA_44 :=
  ⟨by decide +kernel, Or.inl (by decide +kernel), Or.inl (by decide +kernel), by decide +kernel,
    Or.inl (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem stdParams_65 : StdParams Spec.ML_DSA_65 :=
  ⟨by decide +kernel, Or.inr (by decide +kernel), Or.inr (by decide +kernel), by decide +kernel,
    Or.inr (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem stdParams_87 : StdParams Spec.ML_DSA_87 :=
  ⟨by decide +kernel, Or.inr (by decide +kernel), Or.inr (by decide +kernel), by decide +kernel,
    Or.inl (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The canonical bundle -/

/-- The extracted parameter record is the spec set `sp` (`Params.Valid`) and `sp` satisfies the leaf premises
(`StdParams`). Composition proofs take `hp : Params.Std ip K L sp`. -/
def Params.Std (ip : Impl.params.Params) (K L : Usize) (sp : Spec.Params) : Prop :=
  Params.Valid ip K L sp ∧ StdParams sp

theorem Params.Std.valid {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params} (h : Params.Std ip K L sp) :
    Params.Valid ip K L sp := h.1

theorem Params.Std.params {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params} (h : Params.Std ip K L sp) :
    StdParams sp := h.2

/-- Satisfiability witness for `Params.Std`: ML-DSA-44. -/
theorem ML_DSA_44_std :
    ∃ ip, params.ML_DSA_44 = ok ip ∧ Params.Std ip 4#usize 4#usize Spec.ML_DSA_44 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_44_valid
  exact ⟨ip, h, hv, stdParams_44⟩

/-- Satisfiability witness for `Params.Std`: ML-DSA-65. -/
theorem ML_DSA_65_std :
    ∃ ip, params.ML_DSA_65 = ok ip ∧ Params.Std ip 6#usize 5#usize Spec.ML_DSA_65 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_65_valid
  exact ⟨ip, h, hv, stdParams_65⟩

/-- Satisfiability witness for `Params.Std`: ML-DSA-87. -/
theorem ML_DSA_87_std :
    ∃ ip, params.ML_DSA_87 = ok ip ∧ Params.Std ip 8#usize 7#usize Spec.ML_DSA_87 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_87_valid
  exact ⟨ip, h, hv, stdParams_87⟩

end Proofs
