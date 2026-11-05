import Proofs.TopWitnessKG
import Proofs.TopWitnessNf2
import Proofs.TopWitnessNc1
import Proofs.TopWitnessNc2
import Proofs.TopWitnessNc3

/-!
# `Spec.Sign` returns `some` on the witness key (ML-DSA-44, `ξ = 0, 1, ..., 31`, `rnd = 0^32`, `M = [0]`, `ctx = []`)

By `Sign.sign_isSome_iff` the spec returns `some` iff `ExpandA` succeeds and some attempt `a` is accepted with
attempts `0..a-1` rejected. Here `a = 0`: the first attempt is accepted. Its value is chained through the kernel
stage lemmas (`Nf2`, `Nc1`-`Nc3`, `Misc`), each `spec piece literal = literal`, by rewriting.
-/

open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Proofs
namespace TopWitness

theorem skDecode_lit :
    Spec.skDecode Spec.ML_DSA_44 skL = (rhoS, Data.kL, Data.trL, S1v, S2v, T0v) := by
  apply Corr.skDecode_skEncode Spec.ML_DSA_44 rfl rhoS Data.kL Data.trL (by decide +kernel) (by decide +kernel)
    (by decide +kernel) S1v S2v T0v
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- The data of Algorithm 7, steps 1-7, for the witness key. -/
def P0 : Sign.Pre Spec.ML_DSA_44 := ⟨S1v, S2v, T0v, Av, Data.muL, Data.rho2L⟩

theorem pre_eq_of (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd ρ K tr : List UInt8) (s₁ : Vector RPoly sp.ℓ)
    (s₂ t₀ : Vector RPoly sp.k) (Â : Vector (Vector Poly sp.ℓ) sp.k)
    (hd : Spec.skDecode sp sk = (ρ, K, tr, s₁, s₂, t₀)) (hA : Spec.ExpandA sp F.rejNTT ρ = some Â) :
    Sign.pre sp F sk M' rnd = some ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩ := by
  unfold Sign.pre
  rw [hd]
  dsimp only
  rw [hA]

theorem pre_lit :
    Sign.pre Spec.ML_DSA_44 {} skL [0, 0, 0] (List.replicate 32 0) = some P0 := by
  have h := pre_eq_of Spec.ML_DSA_44 {} skL [0, 0, 0] (List.replicate 32 0) _ _ _ _ _ _ _ skDecode_lit expandA_lit
  rw [mu_lit, rho2_lit] at h
  exact h

theorem ntt_s2_lit : Spec.NTTVec (S2v.map RPoly.toZq) = S2hv := by
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTVec, Vector.getElem_map]
  interval_cases i
  · exact nttF_s2_0
  · exact nttF_s2_1
  · exact nttF_s2_2
  · exact nttF_s2_3

theorem ntt_t0_lit : Spec.NTTVec (T0v.map RPoly.toZq) = T0hv := by
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTVec, Vector.getElem_map]
  interval_cases i
  · exact nttF_t0_0
  · exact nttF_t0_1
  · exact nttF_t0_2
  · exact nttF_t0_3

theorem ntt_y_lit : Spec.NTTVec Yv = Yhv := by
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTVec, Vector.getElem_map]
  interval_cases i
  · exact nttF_y_0
  · exact nttF_y_1
  · exact nttF_y_2
  · exact nttF_y_3

theorem intt_w_lit : Spec.NTTInvVec WMVv = Wv := by
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTInvVec, Vector.getElem_map]
  interval_cases i
  · exact nttI_w_0
  · exact nttI_w_1
  · exact nttI_w_2
  · exact nttI_w_3

theorem maskAt_get (sp : Spec.Params) (P : Sign.Pre sp) (κ i : Nat) (hi : i < sp.ℓ) :
    (Sign.maskAt sp P κ)[i] = RPoly.toZq (maskPoly sp P.ρ'' κ i) := by
  unfold Sign.maskAt
  rw [Vector.getElem_map, ExpandMask_get _ _ _ i hi]

theorem maskAt_lit : Sign.maskAt Spec.ML_DSA_44 P0 0 = Yv := by
  apply Vector.ext
  intro i hi
  rw [maskAt_get _ _ _ i hi]
  have h4 : i < 4 := hi
  interval_cases i
  · show RPoly.toZq (maskPoly Spec.ML_DSA_44 Data.rho2L 0 0) = Pl Data.y_0
    rw [maskPoly_fast, yb_0]; exact mask_0
  · show RPoly.toZq (maskPoly Spec.ML_DSA_44 Data.rho2L 0 1) = Pl Data.y_1
    rw [maskPoly_fast, yb_1]; exact mask_1
  · show RPoly.toZq (maskPoly Spec.ML_DSA_44 Data.rho2L 0 2) = Pl Data.y_2
    rw [maskPoly_fast, yb_2]; exact mask_2
  · show RPoly.toZq (maskPoly Spec.ML_DSA_44 Data.rho2L 0 3) = Pl Data.y_3
    rw [maskPoly_fast, yb_3]; exact mask_3

theorem commitAt_lit : Sign.commitAt Spec.ML_DSA_44 P0 0 = Wv := by
  unfold Sign.commitAt
  have hA : P0.Â = Av := rfl
  rw [maskAt_lit, ntt_y_lit, hA, wmv_lit, intt_w_lit]

theorem ctildeAt_lit : Sign.ctildeAt Spec.ML_DSA_44 P0 0 = Data.ctL := by
  unfold Sign.ctildeAt
  rw [commitAt_lit]
  show Spec.H (Data.muL ++ w1Encode Spec.ML_DSA_44 (HighBitsVec Spec.ML_DSA_44 Wv)) (Spec.ML_DSA_44.lam / 4) = Data.ctL
  rw [w1_lit, w1Encode_fast, w1b_lit, ct_lit]

theorem cs1_lit : Spec.NTTInvVec (Spec.ScalarVectorNTT Chat S1hv) = CS1v := by
  rw [ScalarVectorNTT_fast]
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTInvVec, Vector.getElem_map]
  interval_cases i
  · exact nttI_cs1_0
  · exact nttI_cs1_1
  · exact nttI_cs1_2
  · exact nttI_cs1_3

theorem cs2_lit : Spec.NTTInvVec (Spec.ScalarVectorNTT Chat S2hv) = CS2v := by
  rw [ScalarVectorNTT_fast]
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTInvVec, Vector.getElem_map]
  interval_cases i
  · exact nttI_cs2_0
  · exact nttI_cs2_1
  · exact nttI_cs2_2
  · exact nttI_cs2_3

theorem ct0_lit : Spec.NTTInvVec (Spec.ScalarVectorNTT Chat T0hv) = CT0v := by
  rw [ScalarVectorNTT_fast]
  apply Vector.ext
  intro i hi
  have h4 : i < 4 := hi
  simp only [Spec.NTTInvVec, Vector.getElem_map]
  interval_cases i
  · exact nttI_ct0_0
  · exact nttI_ct0_1
  · exact nttI_ct0_2
  · exact nttI_ct0_3

/-- **The first attempt is accepted**: `respond` returns `some`. The four tests are checked one declaration-step
at a time (they are cheap separately and much more expensive when `decide` sees the whole `respond` term). -/
theorem respond_lit : (Sign.respond Spec.ML_DSA_44 P0 Yv Wv Cp).isSome = true := by
  have e1 : NTT (RPoly.toZq Cp) = Chat := nttF_c
  have hs1 : P0.ŝ₁ = S1hv := ntt_s1_lit
  have hs2 : P0.ŝ₂ = S2hv := ntt_s2_lit
  have ht0 : P0.t₀hat = T0hv := ntt_t0_lit
  have hA : ¬ (Spec.ML_DSA_44.γ₁ - Spec.ML_DSA_44.β ≤ ‖Yv + CS1v‖∞) := by decide +kernel
  have hB : ¬ (Spec.ML_DSA_44.γ₂ - Spec.ML_DSA_44.β ≤ ‖LowBitsVec Spec.ML_DSA_44 (Wv - CS2v)‖∞) := by decide +kernel
  have hC : ¬ (Spec.ML_DSA_44.γ₂ ≤ ‖CT0v‖∞) := by decide +kernel
  have hD : ¬ (Spec.ML_DSA_44.ω < HintWeight (MakeHintVec Spec.ML_DSA_44 (-CT0v) (Wv - CS2v + CT0v))) := by
    decide +kernel
  rw [Sign.respond_eq, e1, hs1, hs2, ht0, cs1_lit, cs2_lit, ct0_lit, if_neg (not_or.2 ⟨hA, hB⟩),
    if_neg (not_or.2 ⟨hC, hD⟩)]
  rfl

theorem attempt_eq_of (sp : Spec.Params) (F : Spec.Fuel) (P : Sign.Pre sp) (κ : Nat) (c : RPoly)
    (zh : Vector Poly sp.ℓ × Vector HintPoly sp.k)
    (hc : Spec.SampleInBall sp F.sampleInBall (Sign.ctildeAt sp P κ) = some c)
    (hr : Sign.respond sp P (Sign.maskAt sp P κ) (Sign.commitAt sp P κ) c = some zh) :
    Sign.attemptAt sp F P κ = some (Sign.ctildeAt sp P κ, some zh) := by
  unfold Sign.attemptAt
  rw [hc]
  dsimp only
  rw [hr]

theorem attempt0 :
    ∃ ct z h, Sign.attemptAt Spec.ML_DSA_44 {} P0 (0 * Spec.ML_DSA_44.ℓ) = some (ct, some (z, h)) := by
  rw [Nat.zero_mul]
  have hc : Spec.SampleInBall Spec.ML_DSA_44 ({} : Spec.Fuel).sampleInBall (Sign.ctildeAt Spec.ML_DSA_44 P0 0) =
      some Cp := by rw [ctildeAt_lit]; exact sib_lit
  obtain ⟨⟨z, h⟩, hr'⟩ := Option.isSome_iff_exists.mp respond_lit
  have hr : Sign.respond Spec.ML_DSA_44 P0 (Sign.maskAt Spec.ML_DSA_44 P0 0) (Sign.commitAt Spec.ML_DSA_44 P0 0) Cp
      = some (z, h) := by
    rw [maskAt_lit, commitAt_lit]
    exact hr'
  exact ⟨_, z, h, attempt_eq_of _ _ _ _ _ _ hc hr⟩

/-- **`Spec.Sign` returns `some`** on the witness key, `rnd = 0^32`, `M = [0]`, `ctx = []`, default fuel. -/
theorem sign_lit_isSome :
    (Spec.Sign Spec.ML_DSA_44 skL [0] [] (List.replicate 32 0) {}).isSome = true := by
  rw [API.Sign_short _ _ _ _ _ _ (by simp)]
  have hM : ([0, UInt8.ofNat ([] : List UInt8).length] ++ [] ++ [0] : List UInt8) = [0, 0, 0] := rfl
  rw [hM, Sign.sign_isSome_iff]
  exact ⟨P0, pre_lit, 0, by decide +kernel, by decide +kernel, fun i hi => absurd hi (Nat.not_lt_zero i), attempt0⟩

end TopWitness
end Proofs
