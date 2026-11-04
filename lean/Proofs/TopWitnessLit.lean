import Proofs.TopWitnessData

/-!
# The literals of the witnesses as vectors (ML-DSA-44, `ξ = 0, 1, ..., 31`)

`Data.*` are the candidate values printed by `SpecTests/WitnessGen.lean`; here they become `Poly` / `RPoly` /
vectors. The kernel stage lemmas (`TopWitnessN*`, `TopWitnessKA`, ...) prove each of them equal to what the
specification computes.
-/

open Spec

namespace Proofs
namespace TopWitness
open Data

/-- The matrix `Â` of `ExpandA`. -/
def Av : Vector (Vector Poly Spec.ML_DSA_44.ℓ) Spec.ML_DSA_44.k :=
  v4
  (v4 (Pl Data.a_0_0) (Pl Data.a_0_1) (Pl Data.a_0_2) (Pl Data.a_0_3))
  (v4 (Pl Data.a_1_0) (Pl Data.a_1_1) (Pl Data.a_1_2) (Pl Data.a_1_3))
  (v4 (Pl Data.a_2_0) (Pl Data.a_2_1) (Pl Data.a_2_2) (Pl Data.a_2_3))
  (v4 (Pl Data.a_3_0) (Pl Data.a_3_1) (Pl Data.a_3_2) (Pl Data.a_3_3))

def S1v : Vector RPoly Spec.ML_DSA_44.ℓ := v4 (Rl Data.s1_0) (Rl Data.s1_1) (Rl Data.s1_2) (Rl Data.s1_3)
def S2v : Vector RPoly Spec.ML_DSA_44.k := v4 (Rl Data.s2_0) (Rl Data.s2_1) (Rl Data.s2_2) (Rl Data.s2_3)
def S1hv : Vector Poly Spec.ML_DSA_44.ℓ := v4 (Pl Data.s1h_0) (Pl Data.s1h_1) (Pl Data.s1h_2) (Pl Data.s1h_3)
def MVv : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.mv_0) (Pl Data.mv_1) (Pl Data.mv_2) (Pl Data.mv_3)
def Tv : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.t_0) (Pl Data.t_1) (Pl Data.t_2) (Pl Data.t_3)
def T1v : Vector RPoly Spec.ML_DSA_44.k := v4 (Rl Data.t1_0) (Rl Data.t1_1) (Rl Data.t1_2) (Rl Data.t1_3)
def T0v : Vector RPoly Spec.ML_DSA_44.k := v4 (Rl Data.t0_0) (Rl Data.t0_1) (Rl Data.t0_2) (Rl Data.t0_3)
def S2hv : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.s2h_0) (Pl Data.s2h_1) (Pl Data.s2h_2) (Pl Data.s2h_3)
def T0hv : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.t0h_0) (Pl Data.t0h_1) (Pl Data.t0h_2) (Pl Data.t0h_3)
def Yv : Vector Poly Spec.ML_DSA_44.ℓ := v4 (Pl Data.y_0) (Pl Data.y_1) (Pl Data.y_2) (Pl Data.y_3)
def Yhv : Vector Poly Spec.ML_DSA_44.ℓ := v4 (Pl Data.yh_0) (Pl Data.yh_1) (Pl Data.yh_2) (Pl Data.yh_3)
def WMVv : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.wmv_0) (Pl Data.wmv_1) (Pl Data.wmv_2) (Pl Data.wmv_3)
def Wv : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.w_0) (Pl Data.w_1) (Pl Data.w_2) (Pl Data.w_3)
def W1v : Vector RPoly Spec.ML_DSA_44.k := v4 (Rl Data.w1_0) (Rl Data.w1_1) (Rl Data.w1_2) (Rl Data.w1_3)
def CS1v : Vector Poly Spec.ML_DSA_44.ℓ := v4 (Pl Data.cs1_0) (Pl Data.cs1_1) (Pl Data.cs1_2) (Pl Data.cs1_3)
def CS2v : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.cs2_0) (Pl Data.cs2_1) (Pl Data.cs2_2) (Pl Data.cs2_3)
def CT0v : Vector Poly Spec.ML_DSA_44.k := v4 (Pl Data.ct0_0) (Pl Data.ct0_1) (Pl Data.ct0_2) (Pl Data.ct0_3)
/-- `ĉ = NTT(c)`. -/
def Chat : Poly := Pl Data.ch

/-- The challenge polynomial `c`. -/
def Cp : RPoly := Rl Data.cL

end TopWitness
end Proofs
