import Proofs.TopWitnessLit
import Proofs.TopWitnessMisc

/-!
# Inverse NTTs (kernel stage lemmas): `t = NTT⁻¹(Â ŝ₁) + s₂` of KeyGen, `w = NTT⁻¹(Â NTT(y))` of Sign
-/

open Spec

namespace Proofs
namespace TopWitness

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `t[0]`. -/
theorem nttI_t_0 :
    NTTInv (Pl Data.mv_0) + RPoly.toZq (Rl Data.s2_0) = Pl Data.t_0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `t[1]`. -/
theorem nttI_t_1 :
    NTTInv (Pl Data.mv_1) + RPoly.toZq (Rl Data.s2_1) = Pl Data.t_1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `t[2]`. -/
theorem nttI_t_2 :
    NTTInv (Pl Data.mv_2) + RPoly.toZq (Rl Data.s2_2) = Pl Data.t_2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `t[3]`. -/
theorem nttI_t_3 :
    NTTInv (Pl Data.mv_3) + RPoly.toZq (Rl Data.s2_3) = Pl Data.t_3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `w[0]`. -/
theorem nttI_w_0 :
    NTTInv (Pl Data.wmv_0) = Pl Data.w_0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `w[1]`. -/
theorem nttI_w_1 :
    NTTInv (Pl Data.wmv_1) = Pl Data.w_1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `w[2]`. -/
theorem nttI_w_2 :
    NTTInv (Pl Data.wmv_2) = Pl Data.w_2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `w[3]`. -/
theorem nttI_w_3 :
    NTTInv (Pl Data.wmv_3) = Pl Data.w_3 := by decide +kernel

end TopWitness
end Proofs
