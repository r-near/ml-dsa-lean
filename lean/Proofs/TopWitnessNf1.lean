import Proofs.TopWitnessLit
import Proofs.TopWitnessKA

/-!
# Forward NTTs (kernel stage lemmas): `ŝ₁`, `ŝ₂`

Each `NTT` is one kernel evaluation (measured about 15 GB and 65 s). The modules `TopWitnessKA`, ... are imported only to schedule the heavy modules one after another.
-/

open Spec

namespace Proofs
namespace TopWitness

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₁[0])`. -/
theorem nttF_s1_0 :
    NTT (RPoly.toZq (Rl Data.s1_0)) = Pl Data.s1h_0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₁[1])`. -/
theorem nttF_s1_1 :
    NTT (RPoly.toZq (Rl Data.s1_1)) = Pl Data.s1h_1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₁[2])`. -/
theorem nttF_s1_2 :
    NTT (RPoly.toZq (Rl Data.s1_2)) = Pl Data.s1h_2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₁[3])`. -/
theorem nttF_s1_3 :
    NTT (RPoly.toZq (Rl Data.s1_3)) = Pl Data.s1h_3 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₂[0])`. -/
theorem nttF_s2_0 :
    NTT (RPoly.toZq (Rl Data.s2_0)) = Pl Data.s2h_0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₂[1])`. -/
theorem nttF_s2_1 :
    NTT (RPoly.toZq (Rl Data.s2_1)) = Pl Data.s2h_1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₂[2])`. -/
theorem nttF_s2_2 :
    NTT (RPoly.toZq (Rl Data.s2_2)) = Pl Data.s2h_2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `NTT(s₂[3])`. -/
theorem nttF_s2_3 :
    NTT (RPoly.toZq (Rl Data.s2_3)) = Pl Data.s2h_3 := by decide +kernel

end TopWitness
end Proofs
