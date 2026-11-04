import Spec.MLDSA

/-!
# Non-vacuity witnesses for the top level: the seed (ML-DSA-44, `ξ = 0x00 0x01 ... 0x1f`)

Shared by the `TopWitness*` modules, which are not imported by the default build roots (`scripts/witness-check.sh`
builds them). `outL` is `H(ξ ‖ k ‖ ℓ, 128)` for `k = ℓ = 4`: `ρ = outL[0..32]`, `ρ′ = outL[32..96]`,
`K = outL[96..128]` (Algorithm 6, step 1). The data were produced by running the spec (`Spec.KeyGen`) natively; the
kernel re-derives `outL` below.
-/

namespace Proofs.TopWitness

/-- The seed `ξ = 0, 1, ..., 31`. -/
def xiL : List UInt8 :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]

/-- `H(ξ ‖ 4 ‖ 4, 128)` (SHAKE256, one permutation), as computed by the native spec. -/
def outL : List UInt8 :=
  [215, 178, 180, 114, 84, 170, 224, 219, 69, 231, 147, 13, 74, 152, 210, 201, 125, 143, 19, 151, 209, 120, 157, 175, 161, 112, 36, 179, 22, 233, 190, 201, 85, 183, 80, 14, 25, 27, 208, 49, 34, 19, 53, 161, 248, 145, 52, 165, 190, 103, 232, 2, 98, 187, 92, 241, 2, 120, 214, 80, 103, 125, 42, 25, 45, 79, 108, 177, 116, 116, 214, 116, 167, 25, 122, 10, 3, 85, 181, 240, 220, 38, 0, 188, 72, 147, 56, 154, 131, 97, 52, 108, 248, 7, 137, 96, 57, 206, 15, 127, 119, 248, 219, 86, 68, 220, 218, 54, 107, 254, 71, 52, 189, 149, 244, 53, 255, 154, 97, 58, 165, 74, 164, 28, 44, 105, 76, 4]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The kernel evaluates the first hash of `KeyGen_internal` (Algorithm 6, step 1) on `ξ`. -/
theorem hout_44 :
    Spec.H (xiL ++ Spec.IntegerToBytes Spec.ML_DSA_44.k 1 ++ Spec.IntegerToBytes Spec.ML_DSA_44.ℓ 1) 128 = outL := by
  decide +kernel

/-- `ρ`, the matrix seed. -/
abbrev rhoS : List UInt8 := Spec.slice outL 0 32

/-- `ρ′`, the secret-vector seed. -/
abbrev rho1S : List UInt8 := Spec.slice outL 32 64

end Proofs.TopWitness
