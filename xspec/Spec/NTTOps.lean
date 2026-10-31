import Spec.Params

/-!
# FIPS 204, Section 7.6: arithmetic under the NTT (Algorithms 44-48)

Algorithms 41-43 (`NTT`, `NTTInv`, `BitRev8`) are in `Spec/NTT.lean`. An element of `T_q` is a `Poly` (256
entries of `Zq`) with the componentwise ring structure; `AddNTT` and `MultiplyNTT` are `+` and `∘`.
Vectors over `T_q` are `Vector Poly n`, matrices are `Vector (Vector Poly ℓ) k`.

`k` and `ℓ` are implicit arguments here (FIPS 204 lists them as inputs `k, ℓ ∈ ℕ`).
-/

namespace Spec

/-- Algorithm 44: AddNTT(â, b̂). Computes the sum `â + b̂` of two elements of `T_q`. -/
def AddNTT (a b : Poly) : Poly := Id.run do
  let mut c : Poly := Poly.zero
  for i in [0:256] do                               -- 1
    c := c.set! i (a[i]! + b[i]!)                   -- 2
  return c                                          -- 4

/-- Algorithm 45: MultiplyNTT(â, b̂). Computes the product `â ∘ b̂` of two elements of `T_q`. -/
def MultiplyNTT (a b : Poly) : Poly := Id.run do
  let mut c : Poly := Poly.zero
  for i in [0:256] do                               -- 1
    c := c.set! i (a[i]! * b[i]!)                   -- 2
  return c                                          -- 4

/-- Algorithm 46: AddVectorNTT(v̂, ŵ). Computes the sum `v̂ + ŵ` of two vectors over `T_q`. -/
def AddVectorNTT {ℓ : Nat} (v w : Vector Poly ℓ) : Vector Poly ℓ := Id.run do
  let mut u : Vector Poly ℓ := Vector.replicate ℓ Poly.zero
  for i in [0:ℓ] do                                 -- 1
    u := u.set! i (AddNTT v[i]! w[i]!)              -- 2
  return u                                          -- 4

/-- Algorithm 47: ScalarVectorNTT(ĉ, v̂). Computes the product `ĉ ∘ v̂` of a scalar `ĉ ∈ T_q` and a vector over
`T_q`. -/
def ScalarVectorNTT {ℓ : Nat} (c : Poly) (v : Vector Poly ℓ) : Vector Poly ℓ := Id.run do
  let mut w : Vector Poly ℓ := Vector.replicate ℓ Poly.zero
  for i in [0:ℓ] do                                 -- 1
    w := w.set! i (MultiplyNTT c v[i]!)             -- 2
  return w                                          -- 4

/-- Algorithm 48: MatrixVectorNTT(M̂, v̂). Computes the product `M̂ ∘ v̂` of a `k × ℓ` matrix and a vector of
length `ℓ` over `T_q`. -/
def MatrixVectorNTT {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (v : Vector Poly ℓ) : Vector Poly k := Id.run do
  let mut w : Vector Poly k := Vector.replicate k Poly.zero    -- 1
  for i in [0:k] do                                 -- 2
    for j in [0:ℓ] do                               -- 3
      w := w.set! i (AddNTT w[i]! (MultiplyNTT M[i]![j]! v[j]!))    -- 4
  return w                                          -- 7

/-- `NTT` applied to every entry of a vector over `R_q` (FIPS 204 writes `NTT(𝐯)`). -/
def NTTVec {n : Nat} (v : Vector Poly n) : Vector Poly n := v.map NTT

/-- `NTT⁻¹` applied to every entry of a vector over `T_q` (FIPS 204 writes `NTT⁻¹(𝐯̂)`). -/
def NTTInvVec {n : Nat} (v : Vector Poly n) : Vector Poly n := v.map NTTInv

end Spec
