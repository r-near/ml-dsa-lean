import Spec.NTT

/-!
# FIPS 204, Section 4 (Table 1): parameter sets, and the data types of the specification

## Parameter sets

`Params` holds the free entries of Table 1. The two entries that are the same in all three sets are not
fields: the modulus `q = 8380417` is `Spec.q` and the root of unity `ζ = 1753` is `Spec.ζ` (both in
`Spec/NTT.lean`), because the coefficient ring `Zq = ZMod q` is a fixed type. `β = τ ⋅ η` (a derived entry of
Table 1) is the def `Params.β`. `λ` is a reserved word in Lean, so the field is called `lam`.

The lengths of keys and signatures are the exponents in the input/output types of Algorithms 1, 2, 6, 7:
`pkLen`, `skLen`, `sigLen`.

## Data types (FIPS 204, Section 2)

* A byte string `𝔹^n` is a `List UInt8`. Lengths are not part of the type; they are stated in docstrings and
  enforced where FIPS 204 demands it (`Verify_internal`).
* A bit string is a `List Bool` (`true` is the bit 1). Only Algorithms 9-13 and the pack/unpack functions
  see bit strings.
* An element of `Z_q` is a `Zq`; an element of `R_q` or `T_q` is a `Poly = Vector Zq 256`. Vectors over `R_q`
  or `T_q` are `Vector Poly n`, and a `k × ℓ` matrix is `Vector (Vector Poly ℓ) k` (row `r`, column `s` is
  `A[r][s]`, as `A[r, s]` in FIPS 204).
* An element of `R` (integer coefficients, as returned by `ExpandS`, `SampleInBall`, `Power2Round`,
  `BitUnpack`, ...) is an `RPoly = Vector Int 256`. The implicit coercion `R → R_q` of FIPS 204 (for example
  `NTT(𝐬₁)` in Algorithm 7) is written `RPoly.toZq`. The converse "mod± q" is `Poly.modPM` (Rounding.lean).
* An element of `R_2` (a hint polynomial) is a `HintPoly = Vector Bool 256` (`true` is 1).
-/

namespace Spec

/-- `bitlen a`: the number of binary digits of `a` (FIPS 204, Section 2.5: `bitlen 32 = 6`, `bitlen 31 = 5`).
Only called with positive arguments in FIPS 204; `bitlen 0 = 0` here. -/
def bitlen (a : Nat) : Nat := if a = 0 then 0 else Nat.log2 a + 1

example : bitlen 32 = 6 := by decide +kernel
example : bitlen 31 = 5 := by decide +kernel

/-- FIPS 204, Table 1: an ML-DSA parameter set. -/
structure Params where
  /-- `d`: number of dropped bits from `t`. -/
  d : Nat
  /-- `τ`: number of ±1's in the challenge polynomial `c`. -/
  τ : Nat
  /-- `λ`: collision strength of `c̃` (bits); `c̃` has `λ/4` bytes. -/
  lam : Nat
  /-- `γ₁`: coefficient range of the masking vector `y`. -/
  γ₁ : Nat
  /-- `γ₂`: low-order rounding range. -/
  γ₂ : Nat
  /-- `k`: rows of `A`. -/
  k : Nat
  /-- `ℓ`: columns of `A`. -/
  ℓ : Nat
  /-- `η`: private key range. -/
  η : Nat
  /-- `ω`: maximum number of 1's in the hint `h`. -/
  ω : Nat

/-- ML-DSA-44 (Table 1, first column). -/
def ML_DSA_44 : Params :=
  { d := 13, τ := 39, lam := 128, γ₁ := 2 ^ 17, γ₂ := (q - 1) / 88, k := 4, ℓ := 4, η := 2, ω := 80 }

/-- ML-DSA-65 (Table 1, second column). -/
def ML_DSA_65 : Params :=
  { d := 13, τ := 49, lam := 192, γ₁ := 2 ^ 19, γ₂ := (q - 1) / 32, k := 6, ℓ := 5, η := 4, ω := 55 }

/-- ML-DSA-87 (Table 1, third column). -/
def ML_DSA_87 : Params :=
  { d := 13, τ := 60, lam := 256, γ₁ := 2 ^ 19, γ₂ := (q - 1) / 32, k := 8, ℓ := 7, η := 2, ω := 75 }

/-- `β = τ ⋅ η` (Table 1). -/
def Params.β (p : Params) : Nat := p.τ * p.η

/-- `m = (q − 1) / (2 γ₂)`: the number of values of `HighBits` (Algorithms 40 and 28). -/
def Params.m (p : Params) : Nat := (q - 1) / (2 * p.γ₂)

/-- Length in bytes of a public key: `32 + 32 k (bitlen (q − 1) − d)` (Algorithm 1). -/
def Params.pkLen (p : Params) : Nat := 32 + 32 * p.k * (bitlen (q - 1) - p.d)

/-- Length in bytes of a private key: `32 + 32 + 64 + 32 ((ℓ + k) bitlen (2η) + d k)` (Algorithm 1). -/
def Params.skLen (p : Params) : Nat := 32 + 32 + 64 + 32 * ((p.ℓ + p.k) * bitlen (2 * p.η) + p.d * p.k)

/-- Length in bytes of a signature: `λ/4 + ℓ ⋅ 32 (1 + bitlen (γ₁ − 1)) + ω + k` (Algorithm 2). -/
def Params.sigLen (p : Params) : Nat := p.lam / 4 + p.ℓ * 32 * (1 + bitlen (p.γ₁ - 1)) + p.ω + p.k

-- Table 1 sanity checks, and the sizes of FIPS 204, Table 2.
example : ML_DSA_44.β = 78 ∧ ML_DSA_65.β = 196 ∧ ML_DSA_87.β = 120 := by decide +kernel
example : ML_DSA_44.γ₂ = 95232 ∧ ML_DSA_65.γ₂ = 261888 ∧ ML_DSA_87.γ₂ = 261888 := by decide +kernel
example : ML_DSA_44.pkLen = 1312 ∧ ML_DSA_65.pkLen = 1952 ∧ ML_DSA_87.pkLen = 2592 := by decide +kernel
example : ML_DSA_44.skLen = 2560 ∧ ML_DSA_65.skLen = 4032 ∧ ML_DSA_87.skLen = 4896 := by decide +kernel
example : ML_DSA_44.sigLen = 2420 ∧ ML_DSA_65.sigLen = 3309 ∧ ML_DSA_87.sigLen = 4627 := by decide +kernel

/-! ## Data types -/

/-- An element of `R`: a polynomial with integer coefficients (256 of them). -/
abbrev RPoly := Vector Int 256

/-- An element of `R_2`: a hint polynomial (`true` is the coefficient 1). -/
abbrev HintPoly := Vector Bool 256

/-- The coercion `R → R_q` (reduce each coefficient mod `q`). -/
def RPoly.toZq (w : RPoly) : Poly := w.map (fun (c : Int) => (c : Zq))

/-- The zero polynomial of `R_q` / `T_q`. -/
def Poly.zero : Poly := Vector.replicate 256 0

/-- Coefficientwise addition of vectors (used for `R_q^n`, `T_q^n` and for polynomials themselves; for `T_q`
this is `AddNTT`). -/
instance {α : Type} {n : Nat} [Add α] : Add (Vector α n) := ⟨Vector.zipWith (· + ·)⟩

/-- Coefficientwise subtraction of vectors. -/
instance {α : Type} {n : Nat} [Sub α] : Sub (Vector α n) := ⟨Vector.zipWith (· - ·)⟩

/-- Coefficientwise negation of vectors. -/
instance {α : Type} {n : Nat} [Neg α] : Neg (Vector α n) := ⟨Vector.map (- ·)⟩

end Spec
