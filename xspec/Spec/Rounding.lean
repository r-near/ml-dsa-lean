import Spec.Params
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.ValMinAbs

/-!
# FIPS 204, Sections 2.5 and 7.4: mod±, the infinity norm, and the rounding / hint functions (Algorithms 35-40)

## From `Z_q` to `Z` (this is where specifications usually go wrong)

FIPS 204 mixes elements of `Z_q` with integers. This file fixes the two maps once and for all.

* `r mod q` for `r ∈ Z_q` is the representative in `[0, q)`: `r.val` (`ZMod.val`).
* `m mod± α` (Section 2.5) is the unique `m'` with `−⌈α/2⌉ < m' ≤ ⌊α/2⌋` and `m' ≡ m (mod α)`; it is `modPM m α`
  for an integer `m`. Note the asymmetry: the upper end is included, the lower end is not
  (`modPM 4 8 = 4`, `modPM 5 8 = -3`).
* For `c ∈ Z_q`, `c mod± q` is `Zq.modPM c = modPM c.val q` (it equals Mathlib's `ZMod.valMinAbs`, see
  `Zq.modPM_eq_valMinAbs`), and `Poly.modPM` applies it coefficientwise.
* `‖·‖∞` (Section 2.5): `|w|` on `Z`, `|w mod± q|` on `Z_q`, and the maximum over the coefficients (and then over
  the entries) on polynomials and vectors. It is the single class `InfNorm`, with notation `‖w‖∞`, returning a
  `Nat`.

Functions that FIPS 204 states on `Z_q` and then extends "coefficientwise" to `R_q^k` (Section 7.4) are
given in both forms: the scalar algorithm on `Zq`, and a wrapper (`Power2RoundVec`, `HighBitsVec`, `LowBitsVec`,
`MakeHintVec`, `UseHintVec`) on `Vector Poly n`.

The integer division `(r⁺ − r₀) / 2^d` and `(r⁺ − r₀) / (2γ₂)` of Algorithms 35 and 36 is exact
(`r⁺ − r₀` is a multiple of the divisor), so `Int` division is unambiguous there. `(r₁ ± 1) mod m` in
Algorithm 40 is `Int` `%` (nonnegative remainder for a positive modulus).
-/

namespace Spec

/-! ## mod± -/

/-- `m mod± α` (FIPS 204, Section 2.5): the unique `m' ∈ (−⌈α/2⌉, ⌊α/2⌋]` congruent to `m` modulo `α`. -/
def modPM (m : Int) (α : Nat) : Int :=
  let r := m % (α : Int)                            -- m mod α, in [0, α)
  if r > ((α / 2 : Nat) : Int) then r - α else r

/-- Lower bound of `modPM`: `−⌈α/2⌉ < m mod± α`. -/
theorem modPM_lower (m : Int) (α : Nat) (hα : 0 < α) : -(((α + 1) / 2 : Nat) : Int) < modPM m α := by
  have h0 : 0 ≤ m % (α : Int) := Int.emod_nonneg _ (by omega)
  have h1 : m % (α : Int) < α := Int.emod_lt_of_pos _ (by omega)
  simp only [modPM]
  split <;> omega

/-- Upper bound of `modPM`: `m mod± α ≤ ⌊α/2⌋`. -/
theorem modPM_upper (m : Int) (α : Nat) (hα : 0 < α) : modPM m α ≤ ((α / 2 : Nat) : Int) := by
  have h0 : 0 ≤ m % (α : Int) := Int.emod_nonneg _ (by omega)
  have h1 : m % (α : Int) < α := Int.emod_lt_of_pos _ (by omega)
  simp only [modPM]
  split <;> omega

/-- Congruence: `m mod± α ≡ m (mod α)`. -/
theorem modPM_dvd (m : Int) (α : Nat) : (α : Int) ∣ modPM m α - m := by
  simp only [modPM]
  split
  · exact ⟨-(m / α) - 1, by rw [Int.emod_def]; ring⟩
  · exact ⟨-(m / α), by rw [Int.emod_def]; ring⟩

/-- `r mod± q` for `r ∈ Z_q`: the centered representative of `r` in `(−q/2, q/2]`. -/
def Zq.modPM (r : Zq) : Int := Spec.modPM (r.val : Int) q

/-- `w mod± q` for `w ∈ R_q`, coefficientwise (an element of `R`). -/
def Poly.modPM (w : Poly) : RPoly := w.map Zq.modPM

/-- The centered representative of `c ∈ Z_q` is a representative of `c`: casting it back gives `c`. -/
theorem Zq.modPM_cast (c : Zq) : ((Zq.modPM c : Int) : Zq) = c := by
  haveI : NeZero q := ⟨by decide⟩
  have hd := modPM_dvd (c.val : Int) q
  have h1 : ((Zq.modPM c : Int) : Zq) = (((c.val : Nat) : Int) : Zq) := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact dvd_sub_comm.mp hd
  rw [h1]
  simp

/-- `Zq.modPM` is Mathlib's `ZMod.valMinAbs`. -/
theorem Zq.modPM_eq_valMinAbs (c : Zq) : Zq.modPM c = ZMod.valMinAbs c := by
  haveI : NeZero q := ⟨by decide⟩
  have hlt : c.val < q := ZMod.val_lt c
  have hmod : (c.val : Int) % (q : Int) = c.val := Int.emod_eq_of_lt (by omega) (by omega)
  simp only [Zq.modPM, Spec.modPM, hmod, ZMod.valMinAbs_def_pos]
  split_ifs <;> omega

/-! ## The infinity norm -/

/-- Types with an infinity norm `‖·‖∞` (FIPS 204, Section 2.5). -/
class InfNorm (α : Type) where
  /-- The infinity norm. -/
  infNorm : α → Nat

/-- `‖w‖∞ = |w|` for `w ∈ Z`. -/
instance : InfNorm Int := ⟨fun w => w.natAbs⟩

/-- `‖w‖∞ = |w mod± q|` for `w ∈ Z_q`. -/
instance : InfNorm Zq := ⟨fun w => (Zq.modPM w).natAbs⟩

/-- The maximum of the norms of the entries: polynomials (256 entries) and vectors of polynomials. -/
instance {α : Type} {n : Nat} [InfNorm α] : InfNorm (Vector α n) :=
  ⟨fun w => w.foldl (fun m x => max m (InfNorm.infNorm x)) 0⟩

@[inherit_doc InfNorm.infNorm]
notation:max "‖" x "‖∞" => InfNorm.infNorm x

/-! ## Algorithms 35-40 -/

/-- Algorithm 35: Power2Round(r). Decomposes `r` into `(r₁, r₀)` such that `r ≡ r₁ 2^d + r₀ (mod q)`. -/
def Power2Round (p : Params) (r : Zq) : Int × Int := Id.run do
  let rp : Int := r.val                             -- 1: r⁺ <- r mod q
  let r₀ := modPM rp (2 ^ p.d)                      -- 2: r₀ <- r⁺ mod± 2^d
  return ((rp - r₀) / 2 ^ p.d, r₀)                  -- 3

/-- Algorithm 36: Decompose(r). Decomposes `r` into `(r₁, r₀)` such that `r ≡ r₁ (2γ₂) + r₀ (mod q)`. -/
def Decompose (p : Params) (r : Zq) : Int × Int := Id.run do
  let rp : Int := r.val                             -- 1: r⁺ <- r mod q
  let mut r₀ := modPM rp (2 * p.γ₂)                 -- 2: r₀ <- r⁺ mod± (2γ₂)
  let mut r₁ : Int := 0
  if rp - r₀ = (q : Int) - 1 then                   -- 3
    r₁ := 0                                         -- 4
    r₀ := r₀ - 1                                    -- 5
  else
    r₁ := (rp - r₀) / (2 * p.γ₂)                    -- 6
  return (r₁, r₀)                                   -- 8

/-- Algorithm 37: HighBits(r). Returns `r₁` from the output of `Decompose(r)`. -/
def HighBits (p : Params) (r : Zq) : Int :=
  let (r₁, _) := Decompose p r                      -- 1
  r₁                                                -- 2

/-- Algorithm 38: LowBits(r). Returns `r₀` from the output of `Decompose(r)`. -/
def LowBits (p : Params) (r : Zq) : Int :=
  let (_, r₀) := Decompose p r                      -- 1
  r₀                                                -- 2

/-- Algorithm 39: MakeHint(z, r). The hint bit says whether adding `z` to `r` alters the high bits of `r`. -/
def MakeHint (p : Params) (z r : Zq) : Bool :=
  let r₁ := HighBits p r                            -- 1
  let v₁ := HighBits p (r + z)                      -- 2
  r₁ != v₁                                          -- 3

/-- Algorithm 40: UseHint(h, r). Returns the high bits of `r` adjusted according to the hint `h`. -/
def UseHint (p : Params) (h : Bool) (r : Zq) : Int :=
  let m : Int := ((q - 1) / (2 * p.γ₂) : Nat)       -- 1
  let (r₁, r₀) := Decompose p r                     -- 2
  if h ∧ r₀ > 0 then (r₁ + 1) % m                   -- 3
  else if h ∧ r₀ ≤ 0 then (r₁ - 1) % m              -- 4
  else r₁                                           -- 5

/-! ## Coefficientwise extension to vectors (Section 7.4) -/

/-- `(r₁, r₀) = Power2Round(r)` for `r ∈ R_q^n`, coefficientwise. -/
def Power2RoundVec {n : Nat} (p : Params) (r : Vector Poly n) : Vector RPoly n × Vector RPoly n :=
  (r.map (·.map (fun c => (Power2Round p c).1)), r.map (·.map (fun c => (Power2Round p c).2)))

/-- `r₁ = HighBits(r)` for `r ∈ R_q^n`, coefficientwise. -/
def HighBitsVec {n : Nat} (p : Params) (r : Vector Poly n) : Vector RPoly n :=
  r.map (·.map (HighBits p))

/-- `r₀ = LowBits(r)` for `r ∈ R_q^n`, coefficientwise. -/
def LowBitsVec {n : Nat} (p : Params) (r : Vector Poly n) : Vector RPoly n :=
  r.map (·.map (LowBits p))

/-- `h = MakeHint(z, r)` for `z, r ∈ R_q^n`, coefficientwise (an element of `R_2^n`). -/
def MakeHintVec {n : Nat} (p : Params) (z r : Vector Poly n) : Vector HintPoly n :=
  Vector.zipWith (fun zi ri => Vector.zipWith (MakeHint p) zi ri) z r

/-- `r₁ = UseHint(h, r)` for `h ∈ R_2^n`, `r ∈ R_q^n`, coefficientwise. -/
def UseHintVec {n : Nat} (p : Params) (h : Vector HintPoly n) (r : Vector Poly n) : Vector RPoly n :=
  Vector.zipWith (fun hi ri => Vector.zipWith (UseHint p) hi ri) h r

/-- The number of 1's in a hint `h ∈ R_2^n` (Algorithm 7, step 28). -/
def HintWeight {n : Nat} (h : Vector HintPoly n) : Nat :=
  h.foldl (fun s hi => s + hi.countP (fun b => b)) 0

end Spec
