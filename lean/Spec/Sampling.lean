import Spec.Keccak
import Spec.Encode

/-!
# FIPS 204, Section 3.7 (H and G) and Sections 7.1 and 7.3: pseudorandom sampling (Algorithms 14, 15, 29-34)

## H, G and the incremental XOF interface

`H(str, ℓ) = SHAKE256(str, 8ℓ)` and `G(str, ℓ) = SHAKE128(str, 8ℓ)` (Section 3.7), on byte strings; `ℓ` is a
number of bytes. FIPS 204 Section 3.7 states that any `Init`, `Absorb`, `Squeeze`, ..., `Squeeze` sequence
produces the concatenation of the `Squeeze` outputs as the prefix of the single call
`SHAKE(str₁ ‖ ... ‖ str_m, 8 (b₁ + ... + b_k))`. The samplers use the incremental interface (`H.Squeeze`,
`G.Squeeze`), which is modeled here as **reading consecutive bytes of one long output**:

* `Ctx` is a context after `Init` and `Absorb`: the first `N` bytes of the XOF output on the absorbed string
  (`stream`), and the number of bytes already squeezed (`pos`).
* `H.InitAbsorb N str` / `G.InitAbsorb N str` performs `Init()` and the single `Absorb(ctx, str)` that every
  sampler does (steps 2-3 of Algorithms 29 and 31, 2-3 of Algorithm 30), with a capacity `N`.
* `Ctx.Squeeze ctx ℓ` (`H.Squeeze`, `G.Squeeze`) returns the next `ℓ` bytes and the advanced context, or `none`
  if fewer than `ℓ` bytes of the `N`-byte stream are left.

The capacity `N` is an artifact of the model, not of FIPS 204. Because `SHAKE256 str M = (SHAKE256 str N).take M`
for `M ≤ N` (the prefix lemma `SHAKE256_prefix` of `Spec/Keccak.lean`), the bytes returned by a `Squeeze` do not
depend on `N` as long as the read stays inside the stream (`Ctx.read_eq_of_le`, `Ctx.read_eq_of_le_G`). Each sampler below picks `N`
from its fuel, so "`Squeeze` returns `none`" happens only where the fuel is exhausted.

## Fuel

FIPS 204's rejection loops (`while j < 256`) are unbounded. Here each takes an explicit `fuel : Nat` and returns
`Option`: `none` means that the fuel ran out before the loop finished (for FIPS 204, an event of negligible
probability; the later named premise `RejTerm` says it does not happen for the inputs at hand).

* `RejNTTPoly fuel ρ`: `fuel` is the number of iterations of the `while` loop (each squeezes 3 bytes).
* `RejBoundedPoly p fuel ρ`: `fuel` is the number of iterations (each squeezes 1 byte).
* `SampleInBall p fuel ρ`: `fuel` is the number of bytes available after the 8 sign bytes.
* `ExpandA`, `ExpandS` pass their fuel on to every polynomial they sample.

A result that is `some` for some fuel is the same `some` for every larger fuel (a consequence of the prefix lemma;
not proved in this file). `Fuel` bundles the three
numbers, with defaults (`512`) that are far beyond what any input needs (the expected counts are about 256,
256 to 300, and 70).
-/

namespace Spec

/-- FIPS 204 Section 3.7: `H(str, ℓ) = SHAKE256(str, 8ℓ)`; `ℓ` is a number of bytes. -/
def H (str : List UInt8) (ℓ : Nat) : List UInt8 := SHAKE256 str ℓ

/-- FIPS 204 Section 3.7: `G(str, ℓ) = SHAKE128(str, 8ℓ)`; `ℓ` is a number of bytes. -/
def G (str : List UInt8) (ℓ : Nat) : List UInt8 := SHAKE128 str ℓ

/-- An XOF context after `Init` and `Absorb`: the first `N = stream.length` bytes of the output, and how many of
them have been squeezed. See the module documentation. -/
structure Ctx where
  /-- The first `N` bytes of the XOF output on the absorbed string. -/
  stream : List UInt8
  /-- The number of bytes squeezed so far. -/
  pos : Nat

/-- `H.Init()` followed by `H.Absorb(ctx, str)`, with a stream capacity of `N` bytes. -/
def H.InitAbsorb (N : Nat) (str : List UInt8) : Ctx := ⟨H str N, 0⟩

/-- `G.Init()` followed by `G.Absorb(ctx, str)`, with a stream capacity of `N` bytes. -/
def G.InitAbsorb (N : Nat) (str : List UInt8) : Ctx := ⟨G str N, 0⟩

/-- `Squeeze(ctx, ℓ)` (for `H` and `G` alike): the next `ℓ` bytes of the stream and the advanced context, or
`none` if the stream has fewer than `ℓ` bytes left. -/
def Ctx.Squeeze (ctx : Ctx) (ℓ : Nat) : Option (Ctx × List UInt8) :=
  if ctx.pos + ℓ ≤ ctx.stream.length then
    some ({ ctx with pos := ctx.pos + ℓ }, (ctx.stream.drop ctx.pos).take ℓ)
  else none

/-- `H.Squeeze(ctx, ℓ)`. -/
abbrev H.Squeeze := Ctx.Squeeze

/-- `G.Squeeze(ctx, ℓ)`. -/
abbrev G.Squeeze := Ctx.Squeeze

/-- Reading `ℓ` bytes at offset `pos` of the `N`-byte stream of `SHAKE256 str N` gives the same bytes as reading
them from the `N'`-byte stream, for `pos + ℓ ≤ N ≤ N'`: the capacity does not matter. -/
theorem Ctx.read_eq_of_le (str : List UInt8) (N N' pos ℓ : Nat) (h : pos + ℓ ≤ N) (hN : N ≤ N') :
    (((H.InitAbsorb N str).stream).drop pos).take ℓ = (((H.InitAbsorb N' str).stream).drop pos).take ℓ := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hN
  simp only [H.InitAbsorb, H]
  rw [SHAKE256_prefix str N e, List.drop_take, List.take_take]
  congr 1
  omega

/-- The same for `G` (`SHAKE128`), used by `RejNTTPoly`. -/
theorem Ctx.read_eq_of_le_G (str : List UInt8) (N N' pos ℓ : Nat) (h : pos + ℓ ≤ N) (hN : N ≤ N') :
    (((G.InitAbsorb N str).stream).drop pos).take ℓ = (((G.InitAbsorb N' str).stream).drop pos).take ℓ := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hN
  simp only [G.InitAbsorb, G]
  rw [SHAKE128_prefix str N e, List.drop_take, List.take_take]
  congr 1
  omega

/-- Fuel for the three rejection loops, see the module documentation. -/
structure Fuel where
  /-- Iterations of the `while` loop of `RejNTTPoly` (3 bytes each). -/
  rejNTT : Nat := 512
  /-- Iterations of the `while` loop of `RejBoundedPoly` (1 byte each). -/
  rejBounded : Nat := 512
  /-- Bytes available to `SampleInBall` after its 8 sign bytes. -/
  sampleInBall : Nat := 512

/-- Algorithm 14: CoeffFromThreeBytes(b₀, b₁, b₂). Generates an element of `{0, 1, ..., q − 1}` or `⊥`. -/
def CoeffFromThreeBytes (b₀ b₁ b₂ : UInt8) : Option Zq := Id.run do
  let mut b₂' := b₂.toNat                           -- 1
  if b₂' > 127 then                                 -- 2
    b₂' := b₂' - 128                                -- 3: set the top bit of b₂' to zero
  let z := 2 ^ 16 * b₂' + 2 ^ 8 * b₁.toNat + b₀.toNat    -- 5
  if z < q then return some (z : Zq)                -- 6: rejection sampling
  else return none                                  -- 7

/-- Algorithm 15: CoeffFromHalfByte(b), for `η ∈ {2, 4}`. Generates an element of `{−η, ..., η}` or `⊥`. -/
def CoeffFromHalfByte (η : Nat) (b : Nat) : Option Int :=
  if η = 2 ∧ b < 15 then some (2 - ((b % 5 : Nat) : Int))    -- 1: rejection sampling from {−2, ..., 2}
  else if η = 4 ∧ b < 9 then some (4 - (b : Int))            -- 3: rejection sampling from {−4, ..., 4}
  else none                                                  -- 4

/-- Algorithm 29: SampleInBall(ρ). Samples a polynomial `c ∈ R` with coefficients in `{−1, 0, 1}` and `τ`
nonzero coefficients. `ρ` has `λ/4` bytes. -/
def SampleInBall (p : Params) (fuel : Nat) (ρ : List UInt8) : Option RPoly := Id.run do
  let mut c : RPoly := Vector.replicate 256 0       -- 1
  let mut ctx := H.InitAbsorb (8 + fuel) ρ          -- 2-3
  let some (ctx', s) := H.Squeeze ctx 8 | return none    -- 4
  ctx := ctx'
  let h := BytesToBits s                            -- 5: a bit string of length 64
  for i in [256 - p.τ:256] do                       -- 6: i = 256 − τ, ..., 255
    let some (ctx', s₁) := H.Squeeze ctx 1 | return none    -- 7
    ctx := ctx'
    let mut j := (s₁[0]!).toNat
    for _ in [0:fuel] do                            -- 8: while j > i (each pass squeezes one byte)
      if j ≤ i then break
      let some (ctx', s₁) := H.Squeeze ctx 1 | return none  -- 9
      ctx := ctx'
      j := (s₁[0]!).toNat
    if j > i then return none                       -- (unreachable: the stream is empty before 'fuel' passes)
    c := c.set! i c[j]!                             -- 11
    c := c.set! j (if h[i + p.τ - 256]! then -1 else 1)    -- 12
  return some c                                     -- 14

/-- Algorithm 30: RejNTTPoly(ρ). Samples a polynomial `â ∈ T_q`. `ρ` has 34 bytes. -/
def RejNTTPoly (fuel : Nat) (ρ : List UInt8) : Option Poly := Id.run do
  let mut a : Poly := Poly.zero
  let mut j := 0                                    -- 1
  let mut ctx := G.InitAbsorb (3 * fuel) ρ          -- 2-3
  for _ in [0:fuel] do                              -- 4: while j < 256
    if j ≥ 256 then break
    let some (ctx', s) := G.Squeeze ctx 3 | return none    -- 5
    ctx := ctx'
    match CoeffFromThreeBytes s[0]! s[1]! s[2]! with       -- 6
    | some v =>                                     -- 7
      a := a.set! j v
      j := j + 1                                    -- 8
    | none => pure ()
  if j < 256 then return none                       -- fuel exhausted
  return some a                                     -- 11

/-- Algorithm 31: RejBoundedPoly(ρ). Samples an element `a ∈ R` with coefficients in `[−η, η]` computed via
rejection sampling from `ρ`. `ρ` has 66 bytes. -/
def RejBoundedPoly (p : Params) (fuel : Nat) (ρ : List UInt8) : Option RPoly := Id.run do
  let mut a : RPoly := Vector.replicate 256 0
  let mut j := 0                                    -- 1
  let mut ctx := H.InitAbsorb fuel ρ                -- 2-3
  for _ in [0:fuel] do                              -- 4: while j < 256
    if j ≥ 256 then break
    let some (ctx', s) := H.Squeeze ctx 1 | return none    -- 5
    ctx := ctx'
    let z := (s[0]!).toNat
    let z₀ := CoeffFromHalfByte p.η (z % 16)        -- 6
    let z₁ := CoeffFromHalfByte p.η (z / 16)        -- 7
    if let some v := z₀ then                        -- 8
      a := a.set! j v                               -- 9
      j := j + 1                                    -- 10
    if let some v := z₁ then                        -- 12
      if j < 256 then
        a := a.set! j v                             -- 13
        j := j + 1                                  -- 14
  if j < 256 then return none                       -- fuel exhausted
  return some a                                     -- 17

/-- Algorithm 32: ExpandA(ρ). Samples a `k × ℓ` matrix `Â` of elements of `T_q`. `ρ` has 32 bytes. -/
def ExpandA (p : Params) (fuel : Nat) (ρ : List UInt8) : Option (Vector (Vector Poly p.ℓ) p.k) := Id.run do
  let mut A : Vector (Vector Poly p.ℓ) p.k := Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)
  for r in [0:p.k] do                               -- 1
    for s in [0:p.ℓ] do                             -- 2
      let ρ' := ρ ++ IntegerToBytes s 1 ++ IntegerToBytes r 1    -- 3
      let some a := RejNTTPoly fuel ρ' | return none  -- 4
      A := A.set! r (A[r]!.set! s a)
  return some A                                     -- 7

/-- Algorithm 33: ExpandS(ρ). Samples vectors `s₁ ∈ R^ℓ` and `s₂ ∈ R^k`, each with polynomial coordinates whose
coefficients are in `[−η, η]`. `ρ` has 64 bytes. -/
def ExpandS (p : Params) (fuel : Nat) (ρ : List UInt8) : Option (Vector RPoly p.ℓ × Vector RPoly p.k) := Id.run do
  let mut s₁ : Vector RPoly p.ℓ := Vector.replicate p.ℓ (Vector.replicate 256 0)
  let mut s₂ : Vector RPoly p.k := Vector.replicate p.k (Vector.replicate 256 0)
  for r in [0:p.ℓ] do                               -- 1
    let some a := RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2) | return none    -- 2
    s₁ := s₁.set! r a
  for r in [0:p.k] do                               -- 4
    let some a := RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2) | return none    -- 5
    s₂ := s₂.set! r a
  return some (s₁, s₂)                              -- 7

/-- Algorithm 34: ExpandMask(ρ, μ). Samples a vector `y ∈ R^ℓ` such that each polynomial `y[r]` has
coefficients between `−γ₁ + 1` and `γ₁`. `ρ` has 64 bytes and `μ` is a nonnegative integer. Note that
`IntegerToBytes(μ + r, 2)` reduces `μ + r` modulo `2^16`; the signing loop never lets `μ + r` reach `2^16`
(see `Sign_internal_bounded`). -/
def ExpandMask (p : Params) (ρ : List UInt8) (μ : Nat) : Vector RPoly p.ℓ := Id.run do
  let c := 1 + bitlen (p.γ₁ - 1)                    -- 1
  let mut y : Vector RPoly p.ℓ := Vector.replicate p.ℓ (Vector.replicate 256 0)
  for r in [0:p.ℓ] do                               -- 2
    let ρ' := ρ ++ IntegerToBytes (μ + r) 2         -- 3
    let v := H ρ' (32 * c)                          -- 4
    y := y.set! r (BitUnpack v (p.γ₁ - 1) p.γ₁)     -- 5
  return y                                          -- 7

end Spec
