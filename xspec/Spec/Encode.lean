import Spec.Conversion

/-!
# FIPS 204, Sections 7.1 (Algorithms 16-21) and 7.2 (Algorithms 22-28): encoding polynomials, keys and signatures

Representation notes.

* The packing functions take and return elements of `R` (`RPoly`, integer coefficients), as in the standard.
  A coefficient that is required to lie in `[0, b]` (or `b - w_i ≥ 0`) is turned into a `Nat` with `Int.toNat`;
  FIPS 204 leaves the behavior outside those ranges undefined, and every call in the standard is in range.
* "Split a byte string into consecutive pieces" (steps `(ρ, z₀, ..., z_{k-1}) ← pk` of the decoders) is
  `slice v off len`, the `len` bytes of `v` starting at `off`.
* The hint `h ∈ R_2^k` is a `Vector (Vector Bool 256) k`.
* `sigDecode` returns `none` exactly when the hint is malformed (FIPS 204 Algorithm 27 returns `⊥` as the
  result of `HintBitUnpack`; Algorithm 8 step 3 turns that into `false`).
* Inputs are assumed to have the lengths the standard gives them. On a shorter input the decoders do not fail:
  `slice` truncates and `BitsToInteger` reads missing bits as 0. `Verify_internal` checks |pk| and |σ| first;
  `Sign_internal`'s refinement theorem assumes |sk| = skLen. `HintBitPack` likewise assumes at most ω ones
  (Algorithm 7 step 28 guarantees it); with more, `set!` writes out of place.
* `HintBitUnpack`'s `while Index < y[ω+i]` runs `y[ω+i] − First` times; it is written as a `for` over that
  range with `Index` still incremented in the body (a Lean `while` is `partial`, so opaque to proofs).
-/

namespace Spec

/-- `slice v off len`: the bytes `v[off], ..., v[off + len - 1]`. -/
def slice (v : List UInt8) (off len : Nat) : List UInt8 := (v.drop off).take len

/-- Algorithm 16: SimpleBitPack(w, b). Encodes a polynomial `w` with coefficients in `[0, b]` into a byte
string of length `32 ⋅ bitlen b`. -/
def SimpleBitPack (w : RPoly) (b : Nat) : List UInt8 := Id.run do
  let mut z : List Bool := []                       -- 1
  for i in [0:256] do                               -- 2
    z := z ++ IntegerToBits (w[i]!).toNat (bitlen b)    -- 3
  return BitsToBytes z                              -- 5

/-- Algorithm 17: BitPack(w, a, b). Encodes a polynomial `w` with coefficients in `[−a, b]` into a byte
string of length `32 ⋅ bitlen (a + b)`. -/
def BitPack (w : RPoly) (a b : Nat) : List UInt8 := Id.run do
  let mut z : List Bool := []                       -- 1
  for i in [0:256] do                               -- 2
    z := z ++ IntegerToBits ((b : Int) - w[i]!).toNat (bitlen (a + b))    -- 3
  return BitsToBytes z                              -- 5

/-- Algorithm 18: SimpleBitUnpack(v, b). Reverses `SimpleBitPack`. `v` has `32 ⋅ bitlen b` bytes; the
coefficients of the result lie in `[0, 2^c − 1]`, `c = bitlen b`. -/
def SimpleBitUnpack (v : List UInt8) (b : Nat) : RPoly := Id.run do
  let c := bitlen b                                 -- 1
  let z := BytesToBits v                            -- 2
  let mut w : RPoly := Vector.replicate 256 0
  for i in [0:256] do                               -- 3
    w := w.set! i (BitsToInteger ((z.drop (i * c)).take c) c : Nat)    -- 4: (z[ic], ..., z[ic + c − 1])
  return w                                          -- 6

/-- Algorithm 19: BitUnpack(v, a, b). Reverses `BitPack`. `v` has `32 ⋅ bitlen (a + b)` bytes; the
coefficients of the result lie in `[b − 2^c + 1, b]`, `c = bitlen (a + b)`. -/
def BitUnpack (v : List UInt8) (a b : Nat) : RPoly := Id.run do
  let c := bitlen (a + b)                           -- 1
  let z := BytesToBits v                            -- 2
  let mut w : RPoly := Vector.replicate 256 0
  for i in [0:256] do                               -- 3
    w := w.set! i ((b : Int) - (BitsToInteger ((z.drop (i * c)).take c) c : Nat))    -- 4
  return w                                          -- 6

/-- Algorithm 20: HintBitPack(h). Encodes a hint vector `h ∈ R_2^k` with at most `ω` nonzero coefficients
into a byte string of length `ω + k`. -/
def HintBitPack (p : Params) (h : Vector HintPoly p.k) : List UInt8 := Id.run do
  let mut y : Array UInt8 := Array.replicate (p.ω + p.k) 0     -- 1
  let mut Index := 0                                -- 2
  for i in [0:p.k] do                               -- 3
    for j in [0:256] do                             -- 4
      if h[i]![j]! then                             -- 5: h[i]_j ≠ 0
        y := y.set! Index j.toUInt8                 -- 6
        Index := Index + 1                          -- 7
    y := y.set! (p.ω + i) Index.toUInt8             -- 10
  return y.toList                                   -- 12

/-- Algorithm 21: HintBitUnpack(y). Reverses `HintBitPack`; `y` has `ω + k` bytes. Returns `none` (`⊥`) for a
malformed encoding. -/
def HintBitUnpack (p : Params) (y : List UInt8) : Option (Vector HintPoly p.k) := Id.run do
  let mut h : Vector HintPoly p.k := Vector.replicate p.k (Vector.replicate 256 false)   -- 1
  let mut Index := 0                                -- 2
  for i in [0:p.k] do                               -- 3
    let yi := (y[p.ω + i]!).toNat
    if yi < Index ∨ yi > p.ω then return none       -- 4-5: malformed input
    let First := Index                              -- 6
    for _ in [First:yi] do                          -- 7: while Index < y[ω + i]
      if Index > First then                         -- 8
        if y[Index - 1]! ≥ y[Index]! then return none     -- 9-10: malformed input
      h := h.set! i (h[i]!.set! (y[Index]!).toNat true)   -- 12
      Index := Index + 1                            -- 13
  for i in [Index:p.ω] do                           -- 16
    if y[i]! ≠ 0 then return none                   -- 17-18: malformed input
  return some h                                     -- 20

/-- The number of bits per coefficient of `t₁`: `bitlen (q − 1) − d` (10 in all parameter sets). -/
def Params.t1Bits (p : Params) : Nat := bitlen (q - 1) - p.d

/-- Algorithm 22: pkEncode(ρ, t₁). Encodes a public key into a byte string. -/
def pkEncode (p : Params) (ρ : List UInt8) (t₁ : Vector RPoly p.k) : List UInt8 := Id.run do
  let mut pk := ρ                                   -- 1
  for i in [0:p.k] do                               -- 2
    pk := pk ++ SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1)    -- 3
  return pk                                         -- 5

/-- Algorithm 23: pkDecode(pk). Reverses `pkEncode`; returns `(ρ, t₁)`. -/
def pkDecode (p : Params) (pk : List UInt8) : List UInt8 × Vector RPoly p.k := Id.run do
  let ρ := pk.take 32                               -- 1: (ρ, z₀, ..., z_{k−1}) <- pk
  let mut t₁ : Vector RPoly p.k := Vector.replicate p.k (Vector.replicate 256 0)
  for i in [0:p.k] do                               -- 2
    let zᵢ := slice pk (32 + i * (32 * p.t1Bits)) (32 * p.t1Bits)
    t₁ := t₁.set! i (SimpleBitUnpack zᵢ (2 ^ p.t1Bits - 1))    -- 3
  return (ρ, t₁)                                    -- 5

/-- Algorithm 24: skEncode(ρ, K, tr, s₁, s₂, t₀). Encodes a private key into a byte string. -/
def skEncode (p : Params) (ρ K tr : List UInt8) (s₁ : Vector RPoly p.ℓ) (s₂ t₀ : Vector RPoly p.k) :
    List UInt8 := Id.run do
  let mut sk := ρ ++ K ++ tr                        -- 1
  for i in [0:p.ℓ] do                               -- 2
    sk := sk ++ BitPack s₁[i]! p.η p.η              -- 3
  for i in [0:p.k] do                               -- 5
    sk := sk ++ BitPack s₂[i]! p.η p.η              -- 6
  for i in [0:p.k] do                               -- 8
    sk := sk ++ BitPack t₀[i]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))    -- 9
  return sk                                         -- 11

/-- Algorithm 25: skDecode(sk). Reverses `skEncode`; returns `(ρ, K, tr, s₁, s₂, t₀)`. For a malformed `sk`
the coefficients of `s₁`, `s₂` may lie outside `[−η, η]` (see the comments at steps 3 and 6 of FIPS 204). -/
def skDecode (p : Params) (sk : List UInt8) :
    List UInt8 × List UInt8 × List UInt8 × Vector RPoly p.ℓ × Vector RPoly p.k × Vector RPoly p.k := Id.run do
  let ρ := slice sk 0 32                            -- 1: (ρ, K, tr, y₀, ..., y_{ℓ−1}, z₀, ..., z_{k−1}, w₀, ..., w_{k−1}) <- sk
  let K := slice sk 32 32
  let tr := slice sk 64 64
  let szη := 32 * bitlen (2 * p.η)                  -- length of each y_i and z_i
  let szt := 32 * p.d                               -- length of each w_i
  let mut s₁ : Vector RPoly p.ℓ := Vector.replicate p.ℓ (Vector.replicate 256 0)
  let mut s₂ : Vector RPoly p.k := Vector.replicate p.k (Vector.replicate 256 0)
  let mut t₀ : Vector RPoly p.k := Vector.replicate p.k (Vector.replicate 256 0)
  for i in [0:p.ℓ] do                               -- 2
    let yᵢ := slice sk (128 + i * szη) szη
    s₁ := s₁.set! i (BitUnpack yᵢ p.η p.η)          -- 3
  for i in [0:p.k] do                               -- 5
    let zᵢ := slice sk (128 + p.ℓ * szη + i * szη) szη
    s₂ := s₂.set! i (BitUnpack zᵢ p.η p.η)          -- 6
  for i in [0:p.k] do                               -- 8
    let wᵢ := slice sk (128 + (p.ℓ + p.k) * szη + i * szt) szt
    t₀ := t₀.set! i (BitUnpack wᵢ (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1)))    -- 9
  return (ρ, K, tr, s₁, s₂, t₀)                     -- 11

/-- Algorithm 26: sigEncode(c̃, z, h). Encodes a signature into a byte string. `c̃` has `λ/4` bytes and
`z ∈ R^ℓ` has coefficients in `[−γ₁ + 1, γ₁]`. -/
def sigEncode (p : Params) (c_tilde : List UInt8) (z : Vector RPoly p.ℓ) (h : Vector HintPoly p.k) :
    List UInt8 := Id.run do
  let mut σ := c_tilde                                    -- 1
  for i in [0:p.ℓ] do                               -- 2
    σ := σ ++ BitPack z[i]! (p.γ₁ - 1) p.γ₁         -- 3
  σ := σ ++ HintBitPack p h                         -- 5
  return σ                                          -- 6

/-- Algorithm 27: sigDecode(σ). Reverses `sigEncode`; returns `(c̃, z, h)`, or `none` (`⊥`) when `h` is
malformed. -/
def sigDecode (p : Params) (σ : List UInt8) :
    Option (List UInt8 × Vector RPoly p.ℓ × Vector HintPoly p.k) := Id.run do
  let szz := 32 * (1 + bitlen (p.γ₁ - 1))           -- length of each x_i
  let c_tilde := slice σ 0 (p.lam / 4)                    -- 1: (c̃, x₀, ..., x_{ℓ−1}, y) <- σ
  let y := slice σ (p.lam / 4 + p.ℓ * szz) (p.ω + p.k)
  let mut z : Vector RPoly p.ℓ := Vector.replicate p.ℓ (Vector.replicate 256 0)
  for i in [0:p.ℓ] do                               -- 2
    let xᵢ := slice σ (p.lam / 4 + i * szz) szz
    z := z.set! i (BitUnpack xᵢ (p.γ₁ - 1) p.γ₁)    -- 3
  let some h := HintBitUnpack p y | return none     -- 5 (h = ⊥ makes the result ⊥)
  return some (c_tilde, z, h)                             -- 6

/-- Algorithm 28: w1Encode(w₁). Encodes a polynomial vector `w₁ ∈ R^k` with coefficients in
`[0, (q − 1)/(2γ₂) − 1]` into a byte string of length `32 k ⋅ bitlen ((q − 1)/(2γ₂) − 1)`. -/
def w1Encode (p : Params) (w₁ : Vector RPoly p.k) : List UInt8 := Id.run do
  let mut w1_tilde : List UInt8 := []                     -- 1
  for i in [0:p.k] do                               -- 2
    w1_tilde := w1_tilde ++ SimpleBitPack w₁[i]! ((q - 1) / (2 * p.γ₂) - 1)    -- 3
  return w1_tilde                                         -- 5

end Spec
