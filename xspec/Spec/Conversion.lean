import Spec.Params

/-!
# FIPS 204, Section 7.1: conversion between data types (Algorithms 9-13)

Bit strings are `List Bool` (`true` is the bit 1) and byte strings are `List UInt8`. Both use the
little-endian conventions of FIPS 204: bit `i` of a byte `z` is `⌊z / 2^i⌋ mod 2`, and byte `i` of an integer
`x` is `⌊x / 256^i⌋ mod 256`.

Deviations from the letter of the pseudocode, all representational:
* arrays that the pseudocode fills in by index (`y[i] ← ...`) are built with `Array.push` and converted
  to a list at the end; `BitsToBytes` accumulates in `Nat` and converts to bytes at the end (each byte is
  below 256, since it is a sum of distinct powers of two);
* `BytesToBits` keeps the copy `z'[i]` of the current byte only (the pseudocode copies the whole string).
-/

namespace Spec

/-- Algorithm 9: IntegerToBits(x, α). Computes a base-2 representation of `x mod 2^α` using little-endian
order. -/
def IntegerToBits (x α : Nat) : List Bool := Id.run do
  let mut x' := x                                   -- 1
  let mut y : Array Bool := #[]
  for _ in [0:α] do                                 -- 2: i = 0, ..., α - 1
    y := y.push (x' % 2 == 1)                       -- 3: y[i] <- x' mod 2
    x' := x' / 2                                    -- 4
  return y.toList                                   -- 6

/-- Algorithm 10: BitsToInteger(y, α). Computes the integer value expressed by a bit string (of length
`α`) using little-endian order. -/
def BitsToInteger (y : List Bool) (α : Nat) : Nat := Id.run do
  let mut x := 0                                    -- 1
  for i in [1:α + 1] do                             -- 2: i = 1, ..., α
    x := 2 * x + (y[α - i]!).toNat                  -- 3
  return x                                          -- 5

/-- Algorithm 11: IntegerToBytes(x, α). Computes a base-256 representation of `x mod 256^α` using
little-endian order. -/
def IntegerToBytes (x α : Nat) : List UInt8 := Id.run do
  let mut x' := x                                   -- 1
  let mut y : Array UInt8 := #[]
  for _ in [0:α] do                                 -- 2: i = 0, ..., α - 1
    y := y.push (x' % 256).toUInt8                  -- 3: y[i] <- x' mod 256
    x' := x' / 256                                  -- 4
  return y.toList                                   -- 6

/-- Algorithm 12: BitsToBytes(y). Converts a bit string (of length `α`) into a byte string of length
`⌈α / 8⌉` using little-endian order. -/
def BitsToBytes (y : List Bool) : List UInt8 := Id.run do
  let α := y.length
  let mut z : Array Nat := Array.replicate ((α + 7) / 8) 0       -- 1: z ∈ 𝔹^⌈α/8⌉ <- 0^⌈α/8⌉
  for i in [0:α] do                                              -- 2: i = 0, ..., α - 1
    z := z.set! (i / 8) (z[i / 8]! + (y[i]!).toNat * 2 ^ (i % 8))  -- 3
  return (z.map Nat.toUInt8).toList                              -- 5

/-- Algorithm 13: BytesToBits(z). Converts a byte string (of length `α`) into a bit string of length `8α`
using little-endian order. -/
def BytesToBits (z : List UInt8) : List Bool := Id.run do
  let mut y : Array Bool := #[]
  for i in [0:z.length] do                          -- 2: i = 0, ..., α - 1
    let mut b := (z[i]!).toNat                      -- 1: z'[i] (the byte being consumed)
    for _ in [0:8] do                               -- 3: j = 0, ..., 7
      y := y.push (b % 2 == 1)                      -- 4: y[8i + j] <- z'[i] mod 2
      b := b / 2                                    -- 5
  return y.toList                                   -- 8

end Spec
