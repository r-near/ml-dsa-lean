import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Vector.Basic

/-!
# FIPS 204, Algorithms 41 and 42: NTT(w) and NTT⁻¹(ŵ)

Representation choices.

* Coefficients live in `ZMod q`, so `+`, `-`, `*` are the ring operations of Z_q and the "mod q" in the
  algorithm steps is implicit. `ZMod 8380417` unfolds to `Fin 8380417`, so closed terms still evaluate.
* A polynomial is `Vector (ZMod q) 256` (a length-indexed array): the loop bodies read as the pseudocode does
  (`ŵ[j]`, `ŵ.set! j v`), and there is no bounds-proof clutter.
* Pseudocode `while` loops with a known trip count are written as `for` loops over `Std.Range` (the trip
  count is noted in a comment). Algorithm 41 steps 4-14 split into `nttLayer` (steps 5-13, one value of `len`)
  and the outer loop in `NTT`.
-/

namespace Spec

/-- FIPS 204 Table 1: the modulus q = 2^23 - 2^13 + 1. -/
abbrev q : Nat := 8380417

/-- Z_q. -/
abbrev Zq := ZMod q

/-- A polynomial of R_q (or its NTT image T_q) as a vector of 256 coefficients. -/
abbrev Poly := Vector Zq 256

/-- The 512th root of unity ζ = 1753 in Z_q (FIPS 204, Section 7.5). -/
def ζ : Zq := 1753

/-- BitRev8(m) (FIPS 204, Section 7.5): the integer whose 8-bit representation is that of `m`, reversed.
Meant for `m < 256`. -/
def BitRev8 (m : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + ((m >>> i) % 2) * 2 ^ (7 - i)) 0

/-- The twiddle factor `ζ^BitRev8(k) mod q` (the entries of the table in FIPS 204, Appendix B). -/
def zeta (k : Nat) : Zq := ζ ^ BitRev8 k

/-- Steps 5-13 of Algorithm 41 for one value of `len`: all `256 / (2 len)` blocks. Takes and returns the
pair `(ŵ, m)` of the running polynomial and the twiddle counter. -/
def nttLayer (len : Nat) (ŵ : Poly) (m : Nat) : Poly × Nat := Id.run do
  let mut ŵ := ŵ
  let mut m := m
  let mut start := 0                            -- 5
  for _ in [0:256 / (2 * len)] do               -- 6: while start < 256 (256 / (2 len) blocks)
    m := m + 1                                  -- 7
    let z := zeta m                             -- 8: z <- ζ^BitRev8(m) mod q
    for j in [start:start + len] do             -- 9: j = start, ..., start + len - 1
      let t := z * ŵ[j + len]!                  -- 10
      ŵ := ŵ.set! (j + len) (ŵ[j]! - t)         -- 11
      ŵ := ŵ.set! j (ŵ[j]! + t)                 -- 12
    start := start + 2 * len                    -- 13
  return (ŵ, m)

/-- Algorithm 41: NTT(w). Computes the NTT of the polynomial `w` in R_q. -/
def NTT (w : Poly) : Poly := Id.run do
  let mut ŵ := w                                -- 1
  let mut m := 0                                -- 2
  let mut len := 128                            -- 3
  for _ in [0:8] do                             -- 4: while len >= 1 (len = 128, 64, ..., 1)
    (ŵ, m) := nttLayer len ŵ m                  -- 5-13
    len := len / 2                              -- 14
  return ŵ                                      -- 15

/-- Steps 5-14 of Algorithm 42 for one value of `len`: all `256 / (2 len)` blocks. Takes and returns the
pair `(w, m)` of the running polynomial and the twiddle counter (which counts down). -/
def nttInvLayer (len : Nat) (w : Poly) (m : Nat) : Poly × Nat := Id.run do
  let mut w := w
  let mut m := m
  let mut start := 0                            -- 5
  for _ in [0:256 / (2 * len)] do               -- 6: while start < 256 (256 / (2 len) blocks)
    m := m - 1                                  -- 7
    let z := -zeta m                            -- 8: z <- -ζ^BitRev8(m) mod q
    for j in [start:start + len] do             -- 9: j = start, ..., start + len - 1
      let t := w[j]!                            -- 10
      w := w.set! j (t + w[j + len]!)           -- 11
      w := w.set! (j + len) (t - w[j + len]!)   -- 12
      w := w.set! (j + len) (z * w[j + len]!)   -- 13
    start := start + 2 * len                    -- 14
  return (w, m)

/-- Algorithm 42: NTT⁻¹(ŵ). Computes the inverse NTT of `ŵ` in T_q. -/
def NTTInv (ŵ : Poly) : Poly := Id.run do
  let mut w := ŵ                                -- 1
  let mut m := 256                              -- 2
  let mut len := 1                              -- 3
  for _ in [0:8] do                             -- 4: while len < 256 (len = 1, 2, ..., 128)
    (w, m) := nttInvLayer len w m               -- 5-14
    len := 2 * len                              -- 15
  let f : Zq := 8347681                         -- 16: f = 256⁻¹ mod q
  for j in [0:256] do                           -- 17
    w := w.set! j (f * w[j]!)                   -- 18
  return w                                      -- 19

end Spec
