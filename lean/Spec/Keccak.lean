/-!
# FIPS 202: Keccak-f[1600] and SHAKE128 / SHAKE256

Representation choices.

* The state is lane-level: `State := Vector UInt64 25`, lane `A[x, y]` stored at index `x + 5 y`
  (`x, y` taken mod 5). The FIPS 202 §3.1.2 correspondence with the bit string `S` and the state array is
  `A[x, y, z] = S[64 (5 y + x) + z]`, i.e. bit `z` (numbered from the least significant end) of lane `x + 5 y`.
  Byte `i` of `S` (FIPS 202 Appendix B.1: bits of a byte are least significant first) is therefore
  `(lane (i / 8) >>> (8 * (i % 8))) % 256`: lanes are little-endian byte strings.
* The step mappings θ ρ π χ ι act on whole lanes. Each is the lane-wise reading of the corresponding FIPS 202
  algorithm: "bit `z` of `A'[x,y]`" statements become word operations (`z - k mod 64` becomes a rotation).
  The ρ offsets are derived from the walk of Algorithm 2 and the round constants from the LFSR `rc(t)` of
  Algorithm 5 (not listed by hand); `decide +kernel` theorems check both against the well-known tables.
* Messages and outputs are byte strings (`List UInt8`), bits within a byte least significant first (FIPS 204
  §3.7, §2.3). The SHAKE domain suffix `1111` followed by `pad10*1` is therefore the byte `0x1F` (suffix bits
  1,1,1,1 then the first `1` of the pad) and, in the last byte of the block, `0x80` (the closing `1`);
  when both fall in the same byte they combine to `0x9F`.
* Evaluation: everything is executable and cheap. The round constants live in a table computed once, and the
  sponge squeezes only as many permutations as the requested length needs.
-/

namespace Spec

namespace Keccak

/-- Keccak state of width 1600: 25 lanes of 64 bits, lane `A[x, y]` at index `x + 5 y`. -/
abbrev State := Vector UInt64 25

/-- The all-zero state (Algorithm 8 step 5: `S = 0^b`). -/
def zeroState : State := Vector.replicate 25 0

/-- Lane `A[x, y]` (coordinates mod 5). -/
def lane (A : State) (x y : Nat) : UInt64 := A[x % 5 + 5 * (y % 5)]!

/-- Build a state from a function of the coordinates `(x, y)`. -/
def ofLanes (f : Nat → Nat → UInt64) : State :=
  Vector.ofFn (n := 25) fun i => f (i.val % 5) (i.val / 5)

/-- Rotate a lane left by `n` bit positions (mod 64): bit `z` of the result is bit `z - n mod 64` of `v`.
(Lean's `UInt64` shifts take the shift amount mod 64, so `n % 64 = 0` is handled too.) -/
def rotl (v : UInt64) (n : Nat) : UInt64 :=
  (v <<< (n % 64).toUInt64) ||| (v >>> (64 - n % 64).toUInt64)

/-! ### Algorithm 5: rc(t), the LFSR round-constant bits -/

/-- One iteration of the loop of Algorithm 5 (step 3) on `R = R[0] ... R[7]` (as a list, `R[0]` first):
`R = 0 ‖ R; R[0] ⊕= R[8]; R[4] ⊕= R[8]; R[5] ⊕= R[8]; R[6] ⊕= R[8]; R = Trunc8(R)`. -/
def rcStep (R : List Bool) : List Bool :=
  let R := false :: R                                           -- 3.a
  let r8 := R.getD 8 false
  let R := R.set 0 (R.getD 0 false ^^ r8)                       -- 3.b
  let R := R.set 4 (R.getD 4 false ^^ r8)                       -- 3.c
  let R := R.set 5 (R.getD 5 false ^^ r8)                       -- 3.d
  let R := R.set 6 (R.getD 6 false ^^ r8)                       -- 3.e
  R.take 8                                                      -- 3.f

/-- `rcStep` applied `n` times (the loop of Algorithm 5, step 3). -/
def rcIter : Nat → List Bool → List Bool
  | 0, R => R
  | n + 1, R => rcIter n (rcStep R)

/-- Algorithm 5: rc(t). -/
def rc (t : Nat) : Bool :=
  if t % 255 = 0 then true                                      -- 1
  else (rcIter (t % 255) [true, false, false, false, false, false, false, false]).getD 0 false  -- 2-4

/-- Algorithm 6, steps 2-3: the round constant `RC` of round `ir` as a lane, `RC[2^j - 1] = rc(j + 7 ir)`
for `0 ≤ j ≤ ℓ = 6`. -/
def RC (ir : Nat) : UInt64 :=
  (List.range 7).foldl (fun acc j => if rc (j + 7 * ir) then acc ||| ((1 : UInt64) <<< (2 ^ j - 1).toUInt64) else acc) 0

/-- The 24 round constants, computed once. -/
def RCs : Array UInt64 := (Array.range 24).map RC

/-! ### Algorithm 2: the ρ offsets -/

/-- The rotation offsets of ρ (FIPS 202 Table 2), at index `x + 5 y`, derived by walking Algorithm 2:
`(x, y) = (1, 0)`; for `t = 0..23`, lane `(x, y)` gets offset `(t+1)(t+2)/2` and
`(x, y) ← (y, (2x + 3y) mod 5)`. Lane `(0, 0)` has offset 0. Offsets are reduced mod 64. -/
def rhoOffsets : Array Nat :=
  ((List.range 24).foldl
    (fun (acc : Array Nat × Nat × Nat) t =>
      (acc.1.set! (acc.2.1 + 5 * acc.2.2) ((t + 1) * (t + 2) / 2 % 64), acc.2.2, (2 * acc.2.1 + 3 * acc.2.2) % 5))
    (Array.replicate 25 0, 1, 0)).1

/-! ### Section 3.2: the step mappings -/

/-- Algorithm 1: θ. `C[x] = A[x,0] ⊕ ... ⊕ A[x,4]`, `D[x] = C[x-1] ⊕ rotl(C[x+1], 1)`,
`A'[x,y] = A[x,y] ⊕ D[x]`. -/
def theta (A : State) : State :=
  let C := Vector.ofFn (n := 5) fun x =>                                       -- 1
    lane A x 0 ^^^ lane A x 1 ^^^ lane A x 2 ^^^ lane A x 3 ^^^ lane A x 4
  let D := Vector.ofFn (n := 5) fun x =>                                       -- 2
    C[(x.val + 4) % 5]! ^^^ rotl C[(x.val + 1) % 5]! 1
  ofLanes fun x y => lane A x y ^^^ D[x]!                                      -- 3

/-- Algorithm 2: ρ. `A'[x,y] = rotl(A[x,y], offset(x,y))`. -/
def rho (A : State) : State :=
  ofLanes fun x y => rotl (lane A x y) rhoOffsets[x + 5 * y]!

/-- Algorithm 3: π. `A'[x,y] = A[(x + 3y) mod 5, x]`. -/
def pi (A : State) : State :=
  ofLanes fun x y => lane A (x + 3 * y) x

/-- Algorithm 4: χ. `A'[x,y] = A[x,y] ⊕ (¬A[x+1,y] ∧ A[x+2,y])`. -/
def chi (A : State) : State :=
  ofLanes fun x y => lane A x y ^^^ (~~~ lane A (x + 1) y &&& lane A (x + 2) y)

/-- Algorithm 6: ι. Only lane `(0, 0)` changes: `A'[0,0] = A[0,0] ⊕ RC[ir]`. -/
def iota (A : State) (ir : Nat) : State :=
  A.set! 0 (A[0]! ^^^ RCs[ir]!)

/-- `Rnd(A, ir) = ι(χ(π(ρ(θ(A)))), ir)` (§3.3). -/
def Rnd (A : State) (ir : Nat) : State :=
  iota (chi (pi (rho (theta A)))) ir

/-- Algorithm 7 / §3.4: Keccak-f[1600] = Keccak-p[1600, 24], rounds `ir = 0, ..., 23`. -/
def _root_.Spec.KeccakF1600 (A : State) : State :=
  (List.range 24).foldl Rnd A

/-! ### Algorithm 9 and 8: padding and the sponge -/

/-- Algorithm 9 for SHAKE, in byte form: `M ‖ 1111 ‖ pad10*1(8r, 8|M| + 4)`, a whole number of `r`-byte blocks.
At least one byte is appended. With bits least significant first, the suffix `1111` and the opening `1` of
the pad give `0x1F`, the closing `1` gives `0x80`; if one byte is appended, both are in it (`0x9F`). -/
def pad101 (r : Nat) (M : List UInt8) : List UInt8 :=
  let k := r - M.length % r
  M ++ (if k = 1 then [0x9F] else 0x1F :: List.replicate (k - 2) 0 ++ [0x80])

/-- `S ⊕ (P_i ‖ 0^c)` (Algorithm 8 step 6): XOR an `r`-byte block (little-endian lanes) into the state. -/
def xorBlock (S : State) (blk : List UInt8) : State :=
  let b := blk.toArray
  Vector.ofFn (n := 25) fun i =>
    S[i.val]! ^^^ (List.range 8).foldl
      (fun acc j => acc ||| ((b.getD (8 * i.val + j) 0).toUInt64 <<< (8 * j).toUInt64)) 0

/-- Algorithm 8 steps 6-7: absorb the `r`-byte blocks of `P` (`P.length` a multiple of `r`). -/
def absorb (r : Nat) (S : State) (P : List UInt8) : State :=
  if 0 < r ∧ r ≤ P.length then
    absorb r (KeccakF1600 (xorBlock S (P.take r))) (P.drop r)
  else S
termination_by P.length
decreasing_by
  all_goals (try simp only [List.length_drop])
  omega

/-- `Trunc_r(S)` as bytes: the first `r` bytes of the state (little-endian lanes). -/
def stateBytes (r : Nat) (S : State) : List UInt8 :=
  (List.range r).map fun k => (S[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8

/-- Algorithm 8, steps 8-10 (squeezing): output `d` bytes, `r` per permutation, permuting only when more output
is needed. -/
def squeeze (r : Nat) (d : Nat) (S : State) : List UInt8 :=
  if d ≤ r ∨ r = 0 then (stateBytes r S).take d
  else stateBytes r S ++ squeeze r (d - r) (KeccakF1600 S)
termination_by d
decreasing_by
  omega

/-- `SPONGE[Keccak-f[1600], pad10*1, 8r](M ‖ 1111, 8d)` on bytes, rate `r` bytes. -/
def sponge (r : Nat) (M : List UInt8) (d : Nat) : List UInt8 :=
  squeeze r d (absorb r zeroState (pad101 r M))

end Keccak

/-- SHAKE128(M, 8d): the first `d` bytes of the SHAKE128 output on byte string `M` (FIPS 202 §6.2, bytes
little-endian bit order as in FIPS 204 §3.7/§2.3). Rate 168 bytes (r = 1344 = 1600 - 256). -/
def SHAKE128 (M : List UInt8) (d : Nat) : List UInt8 := Keccak.sponge 168 M d

/-- SHAKE256(M, 8d). Rate 136 bytes (r = 1088 = 1600 - 512). -/
def SHAKE256 (M : List UInt8) (d : Nat) : List UInt8 := Keccak.sponge 136 M d

/-! ### Checks of the derived tables against the published ones -/

/-- The ρ offsets agree with FIPS 202 Table 2 (and the `RHO` table of `src/keccak.rs`). -/
theorem Keccak.rhoOffsets_eq :
    Keccak.rhoOffsets.toList =
      [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14] := by
  decide +kernel

/-- The LFSR-derived round constants agree with the published table (and the `RC` table of
`src/keccak.rs`). -/
theorem Keccak.RCs_eq :
    Keccak.RCs.toList.map UInt64.toNat =
      [0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
       0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
       0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
       0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
       0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
       0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008] := by
  decide +kernel

/-! ### Properties of the sponge -/

namespace Keccak

theorem length_stateBytes (r : Nat) (S : State) : (stateBytes r S).length = r := by
  simp [stateBytes]

/-- `squeeze` returns exactly `d` bytes (for a positive rate). -/
theorem length_squeeze (r : Nat) (hr : 0 < r) :
    ∀ (d : Nat) (S : State), (squeeze r d S).length = d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro S
    rw [squeeze]
    by_cases h : d ≤ r ∨ r = 0
    · rw [if_pos h]
      simp only [List.length_take, length_stateBytes]
      omega
    · rw [if_neg h]
      have h' : d - r < d := by omega
      rw [List.length_append, length_stateBytes, ih (d - r) h']
      omega

/-- Incremental squeezing: the first `d` bytes of a longer output are the shorter output. -/
theorem squeeze_prefix (r : Nat) (hr : 0 < r) :
    ∀ (d e : Nat) (S : State), squeeze r d S = (squeeze r (d + e) S).take d := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro e S
    by_cases h1 : d ≤ r
    · have hl : squeeze r d S = (stateBytes r S).take d := by
        rw [squeeze, if_pos (Or.inl h1)]
      rw [hl]
      by_cases h2 : d + e ≤ r
      · have : squeeze r (d + e) S = (stateBytes r S).take (d + e) := by
          rw [squeeze, if_pos (Or.inl h2)]
        rw [this, List.take_take]
        congr 1
        omega
      · have : squeeze r (d + e) S = stateBytes r S ++ squeeze r (d + e - r) (KeccakF1600 S) := by
          rw [squeeze, if_neg (by omega)]
        rw [this, List.take_append_of_le_length (by rw [length_stateBytes]; exact h1)]
    · have hl : squeeze r d S = stateBytes r S ++ squeeze r (d - r) (KeccakF1600 S) := by
        rw [squeeze, if_neg (by omega)]
      have hr' : squeeze r (d + e) S = stateBytes r S ++ squeeze r (d + e - r) (KeccakF1600 S) := by
        rw [squeeze, if_neg (by omega)]
      rw [hl, hr', List.take_append, length_stateBytes, List.take_of_length_le (by rw [length_stateBytes]; omega)]
      congr 1
      have h3 : d + e - r = (d - r) + e := by omega
      rw [h3]
      exact ih (d - r) (by omega) e _

end Keccak

/-- Prefix property (incremental squeezing): consecutive `Squeeze` calls are one longer output. -/
theorem SHAKE128_prefix (M : List UInt8) (d e : Nat) : SHAKE128 M d = (SHAKE128 M (d + e)).take d :=
  Keccak.squeeze_prefix 168 (by omega) d e _

/-- Prefix property for SHAKE256. -/
theorem SHAKE256_prefix (M : List UInt8) (d e : Nat) : SHAKE256 M d = (SHAKE256 M (d + e)).take d :=
  Keccak.squeeze_prefix 136 (by omega) d e _

/-- `SHAKE128 M d` has `d` bytes. -/
theorem SHAKE128_length (M : List UInt8) (d : Nat) : (SHAKE128 M d).length = d :=
  Keccak.length_squeeze 168 (by omega) d _

/-- `SHAKE256 M d` has `d` bytes. -/
theorem SHAKE256_length (M : List UInt8) (d : Nat) : (SHAKE256 M d).length = d :=
  Keccak.length_squeeze 136 (by omega) d _

end Spec
