import Proofs.ExpandA4

/-!
# `tr = H(pk, 64)`: the block schedule of the SHAKE256 absorb, lane by lane

The pure side of `docs/assurance.md` section 1.9 ("`tr` in the fourth lane of the 4-way ExpandA"). For a message `M` (the
public key) the padded message `Pd M = pad101 136 M` has `M.length / 136 + 1` blocks of 136 bytes. `HS M t` is the sponge
state after the first `t` blocks have been absorbed and permuted (`t = 0`: the zero state). `HS_succ` is the one
step the extracted code takes per permutation: XOR block `t` into the state, permute. `shake256_byte` reads `SHAKE256(M, 64)`
off `HS M (M.length / 136 + 1)`.

`Wb blk k` is the little-endian lane `k` of a block (what `Spec.Keccak.xorBlock` XORs into lane `k`); `xor17` is the
state with the 17 rate lanes of a 136-byte block XORed in. The Rust code computes the lanes of block `t` either from `pk`
(`keccak.load_lane`) or from the padded tail lanes (`sampling.tr_tail_lanes`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## The padded message and its blocks -/

/-- The padded message of `SHAKE256`. -/
abbrev Pd (M : List UInt8) : List UInt8 := Spec.Keccak.pad101 136 M

theorem Pd_eq (M : List UInt8) : Pd M = M ++ KM.padBytes (136 - M.length % 136) := rfl

theorem Pd_length (M : List UInt8) : (Pd M).length = 136 * (M.length / 136 + 1) := by
  rw [Pd_eq, List.length_append, KM.padBytes_length _ (by omega)]
  omega

/-- Block `t` of the padded message. -/
def blkT (M : List UInt8) (t : Nat) : List UInt8 := ((Pd M).drop (136 * t)).take 136

theorem blkT_length (M : List UInt8) (t : Nat) (ht : t < M.length / 136 + 1) : (blkT M t).length = 136 := by
  unfold blkT
  rw [List.length_take, List.length_drop, Pd_length]
  omega

/-- The sponge state after the first `t` blocks of the padded message have been absorbed. -/
def HS (M : List UInt8) (t : Nat) : Spec.Keccak.State :=
  Spec.Keccak.absorb 136 Spec.Keccak.zeroState ((Pd M).take (136 * t))

theorem HS_zero (M : List UInt8) : HS M 0 = Spec.Keccak.zeroState := by
  simp [HS, KM.absorb_nil]

/-- One step: XOR block `t` into the state, permute. -/
theorem HS_succ (M : List UInt8) (t : Nat) (ht : t < M.length / 136 + 1) :
    HS M (t + 1) = Spec.KeccakF1600 (Spec.Keccak.xorBlock (HS M t) (blkT M t)) := by
  have hlen := Pd_length M
  have e1 : (Pd M).take (136 * (t + 1)) = (Pd M).take (136 * t) ++ blkT M t := by
    unfold blkT
    rw [show 136 * (t + 1) = 136 * t + 136 by ring, List.take_add]
  have e2 : ((Pd M).take (136 * t)).length = t * 136 := by
    rw [List.length_take]
    omega
  unfold HS
  rw [e1, KM.absorb_append 136 (by norm_num) t _ _ _ e2, KM.absorb_one 136 (by norm_num) _ _ (blkT_length M t ht)]

/-- All blocks absorbed: the absorb phase of the sponge on the padded message. -/
theorem HS_final (M : List UInt8) :
    HS M (M.length / 136 + 1) = Spec.Keccak.absorb 136 Spec.Keccak.zeroState (Pd M) := by
  unfold HS
  rw [List.take_of_length_le (Pd_length M).le]

/-- The first 64 bytes of the output of `SHAKE256` are bytes of the final state. -/
theorem shake256_byte (M : List UInt8) (j : Nat) (hj : j < 64) :
    (Spec.SHAKE256 M 64)[j]? = some (KM.sb (HS M (M.length / 136 + 1)) j) := by
  unfold Spec.SHAKE256 Spec.Keccak.sponge
  rw [HS_final]
  have := KM.getElem?_squeeze 136 (by norm_num) 0
    (Spec.Keccak.absorb 136 Spec.Keccak.zeroState (Pd M)) 64 j (by omega) (by omega)
  simpa using this

/-! ## Blocks as lanes -/

/-- Little-endian lane `k` of a block (what `xorBlock` XORs into lane `k` of the state). -/
def Wb (blk : List UInt8) (k : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc j => acc ||| ((blk.getD (8 * k + j) 0).toUInt64 <<< (8 * j).toUInt64)) 0

theorem byteOf_Wb (blk : List UInt8) (k m : Nat) (hm : m < 8) : KM.byteOf (Wb blk k) m = blk.getD (8 * k + m) 0 := by
  unfold Wb
  rw [KM.fold_byteOf (fun j => blk.getD (8 * k + j) 0) 8 (Nat.le_refl 8) m hm, if_pos hm]

/-- A word whose bytes are those of the block's lane is `Wb`. -/
theorem eq_Wb (blk : List UInt8) (k : Nat) (X : UInt64) (h : ∀ m, m < 8 → KM.byteOf X m = blk.getD (8 * k + m) 0) :
    X = Wb blk k :=
  KM.lane_ext _ _ (fun m hm => by rw [h m hm, byteOf_Wb blk k m hm])

theorem Wb_zero_of_ge (blk : List UInt8) (hl : blk.length ≤ 136) (k : Nat) (hk : 17 ≤ k) : Wb blk k = 0 := by
  apply KM.lane_ext
  intro m hm
  rw [byteOf_Wb blk k m hm]
  have : blk.getD (8 * k + m) 0 = 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  rw [this]
  unfold KM.byteOf
  simp

/-- The state with the 17 rate lanes of `blk` XORed in. -/
def xor17 (S : Spec.Keccak.State) (blk : List UInt8) : Spec.Keccak.State :=
  Vector.ofFn fun k : Fin 25 => if k.val < 17 then S[k.val]! ^^^ Wb blk k.val else S[k.val]!

theorem xor17_getElem (S : Spec.Keccak.State) (blk : List UInt8) (k : Nat) (hk : k < 25) :
    (xor17 S blk)[k]! = if k < 17 then S[k]! ^^^ Wb blk k else S[k]! := by
  have hS : S[k]! = S[k] := getElem!_pos S k (by simpa using hk)
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp [xor17, hS]

/-- XORing a block of at most 136 bytes is XORing its first 17 lanes. -/
theorem xorBlock_eq_xor17 (S : Spec.Keccak.State) (blk : List UInt8) (hl : blk.length ≤ 136) :
    Spec.Keccak.xorBlock S blk = xor17 S blk := by
  apply KM.sb_ext
  intro j hj
  rw [KM.sb_xorBlock S blk j hj]
  unfold KM.sb
  rw [xor17_getElem S blk (j / 8) (by omega)]
  by_cases h17 : j / 8 < 17
  · rw [if_pos h17, KM.byteOf_xor, byteOf_Wb blk (j / 8) (j % 8) (by omega), show 8 * (j / 8) + j % 8 = j by omega]
  · rw [if_neg h17]
    have : blk.getD j 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [this, UInt8.xor_zero]

/-! ## The tail block -/

/-- The last block of the padded message is the bytes after the last whole block, then the padding bytes. -/
theorem blkT_last (M : List UInt8) :
    blkT M (M.length / 136) = M.drop (136 * (M.length / 136)) ++ KM.padBytes (136 - M.length % 136) := by
  unfold blkT
  rw [Pd_eq, List.drop_append_of_le_length (by omega)]
  apply List.take_of_length_le
  rw [List.length_append, List.length_drop, KM.padBytes_length _ (by omega)]
  omega

/-- A whole block before the last: its bytes are those of `M`. -/
theorem blkT_getD_full (M : List UInt8) (t : Nat) (ht : t < M.length / 136) (j : Nat) (hj : j < 136) :
    (blkT M t).getD j 0 = M.getD (136 * t + j) 0 := by
  unfold blkT
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, List.getElem?_drop, Pd_eq,
    List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]

end Proofs
