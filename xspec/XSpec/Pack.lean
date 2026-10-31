import XSpec.Bits
import XSpec.NTTOps

/-!
# Algorithms 16-19 (`SimpleBitPack`, `BitPack`, `SimpleBitUnpack`, `BitUnpack`)

Ours act on `RPoly = Vector Int 256`; ocaml-pq's `OcamlPq.Encoding.Spec` on `List ℕ` / `List ℤ` of length
256.  Adapters: `RPoly.toList` (and `Int.toNat` on each coefficient for the `ℕ`-valued `SimpleBitPack`
input), `UInt8.toNat` on bytes.  The packers are equal for every input (including out-of-range coefficients,
where both truncate to `bitlen b` bits); the unpackers return `Int`s, ocaml-pq's `simpleBitUnpack` returns
`ℕ`s (cast).
-/

open Spec

namespace XSpec

open OcamlPq.Encoding.Spec

theorem SimpleBitPack_fold (w : RPoly) (b : Nat) :
    Spec.SimpleBitPack w b = Spec.BitsToBytes
      ((List.range' 0 256).map (fun i => Spec.IntegerToBits (w[i]!).toNat (Spec.bitlen b))).flatten := by
  unfold Spec.SimpleBitPack
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem BitPack_fold (w : RPoly) (a b : Nat) :
    Spec.BitPack w a b = Spec.BitsToBytes
      ((List.range' 0 256).map (fun i =>
        Spec.IntegerToBits ((b : Int) - w[i]!).toNat (Spec.bitlen (a + b)))).flatten := by
  unfold Spec.BitPack
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem getD_toList_map_toNat (w : RPoly) (i : Nat) :
    (w.toList.map Int.toNat).getD i 0 = (w[i]!).toNat := by
  by_cases h : i < 256
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [vget! w i h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [getElem!_neg, h]

theorem getD_toList (w : RPoly) (i : Nat) : w.toList.getD i 0 = w[i]! := by
  by_cases h : i < 256
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [vget! w i h]
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp [getElem!_neg, h]

theorem flat_bits (f : Nat → List Bool) :
    bitsN ((List.range' 0 256).map f).flatten = (List.range 256).flatMap (fun i => bitsN (f i)) := by
  rw [← List.range_eq_range']
  simp [bitsN, List.flatMap_def, List.map_flatten, List.map_map]
  rfl

/-- `SimpleBitPack` (Algorithm 16). -/
theorem simpleBitPack_eq (w : RPoly) (b : Nat) :
    bytesN (Spec.SimpleBitPack w b) = simpleBitPack (w.toList.map Int.toNat) b := by
  have hl : (w.toList.map Int.toNat).length = 256 := by simp
  rw [OcamlPq.Encoding.Spec.simpleBitPack_eq _ _ hl, SimpleBitPack_fold, bitsToBytes_eq, flat_bits]
  congr 1
  rw [← flatMap_range_getD (w.toList.map Int.toNat) , hl]
  apply List.flatMap_congr
  intro i _
  rw [getD_toList_map_toNat, integerToBits_eq, bitlen_eq_size, OcamlPq.Encoding.Spec.integerToBits_eq]
  rfl

/-- `BitPack` (Algorithm 17). -/
theorem bitPack_eq (w : RPoly) (a b : Nat) :
    bytesN (Spec.BitPack w a b) = bitPack w.toList a b := by
  have hl : w.toList.length = 256 := by simp
  rw [OcamlPq.Encoding.Spec.bitPack_eq _ _ _ hl, BitPack_fold, bitsToBytes_eq, flat_bits]
  congr 1
  rw [List.flatMap_map, ← flatMap_range_getD' w.toList 0, hl]
  apply List.flatMap_congr
  intro i _
  rw [getD_toList, integerToBits_eq, bitlen_eq_size, OcamlPq.Encoding.Spec.integerToBits_eq]
  rfl

theorem tb_getD (v : List UInt8) (t : Nat) :
    (OcamlPq.Encoding.Spec.bytesToBits (bytesN v)).getD t 0 = EB.byteBit v t := by
  rw [← bytesToBits_eq]
  have := EB.bitv_BytesToBits v t
  unfold EB.bitv at this
  rw [List.getD_eq_getElem?_getD]
  simp only [bitsN, List.getElem?_map]
  rw [← this]
  cases (Spec.BytesToBits v)[t]? <;> simp

theorem unpackCodes_eq (v : List UInt8) (c : Nat) :
    unpackCodesSpec (bytesN v) c = (List.range 256).map (fun i => EB.BV (EB.byteBit v) (c * i) c) := by
  unfold unpackCodesSpec unpackCodesSpecN
  apply List.map_congr_left
  intro i _
  rw [OcamlPq.Encoding.Spec.bitsToInteger_eq, BV_eq_ofDigits]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.getD_eq_getElem _ _ (by simpa using List.mem_range.mp ht)]
  simp only [List.getElem_map, List.getElem_range]
  rw [tb_getD, Nat.mul_comm c i]

/-- `SimpleBitUnpack` (Algorithm 18). -/
theorem simpleBitUnpack_eq (v : List UInt8) (b : Nat) :
    (Spec.SimpleBitUnpack v b).toList = (simpleBitUnpack (bytesN v) b).map (fun x : ℕ => (x : ℤ)) := by
  rw [OcamlPq.Encoding.Spec.simpleBitUnpack_eq, unpackCodes_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < 256 := by simpa using h1
    simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range]
    rw [EB.SimpleBitUnpack_get v b i hi, bitlen_eq_size]
    rfl

/-- `BitUnpack` (Algorithm 19). -/
theorem bitUnpack_eq (v : List UInt8) (a b : Nat) :
    (Spec.BitUnpack v a b).toList = bitUnpack (bytesN v) a b := by
  rw [OcamlPq.Encoding.Spec.bitUnpack_eq, unpackCodes_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < 256 := by simpa using h1
    simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range]
    rw [EB.BitUnpack_get v a b i hi, bitlen_eq_size]
    rfl

end XSpec
