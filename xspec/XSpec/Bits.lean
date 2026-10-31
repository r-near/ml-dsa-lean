import XSpec.EncBits
import OcamlPq

/-!
# Algorithms 9-13 (`IntegerToBits`, `BitsToInteger`, `IntegerToBytes`, `BitsToBytes`, `BytesToBits`)

Ours work on `List Bool` / `List UInt8` / `Nat`; ocaml-pq's `OcamlPq.Encoding.Spec` on `List ℕ` (bits as `0`/`1`,
bytes as naturals below 256).  Adapters: `Bool.toNat` on bits, `UInt8.toNat` on bytes.  `bitlen` is
`Nat.size`.
-/

open Spec

namespace XSpec

open OcamlPq.Encoding.Spec

/-- Bits as the naturals `0` and `1`. -/
abbrev bitsN (l : List Bool) : List ℕ := l.map Bool.toNat

/-- Bytes as naturals below 256. -/
abbrev bytesN (l : List UInt8) : List ℕ := l.map UInt8.toNat

theorem bitlen_eq_size (a : Nat) : Spec.bitlen a = Nat.size a := by
  unfold Spec.bitlen
  by_cases h : a = 0
  · simp [h]
  · rw [if_neg h]
    apply le_antisymm
    · have := Nat.lt_size.mpr (Nat.log2_self_le h |> fun h' => by simpa using h')
      omega
    · apply Nat.size_le.mpr
      exact Nat.lt_log2_self (n := a) |> fun h' => by simpa using h'

/-- `IntegerToBits` (Algorithm 9). -/
theorem integerToBits_eq (x α : Nat) :
    bitsN (Spec.IntegerToBits x α) = OcamlPq.Encoding.Spec.integerToBits x α := by
  rw [EB.IntegerToBits_eq, OcamlPq.Encoding.Spec.integerToBits_eq]
  simp only [bitsN, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  have : x / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : x / 2 ^ j % 2 = 0 ∨ x / 2 ^ j % 2 = 1) with h | h <;> simp [h]

theorem BV_eq_ofDigits (g : Nat → Nat) (s n : Nat) :
    EB.BV g s n = Nat.ofDigits 2 ((List.range n).map (fun t => g (s + t))) := by
  induction n generalizing s with
  | zero => simp [EB.BV]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.ofDigits_cons, EB.BV, ih]
    simp only [Function.comp, Nat.add_zero]
    congr 3
    apply List.map_congr_left
    intro t _
    congr 1
    omega

/-- `BitsToInteger` (Algorithm 10). -/
theorem bitsToInteger_eq (y : List Bool) (α : Nat) :
    Spec.BitsToInteger y α = OcamlPq.Encoding.Spec.bitsToInteger (bitsN y) α := by
  rw [EB.BitsToInteger_eq, BV_eq_ofDigits, OcamlPq.Encoding.Spec.bitsToInteger_eq]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [EB.bitv, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases y[t]? <;> simp

theorem bytesLoop_fst (b0 : Nat) (arr : Array UInt8) (m : Nat) :
    (List.foldl (fun (r : Nat × Array UInt8) (_ : Nat) =>
        (r.1 / 256, r.2.push (r.1 % 256).toUInt8))
      (b0, arr) (List.range' 0 m)).1 = b0 / 256 ^ m ∧
    (List.foldl (fun (r : Nat × Array UInt8) (_ : Nat) =>
        (r.1 / 256, r.2.push (r.1 % 256).toUInt8))
      (b0, arr) (List.range' 0 m)).2.toList
      = arr.toList ++ (List.range m).map (fun j => (b0 / 256 ^ j % 256).toUInt8) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · simp only [ih.1]
      rw [pow_succ, Nat.div_div_eq_div_mul]
    · simp only [Array.toList_push, ih.2, ih.1, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

/-- `IntegerToBytes` (Algorithm 11). -/
theorem integerToBytes_eq (x α : Nat) :
    bytesN (Spec.IntegerToBytes x α) = OcamlPq.Encoding.Spec.integerToBytes x α := by
  unfold Spec.IntegerToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have := (bytesLoop_fst x #[] α).2
  simp only [List.nil_append] at this
  simp only [this]
  rw [OcamlPq.Encoding.Spec.integerToBytes_eq]
  simp only [bytesN, List.map_map]
  apply List.map_congr_left
  intro j _
  simp only [Function.comp]
  have : x / 256 ^ j % 256 < 256 := Nat.mod_lt _ (by norm_num)
  simp [Nat.mod_eq_of_lt this]

theorem byteBit_cons (a : UInt8) (z : List UInt8) (t : Nat) :
    EB.byteBit (a :: z) (8 + t) = EB.byteBit z t := by
  unfold EB.byteBit
  have e1 : (8 + t) / 8 = t / 8 + 1 := by omega
  have e2 : (8 + t) % 8 = t % 8 := by omega
  rw [e1, e2]
  rfl

theorem byteBit_cons_lt (a : UInt8) (z : List UInt8) (t : Nat) (ht : t < 8) :
    EB.byteBit (a :: z) t = a.toNat / 2 ^ t % 2 := by
  unfold EB.byteBit
  have e1 : t / 8 = 0 := by omega
  have e2 : t % 8 = t := by omega
  rw [e1, e2]
  rfl

theorem bytes_flat (z : List UInt8) :
    (List.range (8 * z.length)).map (fun t => EB.byteBit z t) =
      (bytesN z).flatMap (fun c => (List.range 8).map (fun i => c / 2 ^ i % 2)) := by
  induction z with
  | nil => simp
  | cons a z ih =>
    rw [List.length_cons, show 8 * (z.length + 1) = 8 + 8 * z.length by ring, List.range_add,
      List.map_append, List.map_map]
    simp only [bytesN, List.map_cons, List.flatMap_cons]
    rw [← bytesN, ← ih]
    have h1 : (List.range 8).map (fun t => EB.byteBit (a :: z) t) =
        (List.range 8).map (fun i => a.toNat / 2 ^ i % 2) := by
      apply List.map_congr_left
      intro t ht
      exact byteBit_cons_lt a z t (List.mem_range.mp ht)
    have h2 : (List.range (8 * z.length)).map ((fun t => EB.byteBit (a :: z) t) ∘ fun x => 8 + x) =
        (List.range (8 * z.length)).map (fun t => EB.byteBit z t) := by
      apply List.map_congr_left
      intro t _
      exact byteBit_cons a z t
    rw [h1, h2]

/-- `BytesToBits` (Algorithm 13). -/
theorem bytesToBits_eq (z : List UInt8) :
    bitsN (Spec.BytesToBits z) = OcamlPq.Encoding.Spec.bytesToBits (bytesN z) := by
  rw [OcamlPq.Encoding.Spec.bytesToBits_eq, EB.BytesToBits_eq, ← bytes_flat]
  simp only [bitsN, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp]
  exact EB.beq_one_toNat _ (EB.byteBit_le z t)

theorem BitsToBytes_fold (y : List Bool) : Spec.BitsToBytes y =
    ((List.foldl (EB.bstep y) (Array.replicate ((y.length + 7) / 8) 0)
      (List.range' 0 y.length)).map Nat.toUInt8).toList := by
  unfold Spec.BitsToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rfl

theorem setIfInBounds_toList (A : Array Nat) (j : Nat) (hj : j < A.size) (δ : Nat) :
    (A.setIfInBounds j (A[j]! + δ)).toList = A.toList.modify j (· + δ) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_modify]
    simp only [Array.toList_setIfInBounds, List.getElem_set]
    have hg := getElem!_pos A j hj
    by_cases hk : j = k
    · subst hk; simp [hg]
    · simp [hk]

theorem bytes_loop_corr (y : List Bool) (n : Nat) (hn : n ≤ y.length) :
    (List.foldl (EB.bstep y) (Array.replicate ((y.length + 7) / 8) 0) (List.range' 0 n)).toList =
      (List.range n).foldl (fun (z : List ℕ) i => z.modify (i / 8) (· + (bitsN y).getD i 0 * 2 ^ (i % 8)))
        (List.replicate ((y.length + 7) / 8) 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    obtain ⟨hs, -⟩ := EB.bstep_inv y n (by omega)
    rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← ih]
    simp only [EB.bstep, Nat.zero_add, Nat.one_mul]
    rw [setIfInBounds_toList _ _ (by rw [hs]; omega)]
    congr 2
    simp only [bitsN, List.getD_eq_getElem?_getD, List.getElem?_map]
    funext x
    cases y[n]? <;> simp

theorem bitsToBytes_lt (y : List ℕ) (hy : ∀ x ∈ y, x < 2) :
    ∀ x ∈ OcamlPq.Encoding.Spec.bitsToBytes y, x < 256 := by
  intro x hx
  obtain ⟨-, -, h3⟩ := OcamlPq.Encoding.Spec.bitsToBytes_loop y hy y.length le_rfl
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := h3 j hj
  have h8 : 2 ^ min 8 (y.length - 8 * j) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  have : (OcamlPq.Encoding.Spec.bitsToBytes y)[j] < 2 ^ 8 := lt_of_lt_of_le this h8
  simpa using this

/-- `BitsToBytes` (Algorithm 12), for every bit string. -/
theorem bitsToBytes_eq (y : List Bool) :
    bytesN (Spec.BitsToBytes y) = OcamlPq.Encoding.Spec.bitsToBytes (bitsN y) := by
  have hy : ∀ x ∈ bitsN y, x < 2 := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
    cases b <;> simp
  have key := bytes_loop_corr y y.length le_rfl
  have hlt := bitsToBytes_lt _ hy
  rw [BitsToBytes_fold]
  unfold OcamlPq.Encoding.Spec.bitsToBytes at hlt ⊢
  simp only [List.length_map] at hlt ⊢
  rw [← key] at hlt ⊢
  rw [Array.toList_map]
  simp only [bytesN, List.map_map]
  conv_rhs => rw [← List.map_id (List.foldl (EB.bstep y) (Array.replicate ((y.length + 7) / 8) 0)
    (List.range' 0 y.length)).toList]
  apply List.map_congr_left
  intro x hx
  have := hlt x hx
  simp [Function.comp, Nat.mod_eq_of_lt this]

end XSpec
