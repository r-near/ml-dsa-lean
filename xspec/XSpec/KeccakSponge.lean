import XSpec.KeccakPerm

/-!
# SHAKE128 / SHAKE256: our byte-level sponge against ocaml-pq's FIPS 202 transcription

`Spec.Keccak.sponge r M d` (rate `r` bytes, suffix and `pad10*1` folded into the byte string `pad101 r M`) is
shown equal to ocaml-pq's `FIPS202.sponge KeccakF pad101 (8 r) (bits M ++ 1111) (8 d)` on bit strings, for every
`M`, `d` and every rate `0 < r ≤ 200`.  The statement of ocaml-pq is the bit-string transcription of FIPS 202
Algorithm 8 (`Hash/KeccakSpec.lean`); the proof reuses ocaml-pq's lemmas about the FIPS side only
(`padded_block_full`, `padded_block_last`, `squeeze_spec`, `tailBlock_toNat`, ...), not any of its OCaml model.
-/

open OcamlPq.Hash

namespace XSpec.KC

theorem term_bit (b : UInt8) (j k : ℕ) (hj : j < 8) :
    (b.toUInt64 <<< (8 * j).toUInt64).toBitVec.getLsbD k =
      (decide (k < 64) && !decide (k < 8 * j) && b.toBitVec.getLsbD (k - 8 * j)) := by
  have e : ((8 * j).toUInt64.toBitVec % 64).toNat = 8 * j := by
    simp [Nat.toUInt64, BitVec.toNat_umod]; omega
  simp only [UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64]
  rw [BitVec.shiftLeft_eq', e, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  have h8 : ∀ n, 8 ≤ n → b.toBitVec.getLsbD n = false := fun n hn => BitVec.getLsbD_of_ge _ _ (by simpa using hn)
  by_cases h1 : k < 8 * j
  · simp [h1]
  · by_cases h2 : k - 8 * j < 8
    · have : k - 8 * j < 64 := by omega
      simp [h1, this]
    · rw [h8 (k - 8 * j) (by omega)]; simp

set_option maxHeartbeats 1000000 in
theorem lane_bit (g : ℕ → UInt8) (k : ℕ) (hk : k < 64) :
    ((List.range 8).foldl (fun (acc : UInt64) j => acc ||| (g j).toUInt64 <<< (8 * j).toUInt64) 0).toBitVec.getLsbD k
      = (g (k / 8)).toNat.testBit (k % 8) := by
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil, UInt64.toBitVec_or, BitVec.getLsbD_or]
  simp only [term_bit _ _ _ (by decide : 0 < 8), term_bit _ _ _ (by decide : 1 < 8),
    term_bit _ _ _ (by decide : 2 < 8), term_bit _ _ _ (by decide : 3 < 8),
    term_bit _ _ _ (by decide : 4 < 8), term_bit _ _ _ (by decide : 5 < 8),
    term_bit _ _ _ (by decide : 6 < 8), term_bit _ _ _ (by decide : 7 < 8)]
  simp only [UInt8.toNat, BitVec.testBit_toNat]
  interval_cases k <;> simp [BitVec.getLsbD_of_ge]

theorem byte_bit (v : UInt64) (s t : ℕ) (hs : s < 8) (ht : t < 8) :
    ((v >>> (8 * s).toUInt64).toUInt8).toNat.testBit t = v.toBitVec.getLsbD (8 * s + t) := by
  have e : ((8 * s).toUInt64.toBitVec % 64).toNat = 8 * s := by
    simp [Nat.toUInt64, BitVec.toNat_umod]; omega
  rw [UInt8.toNat, BitVec.testBit_toNat]
  simp only [UInt64.toBitVec_toUInt8, UInt64.toBitVec_shiftRight]
  rw [BitVec.ushiftRight_eq', e]
  simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, ht, Nat.add_comm]

/-! ### Our state as a 1600-bit string -/

/-- The FIPS 202 string of one of our states: bit `64 i + z` is bit `z` of lane `i`. -/
def bitsOf (A : Spec.Keccak.State) : FIPS202.Bits := Keccak.laneBits (toArr A)

@[simp] theorem bitsOf_length (A : Spec.Keccak.State) : (bitsOf A).length = 1600 := by
  simp [bitsOf]

theorem bitsOf_getElem (A : Spec.Keccak.State) (k : ℕ) (hk : k < 1600) :
    (bitsOf A)[k]'(by simpa using hk) = (A[k / 64]!).toBitVec.getLsbD (k % 64) := by
  simp only [bitsOf]
  rw [Keccak.laneBits_getElem _ _ (by simpa using hk), toArr_getElem! _ _ (by omega)]

theorem bitsOf_keccakF (A : Spec.Keccak.State) :
    bitsOf (Spec.KeccakF1600 A) = FIPS202.KeccakF (bitsOf A) := keccakF_eq A

theorem bitsOf_iterate (m : ℕ) (A : Spec.Keccak.State) :
    bitsOf (Spec.KeccakF1600^[m] A) = FIPS202.KeccakF^[m] (bitsOf A) := by
  induction m generalizing A with
  | zero => simp only [Function.iterate_zero, id_eq]
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', bitsOf_keccakF, ih]

theorem toArr_zeroState : toArr Spec.Keccak.zeroState = Array.replicate 25 0 := by
  apply Array.ext (by simp)
  intro i h1 h2
  simp [toArr, Spec.Keccak.zeroState]

theorem bitsOf_zeroState : bitsOf Spec.Keccak.zeroState = List.replicate 1600 false := by
  rw [bitsOf, toArr_zeroState, Keccak.laneBits_replicate_zero]

theorem getElem!_ofFn25 (f : Fin 25 → UInt64) (i : ℕ) (hi : i < 25) :
    (Vector.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i hi]; simp

/-- XOR of an `r`-byte block into the first `8 r` bits of the state. -/
theorem bitsOf_xorBlock (S : Spec.Keccak.State) (blk : List UInt8) (r : ℕ) (hlen : blk.length = r)
    (hr : r ≤ 200) :
    bitsOf (Spec.Keccak.xorBlock S blk) =
      FIPS202.xorBits (bitsOf S) (FIPS202.bytesToBits blk ++ List.replicate (FIPS202.b - 8 * r) false) := by
  apply List.ext_getElem
  · simp [FIPS202.xorBits, hlen, FIPS202.b]; omega
  · intro k h1 h2
    have hk : k < 1600 := by simpa using h1
    have hi : k / 64 < 25 := by omega
    rw [bitsOf_getElem _ _ hk]
    simp only [FIPS202.xorBits, List.getElem_zipWith]
    rw [bitsOf_getElem _ _ hk]
    simp only [Spec.Keccak.xorBlock]
    rw [getElem!_ofFn25 _ _ hi, UInt64.toBitVec_xor, BitVec.getLsbD_xor,
      lane_bit (fun j => blk.toArray.getD (8 * (k / 64) + j) 0) (k % 64) (by omega)]
    have e1 : 8 * (k / 64) + k % 64 / 8 = k / 8 := by omega
    have e2 : k % 64 % 8 = k % 8 := by omega
    simp only [e1, e2]
    congr 1
    by_cases hkr : k < 8 * r
    · rw [List.getElem_append_left (by simp [hlen]; omega), bytesToBits_getElem]
      simp only [List.getElem_toArray, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
      rw [List.getElem?_eq_getElem (by omega)]
      rfl
    · rw [List.getElem_append_right (by simp [hlen]; omega), List.getElem_replicate]
      have : blk.length ≤ k / 8 := by omega
      simp [List.getD_eq_default, this]

/-! ### Padding -/

/-- The bytes appended by our `pad101` when `k` bytes are needed. -/
def padList (k : ℕ) : List UInt8 := if k = 1 then [0x9F] else 0x1F :: List.replicate (k - 2) 0 ++ [0x80]

theorem pad101_eq_append (r : ℕ) (M : List UInt8) :
    Spec.Keccak.pad101 r M = M ++ padList (r - M.length % r) := rfl

theorem padList_length (k : ℕ) (hk : 1 ≤ k) : (padList k).length = k := by
  unfold padList
  split_ifs with h
  · simp [h]
  · simp; omega

theorem padList_getElem (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : i < (padList k).length) :
    ((padList k)[i]).toNat = (if i = 0 then 31 else 0) ||| (if i = k - 1 then 128 else 0) := by
  rw [padList_length k hk] at hi
  unfold padList
  by_cases h : k = 1
  · subst h
    have : i = 0 := by omega
    subst this
    simp
  · simp only [h, ite_false]
    by_cases h0 : i = 0
    · subst h0
      have : 0 ≠ k - 1 := by omega
      simp [this]
    · by_cases hl : i = k - 1
      · subst hl
        rw [List.getElem_append_right (by simp; omega)]
        have : k - 1 ≠ 0 := by omega
        simp [this]
      · rw [List.getElem_append_left (by simp; omega)]
        obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0
        simp [List.getElem_cons_succ, List.getElem_replicate]
        omega

/-- The padded message of ours is the full blocks of `M` followed by ocaml-pq's tail block of `M` (suffix
`0x1f`, `0x80` or-ed into the last byte). -/
theorem pad101_eq (r : ℕ) (M : List UInt8) (hr : 0 < r) :
    Spec.Keccak.pad101 r M = M.take (M.length / r * r) ++ Keccak.tailBlock r 0x1f M := by
  have hm := Nat.mod_lt M.length hr
  have hdm := Nat.div_add_mod M.length r
  set q := M.length / r with hq
  set m := M.length % r with hmm
  have hqr : q * r + m = M.length := by rw [Nat.mul_comm]; exact hdm
  rw [pad101_eq_append, ← hmm]
  have hs : M ++ padList (r - m) = M.take (q * r) ++ (M.drop (q * r) ++ padList (r - m)) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hs]
  congr 1
  have hk : 1 ≤ r - m := by omega
  apply List.ext_getElem
  · rw [List.length_append, padList_length _ hk, Keccak.tailBlock_length]
    simp only [List.length_drop]; omega
  · intro j h1 h2
    have hj : j < r := by rw [Keccak.tailBlock_length] at h2; exact h2
    apply UInt8.toNat_inj.mp
    have h3 := Keccak.tailBlock_toNat r 0x1f M hr (by decide) j hj
    rw [getElem!_pos _ j h2] at h3
    rw [h3]
    simp only [← hmm, ← hq]
    have hlen : (List.drop (q * r) M).length = m := by simp only [List.length_drop]; omega
    by_cases hjm : j < m
    · rw [List.getElem_append_left (by rw [hlen]; exact hjm), List.getElem_drop, if_pos hjm,
        if_neg (by omega), Nat.or_zero, getElem!_pos M _ (by omega)]
    · rw [List.getElem_append_right (by rw [hlen]; omega), if_neg hjm,
        padList_getElem _ hk _ (by rw [padList_length _ hk]; omega)]
      simp only [hlen]
      split_ifs <;> first | rfl | (exfalso; omega)

/-! ### Absorbing -/

theorem block_succ (P : List UInt8) (r i : ℕ) :
    ((FIPS202.bytesToBits P).drop ((i + 1) * (8 * r))).take (8 * r) =
      ((FIPS202.bytesToBits (P.drop r)).drop (i * (8 * r))).take (8 * r) := by
  rw [← Keccak.bytesToBits_drop, List.drop_drop]
  congr 2
  ring

theorem bitsOf_absorb (r : ℕ) (hr : 0 < r) (hr200 : r ≤ 200) :
    ∀ (n : ℕ) (S : Spec.Keccak.State) (P : List UInt8), P.length = n * r →
    bitsOf (Spec.Keccak.absorb r S P) =
      (List.range n).foldl (fun T i => FIPS202.KeccakF (FIPS202.xorBits T
        (((FIPS202.bytesToBits P).drop (i * (8 * r))).take (8 * r) ++
          List.replicate (FIPS202.b - 8 * r) false))) (bitsOf S) := by
  intro n
  induction n with
  | zero =>
    intro S P hP
    have : P = [] := List.eq_nil_of_length_eq_zero (by simpa using hP)
    subst this
    rw [Spec.Keccak.absorb, if_neg (by rintro ⟨_, h⟩; simp at h; omega), List.range_zero, List.foldl_nil]
  | succ n ih =>
    intro S P hP
    have hle : r ≤ P.length := by rw [hP]; nlinarith
    rw [Spec.Keccak.absorb, if_pos ⟨hr, hle⟩]
    rw [ih _ (P.drop r) (by simp only [List.length_drop, hP]; rw [Nat.succ_mul]; omega)]
    have hblk : (P.take r).length = r := by simp only [List.length_take]; omega
    rw [bitsOf_keccakF, bitsOf_xorBlock _ _ r hblk hr200, List.range_succ_eq_map, List.foldl_cons,
      List.foldl_map]
    have h0 : ((FIPS202.bytesToBits P).drop (0 * (8 * r))).take (8 * r) = FIPS202.bytesToBits (P.take r) := by
      rw [Nat.zero_mul, List.drop_zero, Keccak.bytesToBits_take]
    rw [h0]
    simp only [block_succ, Nat.succ_eq_add_one, Function.comp_def]

/-- `ds` for SHAKE: the four domain bits `1111`. -/
abbrev shakeDS : FIPS202.Bits := [true, true, true, true]

theorem tailBlock_len (r : ℕ) (M : List UInt8) : (Keccak.tailBlock r 0x1f M).length = r :=
  Keccak.tailBlock_length r 0x1f M

theorem pad101_length (r : ℕ) (M : List UInt8) (hr : 0 < r) :
    (Spec.Keccak.pad101 r M).length = (M.length / r + 1) * r := by
  have hdm := Nat.div_add_mod M.length r
  have hle : M.length / r * r ≤ M.length := Nat.div_mul_le_self _ _
  rw [pad101_eq r M hr, List.length_append, List.length_take, tailBlock_len, Nat.add_mul, one_mul,
    Nat.min_eq_left hle]

theorem pad_block (r : ℕ) (M : List UInt8) (hr : 0 < r) (i : ℕ) (hi : i < M.length / r + 1) :
    ((FIPS202.bytesToBits (Spec.Keccak.pad101 r M)).drop (i * (8 * r))).take (8 * r) =
      ((Keccak.padded r M shakeDS).drop (i * (8 * r))).take (8 * r) := by
  have hle : M.length / r * r ≤ M.length := Nat.div_mul_le_self _ _
  have htk : (M.take (M.length / r * r)).length = M.length / r * r := by
    simp only [List.length_take]; omega
  by_cases hlt : i < M.length / r
  · rw [Keccak.padded_block_full r M shakeDS i hlt]
    have e : i * (8 * r) = 8 * (i * r) := by ring
    rw [e, Keccak.bytesToBits_drop, Keccak.bytesToBits_take, pad101_eq r M hr]
    congr 1
    have h1 : i * r ≤ (M.take (M.length / r * r)).length := by
      rw [htk]; exact Nat.mul_le_mul_right r (by omega)
    have h2 : r ≤ ((M.take (M.length / r * r)).drop (i * r)).length := by
      simp only [List.length_drop, htk]
      have : (i + 1) * r ≤ M.length / r * r := Nat.mul_le_mul_right r (by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    rw [List.drop_append_of_le_length h1, List.take_append_of_le_length h2, Keccak.stringSub,
      List.drop_take, List.take_take]
    congr 1
    have : (i + 1) * r ≤ M.length / r * r := Nat.mul_le_mul_right r (by omega)
    rw [Nat.add_mul, one_mul] at this
    omega
  · have hiq : i = M.length / r := by omega
    subst hiq
    rw [Keccak.padded_block_last r 0x1f M shakeDS hr Keccak.suffixOK_shake]
    have e : M.length / r * (8 * r) = 8 * (M.length / r * r) := by ring
    rw [e, Keccak.bytesToBits_drop, Keccak.bytesToBits_take, pad101_eq r M hr,
      List.drop_left' htk, List.take_of_length_le (by rw [tailBlock_len])]

theorem bitsOf_absorb_pad (r : ℕ) (M : List UInt8) (hr : 0 < r) (hr200 : r ≤ 200) :
    bitsOf (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M)) =
      (List.range ((Keccak.padded r M shakeDS).length / (8 * r))).foldl
        (fun S i => FIPS202.KeccakF (FIPS202.xorBits S (((Keccak.padded r M shakeDS).drop (i * (8 * r))).take
          (8 * r) ++ List.replicate (FIPS202.b - 8 * r) false))) (List.replicate FIPS202.b false) := by
  have hlenP : (Keccak.padded r M shakeDS).length = (M.length / r + 1) * (8 * r) :=
    Keccak.padded_length r M shakeDS hr (by decide)
  rw [hlenP, Nat.mul_div_cancel _ (by omega : 0 < 8 * r),
    bitsOf_absorb r hr hr200 _ _ _ (pad101_length r M hr), bitsOf_zeroState]
  refine List.foldl_ext _ _ _ (fun T i hi => ?_)
  rw [pad_block r M hr i (List.mem_range.mp hi)]

/-! ### Squeezing -/

theorem stateBytes_getElem (r : ℕ) (T : Spec.Keccak.State) (j : ℕ) (hj : j < r) :
    (Spec.Keccak.stateBytes r T)[j]! = (T[j / 8]! >>> (8 * (j % 8)).toUInt64).toUInt8 := by
  rw [getElem!_pos _ j (by simpa [Spec.Keccak.length_stateBytes] using hj)]
  simp [Spec.Keccak.stateBytes]

theorem squeeze_getElem (r : ℕ) (hr : 0 < r) :
    ∀ (d : ℕ) (S : Spec.Keccak.State) (k : ℕ), k < d →
      (Spec.Keccak.squeeze r d S)[k]! =
        (Spec.Keccak.stateBytes r (Spec.KeccakF1600^[k / r] S))[k % r]! := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro S k hk
    rw [Spec.Keccak.squeeze]
    by_cases h : d ≤ r ∨ r = 0
    · rw [if_pos h]
      have hdr : d ≤ r := by omega
      rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Function.iterate_zero_apply]
      rw [getElem!_pos _ k (by simp [Spec.Keccak.length_stateBytes]; omega), getElem!_pos _ k
        (by simp [Spec.Keccak.length_stateBytes]; omega)]
      simp
    · rw [if_neg h]
      have hrd : r < d := by omega
      by_cases hkr : k < r
      · rw [Nat.div_eq_of_lt hkr, Nat.mod_eq_of_lt hkr, Function.iterate_zero_apply]
        rw [getElem!_pos _ k (by simp [Spec.Keccak.length_stateBytes]; omega), getElem!_pos _ k
          (by simp [Spec.Keccak.length_stateBytes]; omega)]
        simp [List.getElem_append_left, Spec.Keccak.length_stateBytes, hkr]
      · have hlen : (Spec.Keccak.stateBytes r S).length = r := Spec.Keccak.length_stateBytes r S
        rw [getElem!_pos _ k (by simp [Spec.Keccak.length_stateBytes, Spec.Keccak.length_squeeze _ hr]; omega),
          List.getElem_append_right (by omega)]
        simp only [hlen]
        rw [← getElem!_pos (Spec.Keccak.squeeze r (d - r) (Spec.KeccakF1600 S)) (k - r)
            (by rw [Spec.Keccak.length_squeeze _ hr]; omega),
          ih (d - r) (by omega) _ (k - r) (by omega)]
        have e1 : k / r = (k - r) / r + 1 := by
          rw [← Nat.add_div_right _ hr, Nat.sub_add_cancel (by omega)]
        have e2 : k % r = (k - r) % r := by
          rw [← Nat.add_mod_right (k - r) r, Nat.sub_add_cancel (by omega)]
        rw [e1, e2, Function.iterate_succ_apply]

theorem bytesToBits_squeeze (r : ℕ) (hr : 0 < r) (hr200 : r ≤ 200) (d : ℕ) (S : Spec.Keccak.State) :
    FIPS202.bytesToBits (Spec.Keccak.squeeze r d S) =
      List.ofFn fun t : Fin (8 * d) => Keccak.Zbit FIPS202.KeccakF (8 * r) (bitsOf S) t := by
  apply List.ext_getElem
  · simp [Spec.Keccak.length_squeeze r hr]
  · intro t h1 h2
    have ht : t < 8 * d := by simpa using h2
    rw [List.getElem_ofFn, bytesToBits_getElem, ← getElem!_pos (Spec.Keccak.squeeze r d S) (t / 8)
      (by rw [Spec.Keccak.length_squeeze r hr]; omega), squeeze_getElem r hr d S (t / 8) (by omega)]
    have hj : (t / 8) % r < r := Nat.mod_lt _ hr
    rw [stateBytes_getElem r _ _ hj, byte_bit _ _ _ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
    simp only [Keccak.Zbit, Fin.val_mk]
    rw [← bitsOf_iterate, ← Nat.div_div_eq_div_mul]
    have hu : t % (8 * r) < 8 * r := Nat.mod_lt _ (by omega)
    rw [List.getD_eq_getElem _ _ (by rw [bitsOf_length]; omega),
      bitsOf_getElem _ _ (by omega)]
    have hmm : t % (8 * r) = t % 8 + 8 * (t / 8 % r) := Nat.mod_mul
    have h8 : t % 8 < 8 := Nat.mod_lt _ (by decide)
    generalize t / 8 % r = j at hmm hj ⊢
    have e1 : t % (8 * r) / 64 = j / 8 := by omega
    have e2 : t % (8 * r) % 64 = 8 * (j % 8) + t % 8 := by omega
    rw [e1, e2]

/-! ### The sponge and SHAKE -/

/-- **The sponge.**  Our byte-level `Keccak.sponge r M d` is, on bit strings (FIPS 202 Appendix B.1), ocaml-pq's
`FIPS202.sponge KeccakF pad10*1 (8 r) (M ‖ 1111) (8 d)` (FIPS 202 Algorithm 8), for every message, output length
and rate `0 < r ≤ 200` bytes. -/
theorem sponge_bits (r : ℕ) (M : List UInt8) (d : ℕ) (hr : 0 < r) (hr200 : r ≤ 200) :
    FIPS202.bytesToBits (Spec.Keccak.sponge r M d) =
      FIPS202.sponge FIPS202.KeccakF FIPS202.pad101 (8 * r) (FIPS202.bytesToBits M ++ shakeDS) (8 * d) := by
  have hsq := Keccak.squeeze_spec FIPS202.KeccakF (8 * r) (8 * d)
    (bitsOf (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M)))
    (fun m => by rw [← bitsOf_iterate, bitsOf_length]; omega)
    (8 * d + 1) 0 [] (by simp) (by simp) (Or.inl rfl) (by nlinarith)
  rw [Function.iterate_zero_apply] at hsq
  show _ = FIPS202.squeeze FIPS202.KeccakF (8 * r) (8 * d) (8 * d + 1)
    ((List.range ((Keccak.padded r M shakeDS).length / (8 * r))).foldl
        (fun S i => FIPS202.KeccakF (FIPS202.xorBits S (((Keccak.padded r M shakeDS).drop (i * (8 * r))).take
          (8 * r) ++ List.replicate (FIPS202.b - 8 * r) false))) (List.replicate FIPS202.b false)) []
  rw [← bitsOf_absorb_pad r M hr hr200, hsq]
  exact bytesToBits_squeeze r hr hr200 d _

/-- **SHAKE128.**  Our `SHAKE128 M d` is ocaml-pq's FIPS 202 `SHAKE128(M, 8 d)` (`FIPS202.SHAKE128`,
`Hash/KeccakSpec.lean`) on bit strings, for all `M` and `d`. -/
theorem shake128_bits (M : List UInt8) (d : ℕ) :
    FIPS202.bytesToBits (Spec.SHAKE128 M d) = FIPS202.SHAKE128 (FIPS202.bytesToBits M) (8 * d) :=
  sponge_bits 168 M d (by norm_num) (by norm_num)

/-- **SHAKE256.**  Our `SHAKE256 M d` is ocaml-pq's FIPS 202 `SHAKE256(M, 8 d)`. -/
theorem shake256_bits (M : List UInt8) (d : ℕ) :
    FIPS202.bytesToBits (Spec.SHAKE256 M d) = FIPS202.SHAKE256 (FIPS202.bytesToBits M) (8 * d) :=
  sponge_bits 136 M d (by norm_num) (by norm_num)

/-- The FIPS 202 bit string of a byte list determines the list. -/
theorem bytesToBits_injective : Function.Injective FIPS202.bytesToBits := by
  intro a b h
  have hl : a.length = b.length := by
    have := congrArg List.length h
    simp only [bytesToBits_length] at this
    omega
  apply List.ext_getElem hl
  intro j h1 h2
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · have hk : 8 * j + i < (FIPS202.bytesToBits a).length := by simp; omega
    have := bytesToBits_getElem a (8 * j + i) hk
    have h' := bytesToBits_getElem b (8 * j + i) (by rw [← h]; exact hk)
    have e1 : (8 * j + i) / 8 = j := by omega
    have e2 : (8 * j + i) % 8 = i := by omega
    simp only [e1, e2] at this h'
    rw [← this, ← h', List.getElem_of_eq h hk]
  · rw [UInt8.testBit_ge _ (by omega), UInt8.testBit_ge _ (by omega)]

/-- **`Spec.SHAKE128` is ocaml-pq's `Mldsa_keccak.shake128`** (the model of `lib/keccak.ml`), as byte lists. -/
theorem SHAKE128_eq_ocaml (M : List UInt8) (d : ℕ) : Spec.SHAKE128 M d = Keccak.shake128 d M :=
  bytesToBits_injective (by rw [shake128_bits, Keccak.shake128_eq])

/-- **`Spec.SHAKE256` is ocaml-pq's `Mldsa_keccak.shake256`.** -/
theorem SHAKE256_eq_ocaml (M : List UInt8) (d : ℕ) : Spec.SHAKE256 M d = Keccak.shake256 d M :=
  bytesToBits_injective (by rw [shake256_bits, Keccak.shake256_eq])

end XSpec.KC
