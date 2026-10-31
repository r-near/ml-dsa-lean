import Spec.Keccak
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Conv
import Mathlib.Logic.Function.Iterate

/-!
# Keccak states as byte strings

Spec-level facts (no extracted code) that the sponge proof needs: the byte view `sb` of a lane-level state,
`xorByte` (what `Shake::xor_byte` does), and the fact that the spec's `xorBlock` is the pointwise byte XOR.
-/

set_option maxRecDepth 8192

namespace Proofs.KM
open Spec Spec.Keccak

/-- Byte `m` (little-endian) of a lane. -/
def byteOf (X : UInt64) (m : Nat) : UInt8 := (X >>> (8 * m).toUInt64).toUInt8

theorem byteOf_xor (X Y : UInt64) (m : Nat) : byteOf (X ^^^ Y) m = byteOf X m ^^^ byteOf Y m := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [byteOf, hi]

theorem byteOf_or (X Y : UInt64) (m : Nat) : byteOf (X ||| Y) m = byteOf X m ||| byteOf Y m := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [byteOf, hi]

theorem byteOf_shl (b : UInt8) (k m : Nat) (hk : k < 8) (hm : m < 8) :
    byteOf (b.toUInt64 <<< (8 * k).toUInt64) m = if m = k then b else 0 := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [byteOf]
  have h1 : 8 * m % 64 = 8 * m := by omega
  have h2 : 8 * k % 64 = 8 * k := by omega
  simp [hi, h1, h2]
  by_cases hmk : m = k
  · subst hmk
    have h3 : 8 * m + i < 64 := by omega
    have h4 : ¬ 8 * m + i < 8 * m := by omega
    have h5 : i < 64 := by omega
    simp [h3, h4, h5]
    exact BitVec.getLsbD_eq_getElem hi
  · rcases Nat.lt_or_gt_of_ne hmk with h | h
    · have h3 : 8 * m + i < 8 * k := by omega
      simp [h3, hmk]
    · have h3 : 8 ≤ 8 * m + i - 8 * k := by omega
      simp [hmk, BitVec.getLsbD_of_ge _ _ (show 8 ≤ 8 * m + i - 8 * k from h3)]

theorem lane_ext (X Y : UInt64) (h : ∀ m < 8, byteOf X m = byteOf Y m) : X = Y := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun u : UInt8 => u.toBitVec.getLsbD (j % 8)) (h (j / 8) (by omega))
  simp [byteOf] at this
  have e : 8 * (j / 8) % 64 + j % 8 = j := by omega
  have h8 : j % 8 < 8 := by omega
  simpa [e, h8] using this


/-! ### The byte view of a state -/

/-- Byte `k` of the state (the byte `stateBytes` reads). -/
def sb (S : State) (k : Nat) : UInt8 := byteOf S[k / 8]! (k % 8)

theorem stateBytes_eq (r : Nat) (S : State) : stateBytes r S = (List.range r).map (sb S) := rfl

/-- What `Shake::xor_byte` does: XOR byte `b` into byte position `i` of the state. -/
def xorByte (S : State) (i : Nat) (b : UInt8) : State :=
  S.set! (i / 8) (S[i / 8]! ^^^ (b.toUInt64 <<< (8 * (i % 8)).toUInt64))

theorem getElem!_set!' (S : State) (i j : Nat) (x : UInt64) (hj : j < 25) :
    (S.set! i x)[j]! = if i = j then x else S[j]! := by
  have e : S.set! i x = S.setIfInBounds i x := rfl
  rw [e, getElem!_pos _ _ (by simpa using hj), Vector.getElem_setIfInBounds hj,
    getElem!_pos S j (by simpa using hj)]

theorem sb_ext {S T : State} (h : ∀ k < 200, sb S k = sb T k) : S = T := by
  apply Vector.ext
  intro i hi
  have := lane_ext S[i]! T[i]! (fun m hm => by
    have := h (8 * i + m) (by omega)
    simp only [sb] at this
    rwa [show (8 * i + m) / 8 = i by omega, show (8 * i + m) % 8 = m by omega] at this)
  rwa [getElem!_pos S i (by simpa using hi), getElem!_pos T i (by simpa using hi)] at this

theorem sb_xorByte (S : State) (i : Nat) (b : UInt8) (hi : i < 200) (k : Nat) (hk : k < 200) :
    sb (xorByte S i b) k = if k = i then sb S k ^^^ b else sb S k := by
  unfold sb xorByte
  rw [getElem!_set!' _ _ _ _ (by omega)]
  by_cases h1 : i / 8 = k / 8
  · rw [if_pos h1, byteOf_xor, byteOf_shl _ _ _ (by omega) (by omega), h1]
    by_cases h2 : k % 8 = i % 8
    · have : k = i := by omega
      simp [this, h2]
    · have : k ≠ i := by omega
      simp [this, h2]
  · rw [if_neg h1]
    have : k ≠ i := by omega
    simp [this]

theorem fold_byteOf (c : Nat → UInt8) :
    ∀ n ≤ 8, ∀ m < 8,
      byteOf ((List.range n).foldl (fun acc j => acc ||| ((c j).toUInt64 <<< (8 * j).toUInt64)) 0) m =
        if m < n then c m else 0 := by
  intro n
  induction n with
  | zero => intro _ m _; simp [byteOf]
  | succ n ih =>
    intro hn m hm
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, byteOf_or, ih (by omega) m hm,
      byteOf_shl _ _ _ (by omega) hm]
    by_cases h1 : m < n
    · have : m ≠ n := by omega
      simp [h1, this, show m < n + 1 by omega]
    · by_cases h2 : m = n
      · subst h2; simp
      · have : ¬ m < n + 1 := by omega
        simp [h1, h2, this]

theorem sb_xorBlock (S : State) (blk : List UInt8) (k : Nat) (hk : k < 200) :
    sb (xorBlock S blk) k = sb S k ^^^ blk.getD k 0 := by
  unfold sb xorBlock
  rw [getElem!_pos _ (k / 8) (by simpa using (by omega : k / 8 < 25)), Vector.getElem_ofFn, byteOf_xor]
  dsimp only
  rw [fold_byteOf (fun j => blk.toArray.getD (8 * (k / 8) + j) 0) 8 (Nat.le_refl 8) (k % 8) (by omega),
    if_pos (by omega), show 8 * (k / 8) + k % 8 = k by omega,
    getElem!_pos S (k / 8) (by simpa using (by omega : k / 8 < 25))]
  simp [Array.getD, List.getD_eq_getElem?_getD]
  by_cases h : k < blk.length <;> simp [h]


/-! ### `xorBlock` is bytewise -/

theorem xorBlock_nil (S : State) : xorBlock S [] = S := by
  apply sb_ext
  intro k hk
  rw [sb_xorBlock S [] k hk]
  simp

theorem xorBlock_snoc (S : State) (l : List UInt8) (b : UInt8) (hl : l.length < 200) :
    xorBlock S (l ++ [b]) = xorByte (xorBlock S l) l.length b := by
  apply sb_ext
  intro k hk
  rw [sb_xorBlock _ _ k hk, sb_xorByte _ _ _ hl k hk, sb_xorBlock _ _ k hk]
  by_cases h : k = l.length
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [if_neg h]
    congr 1
    by_cases h2 : k < l.length
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    · have h3 : l.length < k := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show l.length ≤ k by omega),
        List.getElem?_eq_none (show l.length ≤ k by omega)]
      rw [List.getElem?_eq_none (show [b].length ≤ k - l.length by simp; omega)]
      rfl

/-! ### Absorbing -/

theorem absorb_step (r : Nat) (S : State) (P : List UInt8) (h : 0 < r ∧ r ≤ P.length) :
    absorb r S P = absorb r (KeccakF1600 (xorBlock S (P.take r))) (P.drop r) := by
  conv_lhs => rw [absorb]
  rw [if_pos h]

theorem absorb_nil (r : Nat) (S : State) : absorb r S [] = S := by
  rw [absorb, if_neg (by intro h; simp at h; omega)]

theorem absorb_one (r : Nat) (hr : 0 < r) (S : State) (B : List UInt8) (hB : B.length = r) :
    absorb r S B = KeccakF1600 (xorBlock S B) := by
  rw [absorb_step r S B ⟨hr, by omega⟩, List.take_of_length_le (by omega), List.drop_of_length_le (by omega),
    absorb_nil]

theorem absorb_append (r : Nat) (hr : 0 < r) :
    ∀ (q : Nat) (S : State) (P B : List UInt8), P.length = q * r →
      absorb r S (P ++ B) = absorb r (absorb r S P) B := by
  intro q
  induction q with
  | zero =>
    intro S P B h
    have : P = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    simp [absorb_nil]
  | succ q ih =>
    intro S P B h
    rw [Nat.succ_mul] at h
    have hP : r ≤ P.length := by omega
    rw [absorb_step r S (P ++ B) ⟨hr, by simp; omega⟩, absorb_step r S P ⟨hr, hP⟩,
      List.take_append_of_le_length hP, List.drop_append_of_le_length hP]
    exact ih _ (P.drop r) B (by simp [h])

/-- The state after absorbing `M` (not yet padded): full blocks permuted, the partial block XORed in. -/
def absSt (r : Nat) (M : List UInt8) : State :=
  xorBlock (absorb r zeroState (M.take (M.length / r * r))) (M.drop (M.length / r * r))

theorem absSt_eq (r : Nat) (M : List UInt8) (q : Nat) (hq : M.length / r = q) :
    absSt r M = xorBlock (absorb r zeroState (M.take (q * r))) (M.drop (q * r)) := by
  subst hq; rfl

theorem absSt_nil (r : Nat) : absSt r [] = zeroState := by
  simp [absSt, absorb_nil, xorBlock_nil]

theorem absSt_push (r : Nat) (hr : 0 < r) (hr2 : r ≤ 200) (M : List UInt8) (b : UInt8) :
    (M.length % r + 1 < r → absSt r (M ++ [b]) = xorByte (absSt r M) (M.length % r) b) ∧
    (M.length % r + 1 = r → absSt r (M ++ [b]) = KeccakF1600 (xorByte (absSt r M) (M.length % r) b)) := by
  have hdm : M.length / r * r + M.length % r = M.length := Nat.div_add_mod' _ _
  have hlt : M.length % r < r := Nat.mod_lt _ hr
  obtain ⟨q, hq⟩ : ∃ q, M.length / r = q := ⟨_, rfl⟩
  obtain ⟨rem, hrem⟩ : ∃ rem, M.length % r = rem := ⟨_, rfl⟩
  rw [hq, hrem] at hdm
  rw [hrem] at hlt ⊢
  have hl : (M ++ [b]).length = M.length + 1 := by simp
  constructor
  · intro h1
    have hdiv : (M ++ [b]).length / r = q :=
      Nat.div_eq_of_lt_le (by omega) (by rw [hl, Nat.succ_mul]; omega)
    rw [absSt_eq r _ q hdiv, absSt_eq r M q hq, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega)]
    rw [xorBlock_snoc _ _ _ (by simp; omega)]
    congr 2
    simp; omega
  · intro h1
    have hdiv : (M ++ [b]).length / r = q + 1 :=
      Nat.div_eq_of_lt_le (by rw [hl, Nat.succ_mul]; omega) (by rw [hl, Nat.succ_mul, Nat.succ_mul]; omega)
    rw [absSt_eq r _ (q + 1) hdiv, absSt_eq r M q hq]
    have e1 : (M ++ [b]).take ((q + 1) * r) = M.take (q * r) ++ (M.drop (q * r) ++ [b]) := by
      rw [List.take_of_length_le (by rw [hl, Nat.succ_mul]; omega), ← List.append_assoc, List.take_append_drop]
    have e2 : (M ++ [b]).drop ((q + 1) * r) = [] := by
      rw [List.drop_of_length_le (by rw [hl, Nat.succ_mul]; omega)]
    have e3 : (M.drop (q * r) ++ [b]).length = r := by simp; omega
    have e4 : (M.take (q * r)).length = q * r := by simp; omega
    rw [e1, e2, xorBlock_nil, absorb_append r hr q _ _ _ e4, absorb_one r hr _ _ e3,
      xorBlock_snoc _ _ _ (by simp; omega)]
    congr 3
    simp; omega

/-! ### Padding and the first permutation of the squeeze phase -/

/-- The bytes `pad101` appends when `K` bytes are needed to fill the block. -/
def padBytes (K : Nat) : List UInt8 := if K = 1 then [0x9F] else 0x1F :: List.replicate (K - 2) 0 ++ [0x80]

theorem pad101_eq (r : Nat) (M : List UInt8) : pad101 r M = M ++ padBytes (r - M.length % r) := rfl

theorem padBytes_length (K : Nat) (hK : 1 ≤ K) : (padBytes K).length = K := by
  unfold padBytes
  split_ifs with h
  · simp [h]
  · simp; omega

theorem padBytes_getD (K : Nat) (hK : 1 ≤ K) (j : Nat) :
    (padBytes K).getD j 0 = (if j = 0 then 0x1F else 0) ^^^ (if j = K - 1 then 0x80 else 0) := by
  unfold padBytes
  by_cases h1 : K = 1
  · subst h1
    rcases j with _ | j
    · simp; decide
    · simp [List.getD_eq_getElem?_getD]
  · rw [if_neg h1]
    rcases j with _ | j
    · have h0 : ¬ (0 = K - 1) := by omega
      simp [h0]
    · simp only [List.cons_append, List.getD_cons_succ, Nat.add_one_ne_zero, if_false, UInt8.zero_xor]
      by_cases h2 : j < K - 2
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_replicate]
        simp [show j + 1 ≠ K - 1 by omega, h2]
      · by_cases h3 : j = K - 2
        · subst h3
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
          simp [show K - 2 + 1 = K - 1 by omega]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
          simp [show j + 1 ≠ K - 1 by omega]

theorem blk_pad_getD (blk : List UInt8) (r rem : Nat) (hlen : blk.length = rem) (hrem : rem < r) (k : Nat) :
    (blk ++ padBytes (r - rem)).getD k 0 =
      (blk.getD k 0 ^^^ (if k = rem then 0x1F else 0)) ^^^ (if k = r - 1 then 0x80 else 0) := by
  by_cases h : k < rem
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    simp [show k ≠ rem by omega, show k ≠ r - 1 by omega]
  · have hb : blk.getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have hp : (blk ++ padBytes (r - rem)).getD k 0 = (padBytes (r - rem)).getD (k - blk.length) 0 := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega)]
    rw [hp, hb, padBytes_getD _ (by omega)]
    have e1 : (k - blk.length = 0) ↔ k = rem := by omega
    have e2 : (k - blk.length = r - rem - 1) ↔ k = r - 1 := by omega
    simp only [e1, e2, UInt8.zero_xor]

theorem finalState (r : Nat) (hr : 0 < r) (hr2 : r ≤ 200) (M : List UInt8) :
    absorb r zeroState (pad101 r M) =
      KeccakF1600 (xorByte (xorByte (absSt r M) (M.length % r) 0x1F) (r - 1) 0x80) := by
  have hdm : M.length / r * r + M.length % r = M.length := Nat.div_add_mod' _ _
  have hlt : M.length % r < r := Nat.mod_lt _ hr
  obtain ⟨q, hq⟩ : ∃ q, M.length / r = q := ⟨_, rfl⟩
  obtain ⟨rem, hrem⟩ : ∃ rem, M.length % r = rem := ⟨_, rfl⟩
  rw [hq, hrem] at hdm
  rw [hrem] at hlt ⊢
  rw [pad101_eq, hrem, absSt_eq r M q hq]
  have e1 : M ++ padBytes (r - rem) = M.take (q * r) ++ (M.drop (q * r) ++ padBytes (r - rem)) := by
    rw [← List.append_assoc, List.take_append_drop]
  have e4 : (M.take (q * r)).length = q * r := by simp; omega
  have e5 : (M.drop (q * r) ++ padBytes (r - rem)).length = r := by
    simp [padBytes_length _ (show 1 ≤ r - rem by omega)]; omega
  rw [e1, absorb_append r hr q _ _ _ e4, absorb_one r hr _ _ e5]
  refine congrArg KeccakF1600 ?_
  apply sb_ext
  intro k hk
  have hl : (M.drop (q * r)).length = rem := by simp; omega
  rw [sb_xorBlock _ _ k hk, sb_xorByte _ _ _ (show r - 1 < 200 by omega) k hk,
    sb_xorByte _ _ _ (show rem < 200 by omega) k hk, sb_xorBlock _ _ k hk,
    blk_pad_getD _ r rem hl hlt k]
  generalize sb (absorb r zeroState (M.take (q * r))) k = A
  generalize (M.drop (q * r)).getD k 0 = B
  split_ifs <;> simp only [UInt8.xor_assoc, UInt8.xor_zero]

/-! ### Squeezing -/

theorem getElem?_squeeze (r : Nat) (hr : 0 < r) :
    ∀ (k : Nat) (S : State) (d off : Nat), off < r → k * r + off < d →
      (squeeze r d S)[k * r + off]? = some (sb (KeccakF1600^[k] S) off) := by
  intro k
  induction k with
  | zero =>
    intro S d off hoff hd
    rw [squeeze]
    split_ifs with h
    · simp only [Nat.zero_mul, Nat.zero_add, Function.iterate_zero, id] at hd ⊢
      rw [List.getElem?_take_of_lt hd]
      simp [stateBytes_eq, hoff]
    · simp only [Nat.zero_mul, Nat.zero_add, Function.iterate_zero, id] at hd ⊢
      rw [List.getElem?_append_left (by simp [stateBytes_eq]; omega)]
      simp [stateBytes_eq, hoff]
  | succ k ih =>
    intro S d off hoff hd
    rw [Nat.succ_mul] at hd ⊢
    rw [squeeze, if_neg (by omega), List.getElem?_append_right (by simp [stateBytes_eq]; omega)]
    have : k * r + r + off - (stateBytes r S).length = k * r + off := by simp [stateBytes_eq]; omega
    rw [this, ih _ (d - r) off hoff (by omega), Function.iterate_succ_apply]

/-! ### Whole lanes -/

/-- What `Shake::xor_lane` does: XOR the lane `X` into lane `j` of the state. -/
def xorLane (S : State) (j : Nat) (X : UInt64) : State := S.set! j (S[j]! ^^^ X)

theorem sb_xorLane (S : State) (j : Nat) (X : UInt64) (hj : j < 25) (k : Nat) (hk : k < 200) :
    sb (xorLane S j X) k = if k / 8 = j then sb S k ^^^ byteOf X (k % 8) else sb S k := by
  unfold sb xorLane
  rw [getElem!_set!' _ _ _ _ (by omega)]
  by_cases h : j = k / 8
  · have h' : k / 8 = j := h.symm
    rw [if_pos h, if_pos h', byteOf_xor, h']
  · have h' : ¬ k / 8 = j := fun e => h e.symm
    rw [if_neg h, if_neg h']

/-- Appending a lane (8 bytes at a lane boundary) to a block XORs the little-endian lane `X` into one lane. -/
theorem xorBlock_lane (S : State) (l B : List UInt8) (X : UInt64) (hl8 : l.length % 8 = 0)
    (hl : l.length + 8 ≤ 200) (hB : B.length = 8) (hX : ∀ m < 8, byteOf X m = B.getD m 0) :
    xorBlock S (l ++ B) = xorLane (xorBlock S l) (l.length / 8) X := by
  apply sb_ext
  intro k hk
  rw [sb_xorBlock _ _ k hk, sb_xorLane _ _ _ (by omega) k hk, sb_xorBlock _ _ k hk]
  by_cases h : k / 8 = l.length / 8
  · rw [if_pos h]
    have hk1 : l.length ≤ k := by omega
    have hk2 : k - l.length = k % 8 := by omega
    have h3 : (l ++ B).getD k 0 = B.getD (k % 8) 0 := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right hk1, hk2]
    have h4 : l.getD k 0 = 0 := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none hk1]
      rfl
    rw [h3, h4, hX (k % 8) (by omega), UInt8.xor_zero]
  · rw [if_neg h]
    congr 1
    by_cases hk1 : k < l.length
    · simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hk1]
    · have hk2 : l.length + 8 ≤ k := by omega
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (show (l ++ B).length ≤ k by simp [hB]; omega),
        List.getElem?_eq_none (show l.length ≤ k by omega)]

/-- Absorbing a whole lane at a lane boundary of the current block (the `Shake::absorb` lane step). -/
theorem absSt_lane (r : Nat) (hr : 0 < r) (hr2 : r ≤ 200) (M B : List UInt8) (X : UInt64) (hB : B.length = 8)
    (hX : ∀ m < 8, byteOf X m = B.getD m 0) (h8 : M.length % r % 8 = 0) (hle : M.length % r + 8 ≤ r) :
    (M.length % r + 8 < r → absSt r (M ++ B) = xorLane (absSt r M) (M.length % r / 8) X) ∧
    (M.length % r + 8 = r → absSt r (M ++ B) = KeccakF1600 (xorLane (absSt r M) (M.length % r / 8) X)) := by
  have hdm : M.length / r * r + M.length % r = M.length := Nat.div_add_mod' _ _
  have hlt : M.length % r < r := Nat.mod_lt _ hr
  obtain ⟨q, hq⟩ : ∃ q, M.length / r = q := ⟨_, rfl⟩
  obtain ⟨rem, hrem⟩ : ∃ rem, M.length % r = rem := ⟨_, rfl⟩
  rw [hq, hrem] at hdm
  rw [hrem] at hlt h8 hle ⊢
  have hl : (M ++ B).length = M.length + 8 := by simp [hB]
  have hdl : (M.drop (q * r)).length = rem := by simp; omega
  constructor
  · intro h1
    have hdiv : (M ++ B).length / r = q :=
      Nat.div_eq_of_lt_le (by omega) (by rw [hl, Nat.succ_mul]; omega)
    rw [absSt_eq r _ q hdiv, absSt_eq r M q hq, List.take_append_of_le_length (by omega),
      List.drop_append_of_le_length (by omega),
      xorBlock_lane _ (M.drop (q * r)) B X (by rw [hdl]; exact h8) (by rw [hdl]; omega) hB hX, hdl]
  · intro h1
    have hdiv : (M ++ B).length / r = q + 1 :=
      Nat.div_eq_of_lt_le (by rw [hl, Nat.succ_mul]; omega) (by rw [hl, Nat.succ_mul, Nat.succ_mul]; omega)
    rw [absSt_eq r _ (q + 1) hdiv, absSt_eq r M q hq]
    have e1 : (M ++ B).take ((q + 1) * r) = M.take (q * r) ++ (M.drop (q * r) ++ B) := by
      rw [List.take_of_length_le (by rw [hl, Nat.succ_mul]; omega), ← List.append_assoc, List.take_append_drop]
    have e2 : (M ++ B).drop ((q + 1) * r) = [] := by
      rw [List.drop_of_length_le (by rw [hl, Nat.succ_mul]; omega)]
    have e3 : (M.drop (q * r) ++ B).length = r := by simp [hB]; omega
    have e4 : (M.take (q * r)).length = q * r := by simp; omega
    rw [e1, e2, xorBlock_nil, absorb_append r hr q _ _ _ e4, absorb_one r hr _ _ e3,
      xorBlock_lane _ (M.drop (q * r)) B X (by rw [hdl]; exact h8) (by rw [hdl]; omega) hB hX, hdl]

end Proofs.KM
