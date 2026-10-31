import Spec


/-!
# Bit-level model of the FIPS 204 packing algorithms (arithmetic and spec lemmas)

The Rust bit accumulator keeps "a window of the bit string" in a machine word. This file gives the
window-value function `BV` and the closed forms of the spec's bit/byte conversions in terms of it:

* `BV g s n = Σ_{j<n} g(s+j) · 2^j` is the integer whose little-endian bits are `g s, ..., g (s+n-1)`;
* `pack_model`: for any `f` and `c`, `BitsToBytes (IntegerToBits (f 0) c ++ ... ++ IntegerToBits (f 255) c)`
  is the list of the bytes `BV g (8k) 8` of one 0/1 bit function `g`, whose `c`-bit window at `c·i` is `f i mod 2^c`;
* `SimpleBitUnpack_get`, `BitUnpack_get`: coefficient `i` of the decoders is the window of `byteBit v` at `c·i`.
-/

open Spec
namespace XSpec.EB

/-! ## Window values -/

/-- The integer whose little-endian bits are `g s, g (s+1), ..., g (s+n-1)`. -/
def BV (g : Nat → Nat) (s : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => g s + 2 * BV g (s+1) n

theorem BV_zero (g : Nat → Nat) (s : Nat) : BV g s 0 = 0 := rfl

theorem BV_add (g : Nat → Nat) (s n m : Nat) :
    BV g s (n+m) = BV g s n + 2^n * BV g (s+n) m := by
  induction n generalizing s with
  | zero => simp [BV]
  | succ n ih =>
    have e1 : n + 1 + m = (n + m) + 1 := by omega
    rw [e1]
    simp only [BV]
    rw [ih (s+1)]
    have e2 : s + 1 + n = s + (n + 1) := by omega
    rw [e2, pow_succ]
    ring

theorem BV_lt (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (s n : Nat) : BV g s n < 2^n := by
  induction n generalizing s with
  | zero => simp [BV]
  | succ n ih =>
    simp only [BV]
    have := ih (s+1)
    have := hg s
    rw [pow_succ]
    omega

theorem BV_congr (g g' : Nat → Nat) (s s' n : Nat) (h : ∀ j < n, g (s + j) = g' (s' + j)) :
    BV g s n = BV g' s' n := by
  induction n generalizing s s' with
  | zero => rfl
  | succ n ih =>
    simp only [BV]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0, ih (s+1) (s'+1)]
    intro j hj
    have := h (j+1) (by omega)
    rwa [show s + (j+1) = s + 1 + j by omega, show s' + (j+1) = s' + 1 + j by omega] at this

/-- Splitting off the low byte of a window. -/
theorem BV_byte (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (s m : Nat) :
    BV g s (8 + m) % 256 = BV g s 8 ∧ BV g s (8 + m) / 256 = BV g (s + 8) m := by
  have h := BV_add g s 8 m
  have hl := BV_lt g hg s 8
  norm_num at h hl
  omega

/-- The `j`-th binary digit of `x`. -/
def dig (x j : Nat) : Nat := (x / 2^j) % 2

theorem dig_le (x j : Nat) : dig x j ≤ 1 := by
  unfold dig; omega

theorem BV_dig (x s n : Nat) : BV (dig x) s n = (x / 2^s) % 2^n := by
  induction n generalizing s with
  | zero => simp [BV, Nat.mod_one]
  | succ n ih =>
    simp only [BV]
    rw [ih (s+1)]
    unfold dig
    have h1 : x / 2^(s+1) = x / 2^s / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [h1, pow_succ', Nat.mod_mul]

/-! ## IntegerToBits -/

/-- Bits of a list, as 0/1 naturals (0 outside the list). -/
def bitv (y : List Bool) (t : Nat) : Nat := (y[t]?.getD false).toNat

theorem bitsLoop_fst (b0 : Nat) (arr : Array Bool) (m : Nat) :
    (List.foldl (fun (r : Nat × Array Bool) (_ : Nat) =>
        (r.1 / 2, r.2.push (r.1 % 2 == 1)))
      (b0, arr) (List.range' 0 m)).1 = b0 / 2^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [ih]
    rw [pow_succ, Nat.div_div_eq_div_mul]

theorem bitsLoop_snd (b0 : Nat) (arr : Array Bool) (m : Nat) :
    (List.foldl (fun (r : Nat × Array Bool) (_ : Nat) =>
        (r.1 / 2, r.2.push (r.1 % 2 == 1)))
      (b0, arr) (List.range' 0 m)).2.toList
      = arr.toList ++ (List.range m).map (fun j => (b0 / 2^j) % 2 == 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Array.toList_push, ih, bitsLoop_fst, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc]

/-- The inner (8-bit) loop of `BytesToBits`, whose state is `(y, b)`. -/
theorem bitsLoop2_snd (b0 : Nat) (arr : Array Bool) (m : Nat) :
    (List.foldl (fun (r : Array Bool × Nat) (_ : Nat) =>
        (r.1.push (r.2 % 2 == 1), r.2 / 2))
      (arr, b0) (List.range' 0 m)).1.toList
      = arr.toList ++ (List.range m).map (fun j => (b0 / 2^j) % 2 == 1) := by
  have h : ∀ m, List.foldl (fun (r : Array Bool × Nat) (_ : Nat) =>
        (r.1.push (r.2 % 2 == 1), r.2 / 2)) (arr, b0) (List.range' 0 m) =
      ((List.foldl (fun (r : Nat × Array Bool) (_ : Nat) =>
        (r.1 / 2, r.2.push (r.1 % 2 == 1))) (b0, arr) (List.range' 0 m)).2,
       (List.foldl (fun (r : Nat × Array Bool) (_ : Nat) =>
        (r.1 / 2, r.2.push (r.1 % 2 == 1))) (b0, arr) (List.range' 0 m)).1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
  rw [h m]
  exact bitsLoop_snd b0 arr m

theorem IntegerToBits_eq (x α : Nat) :
    IntegerToBits x α = (List.range α).map (fun j => (x / 2^j) % 2 == 1) := by
  unfold IntegerToBits
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have := bitsLoop_snd x #[] α
  simpa using this

theorem IntegerToBits_length (x α : Nat) : (IntegerToBits x α).length = α := by
  simp [IntegerToBits_eq]

theorem beq_one_toNat (n : Nat) (h : n ≤ 1) : (n == 1).toNat = n := by
  rcases (by omega : n = 0 ∨ n = 1) with h | h <;> simp [h]

theorem bitv_IntegerToBits (x α j : Nat) (hj : j < α) : bitv (IntegerToBits x α) j = dig x j := by
  simp only [bitv, IntegerToBits_eq, List.getElem?_map, List.getElem?_range, hj, if_true,
    Option.map_some, Option.getD_some]
  exact beq_one_toNat _ (dig_le x j)

/-! ## BytesToBits -/

/-- Bit `t` of the byte string `v` (0 past its end). -/
def byteBit (v : List UInt8) (t : Nat) : Nat := ((v[t/8]?.getD default).toNat / 2^(t%8)) % 2

theorem byteBit_le (v : List UInt8) (t : Nat) : byteBit v t ≤ 1 := by
  unfold byteBit; omega

theorem BytesToBits_eq (v : List UInt8) :
    BytesToBits v = (List.range (8 * v.length)).map (fun t => byteBit v t == 1) := by
  unfold BytesToBits
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have key : ∀ n, (List.foldl (fun (b : Array Bool) (a : Nat) =>
      (List.foldl (fun (r : Array Bool × Nat) (_ : Nat) =>
        (r.1.push (r.2 % 2 == 1), r.2 / 2))
        (b, (v[a]?.getD default).toNat) (List.range' 0 8)).1) #[] (List.range' 0 n)).toList
      = (List.range (8 * n)).map (fun t => byteBit v t == 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil, bitsLoop2_snd, ih]
      rw [show 8 * (n+1) = 8 * n + 8 by ring, List.range_add, List.map_append, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      simp only [Function.comp, byteBit]
      have e1 : (8 * n + j) / 8 = n := by omega
      have e2 : (8 * n + j) % 8 = j := by omega
      rw [e1, e2]
      simp
  have := key v.length
  simpa using this

theorem bitv_BytesToBits (v : List UInt8) (t : Nat) : bitv (BytesToBits v) t = byteBit v t := by
  rw [BytesToBits_eq]
  unfold bitv
  by_cases ht : t < 8 * v.length
  · simp only [List.getElem?_map, List.getElem?_range, ht, if_true, Option.map_some, Option.getD_some]
    exact beq_one_toNat _ (byteBit_le v t)
  · have h1 : v[t/8]? = none := by
      rw [List.getElem?_eq_none_iff]; omega
    simp [ht, byteBit, h1, show (default : UInt8).toNat = 0 from rfl]

/-! ## BitsToInteger -/

theorem BitsToInteger_eq (y : List Bool) (α : Nat) : BitsToInteger y α = BV (bitv y) 0 α := by
  unfold BitsToInteger
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have key : ∀ m, m ≤ α → List.foldl (fun (b : Nat) (a : Nat) => 2 * b + (y[α - a]?.getD false).toNat) 0
      (List.range' 1 m) = BV (bitv y) (α - m) m := by
    intro m
    induction m with
    | zero => intro _; simp [BV]
    | succ m ih =>
      intro hm
      rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
      simp only [BV]
      rw [show α - (m+1) + 1 = α - m by omega, show α - (1 + 1 * m) = α - (m+1) by omega]
      simp only [bitv]
      ring
  have := key α le_rfl
  simpa using this

/-! ## BitsToBytes -/

/-- One iteration of the loop of `BitsToBytes`. -/
def bstep (y : List Bool) (b : Array Nat) (a : Nat) : Array Nat :=
  b.setIfInBounds (a / 8) (b[a / 8]! + (y[a]?.getD false).toNat * 2 ^ (a % 8))

theorem bstep_inv (y : List Bool) : ∀ n, n ≤ y.length →
    (List.foldl (bstep y) (Array.replicate ((y.length + 7) / 8) 0) (List.range' 0 n)).size
        = (y.length + 7) / 8 ∧
    ∀ k (hk : k < (y.length + 7) / 8),
      (List.foldl (bstep y) (Array.replicate ((y.length + 7) / 8) 0) (List.range' 0 n))[k]!
        = BV (bitv y) (8*k) (min 8 (n - 8*k)) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by simp, fun k hk => ?_⟩
    rw [getElem!_pos _ _ (by simpa using hk)]
    simp [BV]
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hA : List.foldl (bstep y) (Array.replicate ((y.length + 7) / 8) 0) (List.range' 0 n) = A
      at ih1 ih2 ⊢
    have hi : (0 + 1 * n) / 8 < A.size := by omega
    refine ⟨by simp [bstep, ih1], fun k hk => ?_⟩
    have hkA : k < (bstep y A (0 + 1 * n)).size := by simp [bstep]; omega
    rw [getElem!_pos (bstep y A (0 + 1 * n)) k hkA]
    simp only [bstep]
    rw [Array.getElem_setIfInBounds (xs := A) (by omega)]
    split
    · rename_i hk8
      have hkk : k = n / 8 := by omega
      subst hkk
      simp only [Nat.zero_add, Nat.one_mul]
      rw [ih2 (n/8) hk]
      have h8 : min 8 (n - 8*(n/8)) = n % 8 := by omega
      have h9 : min 8 (n + 1 - 8*(n/8)) = n % 8 + 1 := by omega
      rw [h8, h9, BV_add (bitv y) (8*(n/8)) (n%8) 1]
      have : 8*(n/8) + n%8 = n := by omega
      rw [this]
      simp [BV, bitv]
      ring
    · rename_i hk8
      have := ih2 k hk
      rw [getElem!_pos A k (by omega)] at this
      rw [this]
      congr 1
      omega

theorem BitsToBytes_eq (y : List Bool) (h8 : y.length % 8 = 0) :
    BitsToBytes y = (List.range (y.length / 8)).map (fun k => (BV (bitv y) (8*k) 8).toUInt8) := by
  unfold BitsToBytes
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  obtain ⟨h1, h2⟩ := bstep_inv y y.length le_rfl
  have e : (fun (b : Array Nat) (a : Nat) =>
      b.setIfInBounds (a / 8) (b[a / 8]! + (y[a]?.getD false).toNat * 2 ^ (a % 8))) = bstep y := rfl
  rw [e]
  apply List.ext_getElem
  · simp [h1]; omega
  · intro k hk1 hk2
    have hk3 : k < (y.length+7)/8 := by simpa [h1] using hk1
    have := h2 k hk3
    rw [getElem!_pos _ _ (by omega)] at this
    simp [this]
    congr 2
    omega

/-! ## The packed bit string -/

theorem bitv_le (y : List Bool) (t : Nat) : bitv y t ≤ 1 := by
  unfold bitv; cases y[t]?.getD false <;> simp

theorem bitv_append_left (l l' : List Bool) (t : Nat) (h : t < l.length) :
    bitv (l ++ l') t = bitv l t := by
  simp [bitv, List.getElem?_append_left h]

theorem bitv_append_right (l l' : List Bool) (t : Nat) (h : l.length ≤ t) :
    bitv (l ++ l') t = bitv l' (t - l.length) := by
  simp [bitv, List.getElem?_append_right h]

theorem flatten_bits (f : Nat → Nat) (c : Nat) : ∀ n,
    ((List.range' 0 n).map (fun i => IntegerToBits (f i) c)).flatten.length = n * c ∧
    ∀ i < n, ∀ j < c,
      bitv ((List.range' 0 n).map (fun i => IntegerToBits (f i) c)).flatten (i*c+j) = dig (f i) j := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.range'_concat (n := n)]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.length_append, ih1, IntegerToBits_length,
      Nat.zero_add, Nat.one_mul]
    refine ⟨by ring, fun i hi j hj => ?_⟩
    by_cases hin : i < n
    · have hlt : i * c + j < n * c := by nlinarith
      rw [bitv_append_left _ _ _ (by rw [ih1]; exact hlt)]
      exact ih2 i hin j hj
    · have hi' : i = n := by omega
      subst hi'
      rw [bitv_append_right _ _ _ (by rw [ih1]; omega), ih1,
        show i * c + j - i * c = j by omega]
      exact bitv_IntegerToBits _ _ _ hj

theorem pack_model (f : Nat → Nat) (c : Nat) :
    ∃ g : Nat → Nat, (∀ t, g t ≤ 1) ∧ (∀ i < 256, BV g (c*i) c = f i % 2^c) ∧
      BitsToBytes ((List.range' 0 256).map (fun i => IntegerToBits (f i) c)).flatten
        = (List.range (32*c)).map (fun k => (BV g (8*k) 8).toUInt8) := by
  obtain ⟨hl, hb⟩ := flatten_bits f c 256
  refine ⟨bitv ((List.range' 0 256).map (fun i => IntegerToBits (f i) c)).flatten,
    fun t => bitv_le _ t, fun i hi => ?_, ?_⟩
  · have h := BV_dig (f i) 0 c
    simp only [pow_zero, Nat.div_one] at h
    rw [← h]
    apply BV_congr
    intro j hj
    rw [Nat.mul_comm c i]
    simpa using hb i hi j hj
  · rw [BitsToBytes_eq _ (by rw [hl]; omega), hl]
    congr 2
    omega

/-- `SimpleBitPack` as the bytes of a bit function whose `c`-bit windows are the coefficients. -/
theorem SimpleBitPack_model (w : RPoly) (b : Nat) :
    ∃ g : Nat → Nat, (∀ t, g t ≤ 1) ∧
      (∀ i < 256, BV g (bitlen b * i) (bitlen b) = (w[i]!).toNat % 2^(bitlen b)) ∧
      SimpleBitPack w b = (List.range (32 * bitlen b)).map (fun k => (BV g (8*k) 8).toUInt8) := by
  obtain ⟨g, h1, h2, h3⟩ := pack_model (fun i => (w[i]!).toNat) (bitlen b)
  refine ⟨g, h1, h2, ?_⟩
  rw [← h3]
  unfold SimpleBitPack
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-- `BitPack` likewise (the packed integer is `b - w[i]`). -/
theorem BitPack_model (w : RPoly) (a b : Nat) :
    ∃ g : Nat → Nat, (∀ t, g t ≤ 1) ∧
      (∀ i < 256, BV g (bitlen (a + b) * i) (bitlen (a + b)) = ((b : Int) - w[i]!).toNat % 2^(bitlen (a + b))) ∧
      BitPack w a b = (List.range (32 * bitlen (a + b))).map (fun k => (BV g (8*k) 8).toUInt8) := by
  obtain ⟨g, h1, h2, h3⟩ := pack_model (fun i => ((b : Int) - w[i]!).toNat) (bitlen (a + b))
  refine ⟨g, h1, h2, ?_⟩
  rw [← h3]
  unfold BitPack
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

/-! ## Unpacking model -/

theorem vec_fold_gen {α : Type} {m : Nat} (d : α) (f : Nat → α) : ∀ n, ∀ i (hi : i < m),
    (List.foldl (fun (w : Vector α m) a => w.set! a (f a)) (Vector.replicate m d)
      (List.range' 0 n))[i] = if i < n then f i else d := by
  intro n
  induction n with
  | zero => intro i hi; simp
  | succ n ih =>
    intro i hi
    rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil]
    show (Vector.setIfInBounds _ _ _)[i] = _
    rw [Vector.getElem_setIfInBounds hi, ih i hi]
    simp only [Nat.zero_add, Nat.one_mul]
    by_cases h1 : n = i
    · subst h1; simp
    · have h2 : (i < n + 1) ↔ (i < n) := by omega
      simp [h1, h2]

theorem vec_fold (f : Nat → Int) : ∀ n, ∀ i (hi : i < 256),
    (List.foldl (fun (w : Vector Int 256) a => w.set! a (f a)) (Vector.replicate 256 0)
      (List.range' 0 n))[i] = if i < n then f i else 0 := vec_fold_gen 0 f

theorem bitv_window (z : List Bool) (s c j : Nat) (hj : j < c) :
    bitv (List.take c (List.drop s z)) j = bitv z (s + j) := by
  simp [bitv, List.getElem?_take, List.getElem?_drop, hj]

theorem BitsToInteger_window (v : List UInt8) (s c : Nat) :
    BitsToInteger (List.take c (List.drop s (BytesToBits v))) c = BV (byteBit v) s c := by
  rw [BitsToInteger_eq]
  apply BV_congr
  intro j hj
  rw [Nat.zero_add, bitv_window _ _ _ _ hj, bitv_BytesToBits]

theorem SimpleBitUnpack_get (v : List UInt8) (b i : Nat) (hi : i < 256) :
    (SimpleBitUnpack v b)[i] = ((BV (byteBit v) (bitlen b * i) (bitlen b) : Nat) : Int) := by
  unfold SimpleBitUnpack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (vec_fold (fun a => ((BitsToInteger (List.take (bitlen b)
    (List.drop (a * bitlen b) (BytesToBits v))) (bitlen b) : Nat) : Int)) 256 i hi).trans ?_
  rw [if_pos hi, BitsToInteger_window, Nat.mul_comm i]

theorem BitUnpack_get (v : List UInt8) (a b i : Nat) (hi : i < 256) :
    (BitUnpack v a b)[i] = (b : Int) - ((BV (byteBit v) (bitlen (a + b) * i) (bitlen (a + b)) : Nat) : Int) := by
  unfold BitUnpack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (vec_fold (fun x => (b : Int) - ((BitsToInteger (List.take (bitlen (a + b))
    (List.drop (x * bitlen (a + b)) (BytesToBits v))) (bitlen (a + b)) : Nat) : Int)) 256 i hi).trans ?_
  rw [if_pos hi, BitsToInteger_window, Nat.mul_comm i]

/-! ## `bitlen` -/

theorem lt_two_pow_bitlen (a : Nat) : a < 2 ^ bitlen a := by
  unfold bitlen
  split
  · subst_vars; simp
  · exact Nat.lt_log2_self

theorem bitlen_le_of_lt {a k : Nat} (h : a < 2 ^ k) : bitlen a ≤ k := by
  unfold bitlen
  split
  · omega
  · rename_i h0
    have := (Nat.log2_lt h0).2 h
    omega

/-- A byte is the window of the bits of the byte string. -/
theorem BV_byteBit (v : List UInt8) (o : Nat) (h : o < v.length) :
    BV (byteBit v) (8 * o) 8 = (v[o]).toNat := by
  have h1 : BV (byteBit v) (8 * o) 8 = BV (dig (v[o]).toNat) 0 8 := by
    apply BV_congr
    intro j hj
    have e1 : (8 * o + j) / 8 = o := by omega
    have e2 : (8 * o + j) % 8 = j := by omega
    simp only [byteBit, dig, e1, e2, Nat.zero_add, List.getElem?_eq_getElem h, Option.getD_some]
  rw [h1, BV_dig]
  have := (v[o]).toNat_lt
  simp

/-! ## The encoders and decoders of Section 7.2, as concatenations / pointwise -/

theorem w1Encode_eq (p : Params) (w₁ : Vector RPoly p.k) :
    w1Encode p w₁ = ((List.range' 0 p.k).map
      fun i => SimpleBitPack w₁[i]! ((q - 1) / (2 * p.γ₂) - 1)).flatten := by
  unfold w1Encode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem pkEncode_eq (p : Params) (ρ : List UInt8) (t₁ : Vector RPoly p.k) :
    pkEncode p ρ t₁ = ρ ++ ((List.range' 0 p.k).map
      fun i => SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1)).flatten := by
  unfold pkEncode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem skEncode_eq (p : Params) (ρ K tr : List UInt8) (s₁ : Vector RPoly p.ℓ) (s₂ t₀ : Vector RPoly p.k) :
    skEncode p ρ K tr s₁ s₂ t₀ = ρ ++ K ++ tr ++
      ((List.range' 0 p.ℓ).map fun i => BitPack s₁[i]! p.η p.η).flatten ++
      ((List.range' 0 p.k).map fun i => BitPack s₂[i]! p.η p.η).flatten ++
      ((List.range' 0 p.k).map fun i => BitPack t₀[i]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))).flatten := by
  unfold skEncode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem pkDecode_fst (p : Params) (pk : List UInt8) : (pkDecode p pk).1 = pk.take 32 := by
  unfold pkDecode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem pkDecode_get (p : Params) (pk : List UInt8) (i : Nat) (hi : i < p.k) :
    (pkDecode p pk).2[i] =
      SimpleBitUnpack (slice pk (32 + i * (32 * p.t1Bits)) (32 * p.t1Bits)) (2 ^ p.t1Bits - 1) := by
  unfold pkDecode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (vec_fold_gen (m := p.k) (Vector.replicate 256 0) (fun a =>
    SimpleBitUnpack (slice pk (32 + a * (32 * p.t1Bits)) (32 * p.t1Bits)) (2 ^ p.t1Bits - 1)) p.k i hi).trans ?_
  rw [if_pos hi]

theorem skDecode_fst (p : Params) (sk : List UInt8) :
    (skDecode p sk).1 = slice sk 0 32 ∧ (skDecode p sk).2.1 = slice sk 32 32 ∧
    (skDecode p sk).2.2.1 = slice sk 64 64 := by
  unfold skDecode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem skDecode_s1 (p : Params) (sk : List UInt8) (i : Nat) (hi : i < p.ℓ) :
    (skDecode p sk).2.2.2.1[i] =
      BitUnpack (slice sk (128 + i * (32 * bitlen (2 * p.η))) (32 * bitlen (2 * p.η))) p.η p.η := by
  unfold skDecode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (vec_fold_gen (m := p.ℓ) (Vector.replicate 256 0) (fun a =>
    BitUnpack (slice sk (128 + a * (32 * bitlen (2 * p.η))) (32 * bitlen (2 * p.η))) p.η p.η) p.ℓ i hi).trans ?_
  rw [if_pos hi]

theorem skDecode_s2 (p : Params) (sk : List UInt8) (i : Nat) (hi : i < p.k) :
    (skDecode p sk).2.2.2.2.1[i] =
      BitUnpack (slice sk (128 + p.ℓ * (32 * bitlen (2 * p.η)) + i * (32 * bitlen (2 * p.η)))
        (32 * bitlen (2 * p.η))) p.η p.η := by
  unfold skDecode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (vec_fold_gen (m := p.k) (Vector.replicate 256 0) (fun a =>
    BitUnpack (slice sk (128 + p.ℓ * (32 * bitlen (2 * p.η)) + a * (32 * bitlen (2 * p.η)))
      (32 * bitlen (2 * p.η))) p.η p.η) p.k i hi).trans ?_
  rw [if_pos hi]

theorem skDecode_t0 (p : Params) (sk : List UInt8) (i : Nat) (hi : i < p.k) :
    (skDecode p sk).2.2.2.2.2[i] =
      BitUnpack (slice sk (128 + (p.ℓ + p.k) * (32 * bitlen (2 * p.η)) + i * (32 * p.d)) (32 * p.d))
        (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1)) := by
  unfold skDecode
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp
  refine (vec_fold_gen (m := p.k) (Vector.replicate 256 0) (fun a =>
    BitUnpack (slice sk (128 + (p.ℓ + p.k) * (32 * bitlen (2 * p.η)) + a * (32 * p.d)) (32 * p.d))
      (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))) p.k i hi).trans ?_
  rw [if_pos hi]

end XSpec.EB
