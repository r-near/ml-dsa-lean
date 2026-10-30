import Spec.Encode
import Spec.Rounding

/-!
# Round trips of the FIPS 204 encoders and decoders (Phase 5, P3)

Everything here imports only `Spec.*`. The first part copies the pure bit-level lemmas of `Proofs.EncodeBits`
(which cannot be imported without the extracted Rust). The new results are

* `BitsToInteger_IntegerToBits`, `SimpleBitUnpack_SimpleBitPack`, `BitUnpack_BitPack`;
* `HintBitUnpack_HintBitPack`: the canonical packing of a hint of weight at most `ω` (`ω < 256`) passes every
  malformedness check of Algorithm 21;
* `pkDecode_pkEncode`, `skDecode_skEncode`, `sigDecode_sigEncode`, `sigDecode_sigEncode_modPM`;
* `pkEncode_length`, `skEncode_length`, `sigEncode_length`.
-/

open Spec
set_option maxRecDepth 8192

namespace Proofs.Corr


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
    (List.foldl (fun (r : MProd Nat (Array Bool)) (_ : Nat) =>
        (⟨r.fst / 2, r.snd.push (r.fst % 2 == 1)⟩ : MProd Nat (Array Bool)))
      ⟨b0, arr⟩ (List.range' 0 m)).fst = b0 / 2^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [ih]
    rw [pow_succ, Nat.div_div_eq_div_mul]

theorem bitsLoop_snd (b0 : Nat) (arr : Array Bool) (m : Nat) :
    (List.foldl (fun (r : MProd Nat (Array Bool)) (_ : Nat) =>
        (⟨r.fst / 2, r.snd.push (r.fst % 2 == 1)⟩ : MProd Nat (Array Bool)))
      ⟨b0, arr⟩ (List.range' 0 m)).snd.toList
      = arr.toList ++ (List.range m).map (fun j => (b0 / 2^j) % 2 == 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Array.toList_push, ih, bitsLoop_fst, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc]

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
      (List.foldl (fun (r : MProd Nat (Array Bool)) (_ : Nat) =>
        (⟨r.fst / 2, r.snd.push (r.fst % 2 == 1)⟩ : MProd Nat (Array Bool)))
        ⟨(v[a]?.getD default).toNat, b⟩ (List.range' 0 8)).snd) #[] (List.range' 0 n)).toList
      = (List.range (8 * n)).map (fun t => byteBit v t == 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil, bitsLoop_snd, ih]
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

/-! # New: bit-level round trips -/

theorem BitsToInteger_IntegerToBits (x n : Nat) (hx : x < 2 ^ n) :
    BitsToInteger (IntegerToBits x n) n = x := by
  rw [BitsToInteger_eq]
  have h1 : BV (bitv (IntegerToBits x n)) 0 n = BV (dig x) 0 n := by
    apply BV_congr
    intro j hj
    rw [Nat.zero_add]
    exact bitv_IntegerToBits x n j hj
  rw [h1, BV_dig]
  simp [Nat.mod_eq_of_lt hx]

/-- The `j`-th binary digit of a window value is the `j`-th bit of the window. -/
theorem dig_BV (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) :
    ∀ n s j, j < n → dig (BV g s n) j = g (s + j) := by
  intro n
  induction n with
  | zero => intro s j hj; omega
  | succ n ih =>
    intro s j hj
    simp only [BV]
    have hgs := hg s
    cases j with
    | zero => unfold dig; simp; omega
    | succ j =>
      have := ih (s+1) j (by omega)
      rw [show s + (j+1) = s+1+j by omega, ← this]
      unfold dig
      have e : (g s + 2 * BV g (s+1) n) / 2^(j+1) = BV g (s+1) n / 2^j := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
        congr 1
        omega
      rw [e]

/-- The bits of the bytes `BV g (8k) 8` are `g`. -/
theorem byteBit_bytes (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (n t : Nat) (ht : t < 8 * n) :
    byteBit ((List.range n).map fun k => (BV g (8*k) 8).toUInt8) t = g t := by
  unfold byteBit
  have h1 : t / 8 < n := by omega
  rw [List.getElem?_map, List.getElem?_range h1]
  simp only [Option.map_some, Option.getD_some]
  have hb : BV g (8*(t/8)) 8 < 256 := by
    have := BV_lt g hg (8*(t/8)) 8
    norm_num at this
    omega
  have e : ((BV g (8*(t/8)) 8).toUInt8).toNat = BV g (8*(t/8)) 8 := by
    simp [Nat.toUInt8, Nat.mod_eq_of_lt hb]
  rw [e]
  have := dig_BV g hg 8 (8*(t/8)) (t % 8) (by omega)
  have e2 : 8 * (t / 8) + t % 8 = t := by omega
  rw [e2] at this
  exact this

theorem bytes_window (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (n c i : Nat) (hc : c * (i+1) ≤ 8 * n) :
    BV (byteBit ((List.range n).map fun k => (BV g (8*k) 8).toUInt8)) (c*i) c = BV g (c*i) c := by
  apply BV_congr
  intro j hj
  exact byteBit_bytes g hg n _ (by nlinarith)

theorem vget_eq {α : Type} [Inhabited α] {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) :
    v[i]! = v[i] := getElem!_pos v i hi

theorem SimpleBitPack_length (w : RPoly) (b : Nat) : (SimpleBitPack w b).length = 32 * bitlen b := by
  obtain ⟨g, -, -, h⟩ := SimpleBitPack_model w b
  rw [h]; simp

theorem BitPack_length (w : RPoly) (a b : Nat) : (BitPack w a b).length = 32 * bitlen (a + b) := by
  obtain ⟨g, -, -, h⟩ := BitPack_model w a b
  rw [h]; simp

/-- `SimpleBitUnpack ∘ SimpleBitPack = id` on coefficients in `[0, b]`. -/
theorem SimpleBitUnpack_SimpleBitPack (w : RPoly) (b : Nat)
    (hw : ∀ (i : Nat) (hi : i < 256), 0 ≤ w[i] ∧ w[i] ≤ (b : Int)) :
    SimpleBitUnpack (SimpleBitPack w b) b = w := by
  obtain ⟨g, hg, hwin, hbytes⟩ := SimpleBitPack_model w b
  apply Vector.ext
  intro i hi
  have hc : bitlen b * (i + 1) ≤ 8 * (32 * bitlen b) := by nlinarith
  rw [SimpleBitUnpack_get _ _ _ hi, hbytes, bytes_window g hg _ _ i hc, hwin i hi]
  obtain ⟨h0, h1⟩ := hw i hi
  have e : w[i]! = w[i] := vget_eq w i hi
  have hlt : (w[i]!).toNat < 2 ^ bitlen b := by
    have := lt_two_pow_bitlen b
    rw [e]
    omega
  rw [Nat.mod_eq_of_lt hlt, e]
  omega

/-- `BitUnpack ∘ BitPack = id` on coefficients in `[-a, b]`. -/
theorem BitUnpack_BitPack (w : RPoly) (a b : Nat)
    (hw : ∀ (i : Nat) (hi : i < 256), -(a : Int) ≤ w[i] ∧ w[i] ≤ (b : Int)) :
    BitUnpack (BitPack w a b) a b = w := by
  obtain ⟨g, hg, hwin, hbytes⟩ := BitPack_model w a b
  apply Vector.ext
  intro i hi
  have hc : bitlen (a + b) * (i + 1) ≤ 8 * (32 * bitlen (a + b)) := by nlinarith
  rw [BitUnpack_get _ _ _ _ hi, hbytes, bytes_window g hg _ _ i hc, hwin i hi]
  obtain ⟨h0, h1⟩ := hw i hi
  have e : w[i]! = w[i] := vget_eq w i hi
  have hlt : ((b : Int) - w[i]!).toNat < 2 ^ bitlen (a + b) := by
    have := lt_two_pow_bitlen (a + b)
    rw [e]
    omega
  rw [Nat.mod_eq_of_lt hlt, e]
  omega

/-! # New: slicing -/

theorem slice_append_left (x y : List UInt8) (off len : Nat) (h : off + len ≤ x.length) :
    slice (x ++ y) off len = slice x off len := by
  unfold slice
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem slice_append_right (x y : List UInt8) (off len : Nat) (h : x.length ≤ off) :
    slice (x ++ y) off len = slice y (off - x.length) len := by
  unfold slice
  rw [List.drop_append, List.drop_of_length_le h, List.nil_append]

theorem slice_self (x : List UInt8) (len : Nat) (h : x.length = len) : slice x 0 len = x := by
  unfold slice
  simp [h]

theorem flat_length (f : Nat → List UInt8) (L : Nat) (hf : ∀ j, (f j).length = L) :
    ∀ n, (((List.range' 0 n).map f).flatten).length = n * L := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range'_concat (n := n)]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.length_append, ih, Nat.zero_add, Nat.one_mul, hf]
    ring

theorem slice_flat (f : Nat → List UInt8) (L : Nat) (hf : ∀ j, (f j).length = L) :
    ∀ n i, i < n → slice ((List.range' 0 n).map f).flatten (i * L) L = f i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rw [List.range'_concat (n := n)]
    simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Nat.zero_add, Nat.one_mul]
    by_cases hin : i < n
    · rw [slice_append_left _ _ _ _ (by rw [flat_length f L hf]; nlinarith)]
      exact ih i hin
    · have e : i = n := by omega
      subst e
      rw [slice_append_right _ _ _ _ (by rw [flat_length f L hf]), flat_length f L hf, Nat.sub_self]
      unfold slice
      simp [hf]

/-! # New: the public key -/

theorem bitlen_q_sub_one : bitlen (q - 1) = 23 := by decide +kernel

theorem t1Bits_eq (p : Params) (hd : p.d = 13) : p.t1Bits = 10 := by
  unfold Params.t1Bits
  rw [hd, bitlen_q_sub_one]

theorem pkEncode_length (p : Params) (hd : p.d = 13) (ρ : List UInt8) (hρ : ρ.length = 32)
    (t₁ : Vector RPoly p.k) : (pkEncode p ρ t₁).length = p.pkLen := by
  rw [pkEncode_eq]
  have hf : ∀ j : Nat, (SimpleBitPack t₁[j]! (2 ^ p.t1Bits - 1)).length = 32 * 10 := by
    intro j
    rw [SimpleBitPack_length, t1Bits_eq p hd]
    have : bitlen (2 ^ 10 - 1) = 10 := by decide +kernel
    rw [this]
  rw [List.length_append, flat_length _ _ hf, hρ]
  unfold Params.pkLen
  rw [hd, bitlen_q_sub_one]
  ring

theorem pkDecode_pkEncode (p : Params) (hd : p.d = 13) (ρ : List UInt8) (hρ : ρ.length = 32)
    (t₁ : Vector RPoly p.k)
    (ht : ∀ (i : Nat) (hi : i < p.k) (j : Nat) (hj : j < 256), 0 ≤ t₁[i][j] ∧ t₁[i][j] < 2 ^ 10) :
    pkDecode p (pkEncode p ρ t₁) = (ρ, t₁) := by
  have hT := t1Bits_eq p hd
  have hB : bitlen (2 ^ 10 - 1) = 10 := by decide +kernel
  have hf : ∀ j : Nat, (SimpleBitPack t₁[j]! (2 ^ p.t1Bits - 1)).length = 32 * p.t1Bits := by
    intro j
    rw [SimpleBitPack_length, hT, hB]
  refine Prod.ext ?_ ?_
  · rw [pkDecode_fst, pkEncode_eq]
    simp [List.take_left' hρ]
  · apply Vector.ext
    intro i hi
    rw [pkDecode_get p _ i hi, pkEncode_eq]
    have hs : slice (ρ ++ ((List.range' 0 p.k).map fun i => SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1)).flatten)
        (32 + i * (32 * p.t1Bits)) (32 * p.t1Bits) = SimpleBitPack t₁[i]! (2 ^ p.t1Bits - 1) := by
      rw [slice_append_right _ _ _ _ (by omega), hρ, Nat.add_sub_cancel_left]
      exact slice_flat _ _ hf p.k i hi
    rw [hs, vget_eq t₁ i hi]
    apply SimpleBitUnpack_SimpleBitPack
    intro j hj
    have := ht i hi j hj
    rw [hT]
    constructor
    · exact this.1
    · have : t₁[i][j] < 1024 := by simpa using this.2
      push_cast
      omega


/-! # Hints: Algorithms 20 and 21 (models copied from `Proofs.Hint`) -/

theorem set!_eq' {α : Type} {n : Nat} (xs : Vector α n) (i : Nat) (x : α) :
    xs.set! i x = xs.setIfInBounds i x := rfl

namespace HintAux


/-- The pure value of an early-exit loop over a list: `inl r` is the early result, `inr b` the final state. -/
def efoldv {α R B : Type} (g : α → B → Sum R B) : List α → B → Sum R B
  | [], b => .inr b
  | a :: l, b => match g a b with
    | .inl r => .inl r
    | .inr b' => efoldv g l b'

theorem forIn_efoldv {α R B : Type} (g : α → B → Sum R B)
    (l : List α)
    (f : α → MProd (Option R) B → Id (ForInStep (MProd (Option R) B)))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a ⟨none, b⟩ = pure (ForInStep.done ⟨some r, s⟩)
        | .inr b' => f a ⟨none, b⟩ = pure (ForInStep.yield ⟨none, b'⟩)) (b : B) :
    ∃ s : MProd (Option R) B, forIn l (⟨none, b⟩ : MProd (Option R) B) f = pure s ∧
      match efoldv g l b with
      | .inl r => s.fst = some r
      | .inr b' => s.fst = none ∧ s.snd = b' := by
  induction l generalizing b with
  | nil => exact ⟨⟨none, b⟩, by simp, by simp [efoldv]⟩
  | cons a l ih =>
    have h1 := hf a (by simp) b
    simp only [efoldv]
    cases hg : g a b with
    | inl r =>
      rw [hg] at h1
      obtain ⟨s, hs⟩ := h1
      exact ⟨⟨some r, s⟩, by rw [List.forIn_cons, hs]; rfl, rfl⟩
    | inr b' =>
      rw [hg] at h1
      obtain ⟨s, hs, hv⟩ := ih (fun a ha => hf a (by simp [ha])) b'
      refine ⟨s, ?_, hv⟩
      rw [List.forIn_cons, h1]
      exact hs


/-- What a consumer of an early-exit loop sees. -/
def qv {R B : Type} (s : MProd (Option R) B) : Sum R B :=
  match s.fst with
  | some r => .inl r
  | none => .inr s.snd

theorem bind_forIn_efoldv {α R B γ : Type} (g : α → B → Sum R B) (l : List α)
    (f : α → MProd (Option R) B → Id (ForInStep (MProd (Option R) B)))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a ⟨none, b⟩ = pure (ForInStep.done ⟨some r, s⟩)
        | .inr b' => f a ⟨none, b⟩ = pure (ForInStep.yield ⟨none, b'⟩))
    (K1 : Sum R B → Id γ) (K : MProd (Option R) B → Id γ) (hK : ∀ s, K s = K1 (qv s)) (b : B) :
    (forIn l (⟨none, b⟩ : MProd (Option R) B) f >>= K) = K1 (efoldv g l b) := by
  obtain ⟨s, hs, hv⟩ := forIn_efoldv g l f hf b
  rw [hs, pure_bind, hK]
  congr 1
  unfold qv
  revert hv
  cases efoldv g l b <;> intro hv
  · simp [hv]
  · simp [hv.1, hv.2]

theorem forIn_efoldv_elim {α R B γ : Type} (g : α → B → Sum R B) (l : List α)
    (f : α → MProd (Option R) B → Id (ForInStep (MProd (Option R) B)))
    (hf : ∀ a, a ∈ l → ∀ b, match g a b with
        | .inl r => ∃ s, f a ⟨none, b⟩ = pure (ForInStep.done ⟨some r, s⟩)
        | .inr b' => f a ⟨none, b⟩ = pure (ForInStep.yield ⟨none, b'⟩))
    (C : Id γ → Prop) (K : MProd (Option R) B → Id γ) (b : B)
    (h : ∀ s : MProd (Option R) B, (match efoldv g l b with
        | .inl r => s.fst = some r
        | .inr b' => s.fst = none ∧ s.snd = b') → C (K s)) :
    C (forIn l (⟨none, b⟩ : MProd (Option R) B) f >>= K) := by
  obtain ⟨s, hs, hv⟩ := forIn_efoldv g l f hf b
  rw [hs, pure_bind]
  exact h s hv

theorem vset_vset {α : Type} {n : Nat} (h : Vector α n) (i : Nat) (a b : α) :
    (h.set! i a).set! i b = h.set! i b := by
  apply Vector.ext; intro j hj
  simp [Vector.set!]

theorem vget_vset {α : Type} [Inhabited α] {n : Nat} (h : Vector α n) (i : Nat) (hi : i < n) (a : α) :
    (h.set! i a)[i]! = a := by
  rw [getElem!_pos _ i (by simpa using hi)]
  rw [set!_eq', Vector.getElem_setIfInBounds hi]
  simp

theorem vset_self {α : Type} [Inhabited α] {n : Nat} (h : Vector α n) (i : Nat) (hi : i < n) :
    h.set! i h[i]! = h := by
  apply Vector.ext; intro j hj
  rw [set!_eq', Vector.getElem_setIfInBounds hj]
  by_cases hij : i = j
  · subst hij; simp; exact getElem!_pos _ _ (by simpa using hj)
  · simp [hij]

def rowLoop (y : List UInt8) (first : Nat) : Nat → Nat → HintPoly → Option HintPoly
  | 0, _, row => some row
  | n+1, idx, row =>
    if idx > first ∧ y[idx-1]! ≥ y[idx]! then none
    else rowLoop y first n (idx+1) (row.set! (y[idx]!).toNat true)

def gIn {k : Nat} (y : List UInt8) (first i : Nat) (_x : Nat) (b : MProd Nat (Vector HintPoly k)) :
    Sum (Option (Vector HintPoly k)) (MProd Nat (Vector HintPoly k)) :=
  if b.fst > first ∧ y[b.fst-1]! ≥ y[b.fst]! then .inl none
  else .inr ⟨b.fst+1, b.snd.set! i (b.snd[i]!.set! (y[b.fst]!).toNat true)⟩

theorem efoldv_gIn {k : Nat} (y : List UInt8) (first i : Nat) (hi : i < k) :
    ∀ (n c idx : Nat) (h : Vector HintPoly k),
    efoldv (gIn y first i) (List.range' c n) ⟨idx, h⟩ =
      match rowLoop y first n idx h[i]! with
      | none => .inl none
      | some row => .inr ⟨idx + n, h.set! i row⟩ := by
  intro n
  induction n with
  | zero => intro c idx h; simp [efoldv, rowLoop, vset_self _ _ hi]
  | succ n ih =>
    intro c idx h
    rw [List.range'_succ]
    simp only [efoldv, gIn, rowLoop]
    by_cases hc : idx > first ∧ y[idx-1]! ≥ y[idx]!
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      dsimp only
      rw [ih, vget_vset _ _ hi]
      rcases rowLoop y first n (idx + 1) (Vector.set! h[i]! y[idx]!.toNat true) with _ | row
      · rfl
      · simp only [vset_vset]
        rw [show idx + 1 + n = idx + (n + 1) by omega]

def gOut (sp : Params) (y : List UInt8) (i : Nat) (b : MProd Nat (Vector HintPoly sp.k)) :
    Sum (Option (Vector HintPoly sp.k)) (MProd Nat (Vector HintPoly sp.k)) :=
  if (y[sp.ω+i]!).toNat < b.fst ∨ (y[sp.ω+i]!).toNat > sp.ω then .inl none
  else match rowLoop y b.fst ((y[sp.ω+i]!).toNat - b.fst) b.fst b.snd[i]! with
    | none => .inl none
    | some row => .inr ⟨(y[sp.ω+i]!).toNat, b.snd.set! i row⟩

def gPad {R : Type} (y : List UInt8) (j : Nat) (_u : PUnit) : Sum (Option R) PUnit :=
  if y[j]! ≠ 0 then .inl none else .inr PUnit.unit

def padB (y : List UInt8) (ω idx : Nat) : Bool :=
  (List.range' idx (ω - idx)).all fun j => y[j]! == 0

theorem efoldv_gPad {R : Type} (y : List UInt8) : ∀ (n c : Nat),
    efoldv (gPad (R := R) y) (List.range' c n) PUnit.unit =
      if (List.range' c n).all (fun j => y[j]! == 0) then .inr PUnit.unit else .inl none := by
  intro n
  induction n with
  | zero => intro c; simp [efoldv]
  | succ n ih =>
    intro c
    rw [List.range'_succ]
    by_cases h0 : y[c]! = 0
    · have e : (y[c]! == 0) = true := beq_iff_eq.2 h0
      simp only [efoldv, gPad, List.all_cons, e, Bool.true_and]
      rw [if_neg (by simpa using h0)]
      exact ih (c + 1)
    · have e : (y[c]! == 0) = false := by simpa using h0
      simp only [efoldv, gPad, List.all_cons, e, Bool.false_and]
      rw [if_pos h0]
      simp

abbrev OutSt (k : Nat) := MProd (Option (Option (Vector HintPoly k))) (MProd Nat (Vector HintPoly k))

def unpackModel (sp : Params) (y : List UInt8) : Option (Vector HintPoly sp.k) :=
  match efoldv (gOut sp y) (List.range' 0 sp.k)
      ⟨0, Vector.replicate sp.k (Vector.replicate 256 false)⟩ with
  | .inl a => a
  | .inr s => if padB y sp.ω s.fst = true then some s.snd else none

theorem unpack_eq (sp : Params) (y : List UInt8) : HintBitUnpack sp y = unpackModel sp y := by
  unfold HintBitUnpack
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine forIn_efoldv_elim (gOut sp y) (List.range' 0 sp.k) _ ?hf
    (fun X => Id.run X = unpackModel sp y) _ _ ?main
  case hf =>
    intro i hi b
    obtain ⟨idx, h⟩ := b
    have hik : i < sp.k := by simpa using hi
    unfold gOut
    by_cases hc : (y[sp.ω+i]!).toNat < idx ∨ (y[sp.ω+i]!).toNat > sp.ω
    · simp only [hc, if_true]
      exact ⟨_, rfl⟩
    · simp only [hc, if_false]
      have hc' : idx ≤ (y[sp.ω+i]!).toNat := by omega
      rcases hrl : rowLoop y idx ((y[sp.ω+i]!).toNat - idx) idx h[i]! with _ | row
      · simp only [pure_bind]
        refine forIn_efoldv_elim (gIn y idx i) (List.range' idx _) _ ?hf1
          (fun X => ∃ s : MProd Nat (Vector HintPoly sp.k), X =
            (pure (ForInStep.done ⟨some none, s⟩) : Id (ForInStep (OutSt sp.k)))) _ ⟨idx, h⟩ ?main1
        case main1 =>
          intro s hs
          rw [efoldv_gIn y idx i hik, hrl] at hs
          simp only at hs
          rw [hs]
          exact ⟨_, rfl⟩
        case hf1 =>
          intro x hx b
          obtain ⟨j, hh⟩ := b
          unfold gIn
          by_cases hj : j > idx
          · by_cases hge : y[j-1]! ≥ y[j]!
            · rw [if_pos ⟨hj, hge⟩]
              dsimp only
              rw [if_pos hj, if_pos hge]
              exact ⟨_, rfl⟩
            · rw [if_neg (fun h => hge h.2)]
              dsimp only
              rw [if_pos hj, if_neg hge]
          · rw [if_neg (fun h => hj h.1)]
            dsimp only
            rw [if_neg hj]
      · dsimp only
        simp only [pure_bind]
        refine forIn_efoldv_elim (gIn y idx i) (List.range' idx _) _ ?hf1
          (fun X => X = (pure (ForInStep.yield ⟨none, ⟨(y[sp.ω+i]!).toNat, h.set! i row⟩⟩) :
            Id (ForInStep (OutSt sp.k)))) _ ⟨idx, h⟩ ?main1
        case main1 =>
          intro s hs
          rw [efoldv_gIn y idx i hik, hrl] at hs
          rcases s with ⟨o, a, hh⟩
          simp only [MProd.mk.injEq] at hs
          obtain ⟨rfl, rfl, rfl⟩ := hs
          simp only
          have : idx + ((y[sp.ω+i]!).toNat - idx) = (y[sp.ω+i]!).toNat := by omega
          rw [this]
        case hf1 =>
          intro x hx b
          obtain ⟨j, hh⟩ := b
          unfold gIn
          by_cases hj : j > idx
          · by_cases hge : y[j-1]! ≥ y[j]!
            · rw [if_pos ⟨hj, hge⟩]
              dsimp only
              rw [if_pos hj, if_pos hge]
              exact ⟨_, rfl⟩
            · rw [if_neg (fun h => hge h.2)]
              dsimp only
              rw [if_pos hj, if_neg hge]
          · rw [if_neg (fun h => hj h.1)]
            dsimp only
            rw [if_neg hj]
  case main =>
    intro s hs
    unfold unpackModel
    rcases hE : efoldv (gOut sp y) (List.range' 0 sp.k)
      ⟨0, Vector.replicate sp.k (Vector.replicate 256 false)⟩ with a | b'
    · rw [hE] at hs
      simp only at hs ⊢
      rw [hs]; rfl
    · rw [hE] at hs
      rcases s with ⟨o, a, hh⟩
      simp only at hs
      obtain ⟨rfl, rfl⟩ := hs
      simp only [pure_bind]
      refine forIn_efoldv_elim (gPad y) (List.range' a (sp.ω - a)) _ ?hf2
        (fun X => Id.run X = if padB y sp.ω a = true then some hh else none) _ PUnit.unit ?main2
      case main2 =>
        intro s2 hs'
        rw [efoldv_gPad] at hs'
        by_cases hp : (List.range' a (sp.ω - a)).all (fun j => y[j]! == 0) = true
        · rw [if_pos hp] at hs'
          simp only at hs'
          rw [hs'.1]
          have : padB y sp.ω a = true := hp
          rw [if_pos this]
          rfl
        · rw [if_neg hp] at hs'
          simp only at hs'
          rw [hs']
          have : ¬ padB y sp.ω a = true := hp
          rw [if_neg this]
          rfl
      case hf2 =>
        intro j hj u
        cases u
        unfold gPad
        by_cases h0 : y[j]! ≠ 0
        · simp only [h0, if_true, ne_eq, not_false_eq_true]
          exact ⟨PUnit.unit, trivial⟩
        · simp only [h0, if_false]


/-! ## HintBitPack: the spec as an explicit fold -/

theorem bind_forIn_foldl {α β γ : Type} (l : List α) (f : α → β → Id (ForInStep β)) (F : α → β → β)
    (hf : ∀ a, a ∈ l → ∀ b, f a b = pure (ForInStep.yield (F a b))) (K : β → Id γ) (b : β) :
    (forIn l b f >>= K) = K (l.foldl (fun b a => F a b) b) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.forIn_cons, hf a (by simp) b]
    simp only [pure_bind, List.foldl_cons]
    exact ih (fun a ha => hf a (by simp [ha])) _

def packRowF (row : HintPoly) (j : Nat) (st : MProd Nat (Array UInt8)) : MProd Nat (Array UInt8) :=
  if row[j]! = true then ⟨st.fst + 1, st.snd.set! st.fst j.toUInt8⟩ else st

def packRow (row : HintPoly) (st : MProd Nat (Array UInt8)) : MProd Nat (Array UInt8) :=
  (List.range' 0 256).foldl (fun b a => packRowF row a b) st

def packRowsF (ω : Nat) {k : Nat} (h : Vector HintPoly k) (i : Nat) (st : MProd Nat (Array UInt8)) :
    MProd Nat (Array UInt8) :=
  ⟨(packRow h[i]! st).fst, (packRow h[i]! st).snd.set! (ω + i) (packRow h[i]! st).fst.toUInt8⟩

def packModel (sp : Params) (h : Vector HintPoly sp.k) : List UInt8 :=
  ((List.range' 0 sp.k).foldl (fun b i => packRowsF sp.ω h i b)
    ⟨0, Array.replicate (sp.ω + sp.k) 0⟩).snd.toList

theorem pack_eq (sp : Params) (h : Vector HintPoly sp.k) : HintBitPack sp h = packModel sp h := by
  unfold HintBitPack packModel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  refine congrArg Id.run ?_
  rw [bind_forIn_foldl (List.range' 0 sp.k) _ (fun i st => packRowsF sp.ω h i st) ?hf]
  case hf =>
    intro i hi st
    rw [bind_forIn_foldl (List.range' 0 256) _ (fun j st => packRowF h[i]! j st) ?hf2]
    · rfl
    · intro j hj r
      unfold packRowF
      by_cases hb : (h[i]!)[j]! = true
      · simp [hb]
      · simp [hb]
  rfl


/-! ## HintBitPack: weights -/

def cntFrom (row : HintPoly) (j : Nat) : Nat := (row.toList.drop j).countP (fun b => b)

def restW {k : Nat} (h : Vector HintPoly k) (i : Nat) : Nat :=
  ((h.toList.drop i).map (fun r => r.toList.countP (fun b => b))).sum

theorem cntFrom_succ (row : HintPoly) (j : Nat) (hj : j < 256) :
    cntFrom row j = (if row[j]! = true then 1 else 0) + cntFrom row (j + 1) := by
  have hl : j < row.toList.length := by simpa using hj
  unfold cntFrom
  rw [List.drop_eq_getElem_cons hl, List.countP_cons, getElem!_pos _ _ (by simpa using hj)]
  simp only [Vector.getElem_toList]
  by_cases hb : row[j] = true <;> simp [hb] <;> omega

theorem cntFrom_256 (row : HintPoly) : cntFrom row 256 = 0 := by
  unfold cntFrom
  rw [List.drop_of_length_le (by simp)]
  rfl

theorem restW_succ {k : Nat} (h : Vector HintPoly k) (i : Nat) (hi : i < k) :
    restW h i = cntFrom h[i]! 0 + restW h (i + 1) := by
  have hl : i < h.toList.length := by simpa using hi
  unfold restW cntFrom
  rw [List.drop_eq_getElem_cons hl, List.map_cons, List.sum_cons, getElem!_pos _ _ (by simpa using hi)]
  simp only [Vector.getElem_toList, List.drop_zero]

theorem foldl_add_sum {α : Type} (f : α → Nat) (l : List α) (a : Nat) :
    l.foldl (fun s x => s + f x) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; omega

theorem vcountP (xs : Vector Bool n) : xs.countP (fun b => b) = xs.toList.countP (fun b => b) := by
  rcases xs with ⟨⟨l⟩, hl⟩
  simp [Vector.countP, Vector.toList]

theorem hintWeight_eq {k : Nat} (h : Vector HintPoly k) : HintWeight h = restW h 0 := by
  unfold HintWeight restW
  rw [← Vector.foldl_toList, List.drop_zero]
  simp only [vcountP]
  rw [foldl_add_sum (fun r : HintPoly => r.toList.countP (fun b => b))]
  simp
theorem packRow_size (row : HintPoly) (st : MProd Nat (Array UInt8)) :
    (packRow row st).snd.size = st.snd.size := by
  unfold packRow
  suffices H : ∀ (l : List Nat) (st : MProd Nat (Array UInt8)),
      (l.foldl (fun b a => packRowF row a b) st).snd.size = st.snd.size from H _ _
  intro l
  induction l with
  | nil => intro st; rfl
  | cons a l ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih]
    unfold packRowF
    split <;> simp

theorem packModel_size (sp : Params) (h : Vector HintPoly sp.k) :
    (packModel sp h).length = sp.ω + sp.k := by
  unfold packModel
  suffices H : ∀ (l : List Nat) (st : MProd Nat (Array UInt8)),
      (l.foldl (fun b i => packRowsF sp.ω h i b) st).snd.size = st.snd.size by
    rw [Array.length_toList, H]; simp
  intro l
  induction l with
  | nil => intro st; rfl
  | cons a l ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih]
    unfold packRowsF
    simp [packRow_size]

theorem HintBitPack_length (sp : Params) (h : Vector HintPoly sp.k) :
    (HintBitPack sp h).length = sp.ω + sp.k := by
  rw [pack_eq]; exact packModel_size sp h


theorem efoldv_append {α R B : Type} (g : α → B → Sum R B) (l₁ l₂ : List α) (b : B) :
    efoldv g (l₁ ++ l₂) b = match efoldv g l₁ b with
      | .inl r => .inl r
      | .inr b' => efoldv g l₂ b' := by
  induction l₁ generalizing b with
  | nil => simp [efoldv]
  | cons a l ih =>
    rcases hg : g a b with r | b' <;> simp [efoldv, hg, ih]

end HintAux
open HintAux

theorem toUInt8_toNat (x : Nat) (hx : x < 256) : x.toUInt8.toNat = x := by
  simp [Nat.toUInt8, Nat.mod_eq_of_lt hx]

/-- The byte at position `i` of a list of positions (`0` past its end). -/
def lget (L : List Nat) (i : Nat) : UInt8 := (L[i]?.getD 0).toUInt8

theorem lget_nil (i : Nat) : lget [] i = 0 := by simp [lget]

theorem lget_of_ge (L : List Nat) (i : Nat) (h : L.length ≤ i) : lget L i = 0 := by
  simp [lget, List.getElem?_eq_none h]

theorem lget_append_left (L L' : List Nat) (i : Nat) (h : i < L.length) :
    lget (L ++ L') i = lget L i := by
  simp [lget, List.getElem?_append_left h]

theorem lget_snoc (L : List Nat) (x : Nat) : lget (L ++ [x]) L.length = x.toUInt8 := by
  simp [lget]

theorem lget_append_right (L L' : List Nat) (i : Nat) (h : L.length ≤ i) :
    lget (L ++ L') i = lget L' (i - L.length) := by
  simp [lget, List.getElem?_append_right h]

theorem lget_cons_zero (s : Nat) (R : List Nat) : lget (s :: R) 0 = s.toUInt8 := by simp [lget]

theorem lget_cons_succ (s : Nat) (R : List Nat) (t : Nat) : lget (s :: R) (t+1) = lget R t := by
  simp [lget]

/-! ## The positions of the 1's -/

/-- The positions of the 1's of a hint polynomial, in increasing order. -/
def Srow (row : HintPoly) : List Nat := (List.range 256).filter (fun j => row[j]!)

/-- The positions of the 1's below `m`. -/
def Sm (row : HintPoly) (m : Nat) : List Nat := (List.range m).filter (fun j => row[j]!)

theorem Sm_256 (row : HintPoly) : Sm row 256 = Srow row := rfl

theorem Sm_succ (row : HintPoly) (m : Nat) :
    Sm row (m+1) = Sm row m ++ (if row[m]! = true then [m] else []) := by
  by_cases hb : row[m]! = true <;> simp [Sm, List.range_succ, List.filter_append, hb]

theorem Sm_length_le (row : HintPoly) (m n : Nat) (h : m ≤ n) :
    (Sm row m).length ≤ (Sm row n).length := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => rw [Sm_succ, List.length_append]; omega

theorem Srow_mem (row : HintPoly) (j : Nat) : j ∈ Srow row ↔ j < 256 ∧ row[j]! = true := by
  simp [Srow, List.mem_filter]

theorem Srow_lt (row : HintPoly) : ∀ s ∈ Srow row, s < 256 := by
  intro s hs
  exact ((Srow_mem row s).1 hs).1

theorem Srow_sorted (row : HintPoly) : (Srow row).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem toList_eq_map (row : HintPoly) : row.toList = (List.range 256).map (fun j => row[j]!) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have h3 : i < 256 := by simpa using h1
    simp [getElem!_pos row i h3]

theorem Srow_length (row : HintPoly) : (Srow row).length = row.toList.countP (fun b => b) := by
  rw [toList_eq_map, List.countP_map, List.countP_eq_length_filter]
  rfl

/-- The positions of all the 1's of the first `r` rows, row by row. -/
def Fp {k : Nat} (h : Vector HintPoly k) (r : Nat) : List Nat :=
  (List.range' 0 r).flatMap (fun i => Srow h[i]!)

theorem Fp_zero {k : Nat} (h : Vector HintPoly k) : Fp h 0 = [] := by simp [Fp]

theorem Fp_succ {k : Nat} (h : Vector HintPoly k) (r : Nat) : Fp h (r+1) = Fp h r ++ Srow h[r]! := by
  simp [Fp, List.range'_concat, List.flatMap_append]

theorem Fp_length_le {k : Nat} (h : Vector HintPoly k) (m n : Nat) (hmn : m ≤ n) :
    (Fp h m).length ≤ (Fp h n).length := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => rw [Fp_succ, List.length_append]; omega

theorem Fp_prefix {k : Nat} (h : Vector HintPoly k) (m n : Nat) (hmn : m ≤ n) :
    ∃ rest, Fp h n = Fp h m ++ rest := by
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ n hn ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r ++ Srow h[n]!, by rw [Fp_succ, hr, List.append_assoc]⟩

theorem Fp_length_sum {k : Nat} (h : Vector HintPoly k) (n : Nat) :
    (Fp h n).length = ((List.range' 0 n).map (fun i => (h[i]!).toList.countP (fun b => b))).sum := by
  induction n with
  | zero => simp [Fp]
  | succ n ih =>
    rw [Fp_succ, List.length_append, ih, Srow_length, List.range'_concat]
    simp

theorem HintWeight_eq_Fp {k : Nat} (h : Vector HintPoly k) : HintWeight h = (Fp h k).length := by
  rw [Fp_length_sum, hintWeight_eq]
  unfold restW
  rw [List.drop_zero]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have h3 : i < k := by simpa using h1
    simp [getElem!_pos h i h3]

/-! ## The packing loop -/

theorem arr_set_get (a : Array UInt8) (p : Nat) (x : UInt8) (idx : Nat) (hidx : idx < a.size) :
    (a.set! p x)[idx]! = if p = idx then x else a[idx]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ idx (by simpa using hidx),
    Array.getElem_setIfInBounds hidx, getElem!_pos a idx hidx]

theorem packRow_inv (row : HintPoly) (base : List Nat) (st : MProd Nat (Array UInt8))
    (hst : st.fst = base.length) (hb : base.length + (Srow row).length ≤ st.snd.size)
    (hbase : ∀ idx, idx < base.length → st.snd[idx]! = lget base idx) :
    ∀ m, m ≤ 256 →
      ((List.range' 0 m).foldl (fun b a => packRowF row a b) st).fst = (base ++ Sm row m).length ∧
      ((List.range' 0 m).foldl (fun b a => packRowF row a b) st).snd.size = st.snd.size ∧
      ∀ idx, idx < st.snd.size →
        ((List.range' 0 m).foldl (fun b a => packRowF row a b) st).snd[idx]! =
          if idx < (base ++ Sm row m).length then lget (base ++ Sm row m) idx else st.snd[idx]! := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨by simp [hst, Sm], by simp, fun idx hidx => ?_⟩
    simp only [List.range'_zero, List.foldl_nil, Sm, List.range_zero, List.filter_nil, List.append_nil]
    split_ifs with h
    · exact hbase idx h
    · rfl
  | succ m ih =>
    intro hm
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    rw [List.range'_concat (n := m), List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hS : List.foldl (fun b a => packRowF row a b) st (List.range' 0 m) = S1 at ih1 ih2 ih3 ⊢
    simp only [Nat.zero_add, Nat.one_mul]
    have hSm : Sm row (m+1) = Sm row m ++ (if row[m]! = true then [m] else []) := Sm_succ row m
    have hlen : (Sm row (m+1)).length ≤ (Srow row).length := by
      rw [← Sm_256]; exact Sm_length_le row _ _ (by omega)
    by_cases hr : row[m]! = true
    · have hcur : packRowF row m S1 = ⟨S1.fst + 1, S1.snd.set! S1.fst m.toUInt8⟩ := by
        unfold packRowF; rw [if_pos hr]
      have hSm' : Sm row (m+1) = Sm row m ++ [m] := by rw [hSm, if_pos hr]
      rw [hcur, hSm']
      rw [hSm'] at hlen
      simp only [List.length_append, List.length_singleton] at hlen
      have hpos : S1.fst < S1.snd.size := by
        rw [ih1, ih2]; simp only [List.length_append]; omega
      rw [← List.append_assoc]
      refine ⟨?_, ?_, ?_⟩
      · show S1.fst + 1 = _
        rw [ih1]; simp <;> omega
      · show (S1.snd.set! S1.fst m.toUInt8).size = _
        simp [ih2]
      · intro idx hidx
        have hidx' : idx < S1.snd.size := by rw [ih2]; exact hidx
        show (S1.snd.set! S1.fst m.toUInt8)[idx]! = _
        rw [arr_set_get _ _ _ _ hidx']
        generalize base ++ Sm row m = L at ih1 ih3 ⊢
        by_cases he : S1.fst = idx
        · have h1 : idx < (L ++ [m]).length := by simp only [List.length_append, List.length_singleton]; omega
          rw [if_pos he, if_pos h1]
          have : idx = L.length := by rw [← he, ih1]
          rw [this, lget_snoc, ]
        · rw [if_neg he]
          by_cases hlt : idx < L.length
          · have h1 : idx < (L ++ [m]).length := by simp only [List.length_append, List.length_singleton]; omega
            rw [if_pos h1, lget_append_left _ _ _ hlt, ih3 idx hidx, if_pos hlt]
          · have h1 : ¬ idx < (L ++ [m]).length := by simp only [List.length_append, List.length_singleton]; omega
            rw [if_neg h1, ih3 idx hidx, if_neg hlt]
    · have hcur : packRowF row m S1 = S1 := by
        unfold packRowF; rw [if_neg hr]
      have hSm' : Sm row (m+1) = Sm row m := by rw [hSm, if_neg hr, List.append_nil]
      rw [hcur, hSm']
      exact ⟨ih1, ih2, ih3⟩

theorem packRow_spec (row : HintPoly) (base : List Nat) (st : MProd Nat (Array UInt8))
    (hst : st.fst = base.length) (hb : base.length + (Srow row).length ≤ st.snd.size)
    (hbase : ∀ idx, idx < base.length → st.snd[idx]! = lget base idx) :
    (packRow row st).fst = (base ++ Srow row).length ∧
    (packRow row st).snd.size = st.snd.size ∧
    ∀ idx, idx < st.snd.size →
      (packRow row st).snd[idx]! =
        if idx < (base ++ Srow row).length then lget (base ++ Srow row) idx else st.snd[idx]! := by
  have := packRow_inv row base st hst hb hbase 256 le_rfl
  rw [Sm_256] at this
  exact this

/-- The state of the outer loop of `HintBitPack` after `n` rows. -/
def OI (ω : Nat) {k : Nat} (h : Vector HintPoly k) (n : Nat) (st : MProd Nat (Array UInt8)) : Prop :=
  st.fst = (Fp h n).length ∧ st.snd.size = ω + k ∧
  (∀ idx, idx < ω → st.snd[idx]! = lget (Fp h n) idx) ∧
  (∀ i, i < k → st.snd[ω + i]! = if i < n then ((Fp h (i+1)).length).toUInt8 else 0)

theorem OI_zero (ω : Nat) {k : Nat} (h : Vector HintPoly k) :
    OI ω h 0 ⟨0, Array.replicate (ω + k) 0⟩ := by
  refine ⟨by simp [Fp_zero], by simp, fun idx hidx => ?_, fun i hi => ?_⟩
  · show (Array.replicate (ω + k) (0 : UInt8))[idx]! = _
    rw [getElem!_pos _ idx (by simp; omega)]
    simp [Fp_zero, lget_nil]
  · show (Array.replicate (ω + k) (0 : UInt8))[ω + i]! = _
    rw [getElem!_pos _ _ (by simp; omega)]
    simp

theorem OI_step (ω : Nat) {k : Nat} (h : Vector HintPoly k) (n : Nat) (hn : n < k)
    (hT : (Fp h (n+1)).length ≤ ω) (st : MProd Nat (Array UInt8)) (hst : OI ω h n st) :
    OI ω h (n+1) (packRowsF ω h n st) := by
  obtain ⟨o1, o2, o3, o4⟩ := hst
  have hle : (Fp h n).length ≤ (Fp h (n+1)).length := Fp_length_le h n (n+1) (by omega)
  have hlen : (Fp h (n+1)).length = (Fp h n).length + (Srow h[n]!).length := by
    rw [Fp_succ, List.length_append]
  obtain ⟨p1, p2, p3⟩ := packRow_spec h[n]! (Fp h n) st o1 (by rw [o2]; omega)
    (fun idx hidx => o3 idx (by omega))
  rw [← Fp_succ] at p1 p3
  show OI ω h (n+1) ⟨(packRow h[n]! st).fst,
    (packRow h[n]! st).snd.set! (ω + n) (packRow h[n]! st).fst.toUInt8⟩
  generalize packRow h[n]! st = P at p1 p2 p3 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p1
  · show (P.snd.set! _ _).size = _
    simp [p2, o2]
  · intro idx hidx
    have hidx' : idx < P.snd.size := by rw [p2, o2]; omega
    show (P.snd.set! (ω + n) P.fst.toUInt8)[idx]! = _
    rw [arr_set_get _ _ _ _ hidx', if_neg (by omega), p3 idx (by rw [o2]; omega)]
    by_cases c : idx < (Fp h (n+1)).length
    · rw [if_pos c]
    · rw [if_neg c, o3 idx hidx, lget_of_ge _ _ (by omega), lget_of_ge _ _ (by omega)]
  · intro i hi
    have hidx' : ω + i < P.snd.size := by rw [p2, o2]; omega
    show (P.snd.set! (ω + n) P.fst.toUInt8)[ω + i]! = _
    rw [arr_set_get _ _ _ _ hidx']
    by_cases c : i = n
    · subst c
      rw [if_pos rfl, p1, if_pos (by omega)]
    · rw [if_neg (by omega), p3 (ω + i) (by rw [o2]; omega), if_neg (by omega), o4 i hi]
      by_cases hin : i < n
      · rw [if_pos hin, if_pos (by omega)]
      · rw [if_neg hin, if_neg (by omega)]

theorem OI_fold (ω : Nat) {k : Nat} (h : Vector HintPoly k) (hT : (Fp h k).length ≤ ω) :
    ∀ n, n ≤ k → OI ω h n ((List.range' 0 n).foldl (fun b i => packRowsF ω h i b)
      ⟨0, Array.replicate (ω + k) 0⟩) := by
  intro n
  induction n with
  | zero => intro _; exact OI_zero ω h
  | succ n ih =>
    intro hn
    rw [List.range'_concat (n := n), List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Nat.zero_add, Nat.one_mul]
    exact OI_step ω h n (by omega) (le_trans (Fp_length_le h (n+1) k hn) hT) _ (ih (by omega))

/-- What `HintBitPack` writes: the positions of the 1's, then zero padding, then the row end indices. -/
theorem HintBitPack_facts (sp : Params) (h : Vector HintPoly sp.k) (hw : HintWeight h ≤ sp.ω) :
    (HintBitPack sp h).length = sp.ω + sp.k ∧
    (∀ idx, idx < sp.ω → (HintBitPack sp h)[idx]! = lget (Fp h sp.k) idx) ∧
    (∀ i, i < sp.k → (HintBitPack sp h)[sp.ω + i]! = ((Fp h (i+1)).length).toUInt8) := by
  have hT : (Fp h sp.k).length ≤ sp.ω := by rw [← HintWeight_eq_Fp]; exact hw
  have hOI := OI_fold sp.ω h hT sp.k le_rfl
  obtain ⟨o1, o2, o3, o4⟩ := hOI
  rw [pack_eq]
  unfold packModel
  generalize (List.range' 0 sp.k).foldl (fun b i => packRowsF sp.ω h i b)
    ⟨0, Array.replicate (sp.ω + sp.k) 0⟩ = S at o1 o2 o3 o4 ⊢
  refine ⟨by simp [o2], fun idx hidx => ?_, fun i hi => ?_⟩
  · simp only [Array.getElem!_toList]
    rw [o3 idx hidx]
  · simp only [Array.getElem!_toList]
    rw [o4 i hi, if_pos hi]

/-! ## The unpacking loop -/

/-- The hint whose first `n` rows are those of `h` and whose other rows are zero. -/
def hv {k : Nat} (h : Vector HintPoly k) (n : Nat) : Vector HintPoly k :=
  Vector.ofFn (fun i : Fin k => if i.val < n then h[i] else Vector.replicate 256 false)

theorem hv_zero {k : Nat} (h : Vector HintPoly k) :
    hv h 0 = Vector.replicate k (Vector.replicate 256 false) := by
  apply Vector.ext; intro i hi; simp [hv]

theorem hv_full {k : Nat} (h : Vector HintPoly k) : hv h k = h := by
  apply Vector.ext; intro i hi; simp [hv, hi]

theorem hv_bang {k : Nat} (h : Vector HintPoly k) (n : Nat) (hn : n < k) :
    (hv h n)[n]! = Vector.replicate 256 false := by
  rw [getElem!_pos _ n hn]; simp [hv]

theorem hv_set {k : Nat} (h : Vector HintPoly k) (n : Nat) (hn : n < k) :
    (hv h n).set! n h[n]! = hv h (n+1) := by
  apply Vector.ext; intro i hi
  rw [set!_eq', Vector.getElem_setIfInBounds hi]
  by_cases e : n = i
  · subst e; simp [hv, getElem!_pos h n hn]
  · have : (i < n) ↔ (i < n + 1) := by omega
    simp [hv, e, this]

theorem vset_true_get (row : HintPoly) (s j : Nat) (hj : j < 256) :
    (row.set! s true)[j]! = (row[j]! || decide (s = j)) := by
  rw [set!_eq', getElem!_pos _ j hj, Vector.getElem_setIfInBounds hj, getElem!_pos row j hj]
  by_cases h : s = j <;> simp [h]

theorem foldl_set_get (R : List Nat) :
    ∀ (row : HintPoly) (j : Nat), j < 256 →
    (R.foldl (fun r s => r.set! s true) row)[j]! = (row[j]! || decide (j ∈ R)) := by
  induction R with
  | nil => intro row j hj; simp
  | cons s R ih =>
    intro row j hj
    simp only [List.foldl_cons]
    rw [ih _ j hj, vset_true_get row s j hj]
    by_cases h1 : s = j <;> by_cases h2 : j ∈ R <;> simp [h1, h2, eq_comm]

theorem row_rebuild (row : HintPoly) :
    (Srow row).foldl (fun r s => r.set! s true) (Vector.replicate 256 false) = row := by
  apply Vector.ext; intro j hj
  have key := foldl_set_get (Srow row) (Vector.replicate 256 false) j hj
  have e1 : ((Srow row).foldl (fun r s => r.set! s true) (Vector.replicate 256 false))[j]! =
      ((Srow row).foldl (fun r s => r.set! s true) (Vector.replicate 256 false))[j] :=
    getElem!_pos _ j hj
  have e3 : (Vector.replicate 256 false)[j]! = false := by
    rw [getElem!_pos _ j hj]; simp
  rw [e1, e3] at key
  rw [key]
  have e2 : row[j]! = row[j] := getElem!_pos row j hj
  by_cases hb : row[j] = true
  · have : j ∈ Srow row := (Srow_mem row j).2 ⟨hj, by rw [e2]; exact hb⟩
    simp [this, hb]
  · have : j ∉ Srow row := fun hm => hb (by have := ((Srow_mem row j).1 hm).2; rwa [e2] at this)
    simp [this, hb]

theorem rowLoop_foldl (y : List UInt8) (first : Nat) : ∀ (R : List Nat) (idx : Nat) (row : HintPoly),
    (∀ t, t < R.length → y[idx + t]! = lget R t) → R.Pairwise (· < ·) → (∀ s ∈ R, s < 256) →
    (first < idx → ∀ s ∈ R, (y[idx - 1]!).toNat < s) →
    rowLoop y first R.length idx row = some (R.foldl (fun r s => r.set! s true) row) := by
  intro R
  induction R with
  | nil => intros; simp [rowLoop]
  | cons s R ih =>
    intro idx row hy hp hlt hprev
    have hys : y[idx]! = s.toUInt8 := by
      have := hy 0 (by simp)
      rwa [Nat.add_zero, lget_cons_zero] at this
    have hs : s < 256 := hlt s (by simp)
    have htn : (y[idx]!).toNat = s := by rw [hys]; exact toUInt8_toNat s hs
    simp only [List.length_cons, rowLoop]
    have hc : ¬ (idx > first ∧ y[idx-1]! ≥ y[idx]!) := by
      rintro ⟨h1, h2⟩
      have h3 := hprev h1 s (by simp)
      have h4 : (y[idx]!).toNat ≤ (y[idx-1]!).toNat := UInt8.le_iff_toNat_le.1 h2
      omega
    rw [if_neg hc, htn]
    simp only [List.foldl_cons]
    have hpc := List.pairwise_cons.1 hp
    apply ih (idx + 1) (row.set! s true)
    · intro t ht
      rw [show idx + 1 + t = idx + (t + 1) by omega]
      have := hy (t + 1) (by simp; omega)
      rwa [lget_cons_succ] at this
    · exact hpc.2
    · intro s' hs'; exact hlt s' (by simp [hs'])
    · intro _ s' hs'
      rw [show idx + 1 - 1 = idx by omega, htn]
      exact hpc.1 s' hs'

theorem gOut_step (sp : Params) (hω : sp.ω < 256) (h : Vector HintPoly sp.k) (y : List UInt8)
    (hY1 : ∀ idx, idx < sp.ω → y[idx]! = lget (Fp h sp.k) idx)
    (hY2 : ∀ i, i < sp.k → y[sp.ω + i]! = ((Fp h (i+1)).length).toUInt8)
    (hT : (Fp h sp.k).length ≤ sp.ω) (n : Nat) (hn : n < sp.k) :
    gOut sp y n ⟨(Fp h n).length, hv h n⟩ = .inr ⟨(Fp h (n+1)).length, hv h (n+1)⟩ := by
  have hle : (Fp h (n+1)).length ≤ sp.ω := le_trans (Fp_length_le h (n+1) sp.k hn) hT
  have hlen : (Fp h (n+1)).length = (Fp h n).length + (Srow h[n]!).length := by
    rw [Fp_succ, List.length_append]
  have hyn : (y[sp.ω + n]!).toNat = (Fp h (n+1)).length := by
    rw [hY2 n hn]; exact toUInt8_toNat _ (by omega)
  have hrl : rowLoop y (Fp h n).length ((Fp h (n+1)).length - (Fp h n).length) (Fp h n).length
      (Vector.replicate 256 false) = some h[n]! := by
    have hsub : (Fp h (n+1)).length - (Fp h n).length = (Srow h[n]!).length := by omega
    rw [hsub, rowLoop_foldl y (Fp h n).length (Srow h[n]!) (Fp h n).length (Vector.replicate 256 false)
      ?hy (Srow_sorted _) (Srow_lt _) (fun hlt => absurd hlt (lt_irrefl _)), row_rebuild]
    case hy =>
      intro t ht
      have h1 : (Fp h n).length + t < sp.ω := by omega
      rw [hY1 _ h1]
      obtain ⟨rest, hr⟩ := Fp_prefix h (n+1) sp.k hn
      rw [hr, Fp_succ, List.append_assoc, lget_append_right _ _ _ (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, lget_append_left _ _ _ ht]
  have hc : ¬ ((Fp h (n+1)).length < (Fp h n).length ∨ (Fp h (n+1)).length > sp.ω) := by omega
  unfold gOut
  dsimp only
  rw [hyn, if_neg hc, hv_bang h n hn, hrl]
  dsimp only
  rw [hv_set h n hn]

theorem unp_inv (sp : Params) (hω : sp.ω < 256) (h : Vector HintPoly sp.k) (y : List UInt8)
    (hY1 : ∀ idx, idx < sp.ω → y[idx]! = lget (Fp h sp.k) idx)
    (hY2 : ∀ i, i < sp.k → y[sp.ω + i]! = ((Fp h (i+1)).length).toUInt8)
    (hT : (Fp h sp.k).length ≤ sp.ω) :
    ∀ n, n ≤ sp.k → efoldv (gOut sp y) (List.range' 0 n)
      ⟨0, Vector.replicate sp.k (Vector.replicate 256 false)⟩ = .inr ⟨(Fp h n).length, hv h n⟩ := by
  intro n
  induction n with
  | zero => intro _; simp [efoldv, Fp_zero, hv_zero]
  | succ n ih =>
    intro hn
    rw [List.range'_concat (n := n), efoldv_append, ih (by omega)]
    simp only [Nat.zero_add, Nat.one_mul, efoldv]
    rw [gOut_step sp hω h y hY1 hY2 hT n (by omega)]

theorem HintBitUnpack_HintBitPack (sp : Params) (hω : sp.ω < 256) (h : Vector HintPoly sp.k)
    (hw : HintWeight h ≤ sp.ω) : HintBitUnpack sp (HintBitPack sp h) = some h := by
  obtain ⟨hl, hY1, hY2⟩ := HintBitPack_facts sp h hw
  have hT : (Fp h sp.k).length ≤ sp.ω := by rw [← HintWeight_eq_Fp]; exact hw
  generalize HintBitPack sp h = y at hl hY1 hY2 ⊢
  rw [unpack_eq]
  unfold unpackModel
  rw [unp_inv sp hω h y hY1 hY2 hT sp.k le_rfl, hv_full]
  have hpad : padB y sp.ω (Fp h sp.k).length = true := by
    unfold padB
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range'_1] at hj
    have : y[j]! = 0 := by rw [hY1 j (by omega)]; exact lget_of_ge _ _ (by omega)
    simp [this]
  simp only
  rw [if_pos hpad]
theorem foldl_max_le_iff {α : Type} (f : α → Nat) (l : List α) (a B : Nat) :
    l.foldl (fun m x => max m (f x)) a ≤ B ↔ a ≤ B ∧ ∀ x ∈ l, f x ≤ B := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, max_le_iff]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- `‖w‖∞` of a vector is the `foldl` of `max` over the list of entries' norms. -/
theorem infNorm_vec_eq {α : Type} [InfNorm α] {n : Nat} (w : Vector α n) :
    ‖w‖∞ = w.toList.foldl (fun m x => max m ‖x‖∞) 0 := by
  show w.foldl (fun m x => max m (InfNorm.infNorm x)) 0 = _
  rw [Vector.foldl, ← Array.foldl_toList]
  rfl

/-- `‖w‖∞ ≤ B` iff every entry's norm is. -/
theorem infNorm_le_iff {α : Type} [InfNorm α] {n : Nat} (w : Vector α n) (B : Nat) :
    ‖w‖∞ ≤ B ↔ ∀ (i : Nat) (hi : i < n), ‖w[i]‖∞ ≤ B := by
  rw [infNorm_vec_eq, foldl_max_le_iff]
  constructor
  · rintro ⟨-, h⟩ i hi
    have e : w[i] = w.toList[i]'(by simpa using hi) := by simp
    rw [e]
    exact h _ (List.getElem_mem _)
  · intro h
    refine ⟨Nat.zero_le _, fun x hx => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have e : w.toList[i] = w[i]'(by simpa using hi) := by simp
    rw [e]
    exact h i (by simpa using hi)

/-! # Slicing a header and three blocks -/

theorem slice_hdr (ρ K tr A B C : List UInt8) (hρ : ρ.length = 32) (hK : K.length = 32)
    (htr : tr.length = 64) :
    slice (ρ ++ K ++ tr ++ A ++ B ++ C) 0 32 = ρ ∧ slice (ρ ++ K ++ tr ++ A ++ B ++ C) 32 32 = K ∧
    slice (ρ ++ K ++ tr ++ A ++ B ++ C) 64 64 = tr := by
  have e : ρ ++ K ++ tr ++ A ++ B ++ C = ρ ++ (K ++ (tr ++ (A ++ (B ++ C)))) := by
    simp [List.append_assoc]
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · unfold slice
    rw [List.drop_zero, List.take_left' hρ]
  · rw [slice_append_right _ _ _ _ (by rw [hρ]), hρ]
    unfold slice
    simp [List.take_left' hK]
  · rw [slice_append_right _ _ _ _ (by rw [hρ] <;> omega), hρ, slice_append_right _ _ _ _ (by rw [hK] <;> omega), hK]
    unfold slice
    simp [List.take_left' htr]

theorem three_blocks (H A B C : List UInt8) (f g hh : Nat → List UInt8) (nA nB nC LA LB : Nat)
    (hH : H.length = 128) (hAl : A.length = nA * LA) (hBl : B.length = nB * LA)
    (hCl : C.length = nC * LB)
    (hA : ∀ i, i < nA → slice A (i * LA) LA = f i) (hB : ∀ i, i < nB → slice B (i * LA) LA = g i)
    (hC : ∀ i, i < nC → slice C (i * LB) LB = hh i) :
    (∀ i, i < nA → slice (H ++ A ++ B ++ C) (128 + i * LA) LA = f i) ∧
    (∀ i, i < nB → slice (H ++ A ++ B ++ C) (128 + nA * LA + i * LA) LA = g i) ∧
    (∀ i, i < nC → slice (H ++ A ++ B ++ C) (128 + (nA + nB) * LA + i * LB) LB = hh i) := by
  have e : H ++ A ++ B ++ C = H ++ (A ++ (B ++ C)) := by simp [List.append_assoc]
  rw [e]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [slice_append_right _ _ _ _ (by omega), hH, Nat.add_sub_cancel_left,
      slice_append_left _ _ _ _ (by rw [hAl]; nlinarith)]
    exact hA i hi
  · rw [slice_append_right _ _ _ _ (by omega), hH,
      show 128 + nA * LA + i * LA - 128 = nA * LA + i * LA by omega,
      slice_append_right _ _ _ _ (by rw [hAl]; omega), hAl, Nat.add_sub_cancel_left,
      slice_append_left _ _ _ _ (by rw [hBl]; nlinarith)]
    exact hB i hi
  · rw [slice_append_right _ _ _ _ (by omega), hH,
      show 128 + (nA + nB) * LA + i * LB - 128 = nA * LA + (nB * LA + i * LB) by
        rw [Nat.add_mul]; omega,
      slice_append_right _ _ _ _ (by rw [hAl]; omega), hAl, Nat.add_sub_cancel_left,
      slice_append_right _ _ _ _ (by rw [hBl]; omega), hBl, Nat.add_sub_cancel_left]
    exact hC i hi

/-! # The private key -/

theorem BitPack_length_eta (w : RPoly) (η : Nat) : (BitPack w η η).length = 32 * bitlen (2 * η) := by
  rw [BitPack_length, show η + η = 2 * η by omega]

theorem BitPack_length_t0 (p : Params) (hd : p.d = 13) (w : RPoly) :
    (BitPack w (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))).length = 32 * p.d := by
  have e : 2 ^ (p.d - 1) = 4096 := by rw [hd]; norm_num
  rw [BitPack_length, e, hd]
  have : bitlen (4096 - 1 + 4096) = 13 := by decide +kernel
  rw [this]

theorem skEncode_length (p : Params) (hd : p.d = 13) (ρ K tr : List UInt8) (hρ : ρ.length = 32)
    (hK : K.length = 32) (htr : tr.length = 64) (s₁ : Vector RPoly p.ℓ) (s₂ t₀ : Vector RPoly p.k) :
    (skEncode p ρ K tr s₁ s₂ t₀).length = p.skLen := by
  rw [skEncode_eq]
  have hA := flat_length (fun i => BitPack s₁[i]! p.η p.η) _ (fun j => BitPack_length_eta _ p.η) p.ℓ
  have hB := flat_length (fun i => BitPack s₂[i]! p.η p.η) _ (fun j => BitPack_length_eta _ p.η) p.k
  have hC := flat_length (fun i => BitPack t₀[i]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))) _
    (fun j => BitPack_length_t0 p hd _) p.k
  simp only [List.length_append, hA, hB, hC, hρ, hK, htr]
  unfold Params.skLen
  ring

theorem skDecode_skEncode (p : Params) (hd : p.d = 13) (ρ K tr : List UInt8) (hρ : ρ.length = 32)
    (hK : K.length = 32) (htr : tr.length = 64) (s₁ : Vector RPoly p.ℓ) (s₂ t₀ : Vector RPoly p.k)
    (hs₁ : ∀ (i : Nat) (hi : i < p.ℓ) (j : Nat) (hj : j < 256), -(p.η : Int) ≤ s₁[i][j] ∧ s₁[i][j] ≤ p.η)
    (hs₂ : ∀ (i : Nat) (hi : i < p.k) (j : Nat) (hj : j < 256), -(p.η : Int) ≤ s₂[i][j] ∧ s₂[i][j] ≤ p.η)
    (ht₀ : ∀ (i : Nat) (hi : i < p.k) (j : Nat) (hj : j < 256), -4095 ≤ t₀[i][j] ∧ t₀[i][j] ≤ 4096) :
    skDecode p (skEncode p ρ K tr s₁ s₂ t₀) = (ρ, K, tr, s₁, s₂, t₀) := by
  have e12 : 2 ^ (p.d - 1) = 4096 := by rw [hd]; norm_num
  have hfη : ∀ (n : Nat) (v : Vector RPoly n) (j : Nat),
      (BitPack v[j]! p.η p.η).length = 32 * bitlen (2 * p.η) := fun n v j => BitPack_length_eta _ p.η
  have hft : ∀ (j : Nat), (BitPack t₀[j]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))).length = 32 * p.d :=
    fun j => BitPack_length_t0 p hd _
  have hH : (ρ ++ K ++ tr).length = 128 := by simp [hρ, hK, htr]
  obtain ⟨b1, b2, b3⟩ := three_blocks (ρ ++ K ++ tr) _ _ _ (fun i => BitPack s₁[i]! p.η p.η)
    (fun i => BitPack s₂[i]! p.η p.η) (fun i => BitPack t₀[i]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1)))
    p.ℓ p.k p.k (32 * bitlen (2 * p.η)) (32 * p.d) hH
    (flat_length _ _ (hfη _ s₁) p.ℓ) (flat_length _ _ (hfη _ s₂) p.k) (flat_length _ _ hft p.k)
    (fun i hi => slice_flat _ _ (hfη _ s₁) p.ℓ i hi) (fun i hi => slice_flat _ _ (hfη _ s₂) p.k i hi)
    (fun i hi => slice_flat _ _ hft p.k i hi)
  have hsk : skEncode p ρ K tr s₁ s₂ t₀ = ρ ++ K ++ tr ++
      ((List.range' 0 p.ℓ).map fun i => BitPack s₁[i]! p.η p.η).flatten ++
      ((List.range' 0 p.k).map fun i => BitPack s₂[i]! p.η p.η).flatten ++
      ((List.range' 0 p.k).map fun i =>
        BitPack t₀[i]! (2 ^ (p.d - 1) - 1) (2 ^ (p.d - 1))).flatten := skEncode_eq _ _ _ _ _ _ _
  obtain ⟨h1, h2, h3⟩ := skDecode_fst p (skEncode p ρ K tr s₁ s₂ t₀)
  obtain ⟨c1, c2, c3⟩ := slice_hdr ρ K tr _ _ _ hρ hK htr
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
  · show (skDecode p _).1 = ρ
    rw [h1, hsk, c1]
  · show (skDecode p _).2.1 = K
    rw [h2, hsk, c2]
  · show (skDecode p _).2.2.1 = tr
    rw [h3, hsk, c3]
  · show (skDecode p _).2.2.2.1 = s₁
    apply Vector.ext; intro i hi
    rw [skDecode_s1 p _ i hi, hsk, b1 i hi]
    beta_reduce
    rw [vget_eq s₁ i hi]
    exact BitUnpack_BitPack _ _ _ (fun j hj => hs₁ i hi j hj)
  · show (skDecode p _).2.2.2.2.1 = s₂
    apply Vector.ext; intro i hi
    rw [skDecode_s2 p _ i hi, hsk, b2 i hi]
    beta_reduce
    rw [vget_eq s₂ i hi]
    exact BitUnpack_BitPack _ _ _ (fun j hj => hs₂ i hi j hj)
  · show (skDecode p _).2.2.2.2.2 = t₀
    apply Vector.ext; intro i hi
    rw [skDecode_t0 p _ i hi, hsk, b3 i hi]
    beta_reduce
    rw [vget_eq t₀ i hi, e12]
    refine BitUnpack_BitPack _ _ _ (fun j hj => ?_)
    have := ht₀ i hi j hj
    omega

/-! # The signature -/

theorem bitlen_two_gamma (p : Params) (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) :
    bitlen (p.γ₁ - 1 + p.γ₁) = 1 + bitlen (p.γ₁ - 1) := by
  rcases hγ with e | e <;> rw [e] <;> decide +kernel

theorem BitPack_length_z (p : Params) (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) (w : RPoly) :
    (BitPack w (p.γ₁ - 1) p.γ₁).length = 32 * (1 + bitlen (p.γ₁ - 1)) := by
  rw [BitPack_length, bitlen_two_gamma p hγ]

theorem sigEncode_eq (p : Params) (c : List UInt8) (z : Vector RPoly p.ℓ) (h : Vector HintPoly p.k) :
    sigEncode p c z h = c ++ ((List.range' 0 p.ℓ).map fun i => BitPack z[i]! (p.γ₁ - 1) p.γ₁).flatten ++
      HintBitPack p h := by
  unfold sigEncode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

def sigZ (p : Params) (σ : List UInt8) : Vector RPoly p.ℓ :=
  (List.range' 0 p.ℓ).foldl (fun (w : Vector RPoly p.ℓ) a => w.set! a
    (BitUnpack (slice σ (p.lam / 4 + a * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.γ₁ - 1) p.γ₁)) (Vector.replicate p.ℓ (Vector.replicate 256 0))

theorem sigZ_get (p : Params) (σ : List UInt8) (i : Nat) (hi : i < p.ℓ) :
    (sigZ p σ)[i] = BitUnpack (slice σ (p.lam / 4 + i * (32 * (1 + bitlen (p.γ₁ - 1))))
      (32 * (1 + bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁ := by
  unfold sigZ
  refine (vec_fold_gen (m := p.ℓ) (Vector.replicate 256 0) (fun a =>
    BitUnpack (slice σ (p.lam / 4 + a * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.γ₁ - 1) p.γ₁) p.ℓ i hi).trans ?_
  rw [if_pos hi]

theorem sigDecode_eq (p : Params) (σ : List UInt8) :
    sigDecode p σ = (HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.ω + p.k))).map (fun h => (slice σ 0 (p.lam / 4), sigZ p σ, h)) := by
  unfold sigDecode sigZ
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases hH : HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1)))) (p.ω + p.k)) <;>
    simp [hH, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem sigEncode_length (p : Params) (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) (c : List UInt8)
    (hc : c.length = p.lam / 4) (z : Vector RPoly p.ℓ) (h : Vector HintPoly p.k) :
    (sigEncode p c z h).length = p.sigLen := by
  rw [sigEncode_eq, List.length_append, List.length_append,
    flat_length _ _ (fun j => BitPack_length_z p hγ _) p.ℓ, HintBitPack_length, hc]
  unfold Params.sigLen
  ring

/-- **`sigDecode ∘ sigEncode = some`**: `c̃` of `λ/4` bytes, `z` with coefficients in `[−γ₁ + 1, γ₁]`
and a hint of weight at most `ω` (`ω < 256`). The decoder's hint check (Algorithm 21) accepts the canonical
packing. -/
theorem sigDecode_sigEncode (p : Params) (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) (hω : p.ω < 256)
    (c : List UInt8) (hc : c.length = p.lam / 4) (z : Vector RPoly p.ℓ) (h : Vector HintPoly p.k)
    (hz : ∀ (i : Nat) (hi : i < p.ℓ) (j : Nat) (hj : j < 256),
      -((p.γ₁ : Int) - 1) ≤ z[i][j] ∧ z[i][j] ≤ p.γ₁)
    (hh : HintWeight h ≤ p.ω) : sigDecode p (sigEncode p c z h) = some (c, z, h) := by
  have hγ1 : 1 ≤ p.γ₁ := by rcases hγ with e | e <;> rw [e] <;> norm_num
  have hf := fun j : Nat => BitPack_length_z p hγ (z[j]!)
  have hZl : (((List.range' 0 p.ℓ).map fun i => BitPack z[i]! (p.γ₁ - 1) p.γ₁).flatten).length =
      p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1))) := flat_length _ _ hf p.ℓ
  have hσ : sigEncode p c z h = c ++ (((List.range' 0 p.ℓ).map fun i =>
      BitPack z[i]! (p.γ₁ - 1) p.γ₁).flatten ++ HintBitPack p h) := by
    rw [sigEncode_eq, List.append_assoc]
  have hy : slice (sigEncode p c z h) (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1)))) (p.ω + p.k) =
      HintBitPack p h := by
    rw [hσ, slice_append_right _ _ _ _ (by omega), hc, Nat.add_sub_cancel_left,
      slice_append_right _ _ _ _ (by rw [hZl]), hZl, Nat.sub_self]
    exact slice_self _ _ (HintBitPack_length p h)
  have hc0 : slice (sigEncode p c z h) 0 (p.lam / 4) = c := by
    rw [hσ, slice_append_left _ _ _ _ (by omega)]
    exact slice_self _ _ hc
  have hz' : sigZ p (sigEncode p c z h) = z := by
    apply Vector.ext; intro i hi
    rw [sigZ_get p _ i hi, hσ, slice_append_right _ _ _ _ (by omega), hc, Nat.add_sub_cancel_left,
      slice_append_left _ _ _ _ (by rw [hZl]; nlinarith), slice_flat _ _ hf p.ℓ i hi, vget_eq z i hi]
    refine BitUnpack_BitPack _ _ _ (fun j hj => ?_)
    have := hz i hi j hj
    omega
  rw [sigDecode_eq, hy, HintBitUnpack_HintBitPack p hω h hh]
  simp only [Option.map_some, hc0, hz']

/-- The form Algorithm 7 step 33 uses: `z mod± q` of a vector `zq ∈ R_q^ℓ` with `‖zq‖∞ < γ₁` (Sign checks
`‖z‖∞ < γ₁ − β`). -/
theorem sigDecode_sigEncode_modPM (p : Params) (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) (hω : p.ω < 256)
    (c : List UInt8) (hc : c.length = p.lam / 4) (zq : Vector Poly p.ℓ) (h : Vector HintPoly p.k)
    (hz : ‖zq‖∞ < p.γ₁) (hh : HintWeight h ≤ p.ω) :
    sigDecode p (sigEncode p c (zq.map Poly.modPM) h) = some (c, zq.map Poly.modPM, h) := by
  apply sigDecode_sigEncode p hγ hω c hc _ h _ hh
  intro i hi j hj
  have h1 : ‖zq‖∞ ≤ p.γ₁ - 1 := by omega
  have h2 := (infNorm_le_iff zq _).1 h1 i hi
  have h3 := (infNorm_le_iff zq[i] _).1 h2 j hj
  have e : (zq.map Poly.modPM)[i][j] = Zq.modPM zq[i][j] := by simp [Poly.modPM]
  rw [e]
  have h4 : (Zq.modPM zq[i][j]).natAbs ≤ p.γ₁ - 1 := h3
  have h5 := Int.natAbs_eq (Zq.modPM zq[i][j])
  omega

/-- `RPoly.toZq (Poly.modPM w) = w`: the centered representative denotes the same residue. -/
theorem toZq_modPM (w : Poly) : RPoly.toZq (Poly.modPM w) = w := by
  apply Vector.ext
  intro k hk
  simp [RPoly.toZq, Poly.modPM, Zq.modPM_cast]

/-! # The ranges `Power2Round` produces -/

theorem Power2Round_t0_range (p : Params) (hd : p.d = 13) (r : Zq) :
    -4095 ≤ (Power2Round p r).2 ∧ (Power2Round p r).2 ≤ 4096 := by
  have e : (Power2Round p r).2 = modPM (r.val : Int) (2 ^ p.d) := rfl
  have e8 : (2 : Nat) ^ p.d = 8192 := by rw [hd]; norm_num
  have h1 := modPM_lower (r.val : Int) (2 ^ p.d) (by positivity)
  have h2 := modPM_upper (r.val : Int) (2 ^ p.d) (by positivity)
  rw [e8] at h1 h2
  rw [e, e8]
  omega

theorem Power2Round_t1_range (p : Params) (hd : p.d = 13) (r : Zq) :
    0 ≤ (Power2Round p r).1 ∧ (Power2Round p r).1 < 2 ^ 10 := by
  have e : (Power2Round p r).1 = ((r.val : Int) - modPM (r.val : Int) (2 ^ p.d)) / 2 ^ p.d := rfl
  have e8 : (2 : Nat) ^ p.d = 8192 := by rw [hd]; norm_num
  have e8' : (2 : Int) ^ p.d = 8192 := by rw [hd]; norm_num
  have e10 : (2 : Int) ^ 10 = 1024 := by norm_num
  haveI : NeZero q := ⟨by decide⟩
  have hv : r.val < 8380417 := ZMod.val_lt r
  have h1 := modPM_lower (r.val : Int) (2 ^ p.d) (by positivity)
  have h2 := modPM_upper (r.val : Int) (2 ^ p.d) (by positivity)
  have h3 := modPM_dvd (r.val : Int) (2 ^ p.d)
  rw [e8] at h1 h2 h3
  rw [e, e8, e8', e10]
  omega

end Proofs.Corr
