import Mathlib.Tactic.IntervalCases
import Proofs.KeccakPerm
import Proofs.KeccakBytes

/-!
# The SHAKE sponge: the extracted `Shake` context against FIPS 202
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## The relations -/

/-- `st` is a fresh SHAKE context of rate `r` that has absorbed exactly the bytes `M`. -/
structure ShakeAbs (st : keccak.Shake) (r : Nat) (M : List UInt8) : Prop where
  rate_pos : 0 < r
  rate_le : r ≤ 200
  rate : st.rate.val = r
  pos : st.pos.val = M.length % r
  state : toLanes st.state = KM.absSt r M

/-- `st` has been finalized after absorbing `M` and has squeezed exactly `n` bytes.

`n = blocks * r + off` with `0 ≤ off ≤ r`: `st.pos = off` is the read offset in the current block, and
`st.state` is the sponge state after `blocks` extra permutations of the absorbed-and-padded state `S0`
(`Spec.Keccak.sponge r M d = squeeze r d S0`). The Rust code permutes lazily at the *next* read, so a block that
has been read completely rests at `off = r`; `off = 0` only occurs right after `finalize` (`n = 0`). -/
def ShakeSqz (st : keccak.Shake) (r : Nat) (M : List UInt8) (n : Nat) : Prop :=
  0 < r ∧ r ≤ 200 ∧ st.rate.val = r ∧
  ∃ blocks off : Nat, n = blocks * r + off ∧ off ≤ r ∧ (off = 0 → blocks = 0) ∧ st.pos.val = off ∧
    toLanes st.state =
      (Spec.KeccakF1600)^[blocks] (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M))

theorem toU64_cast_U8 (b : U8) : toU64 (UScalar.cast .U64 b) = (UInt8.ofNat b.val).toUInt64 := by
  have h1 : (UScalar.cast .U64 b).val = b.val := U8.cast_U64_val_eq b
  have h2 : b.val < 256 := by scalar_tac
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  have : (toU64 (UScalar.cast .U64 b)).toBitVec.toNat = b.val := by
    show (UScalar.cast .U64 b).bv.toNat = b.val
    rw [UScalar.bv_toNat, h1]
  rw [this]
  simp
  omega

theorem toU64_shl (x z : U64) (n : Usize) (hn : n.val < 64) (hz : z.bv = x.bv <<< n.val) :
    toU64 z = toU64 x <<< n.val.toUInt64 := by
  apply UInt64.eq_of_toBitVec_eq
  simp [toU64, hz, UInt64.toBitVec_shiftLeft]
  rw [Nat.mod_eq_of_lt hn]

@[step]
theorem xor_byte_spec (self : keccak.Shake) (i : Usize) (b : U8) (hi : i.val < 200) :
    keccak.Shake.xor_byte self i b ⦃ s => s.rate = self.rate ∧ s.pos = self.pos ∧
      toLanes s.state = KM.xorByte (toLanes self.state) i.val (UInt8.ofNat b.val) ⦄ := by
  unfold keccak.Shake.xor_byte
  step*
  subst i6_post2 a_post
  rw [toLanes_set, KM.xorByte]
  have e7 : toU64 i7 = toU64 (self.state.val[i5.val]) ^^^ toU64 i4 := by
    apply UInt64.eq_of_toBitVec_eq
    simp [toU64, i7_post2]
  have e4 : toU64 i4 = (UInt8.ofNat b.val).toUInt64 <<< (8 * (i.val % 8)).toUInt64 := by
    rw [toU64_shl i1 i4 i3 i4_post3 i4_post2, i1_post, toU64_cast_U8, i3_post, i2_post]
  rw [e7, e4, ← toLanes_getElem! _ _ i6, i5_post]

theorem mod_succ_lt (l r : Nat) (h : l % r + 1 < r) : (l + 1) % r = l % r + 1 := by
  have hr1 : 1 < r := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hr1, Nat.mod_eq_of_lt h]

theorem mod_succ_eq (l r : Nat) (h : l % r + 1 = r) : (l + 1) % r = 0 := by
  have := Nat.div_add_mod l r
  exact Nat.mod_eq_zero_of_dvd ⟨l / r + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩

theorem take_succ_bytes (data : Slice U8) (i : Nat) (hi : i < data.val.length) :
    (bytes data).take (i + 1) = (bytes data).take i ++ [UInt8.ofNat (data.val[i]'hi).val] := by
  rw [List.take_add_one]
  simp [bytes, hi]

theorem read_byte (i4 i7 : U64) (i6 : Usize) (i8 : U8) (m : Nat) (hm : m < 8) (h6 : i6.val = 8 * m)
    (h7 : i7.val = i4.val >>> i6.val) (h8 : i8 = UScalar.cast .U8 i7) :
    UInt8.ofNat i8.val = KM.byteOf (toU64 i4) m := by
  have h8' : i8.val = i7.val % 256 := by rw [h8, UScalar.cast_val_eq]; rfl
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  have ht : (8 * m).toUInt64.toNat = 8 * m := by
    show (UInt64.ofNat (8 * m)).toNat = _
    rw [UInt64.toNat_ofNat']
    omega
  have e1 : (UInt8.ofNat i8.val).toBitVec.toNat = i7.val % 256 := by
    show (UInt8.ofNat i8.val).toNat = _
    rw [UInt8.toNat_ofNat', h8']
    omega
  rw [e1]
  show _ = (KM.byteOf (toU64 i4) m).toNat
  simp only [KM.byteOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, ht, Nat.mod_eq_of_lt (show 8 * m < 64 by omega)]
  have : (toU64 i4).toNat = i4.val := by simp [toU64, UInt64.toNat]
  rw [this, h7, h6]

theorem read_sb (a : Array U64 25#usize) (p : Nat) (_hp : p < 200) (i3 i6 : Usize) (x i7 : U64) (i8 : U8)
    (hlt : i3.val < a.val.length) (h3 : i3.val = p / 8) (hx : x = a.val[i3.val]'hlt)
    (h6 : i6.val = 8 * (p % 8)) (h7 : i7.val = x.val >>> i6.val) (h8 : i8 = UScalar.cast .U8 i7) :
    UInt8.ofNat i8.val = KM.sb (toLanes a) p := by
  have h := read_byte x i7 i6 i8 (p % 8) (by omega) h6 h7 h8
  rw [h]
  have e : toU64 x = (toLanes a)[p / 8]! := by
    have hlt' : p / 8 < a.val.length := by rw [← h3]; exact hlt
    have e2 : a.val[i3.val]'hlt = a.val[p / 8]'hlt' := by simp [h3]
    rw [hx, e2, toLanes_getElem! a (p / 8) hlt']
  rw [e]
  rfl

theorem bytes_set_inv (out : Slice U8) (i : Usize) (v : U8) (T : List UInt8) (n0 : Nat)
    (hi : i.val < out.val.length) (h4 : ∀ j < i.val, (bytes out)[j]? = T[n0 + j]?)
    (hv : T[n0 + i.val]? = some (UInt8.ofNat v.val)) :
    ∀ j < i.val + 1, (bytes (out.set i v))[j]? = T[n0 + j]? := by
  intro j hj
  rw [bytes_set]
  by_cases h : i.val = j
  · subst h
    rw [List.getElem?_set_self (by simpa using hi), hv]
  · rw [List.getElem?_set_ne h]
    exact h4 j (by omega)

theorem mod_add_lt (l n r : Nat) (h : l % r + n < r) : (l + n) % r = l % r + n := by
  have hn : n < r := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt h]

theorem mod_add_eq (l n r : Nat) (h : l % r + n = r) : (l + n) % r = 0 := by
  have := Nat.div_add_mod l r
  exact Nat.mod_eq_zero_of_dvd ⟨l / r + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩

/-! ## One step of the sponge, as relations on contexts (generic in the result context) -/

/-- Absorbing the byte `x` without filling the block. -/
theorem shakeAbs_byte_lt (s st' : keccak.Shake) (r : Nat) (M : List UInt8) (x : U8) (h : ShakeAbs s r M)
    (hrate : st'.rate.val = r) (hpos : st'.pos.val = s.pos.val + 1) (hne : st'.pos.val ≠ r)
    (hst : toLanes st'.state = KM.xorByte (toLanes s.state) s.pos.val (UInt8.ofNat x.val)) :
    ShakeAbs st' r (M ++ [UInt8.ofNat x.val]) := by
  have hlt := Nat.mod_lt M.length h.rate_pos
  have hp : s.pos.val = M.length % r := h.pos
  have hlt2 : M.length % r + 1 < r := by omega
  refine ⟨h.rate_pos, h.rate_le, hrate, ?_, ?_⟩
  · rw [hpos, hp, List.length_append, List.length_singleton, mod_succ_lt _ _ hlt2]
  · rw [hst, (KM.absSt_push r h.rate_pos h.rate_le M _).1 hlt2, h.state, hp]

/-- Absorbing the byte `x` that fills the block (the permutation has been applied). -/
theorem shakeAbs_byte_eq (s st' : keccak.Shake) (r : Nat) (M : List UInt8) (x : U8) (h : ShakeAbs s r M)
    (hrate : st'.rate.val = r) (hpos : st'.pos.val = 0) (hfull : s.pos.val + 1 = r)
    (hst : toLanes st'.state =
      Spec.KeccakF1600 (KM.xorByte (toLanes s.state) s.pos.val (UInt8.ofNat x.val))) :
    ShakeAbs st' r (M ++ [UInt8.ofNat x.val]) := by
  have hp : s.pos.val = M.length % r := h.pos
  have hlt2 : M.length % r + 1 = r := by omega
  refine ⟨h.rate_pos, h.rate_le, hrate, ?_, ?_⟩
  · rw [hpos, List.length_append, List.length_singleton, mod_succ_eq _ _ hlt2]
  · rw [hst, (KM.absSt_push r h.rate_pos h.rate_le M _).2 hlt2, h.state, hp]

/-- Absorbing a whole lane (8 bytes `B`, lane `X`) at a lane boundary without filling the block. -/
theorem shakeAbs_lane_lt (s st' : keccak.Shake) (r : Nat) (M B : List UInt8) (X : UInt64) (h : ShakeAbs s r M)
    (hB : B.length = 8) (hX : ∀ m < 8, KM.byteOf X m = B.getD m 0) (h8 : s.pos.val % 8 = 0)
    (hfit : s.pos.val + 8 ≤ r) (hrate : st'.rate.val = r) (hpos : st'.pos.val = s.pos.val + 8)
    (hne : st'.pos.val ≠ r)
    (hst : toLanes st'.state = KM.xorLane (toLanes s.state) (s.pos.val / 8) X) :
    ShakeAbs st' r (M ++ B) := by
  have hp : s.pos.val = M.length % r := h.pos
  have hlt2 : M.length % r + 8 < r := by omega
  have hab := KM.absSt_lane r h.rate_pos h.rate_le M B X hB hX (by omega) (by omega)
  refine ⟨h.rate_pos, h.rate_le, hrate, ?_, ?_⟩
  · rw [hpos, hp, List.length_append, hB, mod_add_lt _ _ _ hlt2]
  · rw [hst, hab.1 hlt2, h.state, hp]

/-- Absorbing a whole lane that fills the block (the permutation has been applied). -/
theorem shakeAbs_lane_eq (s st' : keccak.Shake) (r : Nat) (M B : List UInt8) (X : UInt64) (h : ShakeAbs s r M)
    (hB : B.length = 8) (hX : ∀ m < 8, KM.byteOf X m = B.getD m 0) (h8 : s.pos.val % 8 = 0)
    (hfull : s.pos.val + 8 = r) (hrate : st'.rate.val = r) (hpos : st'.pos.val = 0)
    (hst : toLanes st'.state =
      Spec.KeccakF1600 (KM.xorLane (toLanes s.state) (s.pos.val / 8) X)) :
    ShakeAbs st' r (M ++ B) := by
  have hp : s.pos.val = M.length % r := h.pos
  have hlt2 : M.length % r + 8 = r := by omega
  have hab := KM.absSt_lane r h.rate_pos h.rate_le M B X hB hX (by omega) (by omega)
  refine ⟨h.rate_pos, h.rate_le, hrate, ?_, ?_⟩
  · rw [hpos, List.length_append, hB, mod_add_eq _ _ _ hlt2]
  · rw [hst, hab.2 hlt2, h.state, hp]

/-! ## Specs of the helpers -/

@[step]
theorem wrap_spec (self : keccak.Shake) :
    keccak.Shake.wrap self ⦃ s => s.rate = self.rate ∧
      (self.pos = self.rate → s.pos.val = 0 ∧ toLanes s.state = Spec.KeccakF1600 (toLanes self.state)) ∧
      (self.pos ≠ self.rate → s = self) ⦄ := by
  unfold keccak.Shake.wrap
  split
  · rename_i h
    step*
  · rename_i h
    simp [WP.spec_ok, h]

@[step]
theorem lane_fits_spec (self : keccak.Shake) (remaining : Usize) (h : self.pos.val ≤ self.rate.val) :
    keccak.Shake.lane_fits self remaining ⦃ b =>
      (b = true ↔ (8 ≤ remaining.val ∧ self.pos.val % 8 = 0 ∧ 8 ≤ self.rate.val - self.pos.val)) ⦄ := by
  unfold keccak.Shake.lane_fits
  step*

@[step]
theorem xor_lane_spec (self : keccak.Shake) (i : Usize) (x : U64) (hi : i.val < 25) :
    keccak.Shake.xor_lane self i x ⦃ s => s.rate = self.rate ∧ s.pos = self.pos ∧
      toLanes s.state = KM.xorLane (toLanes self.state) i.val (toU64 x) ⦄ := by
  unfold keccak.Shake.xor_lane
  step*
  subst a_post i1_post2
  rw [toLanes_set, KM.xorLane, toLanes_getElem! self.state i.val i1]
  congr 1
  apply UInt64.eq_of_toBitVec_eq
  simp [toU64, i2_post2]

/-! ### Lanes as bytes -/

theorem toU64_or_pure (x y : U64) : toU64 (x ||| y) = toU64 x ||| toU64 y := by
  simp [toU64]

theorem byteOf_or_bv (x y z : U64) (h : z.bv = x.bv ||| y.bv) (m : Nat) :
    KM.byteOf (toU64 z) m = KM.byteOf (toU64 x) m ||| KM.byteOf (toU64 y) m := by
  have : toU64 z = toU64 x ||| toU64 y := by
    apply UInt64.eq_of_toBitVec_eq
    simp [toU64, h]
  rw [this, KM.byteOf_or]

theorem byteOf_shl' (b : UInt8) (k s m : Nat) (hs : s = 8 * k) (hk : k < 8) (hm : m < 8) :
    KM.byteOf (b.toUInt64 <<< s.toUInt64) m = if m = k then b else 0 := by
  subst hs
  exact KM.byteOf_shl b k m hk hm

theorem byteOf_toUInt64 (b : UInt8) (m : Nat) (hm : m < 8) :
    KM.byteOf b.toUInt64 m = if m = 0 then b else 0 := by
  have h := KM.byteOf_shl b 0 m (by omega) hm
  have e : b.toUInt64 <<< (8 * 0).toUInt64 = b.toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq
    simp
  rw [e] at h
  exact h

theorem byteOf_cast0 (x : U64) (b : U8) (m : Nat) (hm : m < 8) (hx : x = UScalar.cast .U64 b) :
    KM.byteOf (toU64 x) m = if m = 0 then UInt8.ofNat b.val else 0 := by
  rw [hx, toU64_cast_U8]
  exact byteOf_toUInt64 _ m hm

theorem byteOf_cast_shl (x z : U64) (n : Usize) (b : U8) (k m : Nat) (hk : k < 8) (hm : m < 8)
    (hn : n.val = 8 * k) (hx : x = UScalar.cast .U64 b) (hz : z.bv = x.bv <<< n.val) :
    KM.byteOf (toU64 z) m = if m = k then UInt8.ofNat b.val else 0 := by
  have hn64 : n.val < 64 := by omega
  rw [toU64_shl x z n hn64 hz, hx, toU64_cast_U8]
  exact byteOf_shl' _ k n.val m hn hk hm

theorem bytes_getElem?_of (data : Slice U8) (j : Nat) (v : U8) (h : data.val[j]? = some v) :
    (bytes data)[j]? = some (UInt8.ofNat v.val) := by
  simp [bytes, h]

theorem getD_window (L : List UInt8) (i m : Nat) (hm : m < 8) (v : UInt8) (h : L[i + m]? = some v) :
    ((L.drop i).take 8).getD m 0 = v := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hm, h]

@[step]
theorem load_lane_spec (data : Slice U8) (i : Usize) (h : i.val + 8 ≤ data.val.length) :
    keccak.load_lane data i ⦃ x =>
      ∀ m < 8, (bytes data)[i.val + m]? = some (KM.byteOf (toU64 x) m) ⦄ := by
  unfold keccak.load_lane
  step*
  subst i1_post2 i4_post2 i9_post2 i14_post2 i19_post2 i24_post2 i29_post2 i34_post2
  have hd0 : (bytes data)[i.val]? = some (UInt8.ofNat ((data.val)[i.val]'i1).val) :=
    bytes_getElem?_of data i.val _ (List.getElem?_eq_getElem i1)
  have hd1 : (bytes data)[i.val + 1]? = some (UInt8.ofNat ((data.val)[i3.val]'i4).val) := by
    rw [← i3_post]
    exact bytes_getElem?_of data i3.val _ (List.getElem?_eq_getElem i4)
  have hd2 : (bytes data)[i.val + 2]? = some (UInt8.ofNat ((data.val)[i8.val]'i9).val) := by
    rw [← i8_post]
    exact bytes_getElem?_of data i8.val _ (List.getElem?_eq_getElem i9)
  have hd3 : (bytes data)[i.val + 3]? = some (UInt8.ofNat ((data.val)[i13.val]'i14).val) := by
    rw [← i13_post]
    exact bytes_getElem?_of data i13.val _ (List.getElem?_eq_getElem i14)
  have hd4 : (bytes data)[i.val + 4]? = some (UInt8.ofNat ((data.val)[i18.val]'i19).val) := by
    rw [← i18_post]
    exact bytes_getElem?_of data i18.val _ (List.getElem?_eq_getElem i19)
  have hd5 : (bytes data)[i.val + 5]? = some (UInt8.ofNat ((data.val)[i23.val]'i24).val) := by
    rw [← i23_post]
    exact bytes_getElem?_of data i23.val _ (List.getElem?_eq_getElem i24)
  have hd6 : (bytes data)[i.val + 6]? = some (UInt8.ofNat ((data.val)[i28.val]'i29).val) := by
    rw [← i28_post]
    exact bytes_getElem?_of data i28.val _ (List.getElem?_eq_getElem i29)
  have hd7 : (bytes data)[i.val + 7]? = some (UInt8.ofNat ((data.val)[i33.val]'i34).val) := by
    rw [← i33_post]
    exact bytes_getElem?_of data i33.val _ (List.getElem?_eq_getElem i34)
  intro m hm
  have b0 := byteOf_cast0 i2 _ m hm i2_post
  have b1 := byteOf_cast_shl i5 i6 8#usize _ 1 m (by omega) hm rfl i5_post i6_post2
  have b2 := byteOf_cast_shl i10 i11 16#usize _ 2 m (by omega) hm rfl i10_post i11_post2
  have b3 := byteOf_cast_shl i15 i16 24#usize _ 3 m (by omega) hm rfl i15_post i16_post2
  have b4 := byteOf_cast_shl i20 i21 32#usize _ 4 m (by omega) hm rfl i20_post i21_post2
  have b5 := byteOf_cast_shl i25 i26 40#usize _ 5 m (by omega) hm rfl i25_post i26_post2
  have b6 := byteOf_cast_shl i30 i31 48#usize _ 6 m (by omega) hm rfl i30_post i31_post2
  have b7 := byteOf_cast_shl i35 i36 56#usize _ 7 m (by omega) hm rfl i35_post i36_post2
  rw [toU64_or_pure, KM.byteOf_or, byteOf_or_bv _ _ _ i32_post2, byteOf_or_bv _ _ _ i27_post2,
    byteOf_or_bv _ _ _ i22_post2, byteOf_or_bv _ _ _ i17_post2, byteOf_or_bv _ _ _ i12_post2,
    byteOf_or_bv _ _ _ i7_post2, b0, b1, b2, b3, b4, b5, b6, b7]
  interval_cases m <;> simp [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7]

theorem store_lane_inv (out : Slice U8) (i : Usize) (x : U64) (T : List UInt8) (n0 : Nat)
    (h : i.val + 8 ≤ out.val.length) (h4 : ∀ j < i.val, (bytes out)[j]? = T[n0 + j]?)
    (hT : ∀ m < 8, T[n0 + i.val + m]? = some (KM.byteOf (toU64 x) m)) :
    keccak.store_lane out i x ⦃ o => o.val.length = out.val.length ∧
      ∀ j < i.val + 8, (bytes o)[j]? = T[n0 + j]? ⦄ := by
  unfold keccak.store_lane
  step*
  have hv0 := read_byte x x 0#usize i1 0 (by omega) rfl (by simp) i1_post
  have hv1 := read_byte x i2 8#usize i4 1 (by omega) rfl i2_post1 i4_post
  have hv2 := read_byte x i5 16#usize i7 2 (by omega) rfl i5_post1 i7_post
  have hv3 := read_byte x i8 24#usize i10 3 (by omega) rfl i8_post1 i10_post
  have hv4 := read_byte x i11 32#usize i13 4 (by omega) rfl i11_post1 i13_post
  have hv5 := read_byte x i14 40#usize i16 5 (by omega) rfl i14_post1 i16_post
  have hv6 := read_byte x i17 48#usize i19 6 (by omega) rfl i17_post1 i19_post
  have hv7 := read_byte x i20 56#usize i22 7 (by omega) rfl i20_post1 i22_post
  have c0 := bytes_set_inv out i i1 T n0 (by omega) h4 (by rw [hv0]; simpa using hT 0 (by omega))
  rw [← out1_post2] at c0
  have c1 := bytes_set_inv out1 i3 i4 T n0 (by omega) (fun j hj => c0 j (by omega))
    (by rw [hv1, i3_post, ← Nat.add_assoc]; exact hT 1 (by omega))
  rw [← out2_post2] at c1
  have c2 := bytes_set_inv out2 i6 i7 T n0 (by omega) (fun j hj => c1 j (by omega))
    (by rw [hv2, i6_post, ← Nat.add_assoc]; exact hT 2 (by omega))
  rw [← out3_post2] at c2
  have c3 := bytes_set_inv out3 i9 i10 T n0 (by omega) (fun j hj => c2 j (by omega))
    (by rw [hv3, i9_post, ← Nat.add_assoc]; exact hT 3 (by omega))
  rw [← out4_post2] at c3
  have c4 := bytes_set_inv out4 i12 i13 T n0 (by omega) (fun j hj => c3 j (by omega))
    (by rw [hv4, i12_post, ← Nat.add_assoc]; exact hT 4 (by omega))
  rw [← out5_post2] at c4
  have c5 := bytes_set_inv out5 i15 i16 T n0 (by omega) (fun j hj => c4 j (by omega))
    (by rw [hv5, i15_post, ← Nat.add_assoc]; exact hT 5 (by omega))
  rw [← out6_post2] at c5
  have c6 := bytes_set_inv out6 i18 i19 T n0 (by omega) (fun j hj => c5 j (by omega))
    (by rw [hv6, i18_post, ← Nat.add_assoc]; exact hT 6 (by omega))
  rw [← out7_post2] at c6
  have c7 := bytes_set_inv out7 i21 i22 T n0 (by omega) (fun j hj => c6 j (by omega))
    (by rw [hv7, i21_post, ← Nat.add_assoc]; exact hT 7 (by omega))
  rw [← o_post2] at c7
  refine ⟨?_, fun j hj => c7 j (by omega)⟩
  simp [o_post2, out7_post2, out6_post2, out5_post2, out4_post2, out3_post2, out2_post2, out1_post2, Slice.set]

theorem absorb_loop_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (data : Slice U8)
    (hA : ShakeAbs st r M) :
    keccak.Shake.absorb_loop st data 0#usize ⦃ st' => ShakeAbs st' r (M ++ bytes data) ⦄ := by
  unfold keccak.Shake.absorb_loop
  apply loop.spec_decr_nat
    (fun (p : keccak.Shake × Usize) => data.val.length - p.2.val)
    (fun p => p.2.val ≤ data.val.length ∧ ShakeAbs p.1 r (M ++ (bytes data).take p.2.val))
  · rintro ⟨s, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.Shake.absorb_loop.body]
    split
    · rename_i hi
      have hlt := Nat.mod_lt (M ++ (bytes data).take i.val).length h2.rate_pos
      have hposlt : s.pos.val < r := by rw [h2.pos]; exact hlt
      have hrate : s.rate.val = r := h2.rate
      have hle := h2.rate_le
      have hi' : i.val < data.val.length := by simpa [Slice.len, Slice.length] using hi
      have hlenv : data.len.val = data.val.length := by simp [Slice.len]
      step*
      split
      · rename_i hb
        obtain ⟨h8le, hmod, hrt⟩ := b_post.mp hb
        step with load_lane_spec data i (by omega) as ⟨xl, hxl⟩
        step as ⟨ip, hip⟩
        step with xor_lane_spec s ip xl (by omega) as ⟨s1, hs1, hs2, hs3⟩
        step as ⟨pp, hpp⟩
        step as ⟨i8, hi8⟩
        step as ⟨self1, hw1, hw2, hw3⟩
        have hmain : M ++ (bytes data).take (i.val + 8) =
            (M ++ (bytes data).take i.val) ++ ((bytes data).drop i.val).take 8 := by
          rw [List.take_add, List.append_assoc]
        have hBlen : (((bytes data).drop i.val).take 8).length = 8 := by simp; omega
        have hX : ∀ m < 8, KM.byteOf (toU64 xl) m = (((bytes data).drop i.val).take 8).getD m 0 :=
          fun m hm => (getD_window (bytes data) i.val m hm _ (hxl m hm)).symm
        have hs3' : toLanes s1.state = KM.xorLane (toLanes s.state) (s.pos.val / 8) (toU64 xl) := by
          rw [hs3, hip]
        have hrate' : s1.rate.val = r := by rw [hs1]; exact hrate
        have hpp' : pp.val = s.pos.val + 8 := by rw [hpp, hs2]
        refine ⟨by omega, ?_, by omega⟩
        rw [hi8, hmain]
        by_cases hc : pp = s1.rate
        · obtain ⟨hp0, hst⟩ := hw2 hc
          have hv : pp.val = s1.rate.val := by rw [hc]
          exact shakeAbs_lane_eq s self1 r _ _ (toU64 xl) h2 hBlen hX hmod (by omega)
            (by rw [hw1]; exact hrate') hp0 (by rw [hst, hs3'])
        · have hself := hw3 hc
          have hne : pp.val ≠ r := fun e => hc (UScalar.eq_of_val_eq (by rw [e, hrate']))
          exact shakeAbs_lane_lt s self1 r _ _ (toU64 xl) h2 hBlen hX hmod (by omega)
            (by rw [hw1]; exact hrate') (by rw [hself]; exact hpp') (by rw [hself]; exact hne)
            (by rw [hself]; exact hs3')
      · rename_i hb
        step as ⟨hlt, c, hc⟩
        step with xor_byte_spec s s.pos c (by omega) as ⟨s1, hs1, hs2, hs3⟩
        step as ⟨pp, hpp⟩
        step as ⟨i9, hi9⟩
        step as ⟨self1, hw1, hw2, hw3⟩
        subst hc
        have hmain : M ++ (bytes data).take (i.val + 1) =
            (M ++ (bytes data).take i.val) ++ [UInt8.ofNat (data.val[i.val]'hi').val] := by
          rw [take_succ_bytes data i.val hi', List.append_assoc]
        have hrate' : s1.rate.val = r := by rw [hs1]; exact hrate
        have hpp' : pp.val = s.pos.val + 1 := by rw [hpp, hs2]
        refine ⟨by omega, ?_, by omega⟩
        rw [hi9, hmain]
        by_cases hc : pp = s1.rate
        · obtain ⟨hp0, hst⟩ := hw2 hc
          have hv : pp.val = s1.rate.val := by rw [hc]
          exact shakeAbs_byte_eq s self1 r _ _ h2 (by rw [hw1]; exact hrate') hp0 (by omega)
            (by rw [hst, hs3])
        · have hself := hw3 hc
          have hne : pp.val ≠ r := fun e => hc (UScalar.eq_of_val_eq (by rw [e, hrate']))
          exact shakeAbs_byte_lt s self1 r _ _ h2 (by rw [hw1]; exact hrate')
            (by rw [hself]; exact hpp') (by rw [hself]; exact hne) (by rw [hself]; exact hs3)
    · rename_i hi
      have : i.val = data.val.length := by scalar_tac
      simp only [WP.spec_ok]
      rw [this, List.take_of_length_le (by simp)] at h2
      exact h2
  · refine ⟨by simp, ?_⟩
    simpa using hA


/-- **Absorb.** Absorbing a slice extends the absorbed message by its bytes. -/
@[step]
theorem absorb_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (data : Slice U8) (h : ShakeAbs st r M) :
    keccak.Shake.absorb st data ⦃ st' => ShakeAbs st' r (M ++ bytes data) ⦄ := by
  unfold keccak.Shake.absorb
  exact absorb_loop_spec st r M data h

/-- **Finalize.** Padding and the first permutation: the context now sits at the start of the output stream. -/
@[step]
theorem finalize_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (h : ShakeAbs st r M) :
    keccak.Shake.finalize st ⦃ st' => ShakeSqz st' r M 0 ⦄ := by
  unfold keccak.Shake.finalize
  have hlt := Nat.mod_lt M.length h.rate_pos
  have hpos : st.pos.val < 200 := by have := h.pos; have := h.rate_le; omega
  have hrate := h.rate
  have hrate_pos := h.rate_pos
  have hrate_le := h.rate_le
  step*
  have hr2 : self2.rate.val = r := by rw [self2_post1, self1_post1]; exact hrate
  have hi : i.val = r - 1 := by rw [i_post1, self1_post1]; omega
  have e31 : UInt8.ofNat 31 = 0x1F := rfl
  have e128 : UInt8.ofNat 128 = 0x80 := rfl
  refine ⟨hrate_pos, hrate_le, hr2, 0, 0, by simp, Nat.zero_le _, fun _ => rfl, rfl, ?_⟩
  simp only [Function.iterate_zero, id]
  rw [KM.finalState r hrate_pos hrate_le M, a_post, self2_post3, self1_post3, h.state, hi, e31, e128, h.pos]

def SqzAt (st : keccak.Shake) (r : Nat) (M : List UInt8) (k off : Nat) : Prop :=
  st.rate.val = r ∧ off < r ∧ st.pos.val = off ∧
    toLanes st.state = (Spec.KeccakF1600)^[k] (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M))

/-- The lazy permutation of the squeeze phase: afterwards the read offset is inside a block. -/
theorem wrap_sqz (st : keccak.Shake) (r : Nat) (M : List UInt8) (n : Nat) (h : ShakeSqz st r M n) :
    keccak.Shake.wrap st ⦃ s => ∃ k off, n = k * r + off ∧ SqzAt s r M k off ⦄ := by
  obtain ⟨hrp, hrle, hrate, k, off, hn, hoff, hoz, hpos, hst⟩ := h
  apply WP.spec_mono (wrap_spec st)
  rintro s ⟨hs1, hs2, hs3⟩
  by_cases hc : st.pos = st.rate
  · have hoffr : off = r := by rw [← hpos, hc, hrate]
    obtain ⟨hp0, hs⟩ := hs2 hc
    refine ⟨k + 1, 0, by rw [Nat.succ_mul]; omega, ?_, hrp, hp0, ?_⟩
    · rw [hs1, hrate]
    · rw [hs, hst, Function.iterate_succ_apply']
  · have hs' := hs3 hc
    subst hs'
    have hne : off ≠ r := fun e => hc (UScalar.eq_of_val_eq (by rw [hpos, e, hrate]))
    exact ⟨k, off, hn, hrate, by omega, hpos, hst⟩

theorem squeeze_loop_spec (st : keccak.Shake) (r : Nat) (M : List UInt8) (n0 : Nat) (out0 : Slice U8)
    (hS : ShakeSqz st r M n0) :
    keccak.Shake.squeeze_loop st out0 0#usize ⦃ p =>
      ShakeSqz p.1 r M (n0 + out0.val.length) ∧
      bytes p.2 = (Spec.Keccak.sponge r M (n0 + out0.val.length)).drop n0 ⦄ := by
  unfold keccak.Shake.squeeze_loop
  have hrp : 0 < r := hS.1
  have hS0 : Spec.Keccak.sponge r M (n0 + out0.val.length) =
      Spec.Keccak.squeeze r (n0 + out0.val.length)
        (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M)) := rfl
  apply loop.spec_decr_nat
    (fun (p : keccak.Shake × Slice U8 × Usize) => out0.val.length - p.2.2.val)
    (fun p => p.2.2.val ≤ out0.val.length ∧ p.2.1.val.length = out0.val.length ∧
       ShakeSqz p.1 r M (n0 + p.2.2.val) ∧
       ∀ j < p.2.2.val, (bytes p.2.1)[j]? = (Spec.Keccak.sponge r M (n0 + out0.val.length))[n0 + j]?)
  · rintro ⟨st1, out, i⟩ ⟨h1, h2, h3, h4⟩
    dsimp only at h1 h2 h3 h4
    simp only [keccak.Shake.squeeze_loop.body]
    split
    · rename_i hi
      have hi' : i.val < out.val.length := by simpa [Slice.len, Slice.length] using hi
      have hrle : r ≤ 200 := h3.2.1
      have hlenv : out.len.val = out.val.length := by simp [Slice.len]
      step with wrap_sqz st1 r M (n0 + i.val) h3 as ⟨k, off, self1, hn, hat⟩
      obtain ⟨hrate1, hoffr, hpos1, hst1⟩ := hat
      step*
      · have hb : b = true := by assumption
        obtain ⟨h8le, hmod, hrt⟩ := b_post.mp hb
        rename_i _ _ _ x
        have hoff8 : off % 8 = 0 := by omega
        have hT : ∀ m < 8, (Spec.Keccak.sponge r M (n0 + out0.val.length))[n0 + i.val + m]? =
            some (KM.byteOf (toU64 x) m) := by
          intro m hm
          rw [hS0, show n0 + i.val + m = k * r + (off + m) by omega,
            KM.getElem?_squeeze r hrp k _ _ (off + m) (by omega) (by omega), ← hst1]
          have e1 : (off + m) / 8 = i4.val := by omega
          have e2 : (off + m) % 8 = m := by omega
          have e3 : toU64 x = (toLanes self1.state)[i4.val]! := by
            rw [toLanes_getElem! self1.state i4.val i5, i5_post2]
          rw [e3]
          show some (KM.byteOf (toLanes self1.state)[(off + m) / 8]! ((off + m) % 8)) = _
          rw [e1, e2]
        step with store_lane_inv out i x _ n0 (by omega) h4 hT as ⟨out1, hlen1, hout1⟩
        step as ⟨pp, hpp⟩
        step as ⟨ii, hii⟩
        refine ⟨by omega, by omega, ?_, fun j hj => hout1 j (by omega), by omega⟩
        refine ⟨hrp, hrle, hrate1, k, off + 8, ?_, by omega, fun h => by omega, ?_, hst1⟩
        · omega
        · show pp.val = off + 8
          rw [hpp, hpos1]
      · rename_i hb
        have hbyte := read_sb self1.state self1.pos.val (by omega) i4 i7 _ i8 i9 i5 i4_post i5_post2
          (by rw [i7_post, i6_post]) i8_post1 i9_post
        rw [hst1, hpos1] at hbyte
        have hidx : (Spec.Keccak.sponge r M (n0 + out0.val.length))[n0 + i.val]? =
            some (UInt8.ofNat i9.val) := by
          rw [hS0, show n0 + i.val = k * r + off from hn,
            KM.getElem?_squeeze r hrp k _ _ off hoffr (by omega), hbyte]
        refine ⟨by omega, ?_, ?_, ?_, by omega⟩
        · rw [s_post2]; simp [Slice.set, h2]
        · refine ⟨hrp, hrle, hrate1, k, off + 1, ?_, by omega, fun h => by omega, ?_, hst1⟩
          · omega
          · show i10.val = off + 1
            rw [i10_post, hpos1]
        · rw [s_post2, i11_post]
          exact bytes_set_inv out i _ _ n0 hi' h4 hidx
    · rename_i hi
      have hlen : i.val = out.val.length := by
        have : ¬ i.val < out.val.length := by simpa [Slice.len, Slice.length] using hi
        omega
      simp only [WP.spec_ok]
      refine ⟨?_, ?_⟩
      · have : n0 + out0.val.length = n0 + i.val := by omega
        rw [this]; exact h3
      · rw [hS0]
        apply List.ext_getElem?
        intro j
        rw [List.getElem?_drop]
        by_cases hj : j < i.val
        · rw [h4 j hj, hS0]
        · rw [List.getElem?_eq_none (by simp [bytes]; omega), List.getElem?_eq_none]
          rw [Spec.Keccak.length_squeeze r hrp]
          omega
  · refine ⟨by simp, rfl, ?_, by simp⟩
    simpa using hS


end Proofs
