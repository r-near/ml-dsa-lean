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

theorem shakeAbs_push_lt (s self1 : keccak.Shake) (r : Nat) (M : List UInt8) (x : U8) (h : ShakeAbs s r M)
    (hs1 : self1.rate = s.rate) (hs2 : self1.pos = s.pos)
    (hs3 : toLanes self1.state = KM.xorByte (toLanes s.state) s.pos.val (UInt8.ofNat x.val))
    (i3 : Usize) (hi3 : i3.val = self1.pos.val + 1) (hne : i3 ≠ self1.rate) :
    ShakeAbs { state := self1.state, pos := i3, rate := self1.rate } r (M ++ [UInt8.ofNat x.val]) := by
  have hlt := Nat.mod_lt M.length h.rate_pos
  have hr : self1.rate.val = r := by rw [hs1]; exact h.rate
  have hp : self1.pos.val = M.length % r := by rw [hs2]; exact h.pos
  have hne' : i3.val ≠ r := fun e => hne (UScalar.eq_of_val_eq (by rw [e, hr]))
  have hlt2 : M.length % r + 1 < r := by omega
  refine ⟨h.rate_pos, h.rate_le, hr, ?_, ?_⟩
  · show i3.val = _
    rw [hi3, hp, List.length_append, List.length_singleton, mod_succ_lt _ _ hlt2]
  · show toLanes self1.state = _
    rw [(KM.absSt_push r h.rate_pos h.rate_le M _).1 hlt2, hs3, h.state, h.pos]

theorem shakeAbs_push_eq (s self1 : keccak.Shake) (r : Nat) (M : List UInt8) (x : U8) (h : ShakeAbs s r M)
    (hs1 : self1.rate = s.rate) (hs2 : self1.pos = s.pos)
    (hs3 : toLanes self1.state = KM.xorByte (toLanes s.state) s.pos.val (UInt8.ofNat x.val))
    (i3 : Usize) (hi3 : i3.val = self1.pos.val + 1) (heq : i3 = self1.rate)
    (a : Array U64 25#usize) (ha : toLanes a = Spec.KeccakF1600 (toLanes self1.state)) :
    ShakeAbs { state := a, pos := 0#usize, rate := self1.rate } r (M ++ [UInt8.ofNat x.val]) := by
  have hr : self1.rate.val = r := by rw [hs1]; exact h.rate
  have hp : self1.pos.val = M.length % r := by rw [hs2]; exact h.pos
  have hlt2 : M.length % r + 1 = r := by rw [← hp, ← hi3, heq, hr]
  refine ⟨h.rate_pos, h.rate_le, hr, ?_, ?_⟩
  · show (0#usize).val = _
    rw [List.length_append, List.length_singleton, mod_succ_eq _ _ hlt2]
    rfl
  · show toLanes a = _
    rw [ha, hs3, (KM.absSt_push r h.rate_pos h.rate_le M _).2 hlt2, h.state, h.pos]

theorem take_succ_bytes (data : Slice U8) (i : Nat) (hi : i < data.val.length) :
    (bytes data).take (i + 1) = (bytes data).take i ++ [UInt8.ofNat (data.val[i]'hi).val] := by
  rw [List.take_add_one]
  simp [bytes, hi]

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
      have hpos : s.pos.val < 200 := by
        have := h2.pos; have := Nat.mod_lt (M ++ (bytes data).take i.val).length h2.rate_pos
        have := h2.rate_le; omega
      have hi' : i.val < data.val.length := by simpa [Slice.len, Slice.length] using hi
      step*
      subst i2_post2
      have hmain : M ++ (bytes data).take (i.val + 1) =
          (M ++ (bytes data).take i.val) ++ [UInt8.ofNat (data.val[i.val]'hi').val] := by
        rw [take_succ_bytes data i.val hi', List.append_assoc]
      by_cases hc : i3 = self1.rate
      · simp only [hc, if_true]
        step*
        refine ⟨by omega, ?_, by omega⟩
        rw [i5_post, hmain]
        exact shakeAbs_push_eq s self1 r _ _ h2 self1_post1 self1_post2 self1_post3 i3 i3_post hc x x_post
      · simp only [hc, if_false]
        step*
        refine ⟨by omega, ?_, by omega⟩
        rw [i5_post, hmain]
        exact shakeAbs_push_lt s self1 r _ _ h2 self1_post1 self1_post2 self1_post3 i3 i3_post hc
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

theorem read_sb (a : Array U64 25#usize) (p : Nat) (hp : p < 200) (i3 i6 : Usize) (x i7 : U64) (i8 : U8)
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
      obtain ⟨hrp, hrle, hrate, k, off, hn, hoff, hoz, hpos, hst⟩ := h3
      by_cases hc : st1.pos = st1.rate
      · simp only [hc, if_true]
        step*
        have hoffr : off = r := by rw [← hpos, hc, hrate]
        have hn' : n0 + i.val = (k + 1) * r + 0 := by rw [Nat.succ_mul]; omega
        have hxl : toLanes x = (Spec.KeccakF1600)^[k + 1]
            (Spec.Keccak.absorb r Spec.Keccak.zeroState (Spec.Keccak.pad101 r M)) := by
          rw [x_post, hst, Function.iterate_succ_apply']
        subst i4_post2
        have hbyte := read_sb x 0 (by omega) i3 i6 _ i7 i8 i4 (by rw [i3_post]) rfl
          (by rw [i6_post, i5_post]) i7_post1 i8_post
        rw [hxl] at hbyte
        have hidx : (Spec.Keccak.sponge r M (n0 + out0.val.length))[n0 + i.val]? =
            some (UInt8.ofNat i8.val) := by
          rw [hS0, hn', KM.getElem?_squeeze r hrp (k + 1) _ _ 0 hrp (by rw [← hn']; omega), hbyte]
        refine ⟨by omega, ?_, ?_, ?_, by omega⟩
        · rw [s_post2]; simp [Slice.set, h2]
        · refine ⟨hrp, hrle, hrate, k + 1, 1, ?_, hrp, fun h => by omega, ?_, hxl⟩
          · rw [i10_post, Nat.succ_mul]; omega
          · show i9.val = 1
            rw [i9_post]
        · rw [s_post2, i10_post]
          exact bytes_set_inv out i _ _ n0 hi' h4 hidx
      · simp only [hc, if_false]
        step*
        have hne : off ≠ r := fun e => hc (UScalar.eq_of_val_eq (by rw [hpos, e, hrate]))
        have hoffr : off < r := by omega
        have hn' : n0 + i.val = k * r + off := hn
        subst i4_post2
        have hbyte := read_sb st1.state st1.pos.val (by omega) i3 i6 _ i7 i8 i4 i3_post rfl
          (by rw [i6_post, i5_post]) i7_post1 i8_post
        rw [hst, hpos] at hbyte
        have hidx : (Spec.Keccak.sponge r M (n0 + out0.val.length))[n0 + i.val]? =
            some (UInt8.ofNat i8.val) := by
          rw [hS0, hn', KM.getElem?_squeeze r hrp k _ _ off hoffr (by rw [← hn']; omega), hbyte]
        refine ⟨by omega, ?_, ?_, ?_, by omega⟩
        · rw [s_post2]; simp [Slice.set, h2]
        · refine ⟨hrp, hrle, hrate, k, off + 1, ?_, by omega, fun h => by omega, ?_, hst⟩
          · rw [i10_post]; omega
          · show i9.val = off + 1
            rw [i9_post, hpos]
        · rw [s_post2, i10_post]
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
