import Proofs.Keccak4
import Proofs.PartialSample
import Proofs.Sample4Block

/-!
# The 4-way RejNTTPoly / ExpandA sampler (scratch)
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open SampleA

/-- The padded message block: the state after absorbing the 34-byte message `M` and the SHAKE padding, before the
first permutation. -/
def padSt (M : List UInt8) : Spec.Keccak.State :=
  KM.xorByte (KM.xorByte (Spec.Keccak.xorBlock Spec.Keccak.zeroState M) 34 0x1F) 167 0x80

theorem absorb_pad34 (M : List UInt8) (hM : M.length = 34) :
    Spec.Keccak.absorb 168 Spec.Keccak.zeroState (Spec.Keccak.pad101 168 M) = Spec.KeccakF1600 (padSt M) := by
  rw [KM.finalState 168 (by omega) (by omega) M]
  unfold padSt
  have hq : M.length / 168 = 0 := by omega
  rw [KM.absSt_eq 168 M 0 hq]
  simp [KM.absorb_nil, hM]

theorem sb_zero (k : Nat) : KM.sb Spec.Keccak.zeroState k = 0 := by
  unfold KM.sb KM.byteOf Spec.Keccak.zeroState
  by_cases h : k / 8 < 25
  · rw [getElem!_pos _ _ (by simpa using h)]
    simp
  · rw [getElem!_neg]
    · simp [Inhabited.default]
    · simpa using h

theorem sb_padSt (M : List UInt8) (k : Nat) (hk : k < 200) :
    KM.sb (padSt M) k = M.getD k 0 ^^^ (if k = 34 then 0x1F else 0) ^^^ (if k = 167 then 0x80 else 0) := by
  unfold padSt
  rw [KM.sb_xorByte _ _ _ (by omega) k hk, KM.sb_xorByte _ _ _ (by omega) k hk, KM.sb_xorBlock _ _ k hk, sb_zero]
  split_ifs <;> simp [UInt8.xor_assoc, UInt8.zero_xor, UInt8.xor_zero]

theorem lane4_byte (sv rv : U8) (i1 i3 i4 i5 i6 : U64) (hi1 : i1 = UScalar.cast .U64 sv)
    (hi3 : i3 = UScalar.cast .U64 rv) (h4 : i4.bv = i3.bv <<< (8#usize).val) (h5 : i5.bv = i1.bv ||| i4.bv)
    (h6 : i6.bv = i5.bv ||| (2031616#u64).bv) (m : Nat) (hm : m < 8) :
    KM.byteOf (toU64 i6) m = (if m = 0 then UInt8.ofNat sv.val else 0) ^^^ (if m = 1 then UInt8.ofNat rv.val else 0) ^^^
      (if m = 2 then 0x1F else 0) := by
  have e6 := byteOf_or_bv _ _ _ h6 m
  have e5 := byteOf_or_bv _ _ _ h5 m
  have b1 := byteOf_cast0 i1 sv m hm hi1
  have b4 := byteOf_cast_shl i3 i4 8#usize rv 1 m (by omega) hm rfl hi3 h4
  have bc : KM.byteOf (toU64 2031616#u64) m = if m = 2 then 0x1F else 0 := by
    interval_cases m <;> decide +kernel
  rw [e6, e5, b1, b4, bc]
  interval_cases m <;> simp

theorem at4_set_nat (s : St4) (k : Usize) (v : Array U64 4#usize) (k' kn : Nat) (hkn : k.val = kn) (hk : kn < 25) :
    at4 (s.set k v) k' = if kn = k' then v else at4 s k' := by
  rw [at4_set s k v k' (by omega), hkn]

theorem at4_chain (V0 V1 V2 V3 V4 V20 : Array U64 4#usize) (st1 st2 st3 st4 st5 st : St4)
    (h1 : st1 = (Array.repeat 25#usize (Array.repeat 4#usize 0#u64)).set 0#usize V0)
    (h2 : st2 = st1.set 1#usize V1) (h3 : st3 = st2.set 2#usize V2) (h4 : st4 = st3.set 3#usize V3)
    (h5 : st5 = st4.set 4#usize V4) (h6 : st = st5.set 20#usize V20) (q : Nat) (hq : q < 25) :
    at4 st q = if q = 20 then V20 else if q = 4 then V4 else if q = 3 then V3 else if q = 2 then V2 else
      if q = 1 then V1 else if q = 0 then V0 else Array.repeat 4#usize 0#u64 := by
  rw [h6, at4_set_nat _ _ _ _ 20 rfl (by norm_num), h5, at4_set_nat _ _ _ _ 4 rfl (by norm_num), h4,
    at4_set_nat _ _ _ _ 3 rfl (by norm_num), h3, at4_set_nat _ _ _ _ 2 rfl (by norm_num), h2,
    at4_set_nat _ _ _ _ 1 rfl (by norm_num), h1, at4_set_nat _ _ _ _ 0 rfl (by norm_num)]
  have e : at4 (Array.repeat 25#usize (Array.repeat 4#usize 0#u64)) q = Array.repeat 4#usize 0#u64 := by
    unfold at4
    rw [getElem!_pos _ _ (by simp [hq])]
    simp only [Array.repeat_val, List.getElem_replicate]
  rw [e]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem ln_repeat_zero (j : Nat) (hj : j < 4) : ln (Array.repeat 4#usize 0#u64) j = 0 := by
  unfold ln
  rw [getElem!_pos _ _ (by simp [hj])]
  simp only [Array.repeat_val, List.getElem_replicate]
  rfl

theorem ln_init_chain (x0 x1 x2 x3 i6 i13 i20 i27 : U64) (st1 st2 st3 st4 st5 st : St4)
    (h1 : st1 = (Array.repeat 25#usize (Array.repeat 4#usize 0#u64)).set 0#usize
      (Array.make 4#usize [x0, x0, x0, x0] (by simp)))
    (h2 : st2 = st1.set 1#usize (Array.make 4#usize [x1, x1, x1, x1] (by simp)))
    (h3 : st3 = st2.set 2#usize (Array.make 4#usize [x2, x2, x2, x2] (by simp)))
    (h4 : st4 = st3.set 3#usize (Array.make 4#usize [x3, x3, x3, x3] (by simp)))
    (h5 : st5 = st4.set 4#usize (Array.make 4#usize [i6, i13, i20, i27] (by simp)))
    (L : U64) (h6 : st = st5.set 20#usize (Array.make 4#usize [L, L, L, L] (by simp)))
    (q i : Nat) (hq : q < 25) (hi : i < 4) :
    ln (at4 st q) i = if q = 20 then toU64 L else
      if q = 4 then (if i = 0 then toU64 i6 else if i = 1 then toU64 i13 else if i = 2 then toU64 i20 else toU64 i27) else
      if q = 3 then toU64 x3 else if q = 2 then toU64 x2 else if q = 1 then toU64 x1 else if q = 0 then toU64 x0
      else 0 := by
  rw [at4_chain _ _ _ _ _ _ st1 st2 st3 st4 st5 st h1 h2 h3 h4 h5 h6 q hq]
  by_cases h20 : q = 20
  · subst h20; norm_num only; simp only [if_true, if_false]; rw [ln_make4 _ _ _ _ _ i hi]; split_ifs <;> rfl
  by_cases h4 : q = 4
  · subst h4; norm_num only; simp only [if_true, if_false]; rw [ln_make4 _ _ _ _ _ i hi]
  by_cases h3 : q = 3
  · subst h3; norm_num only; simp only [if_true, if_false]; rw [ln_make4 _ _ _ _ _ i hi]; split_ifs <;> rfl
  by_cases h2 : q = 2
  · subst h2; norm_num only; simp only [if_true, if_false]; rw [ln_make4 _ _ _ _ _ i hi]; split_ifs <;> rfl
  by_cases h1' : q = 1
  · subst h1'; norm_num only; simp only [if_true, if_false]; rw [ln_make4 _ _ _ _ _ i hi]; split_ifs <;> rfl
  by_cases h0 : q = 0
  · subst h0; norm_num only; simp only [if_true, if_false]; rw [ln_make4 _ _ _ _ _ i hi]; split_ifs <;> rfl
  simp only [h20, h4, h3, h2, h1', h0, if_false]
  exact ln_repeat_zero i hi

theorem getD_pad (R : List UInt8) (hR : R.length = 32) (sb rb : UInt8) (k : Nat) :
    (R ++ [sb, rb]).getD k 0 = if k < 32 then R.getD k 0 else if k = 32 then sb else if k = 33 then rb else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : k < 32
  · rw [if_pos h, List.getElem?_append_left (by omega), List.getD_eq_getElem?_getD]
  · rw [if_neg h, List.getElem?_append_right (by omega), hR]
    by_cases h32 : k = 32
    · subst h32; simp
    · rw [if_neg h32]
      by_cases h33 : k = 33
      · subst h33; simp
      · rw [if_neg h33]
        have e : k - 32 = (k - 34) + 2 := by omega
        rw [e]; simp

theorem byteOf_zero (m : Nat) : KM.byteOf 0 m = 0 := by
  unfold KM.byteOf
  apply UInt8.eq_of_toBitVec_eq
  simp

theorem init_byte_core (R : List UInt8) (hR : R.length = 32) (X0 X1 X2 X3 V4 C : UInt64) (sb rb : UInt8)
    (hX0 : ∀ m < 8, R[0 + m]? = some (KM.byteOf X0 m)) (hX1 : ∀ m < 8, R[8 + m]? = some (KM.byteOf X1 m))
    (hX2 : ∀ m < 8, R[16 + m]? = some (KM.byteOf X2 m)) (hX3 : ∀ m < 8, R[24 + m]? = some (KM.byteOf X3 m))
    (hV4 : ∀ m < 8, KM.byteOf V4 m = (if m = 0 then sb else 0) ^^^ (if m = 1 then rb else 0) ^^^ (if m = 2 then 0x1F else 0))
    (hC : ∀ m < 8, KM.byteOf C m = if m = 7 then 0x80 else 0) (k : Nat) (hk : k < 200) :
    KM.byteOf (if k / 8 = 20 then C else if k / 8 = 4 then V4 else if k / 8 = 3 then X3 else
        if k / 8 = 2 then X2 else if k / 8 = 1 then X1 else if k / 8 = 0 then X0 else 0) (k % 8) =
      (((R ++ [sb, rb]).getD k 0 ^^^ if k = 34 then 31 else 0) ^^^ if k = 167 then 128 else 0) := by
  have hm : k % 8 < 8 := Nat.mod_lt _ (by omega)
  have hRg : ∀ j X, (∀ m < 8, R[8 * j + m]? = some (KM.byteOf X m)) → k / 8 = j → R.getD k 0 = KM.byteOf X (k % 8) := by
    intro j X hX hj
    have e : 8 * j + k % 8 = k := by omega
    have := hX (k % 8) hm
    rw [e] at this
    rw [List.getD_eq_getElem?_getD, this]; rfl
  rw [getD_pad R hR sb rb k]
  by_cases h20 : k / 8 = 20
  · rw [if_pos h20, hC _ hm]
    have h1 : ¬ k < 32 := by omega
    have h2 : k ≠ 32 := by omega
    have h3 : k ≠ 33 := by omega
    have h4 : k ≠ 34 := by omega
    simp only [h1, h2, h3, h4, if_false]
    by_cases h7 : k % 8 = 7
    · have : k = 167 := by omega
      subst this; simp
    · have : k ≠ 167 := by omega
      simp [this, h7]
  rw [if_neg h20]
  by_cases h4 : k / 8 = 4
  · rw [if_pos h4, hV4 _ hm]
    have h1 : ¬ k < 32 := by omega
    have h167 : k ≠ 167 := by omega
    simp only [h1, h167, if_false, UInt8.xor_zero, if_neg]
    by_cases h0 : k % 8 = 0
    · have : k = 32 := by omega
      subst this; simp
    by_cases h1' : k % 8 = 1
    · have : k = 33 := by omega
      subst this; simp
    by_cases h2 : k % 8 = 2
    · have : k = 34 := by omega
      subst this; simp
    have : k ≠ 32 := by omega
    have : k ≠ 33 := by omega
    have : k ≠ 34 := by omega
    simp [*]
  rw [if_neg h4]
  by_cases hlt : k < 32
  · have hne1 : k ≠ 34 := by omega
    have hne2 : k ≠ 167 := by omega
    simp only [hlt, hne1, hne2, if_true, if_false, UInt8.xor_zero]
    by_cases h3 : k / 8 = 3
    · rw [if_pos h3]; exact (hRg 3 X3 hX3 h3).symm
    rw [if_neg h3]
    by_cases h2 : k / 8 = 2
    · rw [if_pos h2]; exact (hRg 2 X2 hX2 h2).symm
    rw [if_neg h2]
    by_cases h1 : k / 8 = 1
    · rw [if_pos h1]; exact (hRg 1 X1 hX1 h1).symm
    rw [if_neg h1]
    have h0 : k / 8 = 0 := by omega
    rw [if_pos h0]; exact (hRg 0 X0 hX0 h0).symm
  · have h3 : ¬ k / 8 = 3 := by omega
    have h2 : ¬ k / 8 = 2 := by omega
    have h1 : ¬ k / 8 = 1 := by omega
    have h0 : ¬ k / 8 = 0 := by omega
    have n32 : k ≠ 32 := by omega
    have n33 : k ≠ 33 := by omega
    have n34 : k ≠ 34 := by omega
    have n167 : k ≠ 167 := by omega
    simp only [h3, h2, h1, h0, hlt, n32, n33, n34, n167, if_false, byteOf_zero, UInt8.xor_zero]

theorem getE (a : Array U8 4#usize) (j : Nat) (hj : j < 4) (x : U8)
    (hx : x = a.val[j]'(by rw [a.property]; exact hj)) : a.val[j]! = x := by
  rw [getElem!_pos a.val j (by rw [a.property]; exact hj)]; exact hx.symm

@[step]
theorem init_state_x4_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) :
    sampling.init_state_x4 rho s r ⦃ st => ∀ i, i < 4 →
      pj st i = padSt (bytesA rho ++ [UInt8.ofNat (s.val[i]!).val, UInt8.ofNat (r.val[i]!).val]) ⦄ := by
  unfold sampling.init_state_x4
  step*
  rename_i i
  have hi : i < 4 := st_post2
  have key := fun q hq => ln_init_chain x0 x1 x2 x3 i6 i13 i20 i27 st1 st2 st3 st4 st5 st st1_post st2_post st3_post
    st4_post st5_post _ st_post1 q i hq hi
  apply KM.sb_ext
  intro k hk
  rw [sb_padSt _ k hk]
  unfold KM.sb
  rw [pj_getElem _ _ _ (by omega), key (k/8) (by omega)]
  have hb0 : ∀ m < 8, (bytesA rho)[0 + m]? = some (KM.byteOf (toU64 x0) m) := by
    have := x0_post; rw [s1_post, bytes_to_slice] at this; exact this
  have hb1 : ∀ m < 8, (bytesA rho)[8 + m]? = some (KM.byteOf (toU64 x1) m) := by
    have := x1_post; rw [s2_post, bytes_to_slice] at this; exact this
  have hb2 : ∀ m < 8, (bytesA rho)[16 + m]? = some (KM.byteOf (toU64 x2) m) := by
    have := x2_post; rw [s3_post, bytes_to_slice] at this; exact this
  have hb3 : ∀ m < 8, (bytesA rho)[24 + m]? = some (KM.byteOf (toU64 x3) m) := by
    have := x3_post; rw [s4_post, bytes_to_slice] at this; exact this
  have hR : (bytesA rho).length = 32 := by simp [bytesA]
  have hC : ∀ m < 8, KM.byteOf (toU64 9223372036854775808#u64) m = if m = 7 then 0x80 else 0 := by
    intro m hm
    interval_cases m <;> decide +kernel
  have hV4 : ∀ m < 8, KM.byteOf (if i = 0 then toU64 i6 else if i = 1 then toU64 i13 else if i = 2 then toU64 i20
        else toU64 i27) m =
      (if m = 0 then UInt8.ofNat (s.val[i]!).val else 0) ^^^ (if m = 1 then UInt8.ofNat (r.val[i]!).val else 0) ^^^
        (if m = 2 then 0x1F else 0) := by
    intro m hm
    interval_cases i
    · rw [if_pos rfl]
      rw [getE s 0 (by decide) _ i_post2, getE r 0 (by decide) _ i2_post2]
      exact lane4_byte _ _ i1 i3 i4 i5 i6 i1_post i3_post i4_post2 i5_post2 i6_post2 m hm
    · rw [if_neg (show (1:ℕ) ≠ 0 by omega), if_pos rfl]
      rw [getE s 1 (by decide) _ i7_post2, getE r 1 (by decide) _ i9_post2]
      exact lane4_byte _ _ i8 i10 i11 i12 i13 i8_post i10_post i11_post2 i12_post2 i13_post2 m hm
    · rw [if_neg (show (2:ℕ) ≠ 0 by omega), if_neg (show (2:ℕ) ≠ 1 by omega), if_pos rfl]
      rw [getE s 2 (by decide) _ i14_post2, getE r 2 (by decide) _ i16_post2]
      exact lane4_byte _ _ i15 i17 i18 i19 i20 i15_post i17_post i18_post2 i19_post2 i20_post2 m hm
    · rw [if_neg (show (3:ℕ) ≠ 0 by omega), if_neg (show (3:ℕ) ≠ 1 by omega), if_neg (show (3:ℕ) ≠ 2 by omega)]
      rw [getE s 3 (by decide) _ i21_post2, getE r 3 (by decide) _ i23_post2]
      exact lane4_byte _ _ i22 i24 i25 i26 i27 i22_post i24_post i25_post2 i26_post2 i27_post2 m hm
  exact init_byte_core (bytesA rho) hR _ _ _ _ _ _ _ _ hb0 hb1 hb2 hb3 hV4 hC k hk



/-! ## The four-lane sampler loop -/

/-- The 34-byte seed `ρ ‖ s[i] ‖ r[i]` of lane `i`. -/
def Mi (rho : Array U8 32#usize) (s r : Array U8 4#usize) (i : Nat) : List UInt8 :=
  bytesA rho ++ [UInt8.ofNat (s.val[i]!).val, UInt8.ofNat (r.val[i]!).val]

theorem Mi_length (rho : Array U8 32#usize) (s r : Array U8 4#usize) (i : Nat) : (Mi rho s r i).length = 34 := by
  simp [Mi, bytesA]

/-- Stream of lane `i`, long enough for `N` candidates. -/
def Tn (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N i : Nat) : List UInt8 :=
  SHAKE128 (Mi rho s r i) (3 * N)

theorem shake_stream (M : List UInt8) (hM : M.length = 34) (N b p : Nat) (hp : p < 168) (hb : 168 * b + p < 3 * N) :
    (SHAKE128 M (3 * N))[168 * b + p]? = some (KM.sb (Spec.KeccakF1600^[b + 1] (padSt M)) p) := by
  unfold SHAKE128 Spec.Keccak.sponge
  rw [absorb_pad34 M hM]
  have := KM.getElem?_squeeze 168 (by omega) b (Spec.KeccakF1600 (padSt M)) (3 * N) p hp (by omega)
  rw [Nat.mul_comm b 168] at this
  rw [this, Function.iterate_succ_apply]

/-- The part of the loop invariant after `b` permutations that does not mention `more`. -/
def GCore (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N b : Nat) (st : St4)
    (p0 p1 p2 p3 : Array U32 312#usize) (j0 j1 j2 j3 : Usize) : Prop :=
  (∀ i, i < 4 → pj st i = Spec.KeccakF1600^[b] (padSt (Mi rho s r i))) ∧
  LaneInv (Tn rho s r N 0) (56 * b) p0 j0 ∧ LaneInv (Tn rho s r N 1) (56 * b) p1 j1 ∧
  LaneInv (Tn rho s r N 2) (56 * b) p2 j2 ∧ LaneInv (Tn rho s r N 3) (56 * b) p3 j3

def MoreIff (j0 j1 j2 j3 : Usize) (more : Bool) : Prop :=
  more = true ↔ (j0.val < 256 ∨ j1.val < 256 ∨ j2.val < 256 ∨ j3.val < 256)

def GInv (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N b : Nat)
    (x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Usize × Usize ×
      Usize × Usize × Bool) : Prop :=
  GCore rho s r N b x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1
    x.2.2.2.2.2.2.2.2.1 ∧ MoreIff x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1
    x.2.2.2.2.2.2.2.2.2

theorem keccak_step_lanes (rho : Array U8 32#usize) (s r : Array U8 4#usize) (b : Nat) (st st1 : St4)
    (h : ∀ i, i < 4 → pj st i = Spec.KeccakF1600^[b] (padSt (Mi rho s r i)))
    (h1 : ∀ i, i < 4 → pj st1 i = Spec.KeccakF1600 (pj st i)) :
    ∀ i, i < 4 → pj st1 i = Spec.KeccakF1600^[b + 1] (padSt (Mi rho s r i)) := by
  intro i hi
  rw [h1 i hi, h i hi, Function.iterate_succ_apply']


theorem rej_x4_body_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N b : Nat)
    (st : St4) (p0 p1 p2 p3 : Array U32 312#usize) (j0 j1 j2 j3 : Usize) (more : Bool)
    (hb : more = true → 56 * (b + 1) ≤ N)
    (h : GInv rho s r N b (st, p0, p1, p2, p3, j0, j1, j2, j3, more)) :
    sampling.rej_ntt_poly_x4_loop.body Sh4 st p0 p1 p2 p3 j0 j1 j2 j3 more ⦃ c =>
      match c with
      | .done y => more = false ∧ y = (p0, p1, p2, p3)
      | .cont x' => more = true ∧ GInv rho s r N (b + 1) x' ⦄ := by
  obtain ⟨⟨hst, hl0, hl1, hl2, hl3⟩, hmore⟩ := h
  simp only [sampling.rej_ntt_poly_x4_loop.body]
  split
  · rename_i hm
    step with keccak_f1600_x4_shim_spec
    have hst1' := keccak_step_lanes rho s r b st st1 hst st1_post
    have hT : ∀ (i : Nat), i < 4 → ∀ p < 168, (Tn rho s r N i)[168 * b + p]? = some (KM.sb (pj st1 i) p) := by
      intro i hi p hp
      rw [hst1' i hi]
      have hb' := hb hm
      exact shake_stream _ (Mi_length rho s r i) N b p hp (by omega)
    have b0 := rej_ntt_lane_x4_spec (Tn rho s r N 0) st1 0#usize b (by simp) (hT 0 (by omega)) p0 j0 hl0
    have b1 := rej_ntt_lane_x4_spec (Tn rho s r N 1) st1 1#usize b (by simp) (hT 1 (by omega)) p1 j1 hl1
    have b2 := rej_ntt_lane_x4_spec (Tn rho s r N 2) st1 2#usize b (by simp) (hT 2 (by omega)) p2 j2 hl2
    have b3 := rej_ntt_lane_x4_spec (Tn rho s r N 3) st1 3#usize b (by simp) (hT 3 (by omega)) p3 j3 hl3
    step with b0
    step with b1
    step with b2
    step with b3
    have hcore : GCore rho s r N (b + 1) st1 p01 p11 p21 p31 j01 j11 j21 j31 :=
      ⟨hst1', j01_post, j11_post, j21_post, j31_post⟩
    split
    · rename_i hj
      simp only [WP.spec_ok]
      refine ⟨hm, hcore, fun _ => Or.inl (by scalar_tac), fun _ => rfl⟩
    split
    · rename_i hj0 hj
      simp only [WP.spec_ok]
      refine ⟨hm, hcore, fun _ => Or.inr (Or.inl (by scalar_tac)), fun _ => rfl⟩
    split
    · rename_i hj0 hj1 hj
      simp only [WP.spec_ok]
      refine ⟨hm, hcore, fun _ => Or.inr (Or.inr (Or.inl (by scalar_tac))), fun _ => rfl⟩
    · rename_i hj0 hj1 hj2
      simp only [WP.spec_ok]
      refine ⟨hm, hcore, ?_, ?_⟩
      · intro hh
        have h2 : j31 < 256#usize := of_decide_eq_true hh
        right; right; right; scalar_tac
      · intro hh
        rcases hh with hh | hh | hh | hh
        · exfalso; scalar_tac
        · exfalso; scalar_tac
        · exfalso; scalar_tac
        · have h2 : j31.val < 256 := hh
          show decide (j31 < 256#usize) = true
          exact decide_eq_true (by scalar_tac)
  · rename_i hm
    have hmf : more = false := by simpa using hm
    simp only [WP.spec_ok]
    exact ⟨hmf, trivial⟩


def runLoop (x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
    Usize × Usize × Usize × Usize × Bool) :
    RustM (Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize) :=
  sampling.rej_ntt_poly_x4_loop Sh4 x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1
    x.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2.2.2

def FinAll (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N : Nat)
    (q : Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize) : Prop :=
  FinL (Tn rho s r N 0) N q.1 ∧ FinL (Tn rho s r N 1) N q.2.1 ∧ FinL (Tn rho s r N 2) N q.2.2.1 ∧
    FinL (Tn rho s r N 3) N q.2.2.2

theorem more_lt (rho : Array U8 32#usize) (s r : Array U8 4#usize) (G b : Nat)
    (hfin : ∀ i, i < 4 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2) (hbG : b ≤ G)
    (st : St4) (p0 p1 p2 p3 : Array U32 312#usize) (j0 j1 j2 j3 : Usize) (more : Bool)
    (h : GInv rho s r (56 * G) b (st, p0, p1, p2, p3, j0, j1, j2, j3, more)) (hm : more = true) : b < G := by
  by_contra hcon
  have hbe : b = G := by omega
  subst hbe
  obtain ⟨⟨_, hl0, hl1, hl2, hl3⟩, hmore⟩ := h
  have hany := hmore.mp hm
  dsimp only at hany hl0 hl1 hl2 hl3
  have f0 := hfin 0 (by omega)
  have f1 := hfin 1 (by omega)
  have f2 := hfin 2 (by omega)
  have f3 := hfin 3 (by omega)
  have e0 : min 256 j0.val = (stA (Tn rho s r (56 * b) 0) (56 * b)).2 := hl0.2.1
  have e1 : min 256 j1.val = (stA (Tn rho s r (56 * b) 1) (56 * b)).2 := hl1.2.1
  have e2 : min 256 j2.val = (stA (Tn rho s r (56 * b) 2) (56 * b)).2 := hl2.2.1
  have e3 : min 256 j3.val = (stA (Tn rho s r (56 * b) 3) (56 * b)).2 := hl3.2.1
  rcases hany with h0 | h0 | h0 | h0 <;> omega

theorem rej_x4_loop_step (rho : Array U8 32#usize) (s r : Array U8 4#usize) (G b : Nat)
    (hfin : ∀ i, i < 4 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2) (hbG : b ≤ G)
    (x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
      Usize × Usize × Usize × Usize × Bool)
    (h : GInv rho s r (56 * G) b x)
    (IH : ∀ x', b + 1 ≤ G → GInv rho s r (56 * G) (b + 1) x' → runLoop x' ⦃ q => FinAll rho s r (56 * G) q ⦄) :
    runLoop x ⦃ q => FinAll rho s r (56 * G) q ⦄ := by
  obtain ⟨st, p0, p1, p2, p3, j0, j1, j2, j3, more⟩ := x
  have hbody := rej_x4_body_spec rho s r (56 * G) b st p0 p1 p2 p3 j0 j1 j2 j3 more
    (fun hm => by have := more_lt rho s r G b hfin hbG st p0 p1 p2 p3 j0 j1 j2 j3 more h hm; omega) h
  obtain ⟨res, hr, hp⟩ := WP.spec_imp_exists hbody
  unfold runLoop sampling.rej_ntt_poly_x4_loop
  dsimp only
  rw [loop]
  dsimp only
  rw [hr]
  cases res with
  | cont x' =>
    obtain ⟨hm, hx'⟩ := hp
    have := more_lt rho s r G b hfin hbG st p0 p1 p2 p3 j0 j1 j2 j3 more h hm
    exact IH x' (by omega) hx'
  | done y =>
    obtain ⟨hmf, rfl⟩ := hp
    obtain ⟨⟨_, hl0, hl1, hl2, hl3⟩, hmore⟩ := h
    have hn : ¬ (j0.val < 256 ∨ j1.val < 256 ∨ j2.val < 256 ∨ j3.val < 256) := fun hh => by
      have := hmore.mpr hh; simp [hmf] at this
    simp only [not_or, not_lt] at hn
    simp only [WP.spec_ok]
    refine ⟨lane_fin _ _ _ (by omega) _ _ hl0 hn.1, lane_fin _ _ _ (by omega) _ _ hl1 hn.2.1,
      lane_fin _ _ _ (by omega) _ _ hl2 hn.2.2.1, lane_fin _ _ _ (by omega) _ _ hl3 hn.2.2.2⟩

theorem rej_x4_loop_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (G : Nat)
    (hfin : ∀ i, i < 4 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2) :
    ∀ k b, G - b = k → b ≤ G → ∀ x, GInv rho s r (56 * G) b x →
      runLoop x ⦃ q => FinAll rho s r (56 * G) q ⦄ := by
  intro k
  induction k with
  | zero =>
    intro b hk hbG x h
    exact rej_x4_loop_step rho s r G b hfin hbG x h (fun x' hb _ => by omega)
  | succ k ih =>
    intro b hk hbG x h
    exact rej_x4_loop_step rho s r G b hfin hbG x h (fun x' hb hx' => ih (b + 1) (by omega) hb x' hx')


theorem init_GInv (rho : Array U8 32#usize) (s r : Array U8 4#usize) (N : Nat) (st : St4)
    (hst : ∀ i, i < 4 → pj st i = padSt (bytesA rho ++ [UInt8.ofNat (s.val[i]!).val, UInt8.ofNat (r.val[i]!).val])) :
    GInv rho s r N 0 (st, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32,
      Array.repeat 312#usize 0#u32, 0#usize, 0#usize, 0#usize, 0#usize, true) := by
  have hl : ∀ T : List UInt8, LaneInv T (56 * 0) (Array.repeat 312#usize 0#u32) 0#usize := by
    intro T
    have hj0 : (0#usize).val = 0 := rfl
    have h0 : stA T (56 * 0) = (Poly.zero, 0) := by simp [stA]
    refine ⟨by rw [hj0]; omega, ?_, ?_⟩
    · rw [hj0, h0]; rfl
    · rw [h0]; intro k hk; exact absurd hk (by simp)
  refine ⟨⟨fun i hi => ?_, hl _, hl _, hl _, hl _⟩, ?_⟩
  · rw [hst i hi]; rfl
  · show true = true ↔ _
    exact ⟨fun _ => Or.inl (show (0#usize).val < 256 by simp), fun _ => rfl⟩

theorem rej_ntt_poly_x4_spec (rho : Array U8 32#usize) (s r : Array U8 4#usize) (F : Nat) (P : Nat → Poly)
    (hP : ∀ i, i < 4 → Spec.RejNTTPoly F (Mi rho s r i) = some (P i)) :
    sampling.rej_ntt_poly_x4 Sh4 rho s r ⦃ q =>
      ∀ (i : Nat) (hi : i < q.val.length), i < 4 → Repr (q.val[i]) (P i) ⦄ := by
  have hG : F ≤ 56 * ((F + 55) / 56) := by omega
  set G := (F + 55) / 56 with hGdef
  have hP' : ∀ i, i < 4 → Spec.RejNTTPoly (56 * G) (Mi rho s r i) = some (P i) :=
    fun i hi => RejNTTPoly_mono _ _ _ _ (hP i hi) hG
  have hfinP : ∀ i, i < 4 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2 ∧
      (stA (Tn rho s r (56 * G) i) (56 * G)).1 = P i := fun i hi => rej_eq_some _ _ _ (hP' i hi)
  have hfin : ∀ i, i < 4 → 256 ≤ (stA (Tn rho s r (56 * G) i) (56 * G)).2 := fun i hi => (hfinP i hi).1
  unfold sampling.rej_ntt_poly_x4
  step*
  have hinit := init_GInv rho s r (56 * G) st st_post
  have hloop := rej_x4_loop_spec rho s r G hfin G 0 (by omega) (by omega) _ hinit
  unfold runLoop at hloop
  dsimp only at hloop
  step with hloop
  step*
  intro i hi hi4
  interval_cases i
  · exact repr_of_first_256 _ _ _ a_post (finP_of _ _ _ _ p01_post.1 (hfinP 0 (by omega)).2)
  · exact repr_of_first_256 _ _ _ a1_post (finP_of _ _ _ _ p01_post.2.1 (hfinP 1 (by omega)).2)
  · exact repr_of_first_256 _ _ _ a2_post (finP_of _ _ _ _ p01_post.2.2.1 (hfinP 2 (by omega)).2)
  · exact repr_of_first_256 _ _ _ a3_post (finP_of _ _ _ _ p01_post.2.2.2 (hfinP 3 (by omega)).2)


/-! ## Partial correctness of the 4-lane sampler -/

theorem LaneInv_fuel (rho : Array U8 32#usize) (s r : Array U8 4#usize) (i b N N' : Nat) (hb : 56 * b ≤ N)
    (hN : N ≤ N') (a : Array U32 312#usize) (j : Usize) (h : LaneInv (Tn rho s r N i) (56 * b) a j) :
    LaneInv (Tn rho s r N' i) (56 * b) a j := by
  obtain ⟨hc, ha, hj⟩ := h
  have := stA_shake_mono (Mi rho s r i) (56 * b) N N' hb hN
  refine ⟨hc, ?_, ?_⟩
  · unfold Tn; rw [this]; exact ha
  · unfold Tn; rw [this]; exact hj

theorem GInv_fuel (rho : Array U8 32#usize) (s r : Array U8 4#usize) (b N N' : Nat) (hb : 56 * b ≤ N)
    (hN : N ≤ N') (x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
      Usize × Usize × Usize × Usize × Bool) (h : GInv rho s r N b x) : GInv rho s r N' b x := by
  obtain ⟨⟨hst, hl0, hl1, hl2, hl3⟩, hm⟩ := h
  exact ⟨⟨hst, LaneInv_fuel rho s r 0 b N N' hb hN _ _ hl0, LaneInv_fuel rho s r 1 b N N' hb hN _ _ hl1,
    LaneInv_fuel rho s r 2 b N N' hb hN _ _ hl2, LaneInv_fuel rho s r 3 b N N' hb hN _ _ hl3⟩, hm⟩

theorem GInv_fuel' (rho : Array U8 32#usize) (s r : Array U8 4#usize) (b N N' : Nat) (hb : 56 * b ≤ N)
    (hN : N ≤ N')
    (x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
      Usize × Usize × Usize × Usize × Bool) (h : GInv rho s r N' b x) : GInv rho s r N b x := by
  obtain ⟨⟨hst, hl0, hl1, hl2, hl3⟩, hm⟩ := h
  have back : ∀ i a j, LaneInv (Tn rho s r N' i) (56 * b) a j → LaneInv (Tn rho s r N i) (56 * b) a j := by
    intro i a j hh
    obtain ⟨hc, ha, hj⟩ := hh
    have := stA_shake_mono (Mi rho s r i) (56 * b) N N' hb hN
    refine ⟨hc, ?_, ?_⟩
    · unfold Tn at ha; rw [this] at ha; exact ha
    · unfold Tn at hj; rw [this] at hj; exact hj
  exact ⟨⟨hst, back 0 _ _ hl0, back 1 _ _ hl1, back 2 _ _ hl2, back 3 _ _ hl3⟩, hm⟩

theorem rej_x4_loop_partial (rho : Array U8 32#usize) (s r : Array U8 4#usize)
    (x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
      Usize × Usize × Usize × Usize × Bool) (hx : ∃ b, GInv rho s r (56 * b) b x) :
    runLoop x ⦃ q => ∃ (F : Nat) (P : Nat → Poly),
      (∀ i, i < 4 → Spec.RejNTTPoly F (Mi rho s r i) = some (P i)) ∧
      FinP (P 0) q.1 ∧ FinP (P 1) q.2.1 ∧ FinP (P 2) q.2.2.1 ∧ FinP (P 3) q.2.2.2 ⦄div := by
  unfold runLoop sampling.rej_ntt_poly_x4_loop
  refine loop.dspec_inv _ (fun x : St4 × Array U32 312#usize × Array U32 312#usize × Array U32 312#usize ×
      Array U32 312#usize × Usize × Usize × Usize × Usize × Bool => ∃ b, GInv rho s r (56 * b) b x) ?_ ?_ x hx
  · rintro ⟨st, p0, p1, p2, p3, j0, j1, j2, j3, more⟩ ⟨b, hI⟩
    have hI' := GInv_fuel rho s r b (56 * b) (56 * (b + 1)) le_rfl (by omega) _ hI
    have hbody := rej_x4_body_spec rho s r (56 * (b + 1)) b st p0 p1 p2 p3 j0 j1 j2 j3 more (fun _ => le_rfl) hI'
    refine WP.dspec_mono' (WP.spec_dspec _ _ _ hbody) ?_
    rintro (x' | y) h
    · exact ⟨b + 1, h.2⟩
    · obtain ⟨hmf, rfl⟩ := h
      obtain ⟨⟨_, hl0, hl1, hl2, hl3⟩, hmore⟩ := hI
      have hn : ¬ (j0.val < 256 ∨ j1.val < 256 ∨ j2.val < 256 ∨ j3.val < 256) := fun hh => by
        have := hmore.mpr hh; simp [hmf] at this
      simp only [not_or, not_lt] at hn
      have e0 : min 256 j0.val = (stA (Tn rho s r (56 * b) 0) (56 * b)).2 := hl0.2.1
      have e1 : min 256 j1.val = (stA (Tn rho s r (56 * b) 1) (56 * b)).2 := hl1.2.1
      have e2 : min 256 j2.val = (stA (Tn rho s r (56 * b) 2) (56 * b)).2 := hl2.2.1
      have e3 : min 256 j3.val = (stA (Tn rho s r (56 * b) 3) (56 * b)).2 := hl3.2.1
      have hfin : ∀ i, i < 4 → Spec.RejNTTPoly (56 * b) (Mi rho s r i) =
          some (stA (Tn rho s r (56 * b) i) (56 * b)).1 := by
        intro i hi
        apply rej_some_of_fin
        show 256 ≤ (stA (Tn rho s r (56 * b) i) (56 * b)).2
        interval_cases i <;> omega
      refine ⟨56 * b, fun i => (stA (Tn rho s r (56 * b) i) (56 * b)).1, hfin, ?_, ?_, ?_, ?_⟩
      · exact lane_fin _ _ _ le_rfl _ _ hl0 hn.1
      · exact lane_fin _ _ _ le_rfl _ _ hl1 hn.2.1
      · exact lane_fin _ _ _ le_rfl _ _ hl2 hn.2.2.1
      · exact lane_fin _ _ _ le_rfl _ _ hl3 hn.2.2.2

theorem rej_ntt_poly_x4_partial (rho : Array U8 32#usize) (s r : Array U8 4#usize) :
    sampling.rej_ntt_poly_x4 Sh4 rho s r ⦃ q => ∃ (F : Nat) (P : Nat → Poly),
      (∀ i, i < 4 → Spec.RejNTTPoly F (Mi rho s r i) = some (P i)) ∧
      ∀ (i : Nat) (hi : i < q.val.length), i < 4 → Repr (q.val[i]) (P i) ⦄div := by
  unfold sampling.rej_ntt_poly_x4
  step*
  have hloop := rej_x4_loop_partial rho s r
    (st, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32, Array.repeat 312#usize 0#u32,
      Array.repeat 312#usize 0#u32, 0#usize, 0#usize, 0#usize, 0#usize, true)
    ⟨0, init_GInv rho s r (56 * 0) st st_post⟩
  unfold runLoop at hloop
  dsimp only at hloop
  step with hloop
  obtain ⟨a0, a1, a2, a3⟩ := p21
  step*
  refine ⟨p01, p11, p31, ?_⟩
  intro i hi hi4
  interval_cases i
  · exact repr_of_first_256 _ _ _ a_post p01_post2
  · exact repr_of_first_256 _ _ _ a1_post p01_post3
  · exact repr_of_first_256 _ _ _ a2_post p01_post4
  · exact repr_of_first_256 _ _ _ a3_post p01_post5

end Proofs
