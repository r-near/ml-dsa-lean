import Proofs.Keccak4
import Proofs.PartialSample

/-!
# The branchless block parse of the 4-way sampler

`sampling.push_candidate`, `sampling.rej_ntt_cands8`, `sampling.rej_ntt_block_x4`, `sampling.rej_ntt_lane_x4` and
`sampling.first_256` against the byte-wise sampler's pure fold `SampleA.stA`.

The lane's coefficients live in a 312-word scratch array `a` with fill count `j`. The block parse writes every
candidate to `a[j]` and advances `j` only when the candidate is `< q`, so words from index `min j 256` on are
unspecified (rejected candidates, and the 56 words of slack past 256). `LaneInv T n a j` says that after the first `n`
candidates of the stream `T` the first `(stA T n).2` words of `a` are the pure fold's coefficients and that
`min 256 j` is that count.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open SampleA

/-! ## Candidate values -/

/-- The pure candidate of the stream triple at `n`, from the three bytes (as numbers `< 256`). -/
theorem triAt_of_nat (T : List UInt8) (n : Nat) (x0 x1 x2 z : Nat)
    (h0 : (tripleAt T n)[0]! = UInt8.ofNat x0) (h1 : (tripleAt T n)[1]! = UInt8.ofNat x1)
    (h2 : (tripleAt T n)[2]! = UInt8.ofNat x2) (hx0 : x0 < 256) (hx1 : x1 < 256) (hx2 : x2 < 256)
    (hz : z = 2 ^ 16 * (x2 % 128) + 2 ^ 8 * x1 + x0) :
    triAt T n = if z < Spec.q then some ((z : Nat) : Zq) else none := by
  have t0' : ∀ x : Nat, x < 256 → (UInt8.ofNat x).toNat = x := fun x hx => by simp [Nat.mod_eq_of_lt hx]
  unfold triAt
  rw [h0, h1, h2, CoeffFromThreeBytes_eq, t0' x0 hx0, t0' x1 hx1, t0' x2 hx2, ← hz]

/-! ## The lane invariant -/

/-- After the first `n` candidates of the stream `T`: the fill count `j` of the scratch `a` is the pure fold's count
(saturating at 256: `j` may run on past 256 inside a block) and the first `(stA T n).2` words are its coefficients. -/
def LaneInv (T : List UInt8) (n : Nat) (a : Array U32 312#usize) (j : Usize) : Prop :=
  j.val ≤ 311 ∧ min 256 j.val = (stA T n).2 ∧
    ∀ k, k < (stA T n).2 → (a.val[k]!).val < Spec.q ∧ (((a.val[k]!).val : Nat) : Zq) = (stA T n).1[k]!

theorem arr_get_set (a : Array U32 312#usize) (j : Usize) (z : U32) (hj : j.val < 312) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k then z else a.val[k]! := by
  have hl : a.val.length = 312 := a.property
  by_cases hk : k < 312
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ j.val = k := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

theorem vec_getElem!_set! (xs : Vector Zq 256) (i j : Nat) (x : Zq) (hj : j < 256) :
    (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  rw [set!_eq, getElem!_pos _ _ (by simpa using hj), Vector.getElem_setIfInBounds hj]
  by_cases h : i = j
  · simp [h]
  · simp only [h, if_false]
    rw [getElem!_pos _ _ (by simpa using hj)]

/-- One candidate: write `z` at `a[j]` and advance `j` when `z < q`. -/
theorem laneInv_step (T : List UInt8) (n : Nat) (a a' : Array U32 312#usize) (j j' : Usize) (z : U32)
    (h : LaneInv T n a j) (hj : j.val ≤ 310)
    (htri : triAt T n = if z.val < Spec.q then some ((z.val : Nat) : Zq) else none)
    (ha' : a' = a.set j z) (hj' : j'.val = j.val + (if z.val < Spec.q then 1 else 0)) :
    LaneInv T (n + 1) a' j' := by
  obtain ⟨hj311, hmin, hk⟩ := h
  have hjl : j.val < 312 := by omega
  by_cases hq : z.val < Spec.q
  · rw [if_pos hq] at htri hj'
    by_cases hj256 : j.val < 256
    · have hs2 : (stA T n).2 = j.val := by omega
      have hst := stA_succ_some T n _ htri (by omega)
      have e1 : (stA T (n + 1)).2 = (stA T n).2 + 1 := by rw [hst]
      have e2 : ∀ k, k < 256 → (stA T (n + 1)).1[k]! = if (stA T n).2 = k then ((z.val : Nat) : Zq) else (stA T n).1[k]! := by
        intro k hk256
        rw [hst]
        exact vec_getElem!_set! _ _ _ _ hk256
      refine ⟨by omega, by omega, ?_⟩
      intro k hk'
      rw [e1] at hk'
      rw [e2 k (by omega), ha', arr_get_set a j z hjl k]
      by_cases hkj : k = j.val
      · subst hkj
        rw [if_pos rfl, if_pos hs2]
        exact ⟨hq, rfl⟩
      · have hne : ¬ j.val = k := fun h => hkj h.symm
        have hne2 : ¬ (stA T n).2 = k := by omega
        rw [if_neg hne, if_neg hne2]
        exact hk k (by omega)
    · have hs2 : (stA T n).2 = 256 := by omega
      have hst := stA_stable T n (n + 1) (by omega) (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · rw [hst]; omega
      · intro k hk'
        rw [hst] at hk' ⊢
        rw [ha', arr_get_set a j z hjl k]
        have hne : ¬ j.val = k := by omega
        rw [if_neg hne]
        exact hk k hk'
  · rw [if_neg hq] at htri hj'
    by_cases hj256 : j.val < 256
    · have hs2 : (stA T n).2 = j.val := by omega
      have hst := stA_succ_none T n htri (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · rw [hst]; omega
      · intro k hk'
        rw [hst] at hk' ⊢
        rw [ha', arr_get_set a j z hjl k]
        have hne : ¬ j.val = k := by omega
        rw [if_neg hne]
        exact hk k hk'
    · have hs2 : (stA T n).2 = 256 := by omega
      have hst := stA_stable T n (n + 1) (by omega) (by omega)
      refine ⟨by omega, ?_, ?_⟩
      · rw [hst]; omega
      · intro k hk'
        rw [hst] at hk' ⊢
        rw [ha', arr_get_set a j z hjl k]
        have hne : ¬ j.val = k := by omega
        rw [if_neg hne]
        exact hk k hk'

/-! ## Candidates from the lane words -/

/-- Byte `m` of the 64-bit word `w`, as a number. -/
def lw (w : U64) (m : Nat) : Nat := w.val / 2 ^ (8 * m) % 256

theorem lw_lt (w : U64) (m : Nat) : lw w m < 256 := Nat.mod_lt _ (by norm_num)

/-- The byte of the state that `KM.sb` reads is the byte of the lane word. -/
theorem byteOf_lw (w : U64) (m : Nat) (hm : m < 8) : KM.byteOf (toU64 w) m = UInt8.ofNat (lw w m) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  have ht : (8 * m).toUInt64.toNat = 8 * m := by
    show (UInt64.ofNat (8 * m)).toNat = _
    rw [UInt64.toNat_ofNat']
    omega
  have : (toU64 w).toNat = w.val := by simp [toU64, UInt64.toNat]
  show (KM.byteOf (toU64 w) m).toNat = (UInt8.ofNat (lw w m)).toNat
  simp only [KM.byteOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, ht, Nat.mod_eq_of_lt (show 8 * m < 64 by omega),
    UInt8.toNat_ofNat', lw, this, Nat.shiftRight_eq_div_pow]
  omega

/-- Three consecutive lane words, indexed by `0, 1, 2`. -/
def Wd (w0 w1 w2 : U64) (k : Nat) : U64 := if k = 0 then w0 else if k = 1 then w1 else w2

/-- `push_candidate` is one step of the lane invariant. -/
theorem push_candidate_spec (T : List UInt8) (n : Nat) (a : Array U32 312#usize) (j : Usize) (z : U32)
    (h : LaneInv T n a j) (hj : j.val ≤ 310)
    (htri : triAt T n = if z.val < Spec.q then some ((z.val : Nat) : Zq) else none) :
    sampling.push_candidate a j z ⦃ r => LaneInv T (n + 1) r.2 r.1 ∧ r.1.val ≤ j.val + 1 ⦄ := by
  unfold sampling.push_candidate
  have hQ : (field.Q).val = 8380417 := by first | rfl | decide | simp [field.Q]
  have hzq : z < field.Q ↔ z.val < Spec.q := by
    rw [UScalar.lt_equiv, hQ]
  step*
  have hj6 : i.val = if z.val < Spec.q then 1 else 0 := by
    rw [i_post]
    by_cases hh : z.val < Spec.q
    · rw [if_pos hh, decide_eq_true (hzq.mpr hh)]; rfl
    · rw [if_neg hh, decide_eq_false (fun h => hh (hzq.mp h))]; rfl
  refine ⟨laneInv_step T n a a1 j i1 z h (by omega) htri a1_post (by rw [i1_post, hj6]), ?_⟩
  rw [i1_post, hj6]
  split <;> omega

/-! ## One block of one lane -/

theorem getE_of_opt (T : List UInt8) (k : Nat) (v : UInt8) (h : T[k]? = some v) : T[k]! = v := by
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [getElem!_pos T k hk]

theorem tripleAt_get (T : List UInt8) (n c : Nat) (hc : c < 3) (h : 3 * n + c < T.length) :
    (tripleAt T n)[c]! = T[3 * n + c]! := by
  have h1 : c < (tripleAt T n).length := by
    simp only [tripleAt, List.length_take, List.length_drop]; omega
  rw [getElem!_pos (tripleAt T n) c h1, getElem!_pos T (3 * n + c) h]
  simp [tripleAt, List.getElem_take, List.getElem_drop]

/-- The three bytes of candidate `t` of the group, as lane bytes. -/
theorem group_bytes (T : List UInt8) (n : Nat) (w0 w1 w2 : U64)
    (hw : ∀ p, p < 24 → T[3 * n + p]? = some (UInt8.ofNat (lw (Wd w0 w1 w2 (p / 8)) (p % 8))))
    (t : Nat) (ht : t < 8) (c : Nat) (hc : c < 3) :
    (tripleAt T (n + t))[c]! = UInt8.ofNat (lw (Wd w0 w1 w2 ((3 * t + c) / 8)) ((3 * t + c) % 8)) := by
  have h := hw (3 * t + c) (by omega)
  have hlen := (List.getElem?_eq_some_iff.mp h).1
  rw [tripleAt_get T (n + t) c hc (by omega), show 3 * (n + t) + c = 3 * n + (3 * t + c) by ring]
  exact getE_of_opt T _ _ h

/-- One push with the candidate's three bytes given as numbers. -/
theorem push_cand_at (T : List UInt8) (n : Nat) (a : Array U32 312#usize) (j : Usize) (z : U32)
    (h : LaneInv T n a j) (hj : j.val ≤ 310) (x0 x1 x2 : Nat)
    (b0 : (tripleAt T n)[0]! = UInt8.ofNat x0) (b1 : (tripleAt T n)[1]! = UInt8.ofNat x1)
    (b2 : (tripleAt T n)[2]! = UInt8.ofNat x2) (hx0 : x0 < 256) (hx1 : x1 < 256) (hx2 : x2 < 256)
    (hz : z.val = 2 ^ 16 * (x2 % 128) + 2 ^ 8 * x1 + x0) :
    sampling.push_candidate a j z ⦃ r => LaneInv T (n + 1) r.2 r.1 ∧ r.1.val ≤ j.val + 1 ⦄ :=
  push_candidate_spec T n a j z h hj (triAt_of_nat T n x0 x1 x2 z.val b0 b1 b2 hx0 hx1 hx2 hz)

theorem lw_def (w : U64) (m : Nat) : lw w m = w.val / 2 ^ (8 * m) % 256 := rfl

/-- A candidate at a byte offset inside one lane word: `(w >>> 8m) & (2^23 - 1)`. -/
theorem al_val (w : U64) (m : Nat) (_hm : m ≤ 5) (i2 i3 : U64) (i4 : U32)
    (h2 : i2.val = w.val / 2 ^ (8 * m)) (h3 : i3.val = (i2 &&& sampling.M23).val)
    (h4 : i4 = UScalar.cast UScalarTy.U32 i3) :
    i4.val = 2 ^ 16 * (lw w (m + 2) % 128) + 2 ^ 8 * lw w (m + 1) + lw w m := by
  have hM : sampling.M23.val = 8388607 := by simp [sampling.M23]
  rw [h4, UScalar.cast_val_eq, h3, UScalar.val_and, hM, h2]
  have e : (8388607 : Nat) = 2 ^ 23 - 1 := by norm_num
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  have h32 : (2 : Nat) ^ UScalarTy.U32.numBits = 4294967296 := by decide
  simp only [lw_def, h32]
  have e1 : 2 ^ (8 * (m + 2)) = 2 ^ (8 * m) * 2 ^ 16 := by rw [← pow_add]; ring_nf
  have e2 : 2 ^ (8 * (m + 1)) = 2 ^ (8 * m) * 2 ^ 8 := by rw [← pow_add]; ring_nf
  rw [e1, e2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  generalize w.val / 2 ^ (8 * m) = q
  omega

theorem U64_size_eq : U64.size = 2 ^ 64 := by
  scalar_tac

/-- A candidate that straddles two lane words, `k = 6`: bytes 6 and 7 of `wa` and byte 0 of `wb`. -/
theorem st6_val (wa wb : U64) (i5 i6 i7 i8 : U64) (i9 : U32)
    (h5 : i5.val = wa.val / 2 ^ 48) (h6 : i6.val = wb.val * 2 ^ 16 % 2 ^ 64)
    (h7 : i7.val = (i5.val + i6.val) % 2 ^ 64) (h8 : i8.val = (i7 &&& sampling.M23).val)
    (h9 : i9 = UScalar.cast UScalarTy.U32 i8) :
    i9.val = 2 ^ 16 * (lw wb 0 % 128) + 2 ^ 8 * lw wa 7 + lw wa 6 := by
  have hM : sampling.M23.val = 8388607 := by simp [sampling.M23]
  have h64 : (2 : Nat) ^ UScalarTy.U64.numBits = 18446744073709551616 := by decide
  have hwa := wa.hBounds
  have hwb := wb.hBounds
  rw [h64] at hwa hwb
  rw [h9, UScalar.cast_val_eq, h8, UScalar.val_and, hM]
  have e : (8388607 : Nat) = 2 ^ 23 - 1 := by norm_num
  rw [e, Nat.and_two_pow_sub_one_eq_mod, h7, h5, h6]
  have h32 : (2 : Nat) ^ UScalarTy.U32.numBits = 4294967296 := by decide
  simp only [lw_def, h32, Nat.reduceMul, Nat.reducePow, pow_zero, Nat.div_one]
  omega

/-- The same for `k = 7`: byte 7 of `wa` and bytes 0 and 1 of `wb`. -/
theorem st7_val (wa wb : U64) (i5 i6 i7 i8 : U64) (i9 : U32)
    (h5 : i5.val = wa.val / 2 ^ 56) (h6 : i6.val = wb.val * 2 ^ 8 % 2 ^ 64)
    (h7 : i7.val = (i5.val + i6.val) % 2 ^ 64) (h8 : i8.val = (i7 &&& sampling.M23).val)
    (h9 : i9 = UScalar.cast UScalarTy.U32 i8) :
    i9.val = 2 ^ 16 * (lw wb 1 % 128) + 2 ^ 8 * lw wb 0 + lw wa 7 := by
  have hM : sampling.M23.val = 8388607 := by simp [sampling.M23]
  have h64 : (2 : Nat) ^ UScalarTy.U64.numBits = 18446744073709551616 := by decide
  have hwa := wa.hBounds
  have hwb := wb.hBounds
  rw [h64] at hwa hwb
  rw [h9, UScalar.cast_val_eq, h8, UScalar.val_and, hM]
  have e : (8388607 : Nat) = 2 ^ 23 - 1 := by norm_num
  rw [e, Nat.and_two_pow_sub_one_eq_mod, h7, h5, h6]
  have h32 : (2 : Nat) ^ UScalarTy.U32.numBits = 4294967296 := by decide
  simp only [lw_def, h32, Nat.reduceMul, Nat.reducePow, pow_zero, Nat.div_one]
  omega

/-- The eight candidates of three lane words. -/
theorem rej_ntt_cands8_spec (T : List UInt8) (n : Nat) (w0 w1 w2 : U64)
    (hw : ∀ p, p < 24 → T[3 * n + p]? = some (UInt8.ofNat (lw (Wd w0 w1 w2 (p / 8)) (p % 8))))
    (a : Array U32 312#usize) (j : Usize) (hj : j.val ≤ 303) (h : LaneInv T n a j) :
    sampling.rej_ntt_cands8 w0 w1 w2 a j ⦃ r => LaneInv T (n + 8) r.2 r.1 ∧ r.1.val ≤ j.val + 8 ⦄ := by
  have gb := group_bytes T n w0 w1 w2 hw
  have sh : ∀ (w i : U64) (s : Nat), i.val = w.val >>> s → i.val = w.val / 2 ^ s := by
    intro w i s h; rw [h, Nat.shiftRight_eq_div_pow]
  unfold sampling.rej_ntt_cands8
  step*
  have z0 := al_val w0 0 (by omega) w0 i i1 (by simp) i_post1 i1_post
  step with push_cand_at T (n + 0) a j i1 h (by omega) _ _ _ (gb 0 (by omega) 0 (by omega))
    (gb 0 (by omega) 1 (by omega)) (gb 0 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z0
  step*
  have z1 := al_val w0 3 (by omega) i2 i3 i4 (by simpa using sh w0 i2 24 i2_post1) i3_post1 i4_post
  step with push_cand_at T (n + 1) a1 j1 i4 j1_post1 (by omega) _ _ _ (gb 1 (by omega) 0 (by omega))
    (gb 1 (by omega) 1 (by omega)) (gb 1 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z1
  step*
  have z2 := st6_val w0 w1 i5 i6 i7 i8 i9 (by simpa using sh w0 i5 48 i5_post1) (by rw [i6_post1, Nat.shiftLeft_eq]; rw [U64_size_eq]) (by rw [i7_post]; exact wrapping_add_val_u64 _ _) i8_post1 i9_post
  step with push_cand_at T (n + 2) a2 j2 i9 j2_post1 (by omega) _ _ _ (gb 2 (by omega) 0 (by omega))
    (gb 2 (by omega) 1 (by omega)) (gb 2 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z2
  step*
  have z3 := al_val w1 1 (by omega) i10 i11 i12 (by simpa using sh w1 i10 8 i10_post1) i11_post1 i12_post
  step with push_cand_at T (n + 3) a3 j3 i12 j3_post1 (by omega) _ _ _ (gb 3 (by omega) 0 (by omega))
    (gb 3 (by omega) 1 (by omega)) (gb 3 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z3
  step*
  have z4 := al_val w1 4 (by omega) i13 i14 i15 (by simpa using sh w1 i13 32 i13_post1) i14_post1 i15_post
  step with push_cand_at T (n + 4) a4 j4 i15 j4_post1 (by omega) _ _ _ (gb 4 (by omega) 0 (by omega))
    (gb 4 (by omega) 1 (by omega)) (gb 4 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z4
  step*
  have z5 := st7_val w1 w2 i16 i17 i18 i19 i20 (by simpa using sh w1 i16 56 i16_post1) (by rw [i17_post1, Nat.shiftLeft_eq]; rw [U64_size_eq]) (by rw [i18_post]; exact wrapping_add_val_u64 _ _) i19_post1 i20_post
  step with push_cand_at T (n + 5) a5 j5 i20 j5_post1 (by omega) _ _ _ (gb 5 (by omega) 0 (by omega))
    (gb 5 (by omega) 1 (by omega)) (gb 5 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z5
  step*
  have z6 := al_val w2 2 (by omega) i21 i22 i23 (by simpa using sh w2 i21 16 i21_post1) i22_post1 i23_post
  step with push_cand_at T (n + 6) a6 j6 i23 j6_post1 (by omega) _ _ _ (gb 6 (by omega) 0 (by omega))
    (gb 6 (by omega) 1 (by omega)) (gb 6 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z6
  step*
  have z7 := al_val w2 5 (by omega) i24 i25 i26 (by simpa using sh w2 i24 40 i24_post1) i25_post1 i26_post
  step with push_cand_at T (n + 7) a7 j7 i26 j7_post1 (by omega) _ _ _ (gb 7 (by omega) 0 (by omega))
    (gb 7 (by omega) 1 (by omega)) (gb 7 (by omega) 2 (by omega)) (lw_lt _ _) (lw_lt _ _) (lw_lt _ _) z7
  refine ⟨by assumption, by omega⟩

/-- Lane `i` of the lane vector `k` of the 4-way state, read through two array lookups. -/
theorem lane_word (st : St4) (k i : Usize) (hk : k.val < 25) (hi : i.val < 4) (a1 : Array U64 4#usize) (w : U64)
    (h1 : a1 = st.val[k.val]'(by rw [st.property]; exact hk))
    (h2 : w = a1.val[i.val]'(by rw [a1.property]; exact hi)) :
    toU64 w = ln (at4 st k.val) i.val := by
  have e := at4_idx st k a1 hk h1
  rw [← e]
  exact ln_of_get a1 i.val (by rw [a1.property]; exact hi) w h2

/-- The 24 stream bytes of group `g` of the block are the bytes of the three lane words `3g`, `3g+1`, `3g+2`. -/
theorem block_hw (T : List UInt8) (st : St4) (i b g : Nat) (hg : g < 7) (_hi : i < 4)
    (hT : ∀ p < 168, T[168 * b + p]? = some (KM.sb (pj st i) p)) (w0 w1 w2 : U64)
    (h0 : toU64 w0 = ln (at4 st (3 * g)) i) (h1 : toU64 w1 = ln (at4 st (3 * g + 1)) i)
    (h2 : toU64 w2 = ln (at4 st (3 * g + 2)) i) :
    ∀ p, p < 24 → T[3 * (56 * b + 8 * g) + p]? = some (UInt8.ofNat (lw (Wd w0 w1 w2 (p / 8)) (p % 8))) := by
  intro p hp
  have hp8 : p % 8 < 8 := Nat.mod_lt _ (by norm_num)
  rw [show 3 * (56 * b + 8 * g) + p = 168 * b + (24 * g + p) by ring, hT (24 * g + p) (by omega)]
  congr 1
  have e1 : (24 * g + p) / 8 = 3 * g + p / 8 := by omega
  have e2 : (24 * g + p) % 8 = p % 8 := by omega
  unfold KM.sb
  rw [e1, e2, pj_getElem _ _ _ (by omega)]
  rcases (by omega : p / 8 = 0 ∨ p / 8 = 1 ∨ p / 8 = 2) with h | h | h <;> rw [h]
  · have : Wd w0 w1 w2 0 = w0 := by simp [Wd]
    rw [this, Nat.add_zero, ← h0]; exact byteOf_lw w0 _ hp8
  · have : Wd w0 w1 w2 1 = w1 := by simp [Wd]
    rw [this, ← h1]; exact byteOf_lw w1 _ hp8
  · have : Wd w0 w1 w2 2 = w2 := by simp [Wd]
    rw [this, ← h2]; exact byteOf_lw w2 _ hp8

theorem rej_ntt_block_x4_spec (T : List UInt8) (st : St4) (i : Usize) (b : Nat) (hi : i.val < 4)
    (hT : ∀ p < 168, T[168 * b + p]? = some (KM.sb (pj st i.val) p))
    (a : Array U32 312#usize) (j : Usize) (hj : j.val < 256) (h : LaneInv T (56 * b) a j) :
    sampling.rej_ntt_block_x4 st i a j ⦃ r => LaneInv T (56 * (b + 1)) r.2 r.1 ⦄ := by
  unfold sampling.rej_ntt_block_x4 sampling.rej_ntt_block_x4_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 312#usize × Usize × Usize) => 7 - p.2.2.val)
    (fun (p : Array U32 312#usize × Usize × Usize) =>
      p.2.2.val ≤ 7 ∧ p.2.1.val ≤ j.val + 8 * p.2.2.val ∧ LaneInv T (56 * b + 8 * p.2.2.val) p.1 p.2.1)
  · rintro ⟨a, jc, g⟩ ⟨hg, hjg, hinv⟩
    dsimp only at hg hjg hinv
    simp only [sampling.rej_ntt_block_x4_loop.body]
    split
    · rename_i hglt
      have hg7 : g.val < 7 := by scalar_tac
      step*
      have l0 := lane_word st i1 i (by omega) hi _ _ a1_post2 i2_post2
      have l1 := lane_word st i3 i (by omega) hi _ _ a2_post2 i4_post2
      have l2 := lane_word st i5 i (by omega) hi _ _ a3_post2 i6_post2
      rw [i1_post] at l0
      rw [i3_post, i1_post] at l1
      rw [i5_post, i1_post] at l2
      have hw := block_hw T st i.val b g.val hg7 hi hT _ _ _ l0 l1 l2
      step with rej_ntt_cands8_spec T (56 * b + 8 * g.val) _ _ _ hw a jc (by omega) hinv
      step*
      refine ⟨by omega, by omega, ?_, by omega⟩
      rw [show 56 * b + 8 * g1.val = 56 * b + 8 * g.val + 8 by omega]
      exact j1_post1
    · rename_i hge
      have hg7 : g.val = 7 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hg7] at hinv
      rw [show 56 * (b + 1) = 56 * b + 8 * 7 by ring]
      exact hinv
  · exact ⟨by simp, by simp, by simpa using h⟩

/-! ## One lane of one 4-way block -/

theorem rej_ntt_lane_x4_spec (T : List UInt8) (st : St4) (i : Usize) (b : Nat) (hi : i.val < 4)
    (hT : ∀ p < 168, T[168 * b + p]? = some (KM.sb (pj st i.val) p))
    (a : Array U32 312#usize) (j : Usize) (h : LaneInv T (56 * b) a j) :
    sampling.rej_ntt_lane_x4 st i a j ⦃ r => LaneInv T (56 * (b + 1)) r.2 r.1 ⦄ := by
  unfold sampling.rej_ntt_lane_x4
  split
  · rename_i hj
    have hj256 : j.val < 256 := by scalar_tac
    exact rej_ntt_block_x4_spec T st i b hi hT a j hj256 h
  · rename_i hj
    have hj256 : 256 ≤ j.val := by scalar_tac
    simp only [WP.spec_ok]
    obtain ⟨h1, h2, h3⟩ := h
    have hst := stA_stable T (56 * b) (56 * (b + 1)) (by omega) (by omega)
    refine ⟨h1, ?_, ?_⟩
    · rw [hst]; exact h2
    · intro k hk
      rw [hst] at hk ⊢
      exact h3 k hk


/-! ## The final copy -/

theorem arr_get_set_256 (a : Array U32 256#usize) (j : Usize) (z : U32) (hj : j.val < 256) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k then z else a.val[k]! := by
  have hl : a.val.length = 256 := a.property
  by_cases hk : k < 256
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ j.val = k := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

theorem getE312 (a : Array U32 312#usize) (q : Nat) (hq : q < 312) (x : U32)
    (hx : x = a.val[q]'(by rw [a.property]; exact hq)) : a.val[q]! = x := by
  rw [getElem!_pos a.val q (by rw [a.property]; exact hq)]; exact hx.symm

@[step]
theorem first_256_spec (a : Array U32 312#usize) :
    sampling.first_256 a ⦃ r => ∀ k, k < 256 → r.val[k]! = a.val[k]! ⦄ := by
  unfold sampling.first_256 sampling.first_256_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun (p : Array U32 256#usize × Usize) => p.2.val ≤ 256 ∧ ∀ m, m < p.2.val → p.1.val[m]! = a.val[m]!)
  · rintro ⟨r, k⟩ ⟨hk, hg⟩
    dsimp only at hk hg
    simp only [sampling.first_256_loop.body]
    split
    · rename_i hlt
      have hk256 : k.val < 256 := by scalar_tac
      step*
      refine ⟨by omega, ?_, by omega⟩
      intro m hm
      rw [a1_post, arr_get_set_256 r k _ hk256 m]
      by_cases hmk : m = k.val
      · subst hmk
        rw [if_pos rfl]
        exact (getE312 a k.val (by omega) _ i_post2).symm
      · have : ¬ k.val = m := fun h => hmk h.symm
        rw [if_neg this]
        exact hg m (by omega)
    · rename_i hge
      have : k.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      intro m hm
      exact hg m (by omega)
  · exact ⟨by simp, by intro m hm; simp at hm⟩

/-! ## What a finished lane denotes -/

/-- The first 256 words of the scratch are canonical and denote the polynomial `P`. -/
def FinP (P : Poly) (a : Array U32 312#usize) : Prop :=
  (∀ k, k < 256 → (a.val[k]!).val < Spec.q) ∧ ∀ k, k < 256 → (((a.val[k]!).val : Nat) : Zq) = P[k]!

def FinL (T : List UInt8) (n : Nat) (a : Array U32 312#usize) : Prop := FinP (stA T n).1 a

theorem lane_fin (T : List UInt8) (n m : Nat) (hnm : n ≤ m) (a : Array U32 312#usize) (j : Usize)
    (h : LaneInv T n a j) (hj : 256 ≤ j.val) : FinL T m a := by
  obtain ⟨_, hmin, hk⟩ := h
  have hs : (stA T n).2 = 256 := by omega
  have hst := stA_stable T n m (by omega) hnm
  unfold FinL FinP
  rw [hst]
  exact ⟨fun k hk' => (hk k (by omega)).1, fun k hk' => (hk k (by omega)).2⟩

theorem finP_of (T : List UInt8) (n : Nat) (P : Poly) (a : Array U32 312#usize) (h : FinL T n a)
    (e : (stA T n).1 = P) : FinP P a := by
  subst e; exact h

theorem repr_of_first_256 (r : Array U32 256#usize) (a : Array U32 312#usize) (P : Poly)
    (hr : ∀ k, k < 256 → r.val[k]! = a.val[k]!) (h : FinP P a) : Repr r P := by
  obtain ⟨h1, h2⟩ := h
  have hl := len256 r
  constructor
  · intro x hx
    obtain ⟨k, hk, hxk⟩ := List.getElem_of_mem hx
    subst hxk
    have hk' : k < 256 := by omega
    have e := hr k hk'
    rw [getElem!_pos r.val k hk] at e
    rw [e]
    exact h1 k hk'
  · apply Vector.ext
    intro k hk
    rw [toZq_get r k hk]
    have e := hr k hk
    rw [getElem!_pos r.val k (by omega)] at e
    rw [e, h2 k hk, getElem!_pos _ _ (by simpa using hk)]

end Proofs
