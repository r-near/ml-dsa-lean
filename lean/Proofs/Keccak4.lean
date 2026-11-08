import Proofs.KeccakPerm

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

theorem ln_of_get {n : Usize} (a : Array U64 n) (k : Nat) (hk : k < a.val.length) (v : U64) (hv : v = a.val[k]) :
    toU64 v = ln a k := by
  subst hv; exact (ln_eq a k hk).symm

theorem ln_make4 (x0 x1 x2 x3 : U64) (h : [x0, x1, x2, x3].length = (4#usize).val) (j : Nat) (hj : j < 4) :
    ln (Array.make 4#usize [x0, x1, x2, x3] h) j =
      if j = 0 then toU64 x0 else if j = 1 then toU64 x1 else if j = 2 then toU64 x2 else toU64 x3 := by
  unfold ln
  simp only [Array.make]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp

/-- One lane of a rotation: `(x <<< L) ||| (x >>> R)` with `R = 64 - L` is `Spec.Keccak.rotl x L`. -/
theorem rot_of_bv (x i1 i2 i3 : U64) (L R : U32) (hL : 0 < L.val) (hL' : L.val < 64) (hR : R.val = 64 - L.val)
    (h1 : i1.bv = x.bv <<< L.val) (h2 : i2.bv = x.bv >>> R.val) (h3 : i3.bv = i1.bv ||| i2.bv) :
    toU64 i3 = Spec.Keccak.rotl (toU64 x) L.val := by
  simp only [Spec.Keccak.rotl]
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, toU64, h1, h2, h3, hR]
  simp only [Nat.mod_eq_of_lt hL']
  rw [Nat.mod_eq_of_lt (show 64 - L.val < 64 by omega)]

/-! ## Round -/

abbrev St4 := Array (Array U64 4#usize) 25#usize

instance : Inhabited (Array U64 4#usize) := ⟨Array.repeat 4#usize 0#u64⟩

/-- Lane vector `k` of a 4-way state (a default out of range). -/
def at4 (s : St4) (k : Nat) : Array U64 4#usize := s.val[k]!

/-- State `i` of a 4-way state: lane `k` of state `i` is lane `i` of `s[k]`. -/
def pj (s : St4) (i : Nat) : Spec.Keccak.State :=
  Vector.ofFn fun k : Fin 25 => ln (at4 s k.val) i

theorem pj_getElem (s : St4) (i k : Nat) (hk : k < 25) : (pj s i)[k]! = ln (at4 s k) i := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp [pj]

theorem at4_set (s : St4) (k : Usize) (v : Array U64 4#usize) (k' : Nat) (hk : k.val < 25) :
    at4 (s.set k v) k' = if k.val = k' then v else at4 s k' := by
  have hl : s.val.length = 25 := s.property
  unfold at4
  by_cases h : k' < 25
  · rw [getElem!_pos (s.set k v).val k' (by simp [Array.set_val_eq, hl]; omega),
        getElem!_pos s.val k' (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ k.val = k' := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

theorem pj_getElem' (s : St4) (i k : Nat) (hk : k < 25) : (pj s i)[k] = ln (at4 s k) i := by
  simp [pj]

theorem at4_idx (s : St4) (k : Usize) (v : Array U64 4#usize) (hk : k.val < 25)
    (hv : v = s.val[k.val]'(by rw [s.property]; exact hk)) : v = at4 s k.val := by
  subst hv; unfold at4
  rw [getElem!_pos s.val k.val (by rw [s.property]; exact hk)]

theorem at4_getElem (s : St4) (k : Nat) (h : k < s.val.length) : s.val[k] = at4 s k := by
  unfold at4; rw [getElem!_pos s.val k h]

theorem iota_getElem (A : Spec.Keccak.State) (ir k : Nat) (hk : k < 25) :
    (Spec.Keccak.iota A ir)[k]! = if k = 0 then A[0]! ^^^ Spec.Keccak.RCs[ir]! else A[k]! := by
  simp only [Spec.Keccak.iota, set!_eq']
  rw [getElem!_pos _ _ (by simpa using hk), Vector.getElem_setIfInBounds (by simpa using hk)]
  by_cases h : k = 0
  · subst h; simp
  · simp [h, Ne.symm h]
    rw [getElem!_pos _ _ (by simpa using hk)]

theorem rhoOffsets_eq : Spec.Keccak.rhoOffsets =
    #[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14] := by
  decide +kernel

theorem rotl_zero (v : UInt64) : Spec.Keccak.rotl v 0 = v := by
  simp only [Spec.Keccak.rotl]
  apply UInt64.toBitVec_inj.mp
  simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftRight]

/-- `D[x]` of θ. -/
def Dv' (A : Spec.Keccak.State) (x : Nat) : UInt64 :=
  Cs A ((x + 4) % 5) ^^^ Spec.Keccak.rotl (Cs A ((x + 1) % 5)) 1

/-- Lane `m` of `π(ρ(θ(A)))`. -/
def Bf (A : Spec.Keccak.State) (m : Nat) : UInt64 :=
  Spec.Keccak.rotl (A[srcI m]! ^^^ Dv' A (srcI m % 5)) Spec.Keccak.rhoOffsets[srcI m]!

/-- Lane `k` of `χ(π(ρ(θ(A))))`. -/
def XV (A : Spec.Keccak.State) (k : Nat) : UInt64 :=
  Bf A k ^^^ (~~~Bf A ((k % 5 + 1) % 5 + 5 * (k / 5)) &&& Bf A ((k % 5 + 2) % 5 + 5 * (k / 5)))

theorem srcI_lt (m : Nat) : srcI m < 25 := by simp only [srcI]; omega

theorem Bf_eq (A : Spec.Keccak.State) (m : Nat) (hm : m < 25) :
    (Spec.Keccak.pi (Spec.Keccak.rho (Spec.Keccak.theta A)))[m]! = Bf A m := by
  rw [pi_getElem _ m hm, rho_getElem _ _ (srcI_lt m), theta_getElem _ _ (srcI_lt m)]
  rfl

theorem rnd_getElem (A : Spec.Keccak.State) (ir k : Nat) (hk : k < 25) :
    (Spec.Keccak.Rnd A ir)[k]! = if k = 0 then XV A 0 ^^^ Spec.Keccak.RCs[ir]! else XV A k := by
  simp only [Spec.Keccak.Rnd, iota_getElem _ _ _ hk, chi_getElem _ _ hk]
  have e : ∀ k, k < 25 → chiV (Spec.Keccak.pi (Spec.Keccak.rho (Spec.Keccak.theta A))) k = XV A k := by
    intro k hk
    simp only [chiV, XV]
    rw [Bf_eq A k hk, Bf_eq A _ (by omega), Bf_eq A _ (by omega)]
  split_ifs with h
  · subst h; rw [chi_getElem _ _ (by omega), e 0 (by omega)]
  · rw [e k hk]

/-! ## One round on one state -/

/-- `ι ∘ χ ∘ π ∘ ρ ∘ θ` with an arbitrary round constant `c` in place of `RC[ir]`. -/
def RndC (A : Spec.Keccak.State) (c : UInt64) : Spec.Keccak.State :=
  Vector.ofFn fun k : Fin 25 => if k.val = 0 then XV A 0 ^^^ c else XV A k.val

theorem RndC_getElem (A : Spec.Keccak.State) (c : UInt64) (k : Nat) (hk : k < 25) :
    (RndC A c)[k]! = if k = 0 then XV A 0 ^^^ c else XV A k := by
  rw [RndC, getElem!_ofFn25 _ _ hk]

theorem RndC_eq (A : Spec.Keccak.State) (ir : Nat) : RndC A Spec.Keccak.RCs[ir]! = Spec.Keccak.Rnd A ir := by
  apply vec_ext25
  intro k hk
  rw [RndC_getElem _ _ _ hk, rnd_getElem _ _ _ hk]

theorem toLanes_make25 (xs : List U64) (h : xs.length = (25#usize).val) (k : Nat) (hk : k < 25) :
    (toLanes (Array.make 25#usize xs h))[k]! = toU64 (xs[k]'(by rw [h]; simpa using hk)) := by
  rw [toLanes_getElem! _ _ (by simp [Array.make]; rw [h]; simpa using hk)]
  rfl

set_option maxHeartbeats 8000000 in
/-- **One Keccak round on a scalar state** (`round25`): θ, ρ, π, χ, then ι with the constant passed in. -/
@[local step]
theorem round25_spec (a : Array U64 25#usize) (rc : U64) :
    keccak4.round25 a rc ⦃ o => toLanes o = RndC (toLanes a) (toU64 rc) ⦄ := by
  unfold keccak4.round25
  step*
  apply vec_ext25
  intro k hk
  rw [toLanes_make25 _ _ k hk, RndC_getElem _ _ _ hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply UInt64.toBitVec_inj.mp
    simp [toU64, toLanes_get, XV, Bf, Dv', Cs, srcI, rhoOffsets_eq, Spec.Keccak.rotl, *]

/-! ## Two rounds on one of the four states -/

/-- The scalar state `i` of a 4-way state, from the 25 loaded lanes. -/
theorem toLanes_state (s : St4) (i : Nat) (xs : List U64) (h : xs.length = (25#usize).val)
    (hx : ∀ k (hk : k < 25), toU64 (xs[k]'(by rw [h]; simpa using hk)) = ln (at4 s k) i) :
    toLanes (Array.make 25#usize xs h) = pj s i := by
  apply vec_ext25
  intro k hk
  rw [toLanes_make25 _ _ k hk, pj_getElem _ _ _ hk, hx k hk]

theorem ln_at4_get (s : St4) (k : Nat) (hk : k < 25) (i : Nat) (hi : i < 4) :
    ln (at4 s k) i = toU64 ((s.val[k]'(by rw [s.property]; exact hk)).val[i]'(by
      rw [(s.val[k]'(by rw [s.property]; exact hk)).property]; exact hi)) := by
  unfold at4
  rw [getElem!_pos s.val k (by rw [s.property]; exact hk)]
  exact ln_eq _ i (by rw [(s.val[k]'(by rw [s.property]; exact hk)).property]; exact hi)

/-- One write-back of `lane_rounds2`: after writing `z[n]` into state `i` of lane vector `n`, the lanes `< n + 1` of
state `i` are `z`'s. -/
theorem wb_step (s : St4) (z : Array U64 25#usize) (i : Usize) (hi : i.val < 4) (n : Nat) (hn : n < 25)
    (S : St4)
    (hS : ∀ j, j < 4 → ∀ k, k < 25 → ln (at4 S k) j =
      if j = i.val ∧ k < n then toU64 (z.val[k]!) else ln (at4 s k) j)
    (k : Usize) (hk : k.val = n) (v : U64) (hv : v = z.val[n]'(by rw [z.property]; exact hn))
    (a a' : Array U64 4#usize) (ha : a = S.val[n]'(by rw [S.property]; exact hn)) (ha' : a' = a.set i v)
    (back : Array U64 4#usize → St4) (hb : back = Std.Array.set S k) :
    ∀ j, j < 4 → ∀ k', k' < 25 → ln (at4 (back a') k') j =
      if j = i.val ∧ k' < n + 1 then toU64 (z.val[k']!) else ln (at4 s k') j := by
  intro j hj k' hk'
  have hkn : k.val < 25 := by omega
  subst hb
  rw [at4_set S k a' k' hkn]
  have hi4 : i.val < (4#usize).val := by simpa using hi
  by_cases hkk : k.val = k'
  · rw [if_pos hkk, ha', ln_set _ _ _ _ hi4]
    have e1 := hS j hj n hn
    have hnk : n = k' := by omega
    subst hnk
    rw [ha, at4_getElem S n (by rw [S.property]; exact hn)]
    have hz : z.val[n]! = z.val[n]'(by rw [z.property]; exact hn) := getElem!_pos _ _ _
    by_cases hij : i.val = j
    · subst hij
      simp [hv, hz]
    · rw [if_neg hij]
      have : ¬ (j = i.val ∧ n < n) := by omega
      rw [if_neg this] at e1
      rw [e1]
      have : ¬ (j = i.val ∧ n < n + 1) := by omega
      rw [if_neg this]
  · rw [if_neg hkk, hS j hj k' hk']
    have : (j = i.val ∧ k' < n + 1) ↔ (j = i.val ∧ k' < n) := by omega
    simp only [this]

set_option maxHeartbeats 8000000 in
/-- **Two rounds on state `i` of a 4-way state**: state `i` of the result is `RndC (RndC (state i) rc0) rc1` and the
other three states are unchanged. -/
@[local step]
theorem lane_rounds2_spec (s : St4) (i : Usize) (rc0 rc1 : U64) (hi : i.val < 4) :
    keccak4.lane_rounds2 s i rc0 rc1 ⦃ s' => ∀ j, j < 4 →
      pj s' j = if j = i.val then RndC (RndC (pj s j) (toU64 rc0)) (toU64 rc1) else pj s j ⦄ := by
  unfold keccak4.lane_rounds2
  step*
  have hm : toLanes m = RndC (pj s i.val) (toU64 rc0) := by
    rw [m_post, toLanes_state s i.val _ _ ?hx]
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [ln_at4_get s _ (by omega) i.val hi, a_post2, i1_post2, a1_post2, i2_post2, a2_post2, i3_post2, a3_post2, i4_post2, a4_post2, i5_post2, a5_post2, i6_post2, a6_post2, i7_post2, a7_post2, i8_post2, a8_post2, i9_post2, a9_post2, i10_post2, a10_post2, i11_post2, a11_post2, i12_post2, a12_post2, i13_post2, a13_post2, i14_post2, a14_post2, i15_post2, a15_post2, i16_post2, a16_post2, i17_post2, a17_post2, i18_post2, a18_post2, i19_post2, a19_post2, i20_post2, a20_post2, i21_post2, a21_post2, i22_post2, a22_post2, i23_post2, a23_post2, i24_post2, a24_post2, i25_post2]
  have hz : toLanes z = RndC (RndC (pj s i.val) (toU64 rc0)) (toU64 rc1) := by rw [z_post, hm]
  have I0 : ∀ j, j < 4 → ∀ k, k < 25 → ln (at4 s k) j =
      if j = i.val ∧ k < 0 then toU64 (z.val[k]!) else ln (at4 s k) j := by
    intro j hj k hk; simp
  have I1 := wb_step s z i hi 0 (by norm_num) _ I0 _ (by simp) _ i26_post2 _ _ a25_post2 a26_post index_mut_back a25_post3
  have I2 := wb_step s z i hi 1 (by norm_num) _ I1 _ (by simp) _ i27_post2 _ _ a27_post2 a28_post index_mut_back1 a27_post3
  have I3 := wb_step s z i hi 2 (by norm_num) _ I2 _ (by simp) _ i28_post2 _ _ a29_post2 a30_post index_mut_back2 a29_post3
  have I4 := wb_step s z i hi 3 (by norm_num) _ I3 _ (by simp) _ i29_post2 _ _ a31_post2 a32_post index_mut_back3 a31_post3
  have I5 := wb_step s z i hi 4 (by norm_num) _ I4 _ (by simp) _ i30_post2 _ _ a33_post2 a34_post index_mut_back4 a33_post3
  have I6 := wb_step s z i hi 5 (by norm_num) _ I5 _ (by simp) _ i31_post2 _ _ a35_post2 a36_post index_mut_back5 a35_post3
  have I7 := wb_step s z i hi 6 (by norm_num) _ I6 _ (by simp) _ i32_post2 _ _ a37_post2 a38_post index_mut_back6 a37_post3
  have I8 := wb_step s z i hi 7 (by norm_num) _ I7 _ (by simp) _ i33_post2 _ _ a39_post2 a40_post index_mut_back7 a39_post3
  have I9 := wb_step s z i hi 8 (by norm_num) _ I8 _ (by simp) _ i34_post2 _ _ a41_post2 a42_post index_mut_back8 a41_post3
  have I10 := wb_step s z i hi 9 (by norm_num) _ I9 _ (by simp) _ i35_post2 _ _ a43_post2 a44_post index_mut_back9 a43_post3
  have I11 := wb_step s z i hi 10 (by norm_num) _ I10 _ (by simp) _ i36_post2 _ _ a45_post2 a46_post index_mut_back10 a45_post3
  have I12 := wb_step s z i hi 11 (by norm_num) _ I11 _ (by simp) _ i37_post2 _ _ a47_post2 a48_post index_mut_back11 a47_post3
  have I13 := wb_step s z i hi 12 (by norm_num) _ I12 _ (by simp) _ i38_post2 _ _ a49_post2 a50_post index_mut_back12 a49_post3
  have I14 := wb_step s z i hi 13 (by norm_num) _ I13 _ (by simp) _ i39_post2 _ _ a51_post2 a52_post index_mut_back13 a51_post3
  have I15 := wb_step s z i hi 14 (by norm_num) _ I14 _ (by simp) _ i40_post2 _ _ a53_post2 a54_post index_mut_back14 a53_post3
  have I16 := wb_step s z i hi 15 (by norm_num) _ I15 _ (by simp) _ i41_post2 _ _ a55_post2 a56_post index_mut_back15 a55_post3
  have I17 := wb_step s z i hi 16 (by norm_num) _ I16 _ (by simp) _ i42_post2 _ _ a57_post2 a58_post index_mut_back16 a57_post3
  have I18 := wb_step s z i hi 17 (by norm_num) _ I17 _ (by simp) _ i43_post2 _ _ a59_post2 a60_post index_mut_back17 a59_post3
  have I19 := wb_step s z i hi 18 (by norm_num) _ I18 _ (by simp) _ i44_post2 _ _ a61_post2 a62_post index_mut_back18 a61_post3
  have I20 := wb_step s z i hi 19 (by norm_num) _ I19 _ (by simp) _ i45_post2 _ _ a63_post2 a64_post index_mut_back19 a63_post3
  have I21 := wb_step s z i hi 20 (by norm_num) _ I20 _ (by simp) _ i46_post2 _ _ a65_post2 a66_post index_mut_back20 a65_post3
  have I22 := wb_step s z i hi 21 (by norm_num) _ I21 _ (by simp) _ i47_post2 _ _ a67_post2 a68_post index_mut_back21 a67_post3
  have I23 := wb_step s z i hi 22 (by norm_num) _ I22 _ (by simp) _ i48_post2 _ _ a69_post2 a70_post index_mut_back22 a69_post3
  have I24 := wb_step s z i hi 23 (by norm_num) _ I23 _ (by simp) _ i49_post2 _ _ a71_post2 a72_post index_mut_back23 a71_post3
  have I25 := wb_step s z i hi 24 (by norm_num) _ I24 _ (by simp) _ i50_post2 _ _ a73_post2 a74_post index_mut_back24 a73_post3
  have hzk : ∀ k, k < 25 → toU64 (z.val[k]!) = (toLanes z)[k]! := by
    intro k hk
    rw [toLanes_getElem! z k (by rw [z.property]; exact hk), getElem!_pos _ _ (by rw [z.property]; exact hk)]
  intro j hj
  apply vec_ext25
  intro k hk
  rw [pj_getElem _ _ _ hk, I25 j hj k hk]
  by_cases hji : j = i.val
  · have hc : j = i.val ∧ k < 24 + 1 := ⟨hji, by omega⟩
    rw [if_pos hc, if_pos hji, hzk k hk, hz]
    subst hji
    rfl
  · have hc : ¬ (j = i.val ∧ k < 24 + 1) := fun h => hji h.1
    rw [if_neg hc, if_neg hji, pj_getElem _ _ _ hk]

/-! ## The 24 rounds -/

theorem RC_idx4 (i : Usize) (hi : i.val < 24) (v : U64) (hv : v = keccak.RC.val[i.val]'(by
    rw [RC_len]; exact hi)) : toU64 v = Spec.Keccak.RCs[i.val]! := RC_idx i hi v hv

/-- The loop over the four states: each of them goes through rounds `r` and `r + 1`. -/
theorem keccak_x4_states_loop_spec (s : St4) (r : Usize) (hr : r.val + 1 < 24) :
    keccak4.keccak_f1600_x4_loop0_loop0 s r 0#usize ⦃ s' => ∀ j, j < 4 →
      pj s' j = Spec.Keccak.Rnd (Spec.Keccak.Rnd (pj s j) r.val) (r.val + 1) ⦄ := by
  unfold keccak4.keccak_f1600_x4_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : St4 × Usize) => 4 - p.2.val)
    (fun p => p.2.val ≤ 4 ∧ ∀ j, j < 4 → pj p.1 j =
      if j < p.2.val then Spec.Keccak.Rnd (Spec.Keccak.Rnd (pj s j) r.val) (r.val + 1) else pj s j)
  · rintro ⟨sc, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak4.keccak_f1600_x4_loop0_loop0.body]
    split
    · rename_i hi
      have hi4 : i.val < 4 := by scalar_tac
      step*
      have hrc0 := RC_idx4 r (by omega) _ i1_post2
      have hrc1 := RC_idx4 i2 (by omega) _ i3_post2
      rw [i2_post] at hrc1
      refine ⟨by omega, fun j hj => ?_, by omega⟩
      rw [s1_post j hj, hrc0, hrc1, RndC_eq, RndC_eq, h2 j hj, i4_post]
      by_cases hji : j = i.val
      · subst hji; simp
      · have : (j < i.val + 1) ↔ (j < i.val) := by omega
        simp [hji, this]
    · rename_i hi
      have : i.val = 4 := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj
      rw [h2 j hj, if_pos (by omega)]
  · refine ⟨by simp, fun j hj => ?_⟩
    simp

/-- **Keccak-f[1600] on four states.** Lane `i` of the output state is `Spec.KeccakF1600` of lane `i` of the
input state; it neither fails nor diverges. The kernel runs two rounds per loop iteration, one state at a time. -/
theorem keccak_f1600_x4_spec (s : St4) :
    keccak4.keccak_f1600_x4 s ⦃ s' => ∀ i, i < 4 → pj s' i = Spec.KeccakF1600 (pj s i) ⦄ := by
  unfold keccak4.keccak_f1600_x4 keccak4.keccak_f1600_x4_loop0
  apply loop.spec_decr_nat
    (fun (p : St4 × Usize) => 24 - p.2.val)
    (fun p => p.2.val ≤ 24 ∧ p.2.val % 2 = 0 ∧
      ∀ i, i < 4 → pj p.1 i = (List.range p.2.val).foldl Spec.Keccak.Rnd (pj s i))
  · rintro ⟨sc, r⟩ ⟨h1, h1', h2⟩
    dsimp only at h1 h1' h2
    simp only [keccak4.keccak_f1600_x4_loop0.body]
    split
    · rename_i hr
      have hr24 : r.val < 24 := by scalar_tac
      have hr23 : r.val + 1 < 24 := by omega
      step with keccak_x4_states_loop_spec sc r hr23 as ⟨s1, hs1⟩
      step as ⟨r1, hr1⟩
      refine ⟨by omega, by omega, fun k hk => ?_, by omega⟩
      rw [hs1 k hk, h2 k hk, hr1, List.range_succ, List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    · rename_i hr
      have : r.val = 24 := by scalar_tac
      simp only [WP.spec_ok]
      intro i hi
      rw [h2 i hi, this]
      rfl
  · exact ⟨by simp, by simp, fun i hi => by simp⟩

/-! ## Against the extracted scalar permutation -/

/-- State `i` of a 4-way state, as an extracted `[u64; 25]`. -/
def laneArr (s : St4) (i : Nat) : Array U64 25#usize :=
  ⟨(List.range 25).map (fun k => (at4 s k).val[i]!), by simp⟩

theorem toLanes_laneArr (s : St4) (i : Nat) : toLanes (laneArr s i) = pj s i := by
  apply Vector.ext
  intro k hk
  simp [toLanes, laneArr, pj, ln]

/-- **Lane `i` of the 4-way permutation is the scalar permutation on lane `i`'s state.** For every input, the
4-way kernel neither fails nor diverges, and for each
`i < 4` the extracted scalar `keccak_f1600` run on state `i` returns exactly state `i` of the output. -/
theorem keccak_f1600_x4_eq_scalar (s : St4) :
    keccak4.keccak_f1600_x4 s ⦃ s' => ∀ i, i < 4 →
      keccak.keccak_f1600 (laneArr s i) = ok (laneArr s' i) ⦄ := by
  apply WP.spec_mono (keccak_f1600_x4_spec s)
  intro s' h i hi
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (keccak_f1600_spec (laneArr s i))
  rw [hr]
  congr 1
  apply toLanes_inj
  rw [hp, toLanes_laneArr, toLanes_laneArr, h i hi]

end Proofs
