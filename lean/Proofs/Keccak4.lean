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

theorem shim_xor_spec (a b : Array U64 4#usize) :
    keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.xor a b ⦃ r => ∀ j, j < 4 → ln r j = ln a j ^^^ ln b j ⦄ := by
  unfold keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.xor
  step*
  intro j hj
  rw [ln_make4 _ _ _ _ _ j hj]
  have h0 := ln_of_get a 0 (by simp) _ i_post2
  have h1 := ln_of_get b 0 (by simp) _ i1_post2
  have h2 := ln_of_get a 1 (by simp) _ i3_post2
  have h3 := ln_of_get b 1 (by simp) _ i4_post2
  have h4 := ln_of_get a 2 (by simp) _ i6_post2
  have h5 := ln_of_get b 2 (by simp) _ i7_post2
  have h6 := ln_of_get a 3 (by simp) _ i9_post2
  have h7 := ln_of_get b 3 (by simp) _ i10_post2
  have k0 := xor_of_bv _ _ _ i2_post2
  have k1 := xor_of_bv _ _ _ i5_post2
  have k2 := xor_of_bv _ _ _ i8_post2
  have k3 := xor_of_bv _ _ _ i11_post2
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> simp [k0, k1, k2, k3, h0, h1, h2, h3, h4, h5, h6, h7]

theorem shim_andnot_spec (a b : Array U64 4#usize) :
    keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.andnot a b ⦃ r => ∀ j, j < 4 → ln r j = ~~~ln a j &&& ln b j ⦄ := by
  unfold keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.andnot
  step*
  intro j hj
  rw [ln_make4 _ _ _ _ _ j hj]
  have h0 := ln_of_get a 0 (by simp) _ i_post2
  have h1 := ln_of_get b 0 (by simp) _ i2_post2
  have h2 := ln_of_get a 1 (by simp) _ i4_post2
  have h3 := ln_of_get b 1 (by simp) _ i6_post2
  have h4 := ln_of_get a 2 (by simp) _ i8_post2
  have h5 := ln_of_get b 2 (by simp) _ i10_post2
  have h6 := ln_of_get a 3 (by simp) _ i12_post2
  have h7 := ln_of_get b 3 (by simp) _ i14_post2
  have n0 := not_of_bv _ _ ((congrArg UScalar.bv i1_post).trans (UScalar.bv_not _))
  have n1 := not_of_bv _ _ ((congrArg UScalar.bv i5_post).trans (UScalar.bv_not _))
  have n2 := not_of_bv _ _ ((congrArg UScalar.bv i9_post).trans (UScalar.bv_not _))
  have n3 := not_of_bv _ _ ((congrArg UScalar.bv i13_post).trans (UScalar.bv_not _))
  have k0 := and_of_bv _ _ _ i3_post2
  have k1 := and_of_bv _ _ _ i7_post2
  have k2 := and_of_bv _ _ _ i11_post2
  have k3 := and_of_bv _ _ _ i15_post2
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp [k0, k1, k2, k3, n0, n1, n2, n3, h0, h1, h2, h3, h4, h5, h6, h7]

theorem shim_splat_spec (x : U64) :
    keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.splat x ⦃ r => ∀ j, j < 4 → ln r j = toU64 x ⦄ := by
  unfold keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.splat
  simp only [WP.spec_ok]
  intro j hj
  rw [ln_make4 _ _ _ _ _ j hj]
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

theorem shim_rotl_spec (L R : U32) (a : Array U64 4#usize) (hL : 0 < L.val) (hL' : L.val < 64)
    (hR : R.val = 64 - L.val) :
    keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.rotl L R a ⦃ r =>
      ∀ j, j < 4 → ln r j = Spec.Keccak.rotl (ln a j) L.val ⦄ := by
  unfold keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4.rotl
  step*
  intro j hj
  rw [ln_make4 _ _ _ _ _ j hj]
  have h0 := ln_of_get a 0 (by simp) _ i_post2
  have h1 := ln_of_get a 1 (by simp) _ i4_post2
  have h2 := ln_of_get a 2 (by simp) _ i8_post2
  have h3 := ln_of_get a 3 (by simp) _ i12_post2
  have k0 := rot_of_bv _ _ _ _ L R hL hL' hR i1_post2 i2_post2 i3_post2
  have k1 := rot_of_bv _ _ _ _ L R hL hL' hR i5_post2 i6_post2 i7_post2
  have k2 := rot_of_bv _ _ _ _ L R hL hL' hR i9_post2 i10_post2 i11_post2
  have k3 := rot_of_bv _ _ _ _ L R hL hL' hR i13_post2 i14_post2 i15_post2
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
    simp [k0, k1, k2, k3, h0, h1, h2, h3]

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

attribute [local step] shim_xor_spec shim_andnot_spec shim_splat_spec shim_rotl_spec

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

set_option maxHeartbeats 4000000 in
theorem round_lane (src dst : St4) (rc : U64) (i : Nat) (hi : i < 4) (ir : Nat)
    (hrc : toU64 rc = Spec.Keccak.RCs[ir]!) :
    keccak4.round keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4 src dst rc ⦃ s' =>
      pj s' i = Spec.Keccak.Rnd (pj src i) ir ⦄ := by
  unfold keccak4.round
  step*
  apply vec_ext25
  intro k hk
  rw [pj_getElem _ _ k hk, rnd_getElem _ _ _ hk]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [*, at4_set, at4_getElem, pj_getElem', rotl_zero, rhoOffsets_eq, XV, Bf, Dv', Cs, srcI]

/-! ## One round for all four states, and the 24 rounds -/

/-- The shim instance of the extracted trait, as the generic kernel takes it. -/
abbrev Sh4 := keccak4.Shim4.Insts.Ml_dsa_leanKeccak4Lanes4

/-- **One round, all four states.** Lane `i` of the output is `Rnd` of lane `i` of the input, for every `i < 4`
(whatever `dst` held: the round overwrites all 25 entries). -/
theorem round_spec (src dst : St4) (rc : U64) (ir : Nat) (hrc : toU64 rc = Spec.Keccak.RCs[ir]!) :
    keccak4.round Sh4 src dst rc ⦃ s' => ∀ i, i < 4 → pj s' i = Spec.Keccak.Rnd (pj src i) ir ⦄ := by
  obtain ⟨s0, h0, _⟩ := WP.spec_imp_exists (round_lane src dst rc 0 (by decide) ir hrc)
  rw [h0]
  simp only [WP.spec_ok]
  intro i hi
  obtain ⟨s1, h1, p1⟩ := WP.spec_imp_exists (round_lane src dst rc i hi ir hrc)
  rw [h0] at h1
  have : s0 = s1 := by simpa using h1
  subst this
  exact p1

theorem RC_idx4 (i : Usize) (hi : i.val < 24) (v : U64) (hv : v = keccak.RC.val[i.val]'(by
    rw [RC_len]; exact hi)) : toU64 v = Spec.Keccak.RCs[i.val]! := RC_idx i hi v hv

/-- **Keccak-f[1600] on four states (shim instance).** Lane `i` of the output state is
`Spec.KeccakF1600` of lane `i` of the input state; it neither fails nor diverges. The kernel runs two rounds per loop
iteration, ping-ponging between the state and a scratch copy. -/
theorem keccak_f1600_x4_shim_spec (s : St4) :
    keccak4.keccak_f1600_x4 Sh4 s ⦃ s' => ∀ i, i < 4 → pj s' i = Spec.KeccakF1600 (pj s i) ⦄ := by
  unfold keccak4.keccak_f1600_x4 keccak4.keccak_f1600_x4_loop
  apply loop.spec_decr_nat
    (fun (p : St4 × St4 × Usize) => 24 - p.2.2.val)
    (fun p => p.2.2.val ≤ 24 ∧ p.2.2.val % 2 = 0 ∧
      ∀ i, i < 4 → pj p.1 i = (List.range p.2.2.val).foldl Spec.Keccak.Rnd (pj s i))
  · rintro ⟨sc, tc, r⟩ ⟨h1, h1', h2⟩
    dsimp only at h1 h1' h2
    simp only [keccak4.keccak_f1600_x4_loop.body]
    split
    · rename_i hr
      have hr24 : r.val < 24 := by scalar_tac
      have hr23 : r.val + 1 < 24 := by omega
      step*
      have hrc := RC_idx4 r hr24 _ i_post2
      step with round_spec sc tc _ r.val hrc as ⟨t1, ht1⟩
      step*
      have hrc2 := RC_idx4 i1 (by omega) _ i2_post2
      step with round_spec t1 sc _ i1.val hrc2 as ⟨s1, hs1⟩
      step as ⟨r1, hr1⟩
      refine ⟨by omega, by omega, fun k hk => ?_, by omega⟩
      rw [hs1 k hk, ht1 k hk, h2 k hk, hr1, i1_post, List.range_succ, List.range_succ, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    · rename_i hr
      have : r.val = 24 := by scalar_tac
      simp only [WP.spec_ok]
      intro i hi
      rw [h2 i hi, this]
      rfl
  · exact ⟨by simp, by simp, fun i hi => by simp⟩

/-- The portable entry point is the shim instantiation. -/
theorem keccak_f1600_x4_portable_spec (s : St4) :
    keccak4.keccak_f1600_x4_portable s ⦃ s' => ∀ i, i < 4 → pj s' i = Spec.KeccakF1600 (pj s i) ⦄ := by
  unfold keccak4.keccak_f1600_x4_portable
  exact keccak_f1600_x4_shim_spec s

/-! ## Against the extracted scalar permutation -/

/-- State `i` of a 4-way state, as an extracted `[u64; 25]`. -/
def laneArr (s : St4) (i : Nat) : Array U64 25#usize :=
  ⟨(List.range 25).map (fun k => (at4 s k).val[i]!), by simp⟩

theorem toLanes_laneArr (s : St4) (i : Nat) : toLanes (laneArr s i) = pj s i := by
  apply Vector.ext
  intro k hk
  simp [toLanes, laneArr, pj, ln]

/-- **Lane `i` of the 4-way permutation is the scalar permutation on lane `i`'s state.** For every input, the
portable 4-way kernel (the shim instantiation of the generic kernel) neither fails nor diverges, and for each
`i < 4` the extracted scalar `keccak_f1600` run on state `i` returns exactly state `i` of the output. -/
theorem keccak_f1600_x4_portable_eq_scalar (s : St4) :
    keccak4.keccak_f1600_x4_portable s ⦃ s' => ∀ i, i < 4 →
      keccak.keccak_f1600 (laneArr s i) = ok (laneArr s' i) ⦄ := by
  apply WP.spec_mono (keccak_f1600_x4_portable_spec s)
  intro s' h i hi
  obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (keccak_f1600_spec (laneArr s i))
  rw [hr]
  congr 1
  apply toLanes_inj
  rw [hp, toLanes_laneArr, toLanes_laneArr, h i hi]

end Proofs
