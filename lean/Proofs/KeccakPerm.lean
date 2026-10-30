import Proofs.KeccakLanes

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

theorem rotl_spec (x : U64) (n : U32) (hn : n.val < 64) :
    keccak.rotl x n ⦃ r => toU64 r = Spec.Keccak.rotl (toU64 x) n.val ⦄ := by
  unfold keccak.rotl
  split
  · rename_i h
    have h0 : n.val = 0 := by simpa using congrArg UScalar.val h
    simp only [WP.spec_ok, h0]
    simp only [Spec.Keccak.rotl]
    apply UInt64.toBitVec_inj.mp
    simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  · rename_i h
    have h0 : n.val ≠ 0 := fun e => h (UScalar.eq_of_val_eq (by simpa using e))
    step*
    simp only [Spec.Keccak.rotl]
    apply UInt64.toBitVec_inj.mp
    simp [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, toU64, *]
    simp only [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show 64 - n.val < 64 by omega)]

theorem RHO_lt : ∀ k : Fin 25, (keccak.RHO.val[k.val]!).val < 64 := by
  decide +kernel

theorem RHO_eq : ∀ k : Fin 25, (keccak.RHO.val[k.val]!).val = Spec.Keccak.rhoOffsets[k.val]! := by
  decide +kernel

theorem RC_eq : ∀ k : Fin 24, (keccak.RC.val[k.val]!).val = (Spec.Keccak.RCs[k.val]!).toNat := by
  decide +kernel


/-! ## Lane access on extracted arrays -/

/-- Lane `k` of an extracted array (default `0` out of range). -/
def ln {n : Usize} (a : Array U64 n) (k : Nat) : UInt64 := toU64 a.val[k]!

theorem ln_eq {n : Usize} (a : Array U64 n) (k : Nat) (hk : k < a.val.length) :
    ln a k = toU64 a.val[k] := by
  unfold ln; rw [getElem!_pos a.val k hk]

theorem ln_set {n : Usize} (a : Array U64 n) (i : Usize) (x : U64) (k : Nat) (hi : i.val < n.val) :
    ln (a.set i x) k = if i.val = k then toU64 x else ln a k := by
  have hl : a.val.length = n.val := a.property
  have hl2 : (a.set i x).val.length = n.val := by simp [Array.set_val_eq, hl]
  by_cases hk : k < n.val
  · rw [ln_eq (a.set i x) k (by omega), ln_eq a k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
    split_ifs <;> simp_all
  · have hne : ¬ i.val = k := by omega
    rw [if_neg hne]
    unfold ln
    rw [getElem!_neg, getElem!_neg] <;> simp [hl, hl2] <;> omega

theorem toLanes_ln (a : Array U64 25#usize) (k : Nat) (hk : k < 25) : (toLanes a)[k]! = ln a k := by
  rw [ln_eq a k (by rw [len25 a]; exact hk)]
  exact toLanes_getElem! a k _

/-- `C[j]` of θ on the array. -/
def Cf (a : Array U64 25#usize) (j : Nat) : UInt64 :=
  ln a j ^^^ ln a (j + 5) ^^^ ln a (j + 10) ^^^ ln a (j + 15) ^^^ ln a (j + 20)


theorem ln_idx {n : Usize} (a : Array U64 n) (i : Usize) (k : Nat) (h : i.val = k)
    (hi : i.val < a.val.length) (v : U64) (hv : v = a.val[i.val]) : toU64 v = ln a k := by
  subst hv; subst h; rw [ln_eq a i.val hi]

theorem xor_of_bv (i x y : U64) (h : i.bv = x.bv ^^^ y.bv) : toU64 i = toU64 x ^^^ toU64 y := by
  unfold toU64; rw [h]; rfl

theorem and_of_bv (i x y : U64) (h : i.bv = x.bv &&& y.bv) : toU64 i = toU64 x &&& toU64 y := by
  unfold toU64; rw [h]; rfl

theorem not_of_bv (i x : U64) (h : i.bv = ~~~x.bv) : toU64 i = ~~~toU64 x := by
  unfold toU64; rw [h]; rfl

theorem vec_ext25 {A B : Spec.Keccak.State} (h : ∀ k, k < 25 → A[k]! = B[k]!) : A = B := by
  apply Vector.ext
  intro k hk
  have := h k hk
  rwa [getElem!_pos A k (by simpa using hk), getElem!_pos B k (by simpa using hk)] at this

/-! ## Spec step mappings, pointwise -/

def Cs (A : Spec.Keccak.State) (j : Nat) : UInt64 :=
  A[j]! ^^^ A[j + 5]! ^^^ A[j + 10]! ^^^ A[j + 15]! ^^^ A[j + 20]!

theorem getElem!_ofFn_mod5 {α : Type} [Inhabited α] (f : Fin 5 → α) (m : Nat) :
    (Vector.ofFn f)[m % 5]! = f ⟨m % 5, Nat.mod_lt _ (by omega)⟩ := by
  rw [getElem!_pos _ _ (by simp [Nat.mod_lt])]
  simp

theorem getElem!_ofFn25 {α : Type} [Inhabited α] (f : Fin 25 → α) (k : Nat) (hk : k < 25) :
    (Vector.ofFn f)[k]! = f ⟨k, hk⟩ := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  simp

theorem theta_getElem (A : Spec.Keccak.State) (k : Nat) (hk : k < 25) :
    (Spec.Keccak.theta A)[k]! =
      A[k]! ^^^ (Cs A ((k % 5 + 4) % 5) ^^^ Spec.Keccak.rotl (Cs A ((k % 5 + 1) % 5)) 1) := by
  have e1 : k % 5 + 5 * (k / 5 % 5) = k := by omega
  simp only [Spec.Keccak.theta, Spec.Keccak.ofLanes, getElem!_ofFn25 _ k hk, getElem!_ofFn_mod5,
    Spec.Keccak.lane, Cs]
  simp [e1]

theorem rho_getElem (A : Spec.Keccak.State) (k : Nat) (hk : k < 25) :
    (Spec.Keccak.rho A)[k]! = Spec.Keccak.rotl A[k]! Spec.Keccak.rhoOffsets[k]! := by
  have e1 : k % 5 + 5 * (k / 5 % 5) = k := by omega
  have e2 : k % 5 + 5 * (k / 5) = k := by omega
  simp only [Spec.Keccak.rho, Spec.Keccak.ofLanes, getElem!_ofFn25 _ k hk, Spec.Keccak.lane]
  simp [e1, e2]

/-- Source index of destination lane `k` under π. -/
abbrev srcI (k : Nat) : Nat := (k % 5 + 3 * (k / 5)) % 5 + 5 * (k % 5)

theorem pi_getElem (A : Spec.Keccak.State) (k : Nat) (hk : k < 25) :
    (Spec.Keccak.pi A)[k]! = A[srcI k]! := by
  simp only [Spec.Keccak.pi, Spec.Keccak.ofLanes, getElem!_ofFn25 _ k hk, Spec.Keccak.lane, srcI]
  simp

abbrev chiV (B : Spec.Keccak.State) (k : Nat) : UInt64 :=
  B[k]! ^^^ (~~~B[(k % 5 + 1) % 5 + 5 * (k / 5)]! &&& B[(k % 5 + 2) % 5 + 5 * (k / 5)]!)

theorem chi_getElem (A : Spec.Keccak.State) (k : Nat) (hk : k < 25) :
    (Spec.Keccak.chi A)[k]! = chiV A k := by
  have e1 : k % 5 + 5 * (k / 5 % 5) = k := by omega
  have e2 : k % 5 + 5 * (k / 5) = k := by omega
  simp only [Spec.Keccak.chi, Spec.Keccak.ofLanes, getElem!_ofFn25 _ k hk, Spec.Keccak.lane, chiV]
  have e3 : k / 5 % 5 = k / 5 := by omega
  simp [e1, e2, e3]

theorem iota_getElem (A : Spec.Keccak.State) (ir k : Nat) (hk : k < 25) :
    (Spec.Keccak.iota A ir)[k]! = if k = 0 then A[0]! ^^^ Spec.Keccak.RCs[ir]! else A[k]! := by
  rw [getElem!_pos _ _ (by simpa using hk)]
  change (A.setIfInBounds 0 (A[0]! ^^^ Spec.Keccak.RCs[ir]!))[k] = _
  rw [Vector.getElem_setIfInBounds hk]
  by_cases h : k = 0
  · subst h; simp
  · simp [h, Ne.symm h]
    exact (getElem!_pos A k (by simpa using hk)).symm

theorem Cs_toLanes (a : Array U64 25#usize) (j : Nat) (hj : j < 5) : Cs (toLanes a) j = Cf a j := by
  unfold Cs Cf
  rw [toLanes_ln a j (by omega), toLanes_ln a (j + 5) (by omega), toLanes_ln a (j + 10) (by omega),
    toLanes_ln a (j + 15) (by omega), toLanes_ln a (j + 20) (by omega)]

/-! ## θ -/

theorem c_loop (a : Array U64 25#usize) (c : Array U64 5#usize) :
    keccak.keccak_f1600_loop0_loop0 a c 0#usize ⦃ c' => ∀ j, j < 5 → ln c' j = Cf a j ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U64 5#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ j, j < 5 → ln p.1 j = if j < p.2.val then Cf a j else ln c j)
  · rintro ⟨c1, x⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop0.body]
    split
    · rename_i hx
      have hx5 : x.val < 5 := by scalar_tac
      step*
      have r0 := ln_idx a x x.val rfl i _ i_post2
      have r1 := ln_idx a i1 (x.val + 5) (by omega) i2 _ i2_post2
      have r2 := ln_idx a i4 (x.val + 10) (by omega) i5 _ i5_post2
      have r3 := ln_idx a i7 (x.val + 15) (by omega) i8 _ i8_post2
      have r4 := ln_idx a i10 (x.val + 20) (by omega) i11 _ i11_post2
      have key : toU64 i12 = Cf a x.val := by
        rw [xor_of_bv _ _ _ i12_post2, xor_of_bv _ _ _ i9_post2, xor_of_bv _ _ _ i6_post2,
          xor_of_bv _ _ _ i3_post2, r0, r1, r2, r3, r4]
        rfl
      refine ⟨by omega, fun j hj => ?_, by omega⟩
      rw [a1_post, ln_set c1 x i12 j (by scalar_tac), h2 j hj, x1_post]
      by_cases h : x.val = j
      · subst h; simp [key]
      · simp only [h, if_false]
        by_cases h' : j < x.val
        · simp [h', show j < x.val + 1 by omega]
        · simp [h', show ¬ j < x.val + 1 by omega]
    · rename_i hx
      have : x.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj
      rw [h2 j hj]; simp [this, hj]
  · refine ⟨by simp, fun j hj => by simp⟩

attribute [local step] rotl_spec

theorem d_inner (a : Array U64 25#usize) (x : Usize) (d : U64) (hx : x.val < 5) :
    keccak.keccak_f1600_loop0_loop1_loop0 a x d 0#usize ⦃ a' => ∀ k, k < 25 →
      ln a' k = if k % 5 = x.val then ln a k ^^^ toU64 d else ln a k ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop1_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k, k < 25 →
      ln p.1 k = if k % 5 = x.val ∧ k / 5 < p.2.val then ln a k ^^^ toU64 d else ln a k)
  · rintro ⟨ac, y⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop1_loop0.body]
    split
    · rename_i hy
      have hy5 : y.val < 5 := by scalar_tac
      step*
      have r0 := ln_idx ac i1 i1.val rfl i2 _ i2_post2
      have hb : ln ac i1.val = ln a i1.val := by
        rw [h2 _ (by omega), if_neg (by omega)]
      have key : toU64 i3 = ln a i1.val ^^^ toU64 d := by
        rw [xor_of_bv _ _ _ i3_post2, r0, hb]
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [a1_post, ln_set ac i1 i3 k (by scalar_tac), h2 k hk, y1_post]
      by_cases hk1 : i1.val = k
      · have e1 : k % 5 = x.val := by omega
        have e2 : k / 5 = y.val := by omega
        rw [if_pos hk1, key, hk1, if_pos ⟨e1, by omega⟩]
      · rw [if_neg hk1]
        by_cases hc : k % 5 = x.val ∧ k / 5 < y.val
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
    · rename_i hy
      have : y.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      rw [h2 k hk]
      by_cases h : k % 5 = x.val
      · rw [if_pos ⟨h, by omega⟩, if_pos h]
      · rw [if_neg (by omega), if_neg h]
  · refine ⟨by simp, fun k hk => by simp⟩

/-- `D[j]` of θ, from the array `a` whose column parities are `Cf a`. -/
def Dv (a : Array U64 25#usize) (j : Nat) : UInt64 :=
  Cf a ((j + 4) % 5) ^^^ Spec.Keccak.rotl (Cf a ((j + 1) % 5)) 1

theorem d_outer (a : Array U64 25#usize) (c : Array U64 5#usize) (hc : ∀ j, j < 5 → ln c j = Cf a j) :
    keccak.keccak_f1600_loop0_loop1 a c 0#usize ⦃ a' => ∀ k, k < 25 →
      ln a' k = ln a k ^^^ Dv a (k % 5) ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop1
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k, k < 25 →
      ln p.1 k = if k % 5 < p.2.val then ln a k ^^^ Dv a (k % 5) else ln a k)
  · rintro ⟨ac, x⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop1.body]
    split
    · rename_i hx
      have hx5 : x.val < 5 := by scalar_tac
      step*
      have r0 := ln_idx c i1 ((x.val + 4) % 5) (by omega) i2 _ i2_post2
      have r1 := ln_idx c i4 ((x.val + 1) % 5) (by omega) i5 _ i5_post2
      have key : toU64 d = Dv a x.val := by
        rw [xor_of_bv _ _ _ d_post2, i6_post, r0, r1, hc _ (by omega), hc _ (by omega)]
        rfl
      step with d_inner ac x d hx5 as ⟨a1, ha1⟩
      step*
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [ha1 k hk, h2 k hk, x1_post]
      by_cases h : k % 5 = x.val
      · rw [if_pos h, if_neg (by omega), if_pos (by omega), h, key]
      · rw [if_neg h]
        by_cases hc' : k % 5 < x.val
        · rw [if_pos hc', if_pos (by omega)]
        · rw [if_neg hc', if_neg (by omega)]
    · rename_i hx
      have : x.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      rw [h2 k hk, if_pos (by omega)]
  · refine ⟨by simp, fun k hk => by simp⟩

theorem theta_stage (a : Array U64 25#usize) (c : Array U64 5#usize) (hc : ∀ j, j < 5 → ln c j = Cf a j) :
    keccak.keccak_f1600_loop0_loop1 a c 0#usize ⦃ a' => toLanes a' = Spec.Keccak.theta (toLanes a) ⦄ := by
  apply WP.spec_mono (d_outer a c hc)
  intro a' h
  apply vec_ext25
  intro k hk
  rw [toLanes_ln a' k hk, h k hk, theta_getElem _ k hk, toLanes_ln a k hk,
    Cs_toLanes a _ (by omega), Cs_toLanes a _ (by omega)]
  rfl

/-! ## ρ and π -/

abbrev xsA (k : Nat) : Nat := (k % 5 + 3 * (k / 5)) % 5

/-- omega through the `xsA`/`srcI` abbreviations. -/
macro "om" : tactic => `(tactic| omega)

/-- The ρ-rotated source lane `s`. -/
def Rs (a : Array U64 25#usize) (s : Nat) : UInt64 :=
  Spec.Keccak.rotl (ln a s) Spec.Keccak.rhoOffsets[s]!

theorem RHO_len : keccak.RHO.val.length = 25 := keccak.RHO.property

theorem rho_idx (i : Usize) (hi : i.val < 25) (v : U32) (hv : v = keccak.RHO.val[i.val]'(by
    rw [RHO_len]; exact hi)) :
    v.val = Spec.Keccak.rhoOffsets[i.val]! ∧ v.val < 64 := by
  have h1 := RHO_eq ⟨i.val, hi⟩
  have h2 := RHO_lt ⟨i.val, hi⟩
  simp only [getElem!_pos keccak.RHO.val i.val (by rw [RHO_len]; exact hi)] at h1 h2
  subst hv
  exact ⟨h1, h2⟩

theorem rp_arith : ∀ x < 5, ∀ y < 5, ∀ k < 25,
    (k = y + 5 * ((2 * x + 3 * y) % 5) ↔ (xsA k = x ∧ k % 5 = y)) ∧
    (k = y + 5 * ((2 * x + 3 * y) % 5) → srcI k = x + 5 * y) := by
  decide +kernel

theorem rp_inner (a b : Array U64 25#usize) (x : Usize) (hx : x.val < 5) :
    keccak.keccak_f1600_loop0_loop2_loop0 a b x 0#usize ⦃ b' => ∀ k, k < 25 →
      ln b' k = if xsA k = x.val then Rs a (srcI k) else ln b k ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop2_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k, k < 25 →
      ln p.1 k = if xsA k = x.val ∧ k % 5 < p.2.val then Rs a (srcI k) else ln b k)
  · rintro ⟨bc, y⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop2_loop0.body]
    split
    · rename_i hy
      have hy5 : y.val < 5 := by scalar_tac
      step*
      · exact (rho_idx i3 (by omega) _ i4_post2).2
      obtain ⟨hv1, hv2⟩ := rho_idx i3 (by omega) _ i4_post2
      have r0 := ln_idx a i1 (x.val + 5 * y.val) (by omega) i2 _ i2_post2
      have key : toU64 i5 = Rs a (x.val + 5 * y.val) := by
        rw [i5_post, r0, hv1, show i3.val = x.val + 5 * y.val by omega]
        rfl
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [a1_post, ln_set bc i11 i5 k (by scalar_tac), h2 k hk, y1_post]
      have hi11 : i11.val = y.val + 5 * ((2 * x.val + 3 * y.val) % 5) := by omega
      have ar := rp_arith x.val hx y.val hy5 k hk
      by_cases hk1 : i11.val = k
      · have e1 : xsA k = x.val := by om
        have e2 : k % 5 = y.val := by om
        have e3 : srcI k = x.val + 5 * y.val := by om
        rw [if_pos hk1, if_pos ⟨e1, by omega⟩, e3, key]
      · rw [if_neg hk1]
        by_cases hc : xsA k = x.val ∧ k % 5 < y.val
        · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
        · rw [if_neg hc, if_neg (by om)]
    · rename_i hy
      have : y.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      rw [h2 k hk]
      by_cases h : xsA k = x.val
      · rw [if_pos ⟨h, by omega⟩, if_pos h]
      · rw [if_neg (by om), if_neg h]
  · refine ⟨by simp, fun k hk => by simp⟩

theorem rp_outer (a b : Array U64 25#usize) :
    keccak.keccak_f1600_loop0_loop2 a b 0#usize ⦃ b' => ∀ k, k < 25 → ln b' k = Rs a (srcI k) ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop2
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k, k < 25 →
      ln p.1 k = if xsA k < p.2.val then Rs a (srcI k) else ln b k)
  · rintro ⟨bc, x⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop2.body]
    split
    · rename_i hx
      have hx5 : x.val < 5 := by scalar_tac
      step with rp_inner a bc x hx5 as ⟨b1, hb1⟩
      step*
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [hb1 k hk, h2 k hk, x1_post]
      by_cases h : xsA k = x.val
      · rw [if_pos h, if_pos (by om)]
      · by_cases h' : xsA k < x.val
        · rw [if_neg h, if_pos h', if_pos (by om)]
        · rw [if_neg h, if_neg h', if_neg (by om)]
    · rename_i hx
      have : x.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      rw [h2 k hk, if_pos (by simp only [xsA]; omega)]
  · refine ⟨by simp, fun k hk => by simp⟩

theorem rp_stage (a b : Array U64 25#usize) :
    keccak.keccak_f1600_loop0_loop2 a b 0#usize ⦃ b' =>
      toLanes b' = Spec.Keccak.pi (Spec.Keccak.rho (toLanes a)) ⦄ := by
  apply WP.spec_mono (rp_outer a b)
  intro b' h
  apply vec_ext25
  intro k hk
  have hs : srcI k < 25 := by simp only [srcI]; omega
  rw [toLanes_ln b' k hk, h k hk, pi_getElem _ k hk, rho_getElem _ _ hs, toLanes_ln a _ hs]
  rfl

/-! ## χ -/

def Chi (b : Array U64 25#usize) (k : Nat) : UInt64 :=
  ln b k ^^^ (~~~ln b ((k % 5 + 1) % 5 + 5 * (k / 5)) &&& ln b ((k % 5 + 2) % 5 + 5 * (k / 5)))

theorem chi_inner (a b : Array U64 25#usize) (x : Usize) (hx : x.val < 5) :
    keccak.keccak_f1600_loop0_loop3_loop0 a b x 0#usize ⦃ a' => ∀ k, k < 25 →
      ln a' k = if k % 5 = x.val then Chi b k else ln a k ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop3_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k, k < 25 →
      ln p.1 k = if k % 5 = x.val ∧ k / 5 < p.2.val then Chi b k else ln a k)
  · rintro ⟨ac, y⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop3_loop0.body]
    split
    · rename_i hy
      have hy5 : y.val < 5 := by scalar_tac
      step*
      have r0 := ln_idx b i1 (x.val + 5 * y.val) (by omega) i2 _ i2_post2
      have r1 := ln_idx b i5 ((x.val + 1) % 5 + 5 * y.val) (by omega) i6 _ i6_post2
      have r2 := ln_idx b i10 ((x.val + 2) % 5 + 5 * y.val) (by omega) i11 _ i11_post2
      have h7 : toU64 i7 = ~~~toU64 _ := not_of_bv _ _ ((congrArg UScalar.bv i7_post).trans (UScalar.bv_not _))
      have key : toU64 i14 = Chi b (x.val + 5 * y.val) := by
        have e1 : (x.val + 5 * y.val) % 5 = x.val := by omega
        have e2 : (x.val + 5 * y.val) / 5 = y.val := by omega
        unfold Chi
        rw [e1, e2, xor_of_bv _ _ _ i14_post2, and_of_bv _ _ _ i12_post2, h7, r0, r1, r2]
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [a1_post, ln_set ac i13 i14 k (by scalar_tac), h2 k hk, y1_post]
      by_cases hk1 : i13.val = k
      · have e1 : k % 5 = x.val := by omega
        have e2 : k / 5 = y.val := by omega
        have e3 : k = x.val + 5 * y.val := by omega
        rw [if_pos hk1, e3, key, ← e3, if_pos ⟨e1, by omega⟩]
      · rw [if_neg hk1]
        by_cases hc : k % 5 = x.val ∧ k / 5 < y.val
        · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
        · rw [if_neg hc, if_neg (by omega)]
    · rename_i hy
      have : y.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      rw [h2 k hk]
      by_cases h : k % 5 = x.val
      · rw [if_pos ⟨h, by omega⟩, if_pos h]
      · rw [if_neg (by omega), if_neg h]
  · refine ⟨by simp, fun k hk => by simp⟩

theorem chi_outer (a b : Array U64 25#usize) :
    keccak.keccak_f1600_loop0_loop3 a b 0#usize ⦃ a' => ∀ k, k < 25 → ln a' k = Chi b k ⦄ := by
  unfold keccak.keccak_f1600_loop0_loop3
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k, k < 25 →
      ln p.1 k = if k % 5 < p.2.val then Chi b k else ln a k)
  · rintro ⟨ac, x⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0_loop3.body]
    split
    · rename_i hx
      have hx5 : x.val < 5 := by scalar_tac
      step with chi_inner ac b x hx5 as ⟨a1, ha1⟩
      step*
      refine ⟨by omega, fun k hk => ?_, by omega⟩
      rw [ha1 k hk, h2 k hk, x1_post]
      by_cases h : k % 5 = x.val
      · rw [if_pos h, if_pos (by omega)]
      · by_cases h' : k % 5 < x.val
        · rw [if_neg h, if_pos h', if_pos (by omega)]
        · rw [if_neg h, if_neg h', if_neg (by omega)]
    · rename_i hx
      have : x.val = 5 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      rw [h2 k hk, if_pos (by omega)]
  · refine ⟨by simp, fun k hk => by simp⟩

theorem chi_stage (a b : Array U64 25#usize) :
    keccak.keccak_f1600_loop0_loop3 a b 0#usize ⦃ a' =>
      toLanes a' = Spec.Keccak.chi (toLanes b) ⦄ := by
  apply WP.spec_mono (chi_outer a b)
  intro a' h
  apply vec_ext25
  intro k hk
  rw [toLanes_ln a' k hk, h k hk, chi_getElem _ k hk, chiV, toLanes_ln b k hk,
    toLanes_ln b _ (by omega), toLanes_ln b _ (by omega)]
  rfl

/-! ## ι and the 24 rounds -/

theorem RC_len : keccak.RC.val.length = 24 := keccak.RC.property

theorem RC_idx (i : Usize) (hi : i.val < 24) (v : U64) (hv : v = keccak.RC.val[i.val]'(by
    rw [RC_len]; exact hi)) : toU64 v = Spec.Keccak.RCs[i.val]! := by
  have h := RC_eq ⟨i.val, hi⟩
  rw [getElem!_pos keccak.RC.val i.val (by rw [RC_len]; exact hi)] at h
  subst hv
  have h' : (toU64 (keccak.RC.val[i.val]'(by rw [RC_len]; exact hi))).toNat =
      (Spec.Keccak.RCs[i.val]!).toNat := h
  first
    | exact UInt64.toNat_inj.mp h'
    | exact UInt64.ext (BitVec.eq_of_toNat_eq h')

/-- **Keccak-f[1600]**: the extracted permutation, on every state, returns the lanes of FIPS 202
Algorithm 7 applied to the input lanes; it neither fails nor diverges. -/
@[step]
theorem keccak_f1600_spec (a : Array U64 25#usize) :
    keccak.keccak_f1600 a ⦃ r => toLanes r = Spec.KeccakF1600 (toLanes a) ⦄ := by
  unfold keccak.keccak_f1600 keccak.keccak_f1600_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U64 25#usize × Usize) => 24 - p.2.val)
    (fun p => p.2.val ≤ 24 ∧ toLanes p.1 = (List.range p.2.val).foldl Spec.Keccak.Rnd (toLanes a))
  · rintro ⟨ac, r⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [keccak.keccak_f1600_loop0.body]
    split
    · rename_i hr
      have hr24 : r.val < 24 := by scalar_tac
      step with c_loop ac (Array.repeat 5#usize 0#u64) as ⟨c1, hc1⟩
      step with theta_stage ac c1 hc1 as ⟨a1, ha1⟩
      step with rp_stage a1 (Array.repeat 25#usize 0#u64) as ⟨b1, hb1⟩
      step with chi_stage a1 b1 as ⟨a2, ha2⟩
      step*
      have z : (0#usize).val = 0 := rfl
      have r0 := ln_idx a2 0#usize 0 z (by rw [len25 a2]; decide) _ i1_post2
      have r1 := RC_idx r hr24 _ i_post2
      have key : toU64 i2 = (toLanes a2)[0]! ^^^ Spec.Keccak.RCs[r.val]! := by
        rw [xor_of_bv _ _ _ i2_post2, r0, r1, toLanes_ln a2 0 (by omega)]
      refine ⟨by omega, ?_, by omega⟩
      rw [round1_post, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← h2,
        a3_post, toLanes_set, z, Spec.Keccak.Rnd, ← ha1, ← hb1, ← ha2, key]
      rfl
    · rename_i hr
      have : r.val = 24 := by scalar_tac
      simp only [WP.spec_ok]
      rw [h2, this]
      rfl
  · exact ⟨by simp, by simp⟩

end Proofs
