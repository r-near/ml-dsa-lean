import Spec.Keccak
import OcamlPq.Hash

/-!
# Keccak-f[1600]: our lane-level permutation against ocaml-pq's FIPS 202 transcription

Our `Spec.KeccakF1600` works on 25 `UInt64` lanes (`Spec.Keccak.State`).  ocaml-pq's `OcamlPq.Hash.FIPS202`
(`Hash/KeccakSpec.lean`) is an independent transcription of FIPS 202 on the state array `A[x, y, z]` and on
bit strings.  This file proves that one round, and then the permutation, agree, bit by bit:

* `toArr` reads a state of ours as ocaml-pq's `Array (BitVec 64)`, so that ocaml-pq's `laneBits` (the 1600-bit
  FIPS 202 string of a state), `toState` and `ofString_laneBits` apply.
* `rnd_eq`: `toState (toArr (Rnd A ir)) = FIPS202.Rnd (toState (toArr A)) ir` for `ir < 24`.
* `keccakF_eq`: `laneBits (toArr (KeccakF1600 A)) = FIPS202.KeccakF (laneBits (toArr A))`.
-/

open OcamlPq.Hash

namespace XSpec.KC

/-- Our state as ocaml-pq's 25-lane array. -/
def toArr (A : Spec.Keccak.State) : Array (BitVec 64) := Array.ofFn fun i : Fin 25 => (A[i]).toBitVec

@[simp] theorem toArr_size (A : Spec.Keccak.State) : (toArr A).size = 25 := by simp [toArr]

theorem toArr_getElem! (A : Spec.Keccak.State) (i : ℕ) (hi : i < 25) :
    (toArr A)[i]! = (A[i]!).toBitVec := by
  rw [getElem!_pos (toArr A) i (by simp [toArr]; omega), getElem!_pos A i hi]
  simp [toArr]

/-- Bit `z` of lane `x + 5 y`, as the FIPS 202 state array. -/
def S (A : Spec.Keccak.State) : FIPS202.State :=
  fun x y z => (A[x.val + 5 * y.val]!).toBitVec.getLsbD z.val

theorem S_eq_toState (A : Spec.Keccak.State) : S A = Keccak.toState (toArr A) := by
  funext x y z
  simp only [S, Keccak.toState]
  rw [toArr_getElem! A _ (by omega)]

/-! ### Reading the lanes of a state built by `ofLanes` -/

theorem getElem!_ofLanes (f : ℕ → ℕ → UInt64) (i : ℕ) (hi : i < 25) :
    (Spec.Keccak.ofLanes f)[i]! = f (i % 5) (i / 5) := by
  rw [getElem!_pos _ i hi]
  simp [Spec.Keccak.ofLanes]

theorem getElem!_ofLanes_xy (f : ℕ → ℕ → UInt64) (x y : Fin 5) :
    (Spec.Keccak.ofLanes f)[x.val + 5 * y.val]! = f x.val y.val := by
  rw [getElem!_ofLanes f _ (by omega)]
  congr 1 <;> omega

theorem lane_xy (A : Spec.Keccak.State) (x y : Fin 5) :
    Spec.Keccak.lane A x.val y.val = A[x.val + 5 * y.val]! := by
  have hx := x.isLt; have hy := y.isLt
  simp only [Spec.Keccak.lane, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

/-! ### `rotl` -/

/-- Bit `z` of our `rotl v n` (`n < 64`) is bit `z - n mod 64` of `v`: the FIPS 202 lane rotation. -/
theorem getLsbD_rotl (v : UInt64) (n : ℕ) (hn : n < 64) (z : Fin 64) :
    (Spec.Keccak.rotl v n).toBitVec.getLsbD z.val = v.toBitVec.getLsbD (z - Fin.ofNat 64 n).val := by
  simp only [Spec.Keccak.rotl, UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.getLsbD_or]
  have e1 : ((n % 64).toUInt64.toBitVec % 64).toNat = n := by
    simp [Nat.toUInt64, UInt64.toBitVec_ofNat, BitVec.toNat_umod, Nat.mod_eq_of_lt hn]
  have e2 : ((64 - n % 64).toUInt64.toBitVec % 64).toNat = (64 - n) % 64 := by
    simp [Nat.toUInt64, UInt64.toBitVec_ofNat, BitVec.toNat_umod, Nat.mod_eq_of_lt hn]
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', e1, e2]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  have hz := z.isLt
  have hfin : (z - Fin.ofNat 64 n).val = if z.val < n then 64 - n + z.val else z.val - n := by
    rw [Fin.sub_def]
    simp only [Fin.val_ofNat, Nat.mod_eq_of_lt hn]
    split <;> omega
  rw [hfin]
  by_cases h : z.val < n
  · have hn0 : n ≠ 0 := by omega
    have : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
    simp [h, this, hz]
  · simp only [h, ite_false]
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have : (64 - n) % 64 = 64 - n := Nat.mod_eq_of_lt (by omega)
      have h1 : v.toBitVec.getLsbD (64 - n + z.val) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [h, this, hz, h1]

theorem getElem!_vec5 (f : Fin 5 → UInt64) (i : ℕ) (hi : i < 5) : (Vector.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i hi]; simp

theorem lane_get (A : Spec.Keccak.State) (j k : ℕ) (hj : j < 5) (hk : k < 5) :
    Spec.Keccak.lane A j k = A[j + 5 * k]! := by
  simp only [Spec.Keccak.lane, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk]

theorem fin5_sub_one : ∀ x : Fin 5, (x - 1 : Fin 5).val = (x.val + 4) % 5 := by decide
theorem fin5_add_one : ∀ x : Fin 5, (x + 1 : Fin 5).val = (x.val + 1) % 5 := by decide

theorem getElem!_vec5_mod (f : Fin 5 → UInt64) (i : ℕ) :
    (Vector.ofFn f)[i % 5]! = f ⟨i % 5, Nat.mod_lt _ (by decide)⟩ :=
  getElem!_vec5 f _ (Nat.mod_lt _ (by decide))

theorem lane_mod (A : Spec.Keccak.State) (j k : ℕ) (hk : k < 5) :
    Spec.Keccak.lane A (j % 5) k = A[j % 5 + 5 * k]! :=
  lane_get A _ _ (Nat.mod_lt _ (by decide)) hk

theorem lane_mod' (A : Spec.Keccak.State) (j k : ℕ) (hk : k < 5) :
    Spec.Keccak.lane A j k = A[j % 5 + 5 * k]! := by
  rw [← lane_mod A j k hk]; simp [Spec.Keccak.lane]

theorem theta_eq (A : Spec.Keccak.State) : S (Spec.Keccak.theta A) = FIPS202.theta (S A) := by
  funext x y z
  simp only [S, Spec.Keccak.theta, FIPS202.theta]
  rw [getElem!_ofLanes_xy, lane_xy]
  simp only [getElem!_vec5_mod, lane_mod _ _ _ (by decide : 0 < 5), lane_mod _ _ _ (by decide : 1 < 5),
    lane_mod _ _ _ (by decide : 2 < 5), lane_mod _ _ _ (by decide : 3 < 5), lane_mod _ _ _ (by decide : 4 < 5)]
  rw [getElem!_vec5 _ x.val x.isLt]
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  rw [getLsbD_rotl _ 1 (by decide) z]
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor, ← fin5_sub_one, ← fin5_add_one]
  rfl

/-! ### ρ, π, χ, ι -/

/-- Our ρ offsets are ocaml-pq's `rotation` table (both are FIPS 202 Table 2). -/
theorem rhoOffsets_eq_rotation : ∀ i : Fin 25, Spec.Keccak.rhoOffsets[i.val]! = Keccak.rotation[i.val]! := by
  decide +kernel

theorem rotation_lt (i : ℕ) (hi : i < 25) : Keccak.rotation[i]! < 64 := Keccak.rotation_lt i hi

theorem rho_eq (A : Spec.Keccak.State) : S (Spec.Keccak.rho A) = FIPS202.rho (S A) := by
  funext x y z
  have hxy : x.val + 5 * y.val < 25 := by have := x.isLt; have := y.isLt; omega
  simp only [S]
  rw [Keccak.rho_eq]
  simp only [S, Spec.Keccak.rho]
  rw [getElem!_ofLanes_xy, lane_xy]
  have h1 := rhoOffsets_eq_rotation ⟨x.val + 5 * y.val, hxy⟩
  simp only at h1
  rw [h1, getLsbD_rotl _ _ (rotation_lt _ hxy)]

theorem fin5_add_mul : ∀ x y : Fin 5, (x + 3 * y : Fin 5).val = (x.val + 3 * y.val) % 5 := by decide

theorem pi_eq (A : Spec.Keccak.State) : S (Spec.Keccak.pi A) = FIPS202.pi (S A) := by
  funext x y z
  simp only [S, Spec.Keccak.pi, FIPS202.pi]
  rw [getElem!_ofLanes_xy, lane_mod' _ _ _ x.isLt, ← fin5_add_mul]

theorem fin5_add_two : ∀ x : Fin 5, (x + 2 : Fin 5).val = (x.val + 2) % 5 := by decide

theorem chi_eq (A : Spec.Keccak.State) : S (Spec.Keccak.chi A) = FIPS202.chi (S A) := by
  funext x y z
  simp only [S, Spec.Keccak.chi, FIPS202.chi]
  rw [getElem!_ofLanes_xy, lane_xy, lane_mod' _ _ _ y.isLt, lane_mod' _ _ _ y.isLt,
    ← fin5_add_one, ← fin5_add_two]
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not, BitVec.getLsbD_xor,
    BitVec.getLsbD_and, BitVec.getLsbD_not, z.isLt, decide_true, Bool.true_and, Bool.xor_true]

theorem getElem!_set!_zero (A : Spec.Keccak.State) (v : UInt64) (j : ℕ) (hj : j < 25) :
    (A.set! 0 v)[j]! = if j = 0 then v else A[j]! := by
  rw [getElem!_pos _ j hj, getElem!_pos A j hj]
  simp only [Vector.getElem_set! hj]
  by_cases h : j = 0
  · subst h; simp
  · simp [h, Ne.symm h]

/-- Our round constants are ocaml-pq's `round_constants` (kernel check over the 24 rounds). -/
theorem RCs_eq_roundConstants : ∀ ir : Fin 24,
    (Spec.Keccak.RCs[ir.val]!).toBitVec = Keccak.roundConstants[ir.val]! := by
  decide +kernel

theorem iota_eq (A : Spec.Keccak.State) (ir : ℕ) (hir : ir < 24) :
    S (Spec.Keccak.iota A ir) = FIPS202.iota (S A) ir := by
  funext x y z
  have hxy : x.val + 5 * y.val < 25 := by have := x.isLt; have := y.isLt; omega
  simp only [S, Spec.Keccak.iota, FIPS202.iota]
  rw [getElem!_set!_zero _ _ _ hxy]
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_zero, mul_zero, add_zero, and_self, ite_true]
    rw [UInt64.toBitVec_xor, BitVec.getLsbD_xor, RCs_eq_roundConstants ⟨ir, hir⟩,
      Keccak.roundConstants_eq_RC ⟨ir, hir⟩ z]
  · have h1 : ¬ (x.val + 5 * y.val = 0) := by
      intro h0
      exact h ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
    simp only [h1, h, ite_false]

theorem rnd_eq (A : Spec.Keccak.State) (ir : ℕ) (hir : ir < 24) :
    S (Spec.Keccak.Rnd A ir) = FIPS202.Rnd (S A) ir := by
  simp only [Spec.Keccak.Rnd, FIPS202.Rnd]
  rw [iota_eq _ _ hir, chi_eq, pi_eq, rho_eq, theta_eq]

/-! ### The permutation -/

theorem S_foldl (l : List ℕ) (hl : ∀ r ∈ l, r < 24) (A : Spec.Keccak.State) :
    S (l.foldl Spec.Keccak.Rnd A) = l.foldl FIPS202.Rnd (S A) := by
  induction l generalizing A with
  | nil => rfl
  | cons r l ih =>
    simp only [List.foldl_cons]
    rw [ih (fun r' hr' => hl r' (List.mem_cons_of_mem _ hr')), rnd_eq _ _ (hl r (List.mem_cons_self ..))]

/-- **One permutation.**  The FIPS 202 state array of our `KeccakF1600 A` is `Rnd` iterated over the rounds
`0, …, 23` of ocaml-pq's `FIPS202.Rnd` on the state array of `A`. -/
theorem S_keccakF (A : Spec.Keccak.State) :
    S (Spec.KeccakF1600 A) = (List.range' 0 24).foldl FIPS202.Rnd (S A) := by
  unfold Spec.KeccakF1600
  rw [S_foldl _ (fun r hr => List.mem_range.mp hr), List.range_eq_range']

/-- **Keccak-f[1600], bit strings.**  The 1600-bit FIPS 202 string of `KeccakF1600 A` (bit `64 i + z` is bit
`z` of lane `i`) is ocaml-pq's `FIPS202.KeccakF` of the string of `A`. -/
theorem keccakF_eq (A : Spec.Keccak.State) :
    Keccak.laneBits (toArr (Spec.KeccakF1600 A)) = FIPS202.KeccakF (Keccak.laneBits (toArr A)) := by
  rw [FIPS202.KeccakF, FIPS202.KeccakP, Keccak.ofString_laneBits, ← S_eq_toState,
    show 12 + 2 * FIPS202.ℓ - 24 = 0 by decide, ← S_keccakF, S_eq_toState, Keccak.toString_toState]

end XSpec.KC
