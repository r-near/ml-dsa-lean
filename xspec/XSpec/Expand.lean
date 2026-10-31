import XSpec.SampleBall

/-!
# `ExpandA` and `ExpandS` (Algorithms 32 and 33)

Ours: `Spec.ExpandA p F ρ` and `Spec.ExpandS p F ρ` run the fuel-bounded samplers once per entry and return `none`
as soon as one of them runs out of fuel.  Theirs: `expandA G ρ r s = rejNTTPoly (G (ρ ‖ s ‖ r))` and
`expandS H P ρ = (r ↦ rejBoundedPoly η (H (ρ ‖ r)), r ↦ rejBoundedPoly η (H (ρ ‖ r + ℓ)))`, total functions on
the (infinite) streams that are `0` when the sampler diverges.

* Ours to theirs (`expandA_ours_to_theirs`, `expandS_ours_to_theirs`): if ours returns, every entry's sampler
  terminates on ocaml-pq's side (`ExpandATerm`, `ExpandSTerm`) and ocaml-pq's total function takes the same value.
* Theirs to ours (`expandA_theirs_to_ours`, `expandS_theirs_to_ours`): if every entry's sampler terminates on
  ocaml-pq's side, ours returns for every large enough fuel.

The loops are ported from `lean/Proofs/SampleA.lean` and `SampleS.lean` (`Prod` states instead of `MProd`).
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

/-! ## Fuel-exact and eventual forms of the `RejNTTPoly` / `RejBoundedPoly` bridges -/

namespace RN

/-- Ours at fuel `F` against theirs at fuel `F + 1`, in the direction theirs to ours. -/
theorem rejNTT_theirs_to_ours_at (ρ : List UInt8) (F : ℕ) (b : ℕ → ℤ)
    (h : OcamlPq.MLDSAAlg.rejNTTPolyLoop (oursShake128 (u8ToBytes ρ)) (F + 1) 0 0 (fun _ => 0) = some b) :
    ∃ a, Spec.RejNTTPoly F ρ = some a ∧ canon a = b := by
  rw [loop_eq_foldS, rel_fold ρ F F le_rfl] at h
  by_cases hfin : 256 ≤ (stA (SHAKE128 ρ (3 * F)) F).2
  · rw [if_pos hfin] at h
    exact ⟨_, rej_some_of_fin ρ F hfin, Option.some.inj h⟩
  · rw [if_neg hfin] at h; cases h

/-- If ocaml-pq's `RejNTTPoly` returns `b` on the SHAKE128 stream of `ρ`, then ours returns `a` with `canon a = b`
for every sufficiently large fuel. -/
theorem rejNTT_eventually (ρ : List UInt8) (b : ℕ → ℤ)
    (h : OcamlPq.MLDSAAlg.RejNTTPolyReturns (oursShake128 (u8ToBytes ρ)) b) :
    ∃ F0, ∀ F, F0 ≤ F → ∃ a, Spec.RejNTTPoly F ρ = some a ∧ canon a = b := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun F hF => rejNTT_theirs_to_ours_at ρ F b (OcamlPq.MLDSAAlg.rejNTTPolyLoop_mono hf (by omega))⟩

end RN

namespace RB

theorem rejBounded_theirs_to_ours_at (p : Spec.Params) (ρ : List UInt8) (F : ℕ) (b : ℕ → ℤ)
    (h : OcamlPq.MLDSAAlg.rejBoundedLoop p.η (oursShake256 (u8ToBytes ρ)) (F + 1) 0 (0, fun _ => 0) = some b) :
    ∃ a, Spec.RejBoundedPoly p F ρ = some a ∧ rfn a = b := by
  have hT : (Spec.H ρ F).length = F := Spec.SHAKE256_length ρ F
  have := loopB_eq p.η (oursShake256 (u8ToBytes ρ)) (Spec.H ρ F) F 0 (Vector.replicate 256 0, 0) (by
    intro i _ hi
    rw [oursShake256_val ρ F i (by omega), bang_getD _ i (by omega)]
    rfl)
  simp only [rfn_replicate] at this
  rw [this] at h
  by_cases hfin : 256 ≤ (rbRun p.η (Spec.H ρ F) (Vector.replicate 256 0, 0) 0 F).2
  · rw [if_pos hfin] at h
    refine ⟨_, ?_, Option.some.inj h⟩
    rw [RejBoundedPoly_eq, if_neg (by omega)]
  · rw [if_neg hfin] at h; cases h

theorem rejBounded_eventually (p : Spec.Params) (ρ : List UInt8) (b : ℕ → ℤ)
    (h : OcamlPq.MLDSAAlg.RejBoundedReturns p.η (oursShake256 (u8ToBytes ρ)) b) :
    ∃ F0, ∀ F, F0 ≤ F → ∃ a, Spec.RejBoundedPoly p F ρ = some a ∧ rfn a = b := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun F hF => rejBounded_theirs_to_ours_at p ρ F b (OcamlPq.MLDSAAlg.rejBoundedLoop_mono hf (by omega))⟩

end RB

/-! ## Small tools -/

/-- A common threshold for finitely many eventually-true statements. -/
theorem eventually_forall_lt {P : ℕ → ℕ → Prop} (n : ℕ) (h : ∀ i, i < n → ∃ F0, ∀ F, F0 ≤ F → P i F) :
    ∃ F0, ∀ F, F0 ≤ F → ∀ i, i < n → P i F := by
  induction n with
  | zero => exact ⟨0, fun _ _ i hi => by omega⟩
  | succ n ih =>
    obtain ⟨F1, h1⟩ := ih (fun i hi => h i (by omega))
    obtain ⟨F2, h2⟩ := h n (by omega)
    refine ⟨max F1 F2, fun F hF i hi => ?_⟩
    by_cases hin : i < n
    · exact h1 F (le_trans (le_max_left _ _) hF) i hin
    · have : i = n := by omega
      subst this
      exact h2 F (le_trans (le_max_right _ _) hF)

theorem u8ToBytes_IntegerToBytes (x α : ℕ) :
    u8ToBytes (Spec.IntegerToBytes x α) = OcamlPq.MLDSAAlg.integerToBytes x α := integerToBytes_alg_eq x α

theorem foldlM_isSome {α : Type} (f : α → ℕ → Option α) (l : List ℕ) (hf : ∀ a, ∀ x ∈ l, (f a x).isSome) :
    ∀ a, ((l.foldlM f a).isSome) := by
  induction l with
  | nil => intro a; simp
  | cons x l ih =>
    intro a
    rw [List.foldlM_cons]
    cases hx : f a x with
    | none => have := hf a x (by simp); rw [hx] at this; simp at this
    | some b =>
      exact ih (fun a y hy => hf a y (List.mem_cons_of_mem _ hy)) b

theorem foldlM_range'_succ {α : Type} (f : α → ℕ → Option α) (init : α) (n : ℕ) :
    (List.range' 0 (n + 1)).foldlM f init = (List.range' 0 n).foldlM f init >>= fun a => f a n := by
  simp [List.range'_concat, List.foldlM_append]

/-! ## ExpandA -/

namespace EA

/-- The seed `ρ ‖ s ‖ r` of entry `(r, s)`. -/
def pSeed (ρ : List UInt8) (r s : Nat) : List UInt8 := ρ ++ IntegerToBytes s 1 ++ IntegerToBytes r 1

/-- A `forIn` whose body either yields (`some`) or exits early (`none`) is a `foldlM` in `Option`. -/
theorem forIn_opt {α β γ : Type} (f : β → α → Option β)
    (g : α → (Option (Option γ) × β) → Id (ForInStep (Option (Option γ) × β)))
    (hg1 : ∀ x st b, f st.2 x = some b → g x st = pure (ForInStep.yield (none, b)))
    (hg2 : ∀ x st, f st.2 x = none → ∃ junk, g x st = pure (ForInStep.done (some none, junk))) :
    ∀ (l : List α) (init : β),
      (∀ b, l.foldlM f init = some b → forIn (m := Id) l ((none, init) : Option (Option γ) × β) g = (none, b)) ∧
      (l.foldlM f init = none → (forIn (m := Id) l ((none, init) : Option (Option γ) × β) g).1 = some none) := by
  intro l
  induction l with
  | nil => intro init; exact ⟨fun b hb => by simp at hb; subst hb; rfl, fun h => by simp at h⟩
  | cons x l ih =>
    intro init
    rcases hf : f init x with _ | b0
    · obtain ⟨junk, hj⟩ := hg2 x (none, init) hf
      refine ⟨fun b hb => by simp [hf] at hb, fun _ => ?_⟩
      rw [List.forIn_cons, hj]
      rfl
    · have hj := hg1 x (none, init) b0 hf
      obtain ⟨ih1, ih2⟩ := ih b0
      refine ⟨fun b hb => ?_, fun hb => ?_⟩
      · rw [List.forIn_cons, hj]
        simp only [pure_bind]
        exact ih1 b (by simpa [hf] using hb)
      · rw [List.forIn_cons, hj]
        simp only [pure_bind]
        exact ih2 (by simpa [hf] using hb)

abbrev ESt (p : Spec.Params) :=
  Option (Option (Vector (Vector Poly p.ℓ) p.k)) × Vector (Vector Poly p.ℓ) p.k

def innerF (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r : Nat) (A : Vector (Vector Poly p.ℓ) p.k)
    (s : Nat) : Option (Vector (Vector Poly p.ℓ) p.k) :=
  match Spec.RejNTTPoly fuel (pSeed ρ r s) with
  | some a => some (A.set! r (A[r]!.set! s a))
  | none => none

def outerF (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (A : Vector (Vector Poly p.ℓ) p.k) (r : Nat) :
    Option (Vector (Vector Poly p.ℓ) p.k) :=
  (List.range' 0 p.ℓ).foldlM (innerF p fuel ρ r) A

def eIn (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r s : Nat) (st : ESt p) : Id (ForInStep (ESt p)) :=
  match Spec.RejNTTPoly fuel (pSeed ρ r s) with
  | some a => pure (ForInStep.yield (none, st.2.set! r (st.2[r]!.set! s a)))
  | x => pure (ForInStep.done (some none, st.2))

def eOut (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r : Nat) (st : ESt p) : Id (ForInStep (ESt p)) := do
  let r' ← forIn (m := Id) (List.range' 0 p.ℓ) ((none, st.2) : ESt p) (eIn p fuel ρ r)
  Break.runK r'.1 (fun _ => pure (ForInStep.yield (none, r'.2))) (fun a => pure (ForInStep.done (some a, r'.2)))

def eOutR (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (r : Nat) (st : ESt p) : Id (ForInStep (ESt p)) := do
  let r' ← forIn (m := Id) [0:p.ℓ] ((none, st.2) : ESt p) (eIn p fuel ρ r)
  Break.runK r'.1 (fun _ => pure (ForInStep.yield (none, r'.2))) (fun a => pure (ForInStep.done (some a, r'.2)))

theorem expandA_unfoldR (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.ExpandA p fuel ρ =
      (let r := forIn (m := Id) [0:p.k]
          ((none, Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) : ESt p) (eOutR p fuel ρ)
       Break.runK r.1 (fun _ => some r.2) (fun a => a)) := rfl

theorem eOutR_eq (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) : eOutR p fuel ρ = eOut p fuel ρ := by
  funext r st
  have hs2 : [0:p.ℓ].size = p.ℓ := by simp [Std.Legacy.Range.size]
  unfold eOutR eOut
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', hs2]

theorem expandA_unfold (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.ExpandA p fuel ρ =
      (let r := forIn (m := Id) (List.range' 0 p.k)
          ((none, Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) : ESt p) (eOut p fuel ρ)
       Break.runK r.1 (fun _ => some r.2) (fun a => a)) := by
  have hs1 : [0:p.k].size = p.k := by simp [Std.Legacy.Range.size]
  rw [expandA_unfoldR, eOutR_eq]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', hs1]

theorem expandA_eq (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.ExpandA p fuel ρ =
      (List.range' 0 p.k).foldlM (outerF p fuel ρ) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) := by
  have hin : ∀ r (A : Vector (Vector Poly p.ℓ) p.k),
      (∀ b, (List.range' 0 p.ℓ).foldlM (innerF p fuel ρ r) A = some b →
        forIn (m := Id) (List.range' 0 p.ℓ) ((none, A) : ESt p) (eIn p fuel ρ r) = (none, b)) ∧
      ((List.range' 0 p.ℓ).foldlM (innerF p fuel ρ r) A = none →
        (forIn (m := Id) (List.range' 0 p.ℓ) ((none, A) : ESt p) (eIn p fuel ρ r)).1 = some none) := by
    intro r A
    refine forIn_opt (innerF p fuel ρ r) (eIn p fuel ρ r) ?_ ?_ (List.range' 0 p.ℓ) A
    · intro s st b h
      unfold innerF at h
      unfold eIn
      rcases hr : Spec.RejNTTPoly fuel (pSeed ρ r s) with _ | a
      · simp [hr] at h
      · simp only [hr, Option.some.injEq] at h
        simp only [hr, h]
    · intro s st h
      unfold innerF at h
      unfold eIn
      rcases hr : Spec.RejNTTPoly fuel (pSeed ρ r s) with _ | a
      · exact ⟨st.2, by simp only [hr]⟩
      · simp [hr] at h
  rw [expandA_unfold]
  have hout := forIn_opt (γ := Vector (Vector Poly p.ℓ) p.k) (outerF p fuel ρ) (eOut p fuel ρ) ?_ ?_
    (List.range' 0 p.k) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero))
  · rcases hf : (List.range' 0 p.k).foldlM (outerF p fuel ρ) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero)) with _ | b
    · simp only [hout.2 hf, Break.runK]
    · simp only [hout.1 b hf, Break.runK]
  · intro r st b h
    unfold outerF at h
    unfold eOut
    rw [(hin r st.2).1 b h]
    rfl
  · intro r st h
    unfold outerF at h
    unfold eOut
    have := (hin r st.2).2 h
    rcases hI : forIn (m := Id) (List.range' 0 p.ℓ) ((none, st.2) : ESt p) (eIn p fuel ρ r) with ⟨f1, s1⟩
    rw [hI] at this
    simp only at this
    subst this
    exact ⟨s1, rfl⟩

/-! ### The cells of the matrix -/

theorem inner_inv (p : Spec.Params) (F : ℕ) (ρ : List UInt8) (r : ℕ) (hr : r < p.k) :
    ∀ (n : ℕ), n ≤ p.ℓ → ∀ (A B : Vector (Vector Poly p.ℓ) p.k),
      (List.range' 0 n).foldlM (innerF p F ρ r) A = some B →
      (∀ s, s < n → Spec.RejNTTPoly F (pSeed ρ r s) = some (B[r]!)[s]!) ∧
      (∀ r', r' ≠ r → B[r']! = A[r']!) ∧ (∀ s, n ≤ s → (B[r]!)[s]! = (A[r]!)[s]!) := by
  intro n
  induction n with
  | zero =>
    intro _ A B h
    simp only [List.range'_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨fun s hs => by omega, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro hn A B h
    rw [foldlM_range'_succ] at h
    obtain ⟨Y, hY, hB⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨i1, i2, i3⟩ := ih (by omega) A Y hY
    unfold innerF at hB
    rcases hq : Spec.RejNTTPoly F (pSeed ρ r n) with _ | a
    · rw [hq] at hB; cases hB
    · rw [hq] at hB
      simp only [Option.some.injEq] at hB
      subst hB
      have hrow : (Y.set! r (Y[r]!.set! n a))[r]! = Y[r]!.set! n a := vset_get_eq _ _ hr _
      refine ⟨fun s hs => ?_, fun r' hr' => ?_, fun s hs => ?_⟩
      · rw [hrow]
        by_cases hsn : s = n
        · subst hsn
          rw [vset_get_eq _ _ (by omega)]
          exact hq
        · rw [vset_get_ne _ _ _ _ (Ne.symm hsn)]
          exact i1 s (by omega)
      · rw [vset_get_ne _ _ _ _ (Ne.symm hr')]
        exact i2 r' hr'
      · rw [hrow, vset_get_ne _ _ _ _ (by omega)]
        exact i3 s (by omega)

theorem outer_inv (p : Spec.Params) (F : ℕ) (ρ : List UInt8) :
    ∀ (n : ℕ), n ≤ p.k → ∀ (A B : Vector (Vector Poly p.ℓ) p.k),
      (List.range' 0 n).foldlM (outerF p F ρ) A = some B →
      (∀ r, r < n → ∀ s, s < p.ℓ → Spec.RejNTTPoly F (pSeed ρ r s) = some (B[r]!)[s]!) ∧
      (∀ r, n ≤ r → B[r]! = A[r]!) := by
  intro n
  induction n with
  | zero =>
    intro _ A B h
    simp only [List.range'_zero, List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨fun r hr => by omega, fun _ _ => rfl⟩
  | succ n ih =>
    intro hn A B h
    rw [foldlM_range'_succ] at h
    obtain ⟨Y, hY, hB⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨o1, o2⟩ := ih (by omega) A Y hY
    unfold outerF at hB
    obtain ⟨i1, i2, -⟩ := inner_inv p F ρ n (by omega) p.ℓ le_rfl Y B hB
    refine ⟨fun r hr s hs => ?_, fun r hr => ?_⟩
    · by_cases hrn : r = n
      · subst hrn
        exact i1 s hs
      · rw [i2 r hrn]
        exact o1 r (by omega) s hs
    · rw [i2 r (by omega)]
      exact o2 r (by omega)

theorem ExpandA_cells (p : Spec.Params) (F : ℕ) (ρ : List UInt8) (A : Vector (Vector Poly p.ℓ) p.k)
    (h : Spec.ExpandA p F ρ = some A) :
    ∀ r, r < p.k → ∀ s, s < p.ℓ → Spec.RejNTTPoly F (pSeed ρ r s) = some (A[r]!)[s]! := by
  rw [expandA_eq] at h
  exact (outer_inv p F ρ p.k le_rfl _ A h).1

theorem ExpandA_of_cells (p : Spec.Params) (F : ℕ) (ρ : List UInt8)
    (h : ∀ r, r < p.k → ∀ s, s < p.ℓ → ∃ a, Spec.RejNTTPoly F (pSeed ρ r s) = some a) :
    ∃ A, Spec.ExpandA p F ρ = some A := by
  rw [expandA_eq]
  have := foldlM_isSome (outerF p F ρ) (List.range' 0 p.k) (fun A r hr => by
    have hr' : r < p.k := by simpa using (List.mem_range'_1.mp hr).2
    unfold outerF
    exact foldlM_isSome _ _ (fun A' s hs => by
      have hs' : s < p.ℓ := by simpa using (List.mem_range'_1.mp hs).2
      obtain ⟨a, ha⟩ := h r hr' s hs'
      unfold innerF
      rw [ha]; rfl) A) (Vector.replicate p.k (Vector.replicate p.ℓ Poly.zero))
  exact Option.isSome_iff_exists.mp this

theorem u8ToBytes_pSeed (ρ : List UInt8) (r s : ℕ) :
    u8ToBytes (pSeed ρ r s) = u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes s 1 ++ OcamlPq.MLDSAAlg.integerToBytes r 1 := by
  simp only [pSeed, u8ToBytes_append, integerToBytes_alg_eq]

end EA

/-- Every `RejNTTPoly` call of `ExpandA(ρ)` terminates on ocaml-pq's side (the premise of `expandMatrix_spec`). -/
def ExpandATerm (p : Spec.Params) (ρ : List UInt8) : Prop :=
  ∀ r < p.k, ∀ s < p.ℓ, ∃ a, OcamlPq.MLDSAAlg.RejNTTPolyReturns
    (oursShake128 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes s 1 ++ OcamlPq.MLDSAAlg.integerToBytes r 1)) a

/-- **ExpandA, ours to theirs.**  If `ExpandA F ρ = some A`, every `RejNTTPoly` call of ocaml-pq's `ExpandA`
terminates (on our SHAKE128), and each entry of `A` is ocaml-pq's `expandA`. -/
theorem expandA_ours_to_theirs (p : Spec.Params) (F : ℕ) (ρ : List UInt8) (A : Vector (Vector Poly p.ℓ) p.k)
    (h : Spec.ExpandA p F ρ = some A) :
    ExpandATerm p ρ ∧ ∀ r < p.k, ∀ s < p.ℓ,
      canon ((A[r]!)[s]!) = OcamlPq.MLDSAAlg.expandA oursShake128 (u8ToBytes ρ) r s := by
  have cells := EA.ExpandA_cells p F ρ A h
  have key : ∀ r < p.k, ∀ s < p.ℓ, OcamlPq.MLDSAAlg.RejNTTPolyReturns
      (oursShake128 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes s 1 ++ OcamlPq.MLDSAAlg.integerToBytes r 1))
      (canon ((A[r]!)[s]!)) := by
    intro r hr s hs
    have := RN.rejNTT_ours_to_theirs _ _ _ (cells r hr s hs)
    rwa [EA.u8ToBytes_pSeed] at this
  refine ⟨fun r hr s hs => ⟨_, key r hr s hs⟩, fun r hr s hs => ?_⟩
  unfold OcamlPq.MLDSAAlg.expandA
  exact OcamlPq.MLDSAAlg.RejNTTPolyReturns.eq (key r hr s hs)

/-- **ExpandA, theirs to ours.**  If every `RejNTTPoly` call of ocaml-pq's `ExpandA` terminates, then ours
returns for every sufficiently large fuel. -/
theorem expandA_theirs_to_ours (p : Spec.Params) (ρ : List UInt8) (hT : ExpandATerm p ρ) :
    ∃ F0, ∀ F, F0 ≤ F → ∃ A, Spec.ExpandA p F ρ = some A := by
  have h1 : ∀ r, r < p.k → ∃ F0, ∀ F, F0 ≤ F → ∀ s, s < p.ℓ → ∃ a, Spec.RejNTTPoly F (EA.pSeed ρ r s) = some a := by
    intro r hr
    apply eventually_forall_lt (P := fun s F => ∃ a, Spec.RejNTTPoly F (EA.pSeed ρ r s) = some a)
    intro s hs
    obtain ⟨b, hb⟩ := hT r hr s hs
    rw [← EA.u8ToBytes_pSeed] at hb
    obtain ⟨F0, hF0⟩ := RN.rejNTT_eventually _ _ hb
    exact ⟨F0, fun F hF => by obtain ⟨a, ha, -⟩ := hF0 F hF; exact ⟨a, ha⟩⟩
  obtain ⟨F0, hF0⟩ := eventually_forall_lt (P := fun r F => ∀ s, s < p.ℓ → ∃ a, Spec.RejNTTPoly F (EA.pSeed ρ r s) = some a)
    p.k h1
  exact ⟨F0, fun F hF => EA.ExpandA_of_cells p F ρ (fun r hr => hF0 F hF r hr)⟩

/-! ## ExpandS -/

namespace ES

abbrev FS (β : Type) (n : Nat) := Option (Option β) × Vector RPoly n

def fillBody {β : Type} {n : Nat} (f : Nat → Option RPoly) (r : Nat) (st : FS β n) :
    Id (ForInStep (FS β n)) :=
  match f r with
  | some a => pure (ForInStep.yield (none, st.2.set! r a))
  | none => pure (ForInStep.done (some none, st.2))

theorem fill_forIn {β : Type} {n : Nat} (f : Nat → Option RPoly) (m : Nat) :
    ∀ (s : Nat) (v : Vector RPoly n), ∃ w : Vector RPoly n,
      ((forIn (m := Id) (List.range' s m) ((none, v) : FS β n) (fillBody f) = (none, w) ∧
        (∀ i, i < m → ∀ (hi : s + i < n), f (s + i) = some (w[s + i]'hi)) ∧
        (∀ t (ht : t < n), (t < s ∨ s + m ≤ t) → w[t] = v[t])) ∨
       forIn (m := Id) (List.range' s m) ((none, v) : FS β n) (fillBody f) = (some none, w)) := by
  induction m with
  | zero => intro s v; exact ⟨v, Or.inl ⟨rfl, by intro i hi; omega, fun _ _ _ => rfl⟩⟩
  | succ m ih =>
    intro s v
    cases hf : f s with
    | none =>
      refine ⟨v, Or.inr ?_⟩
      simp [List.range'_succ, List.forIn_cons, fillBody, hf]
      try rfl
    | some a =>
      obtain ⟨w, hw⟩ := ih (s + 1) (v.set! s a)
      have e : forIn (m := Id) (List.range' s (m + 1)) ((none, v) : FS β n) (fillBody f) =
          forIn (m := Id) (List.range' (s + 1) m) ((none, v.set! s a) : FS β n) (fillBody f) := by
        simp [List.range'_succ, List.forIn_cons, fillBody, hf]
        try rfl
      refine ⟨w, ?_⟩
      rcases hw with ⟨h1, h2, h3⟩ | h1
      · left
        rw [e]
        refine ⟨h1, ?_, ?_⟩
        · intro i hi hlt
          cases i with
          | zero =>
            have := h3 s (by simpa using hlt) (Or.inl (by omega))
            simp only [Nat.add_zero]
            rw [this, hf, set!_eq', Vector.getElem_setIfInBounds (by simpa using hlt)]
            simp
          | succ i =>
            have := h2 i (by omega) (by omega)
            simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
        · intro t ht hcase
          rw [h3 t ht (by omega), set!_eq', Vector.getElem_setIfInBounds ht]
          rw [if_neg (by omega)]
      · right; rw [e]; exact h1

/-- If every call succeeds, the loop finishes without an early exit. -/
theorem fill_forIn_some {β : Type} {n : Nat} (f : Nat → Option RPoly) (m : Nat) :
    ∀ (s : Nat) (v : Vector RPoly n), (∀ i, s ≤ i → i < s + m → ∃ a, f i = some a) →
      ∃ w : Vector RPoly n, forIn (m := Id) (List.range' s m) ((none, v) : FS β n) (fillBody f) = (none, w) := by
  induction m with
  | zero => intro s v _; exact ⟨v, rfl⟩
  | succ m ih =>
    intro s v h
    obtain ⟨a, hf⟩ := h s le_rfl (by omega)
    obtain ⟨w, hw⟩ := ih (s + 1) (v.set! s a) (fun i h1 h2 => h i (by omega) (by omega))
    refine ⟨w, ?_⟩
    have e : forIn (m := Id) (List.range' s (m + 1)) ((none, v) : FS β n) (fillBody f) =
        forIn (m := Id) (List.range' (s + 1) m) ((none, v.set! s a) : FS β n) (fillBody f) := by
      simp [List.range'_succ, List.forIn_cons, fillBody, hf]
      try rfl
    rw [e]; exact hw

/-- `ExpandS` as two `fillBody` loops. -/
def expandSModel (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Option (Vector RPoly p.ℓ × Vector RPoly p.k) :=
  let r1 := forIn (m := Id) [:p.ℓ]
    ((none, Vector.replicate p.ℓ (Vector.replicate 256 0)) : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.ℓ)
    (fillBody fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2))
  match r1.1 with
  | none =>
    let r2 := forIn (m := Id) [:p.k]
      ((none, Vector.replicate p.k (Vector.replicate 256 0)) : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.k)
      (fillBody fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2))
    match r2.1 with
    | none => some (r1.2, r2.2)
    | some a => a
  | some a => a

theorem ExpandS_eq (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) :
    Spec.ExpandS p fuel ρ = expandSModel p fuel ρ := by
  have key : ∀ {n : Nat} (m : Nat) (init : FS (Vector RPoly p.ℓ × Vector RPoly p.k) n)
      (F : Nat → FS (Vector RPoly p.ℓ × Vector RPoly p.k) n → Id (ForInStep (FS (Vector RPoly p.ℓ × Vector RPoly p.k) n)))
      (f : Nat → Option RPoly), (∀ x r, F x r = fillBody f x r) →
      forIn (m := Id) [:m] init F = forIn (m := Id) [:m] init (fillBody f) := by
    intro n m init F f h
    rw [show F = fillBody f from funext fun x => funext (h x)]
  unfold Spec.ExpandS expandSModel
  dsimp only
  generalize hA : forIn (m := Id) [:p.ℓ]
    ((none, Vector.replicate p.ℓ (Vector.replicate 256 0)) : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.ℓ)
    (fillBody fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) = A
  generalize hB : forIn (m := Id) [:p.k]
    ((none, Vector.replicate p.k (Vector.replicate 256 0)) : FS (Vector RPoly p.ℓ × Vector RPoly p.k) p.k)
    (fillBody fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) = B
  rw [key p.ℓ _ _ (fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) ?s1,
    key p.k _ _ (fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) ?s2]
  case s1 =>
    intro x r
    obtain ⟨b, v⟩ := r
    simp only [fillBody]
    rcases h : Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes x 2) with _ | a <;> simp [h]
  case s2 =>
    intro x r
    obtain ⟨b, v⟩ := r
    simp only [fillBody]
    rcases h : Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (x + p.ℓ) 2) with _ | a <;> simp [h]
  rw [hA, hB]
  rcases A with ⟨a1, v1⟩
  rcases B with ⟨b1, v2⟩
  rcases a1 with _ | _ | x <;> rcases b1 with _ | _ | y <;> rfl

theorem ExpandS_cells (p : Spec.Params) (fuel : Nat) (ρ : List UInt8) (s₁ : Vector RPoly p.ℓ)
    (s₂ : Vector RPoly p.k) (h : Spec.ExpandS p fuel ρ = some (s₁, s₂)) :
    (∀ (i : Nat) (hi : i < p.ℓ), Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes i 2) = some s₁[i]) ∧
    (∀ (i : Nat) (hi : i < p.k), Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (i + p.ℓ) 2) = some s₂[i]) := by
  rw [ExpandS_eq] at h
  unfold expandSModel at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one] at h
  obtain ⟨w1, hw1⟩ := fill_forIn (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) p.ℓ 0
    (Vector.replicate p.ℓ (Vector.replicate 256 0))
  obtain ⟨w2, hw2⟩ := fill_forIn (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) p.k 0
    (Vector.replicate p.k (Vector.replicate 256 0))
  rcases hw1 with ⟨e1, q1, -⟩ | e1
  · rcases hw2 with ⟨e2, q2, -⟩ | e2
    · rw [e1, e2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun i hi => by simpa using q1 i hi (by simpa using hi),
             fun i hi => by simpa using q2 i hi (by simpa using hi)⟩
    · rw [e1, e2] at h
      simp at h
  · rw [e1] at h
    simp at h

theorem ExpandS_of_cells (p : Spec.Params) (fuel : Nat) (ρ : List UInt8)
    (h1 : ∀ i, i < p.ℓ → ∃ a, Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes i 2) = some a)
    (h2 : ∀ i, i < p.k → ∃ a, Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (i + p.ℓ) 2) = some a) :
    ∃ s, Spec.ExpandS p fuel ρ = some s := by
  rw [ExpandS_eq]
  unfold expandSModel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  obtain ⟨w1, hw1⟩ := fill_forIn_some (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) p.ℓ 0
    (Vector.replicate p.ℓ (Vector.replicate 256 0)) (fun i _ hi => h1 i (by omega))
  obtain ⟨w2, hw2⟩ := fill_forIn_some (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => Spec.RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) p.k 0
    (Vector.replicate p.k (Vector.replicate 256 0)) (fun i _ hi => h2 i (by omega))
  rw [hw1, hw2]
  exact ⟨_, rfl⟩

end ES

/-- Every `RejBoundedPoly` call of `ExpandS(ρ)` terminates on ocaml-pq's side. -/
def ExpandSTerm (p : Spec.Params) (ρ : List UInt8) : Prop :=
  (∀ r < p.ℓ, ∃ a, OcamlPq.MLDSAAlg.RejBoundedReturns p.η
      (oursShake256 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes r 2)) a) ∧
  (∀ r < p.k, ∃ a, OcamlPq.MLDSAAlg.RejBoundedReturns p.η
      (oursShake256 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes (r + p.ℓ) 2)) a)

/-- **ExpandS, ours to theirs.**  If `ExpandS F ρ = some (s₁, s₂)`, every `RejBoundedPoly` call of ocaml-pq's
`ExpandS` terminates (on our SHAKE256), and `s₁`, `s₂` are ocaml-pq's `expandS`, entry by entry. -/
theorem expandS_ours_to_theirs (p : Spec.Params) (F : ℕ) (ρ : List UInt8) (s₁ : Vector RPoly p.ℓ)
    (s₂ : Vector RPoly p.k) (h : Spec.ExpandS p F ρ = some (s₁, s₂)) :
    ExpandSTerm p ρ ∧
    (∀ r (hr : r < p.ℓ), rfn s₁[r] = (OcamlPq.MLDSAAlg.expandS oursShake256 (algParams p) (u8ToBytes ρ)).1 r) ∧
    (∀ r (hr : r < p.k), rfn s₂[r] = (OcamlPq.MLDSAAlg.expandS oursShake256 (algParams p) (u8ToBytes ρ)).2 r) := by
  obtain ⟨c1, c2⟩ := ES.ExpandS_cells p F ρ s₁ s₂ h
  have k1 : ∀ r (hr : r < p.ℓ), OcamlPq.MLDSAAlg.RejBoundedReturns p.η
      (oursShake256 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes r 2)) (rfn s₁[r]) := by
    intro r hr
    have := RB.rejBounded_ours_to_theirs p _ F _ (c1 r hr)
    rwa [u8ToBytes_append, integerToBytes_alg_eq] at this
  have k2 : ∀ r (hr : r < p.k), OcamlPq.MLDSAAlg.RejBoundedReturns p.η
      (oursShake256 (u8ToBytes ρ ++ OcamlPq.MLDSAAlg.integerToBytes (r + p.ℓ) 2)) (rfn s₂[r]) := by
    intro r hr
    have := RB.rejBounded_ours_to_theirs p _ F _ (c2 r hr)
    rwa [u8ToBytes_append, integerToBytes_alg_eq] at this
  refine ⟨⟨fun r hr => ⟨_, k1 r hr⟩, fun r hr => ⟨_, k2 r hr⟩⟩, fun r hr => ?_, fun r hr => ?_⟩
  · simp only [OcamlPq.MLDSAAlg.expandS]
    exact OcamlPq.MLDSAAlg.RejBoundedReturns.eq (k1 r hr)
  · simp only [OcamlPq.MLDSAAlg.expandS]
    exact OcamlPq.MLDSAAlg.RejBoundedReturns.eq (k2 r hr)

/-- **ExpandS, theirs to ours.**  If every `RejBoundedPoly` call of ocaml-pq's `ExpandS` terminates, then ours
returns for every sufficiently large fuel. -/
theorem expandS_theirs_to_ours (p : Spec.Params) (ρ : List UInt8) (hT : ExpandSTerm p ρ) :
    ∃ F0, ∀ F, F0 ≤ F → ∃ s, Spec.ExpandS p F ρ = some s := by
  have g1 : ∀ r, r < p.ℓ → ∃ F0, ∀ F, F0 ≤ F → ∃ a, Spec.RejBoundedPoly p F (ρ ++ IntegerToBytes r 2) = some a := by
    intro r hr
    obtain ⟨b, hb⟩ := hT.1 r hr
    rw [← integerToBytes_alg_eq, ← u8ToBytes_append] at hb
    obtain ⟨F0, hF0⟩ := RB.rejBounded_eventually p _ _ hb
    exact ⟨F0, fun F hF => by obtain ⟨a, ha, -⟩ := hF0 F hF; exact ⟨a, ha⟩⟩
  have g2 : ∀ r, r < p.k → ∃ F0, ∀ F, F0 ≤ F → ∃ a, Spec.RejBoundedPoly p F (ρ ++ IntegerToBytes (r + p.ℓ) 2) = some a := by
    intro r hr
    obtain ⟨b, hb⟩ := hT.2 r hr
    rw [← integerToBytes_alg_eq, ← u8ToBytes_append] at hb
    obtain ⟨F0, hF0⟩ := RB.rejBounded_eventually p _ _ hb
    exact ⟨F0, fun F hF => by obtain ⟨a, ha, -⟩ := hF0 F hF; exact ⟨a, ha⟩⟩
  obtain ⟨F1, h1⟩ := eventually_forall_lt (P := fun r F => ∃ a, Spec.RejBoundedPoly p F (ρ ++ IntegerToBytes r 2) = some a)
    p.ℓ g1
  obtain ⟨F2, h2⟩ := eventually_forall_lt
    (P := fun r F => ∃ a, Spec.RejBoundedPoly p F (ρ ++ IntegerToBytes (r + p.ℓ) 2) = some a) p.k g2
  exact ⟨max F1 F2, fun F hF => ES.ExpandS_of_cells p F ρ
    (fun i hi => h1 F (le_trans (le_max_left _ _) hF) i hi)
    (fun i hi => h2 F (le_trans (le_max_right _ _) hF) i hi)⟩

end XSpec
