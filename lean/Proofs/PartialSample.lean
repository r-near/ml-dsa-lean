import Proofs.Partial
import Proofs.SampleA

/-!
# Partial correctness of RejNTTPoly and ExpandA (FIPS 204 Algorithms 30 and 32)

See `Proofs/Partial.lean` for the technique. Here:

* `rej_ntt_poly_partial`: `sampling.rej_ntt_poly ρ ⦃ r => ∃ a F, RejNTTPoly F ρ = some a ∧ Repr r a ⦄div`.
* `expand_a_partial`: the same for `sampling.expand_a` and `ExpandA` (one fuel for all `K·L` samples, obtained as
  the maximum of the per-sample fuels by the monotonicity lemmas `RejNTTPoly_mono`, `ExpandA_mono`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192
namespace Proofs
open Impl
namespace SampleA

/-! ## Spec-side fuel lemmas -/

theorem tripleAt_shake (ρ : List UInt8) (M i : Nat) (h : i < M) :
    tripleAt (SHAKE128 ρ (3 * M)) i = (SHAKE128 ρ (3 * i + 3)).drop (3 * i) := by
  have hw := sponge_window 168 (by omega) ρ (3 * i) 3 (3 * M) (by omega)
  unfold tripleAt SHAKE128
  exact hw.symm

theorem stA_congr (T T' : List UInt8) (n : Nat) (h : ∀ i < n, tripleAt T i = tripleAt T' i) :
    stA T n = stA T' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stA_succ, stA_succ, ih (fun i hi => h i (by omega))]
    have : triAt T n = triAt T' n := by unfold triAt; rw [h n (by omega)]
    simp [stepA, this]

/-- The first `n` steps of the rejection fold only read the first `3n` bytes: the fuel of the stream is
irrelevant as long as it is `≥ n`. -/
theorem stA_shake_mono (ρ : List UInt8) (n M M' : Nat) (hn : n ≤ M) (hM : M ≤ M') :
    stA (SHAKE128 ρ (3 * M')) n = stA (SHAKE128 ρ (3 * M)) n :=
  stA_congr _ _ n (fun i hi => by
    rw [tripleAt_shake ρ M' i (by omega), tripleAt_shake ρ M i (by omega)])

theorem rej_some_of_fin (ρ : List UInt8) (fuel : Nat) (hfin : 256 ≤ (stA (SHAKE128 ρ (3 * fuel)) fuel).2) :
    Spec.RejNTTPoly fuel ρ = some (stA (SHAKE128 ρ (3 * fuel)) fuel).1 := by
  rw [rej_unfold]
  obtain ⟨c, hc⟩ := rej_loop (SHAKE128 ρ (3 * fuel)) fuel (SHAKE128_length _ _) fuel 0 Poly.zero 0 (by omega)
  have hc' : forIn (m := Id) (List.range' 0 fuel) (⟨none, Poly.zero, G.InitAbsorb (3 * fuel) ρ, 0⟩ : RejSt) rejBody =
      ⟨none, (stA (SHAKE128 ρ (3 * fuel)) fuel).1, c, (stA (SHAKE128 ρ (3 * fuel)) fuel).2⟩ := hc
  simp only [hc']
  have h2 : ¬ (stA (SHAKE128 ρ (3 * fuel)) fuel).2 < 256 := by omega
  simp [h2]

/-- Fuel monotonicity of `RejNTTPoly`. -/
theorem RejNTTPoly_mono (ρ : List UInt8) (F F' : Nat) (a : Spec.Poly) (h : Spec.RejNTTPoly F ρ = some a)
    (hF : F ≤ F') : Spec.RejNTTPoly F' ρ = some a := by
  obtain ⟨hfin, hA⟩ := rej_eq_some F ρ a h
  have e1 : stA (SHAKE128 ρ (3 * F')) F = stA (SHAKE128 ρ (3 * F)) F := stA_shake_mono ρ F F F' le_rfl hF
  have e2 : stA (SHAKE128 ρ (3 * F')) F' = stA (SHAKE128 ρ (3 * F')) F :=
    stA_stable _ F F' (by rw [e1]; exact hfin) hF
  have hfin' : 256 ≤ (stA (SHAKE128 ρ (3 * F')) F').2 := by rw [e2, e1]; exact hfin
  rw [rej_some_of_fin ρ F' hfin', e2, e1, hA]

/-! ## The Rust loop -/

/-- Loop invariant of the partial proof: some `n` iterations have been done. -/
def RejInvU (ρ : List UInt8) (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) : Prop :=
  ∃ n, RejInv ρ n n a ctx j

theorem RejInv_fuel (ρ : List UInt8) (n M : Nat) (hM : n ≤ M) (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) :
    RejInv ρ n n a ctx j → RejInv ρ M n a ctx j := by
  rintro ⟨h1, h2, h3, h4⟩
  have := stA_shake_mono ρ n n M le_rfl hM
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [this]; exact h2
  · rw [this]; exact h3

theorem RejInv_fuel' (ρ : List UInt8) (n M : Nat) (hM : n ≤ M) (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) :
    RejInv ρ M n a ctx j → RejInv ρ n n a ctx j := by
  rintro ⟨h1, h2, h3, h4⟩
  have := stA_shake_mono ρ n n M le_rfl hM
  refine ⟨h1, ?_, ?_, h4⟩
  · rw [← this]; exact h2
  · rw [← this]; exact h3

theorem rej_body_partial (ρ : List UInt8) (n : Nat)
    (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) (h : RejInv ρ n n a ctx j) :
    sampling.rej_ntt_poly_loop.body a ctx j ⦃ r =>
      match r with
      | .done y => Canonical y ∧ toZq y = (stA (SHAKE128 ρ (3 * n)) n).1 ∧ 256 ≤ (stA (SHAKE128 ρ (3 * n)) n).2
      | .cont (a', ctx', j') => RejInvU ρ a' ctx' j' ⦄ := by
  have h' := RejInv_fuel ρ n (n + 1) (by omega) a ctx j h
  obtain ⟨hc, ha, hj, hs⟩ := h'
  have hprefix := stA_shake_mono ρ n n (n + 1) le_rfl (by omega)
  unfold sampling.rej_ntt_poly_loop.body
  split
  · rename_i hlt
    have hj256 : j.val < 256 := by scalar_tac
    have hlt' : (stA (SHAKE128 ρ (3 * (n + 1))) n).2 < 256 := by omega
    have hif : n < n + 1 := by omega
    step*
    all_goals
      have hs1 : s1.val.length = 3 := by rw [s1_post1]; simp
      have hsq : ShakeSqz ctx1 168 ρ (3 * (n + 1)) := by
        have := ctx1_post1; rw [hs1] at this; exact this
      obtain ⟨hl2, hW⟩ := triple_bytes ρ (n + 1) n hif s1 s2 hs1 ctx1_post2
      subst s1_post2 i_post2 i1_post2 i2_post2
      rw [tmb_byte s2 hl2 _ hW 0 i, tmb_byte s2 hl2 _ hW 1 i1, tmb_byte s2 hl2 _ hW 2 i2] at o_post
      have ho : Option.map (fun x => x.val) o = Option.map ZMod.val (triAt (SHAKE128 ρ (3 * (n + 1))) n) := o_post
    · have hon : o = none := ‹o = none›
      subst hon
      have htri : triAt (SHAKE128 ρ (3 * (n + 1))) n = none := by simpa using ho.symm
      have hst := stA_succ_none _ n htri hlt'
      have hst' : stA (SHAKE128 ρ (3 * (n + 1))) (n + 1) = stA (SHAKE128 ρ (3 * (n + 1))) n := hst
      refine ⟨n + 1, hc, ?_, ?_, hsq⟩
      · rw [hst']; exact ha
      · rw [hst']; exact hj
    · have hon : o = some x := ‹o = some x›
      subst hon
      obtain ⟨v, htri, hxv⟩ : ∃ v, triAt (SHAKE128 ρ (3 * (n + 1))) n = some v ∧ x.val = v.val := by
        revert ho
        rcases h : triAt (SHAKE128 ρ (3 * (n + 1))) n with _ | v
        · simp
        · simp only [Option.map_some, Option.some.injEq]
          intro h; exact ⟨v, rfl, h⟩
      have hst := stA_succ_some _ n v htri hlt'
      have hxq : x.val < Spec.q := by rw [hxv]; exact ZMod.val_lt v
      have hxz : ((x.val : Nat) : Zq) = v := by rw [hxv]; exact ZMod.natCast_zmod_val v
      have hjlt : j.val < 256 := hj256
      refine ⟨n + 1, ?_, ?_, ?_, hsq⟩
      · rw [a1_post]; exact canonical_set a j x hc hxq
      · rw [a1_post, toZq_set a j x hjlt, ha, hst, hj, hxz]
      · rw [j1_post, hst, hj]
  · rename_i hlt
    have hj256 : 256 ≤ j.val := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨hc, ?_, ?_⟩
    · rw [ha, hprefix]
    · rw [← hprefix]; omega

theorem rej_loop_partial (ρ : List UInt8) (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize)
    (h : RejInvU ρ a ctx j) :
    sampling.rej_ntt_poly_loop a ctx j ⦃ r => ∃ (a' : Spec.Poly) (F : Nat), Spec.RejNTTPoly F ρ = some a' ∧
      Repr r a' ⦄div := by
  unfold sampling.rej_ntt_poly_loop
  refine loop.dspec_inv _ (fun p : Array U32 256#usize × keccak.Shake × Usize => RejInvU ρ p.1 p.2.1 p.2.2)
    (fun r => ∃ (a' : Spec.Poly) (F : Nat), Spec.RejNTTPoly F ρ = some a' ∧ Repr r a') ?_ (a, ctx, j) h
  rintro ⟨a, ctx, j⟩ ⟨n, hn⟩
  apply WP.spec_dspec
  apply WP.spec_mono (rej_body_partial ρ n a ctx j hn)
  rintro (⟨a', ctx', j'⟩ | y) h
  · exact h
  · obtain ⟨h1, h2, h3⟩ := h
    exact ⟨_, n, rej_some_of_fin ρ n h3, h1, h2⟩

/-- **RejNTTPoly, partial correctness.** The Rust function never panics, and if it returns `r` then `r` represents
the spec's answer at some fuel. (The older `rej_ntt_poly_spec` is the converse: if the spec returns `some a`,
the Rust returns `a`.) -/
theorem rej_ntt_poly_partial_aux (ρ : Array U8 34#usize) :
    sampling.rej_ntt_poly ρ ⦃ r => ∃ (a : Spec.Poly) (F : Nat), Spec.RejNTTPoly F (bytesA ρ) = some a ∧
      Repr r a ⦄div := by
  unfold sampling.rej_ntt_poly
  step*
  subst s_post
  rw [bytes_to_slice, List.nil_append] at ctx2_post
  refine rej_loop_partial (bytesA ρ) _ ctx2 0#usize ⟨0, canonical_repeat_zero, ?_, ?_, ?_⟩
  · rw [toZq_repeat_zero]; rfl
  · show (0#usize).val = 0; rfl
  · simpa using ctx2_post

/-! ## ExpandA -/

theorem innerF_mono (p : Spec.Params) (ρ : List UInt8) (r : Nat) :
    ∀ F F' (A B : Vector (Vector Poly p.ℓ) p.k) (s : Nat), F ≤ F' → innerF p F ρ r A s = some B →
      innerF p F' ρ r A s = some B := by
  intro F F' A B s hF h
  unfold innerF at h ⊢
  rcases hr : Spec.RejNTTPoly F (pSeed ρ r s) with _ | a
  · simp [hr] at h
  · rw [hr] at h
    rw [RejNTTPoly_mono _ F F' a hr hF]
    exact h

theorem outerF_mono (p : Spec.Params) (ρ : List UInt8) :
    ∀ F F' (A B : Vector (Vector Poly p.ℓ) p.k) (r : Nat), F ≤ F' → outerF p F ρ A r = some B →
      outerF p F' ρ A r = some B := by
  intro F F' A B r hF h
  unfold outerF at h ⊢
  exact foldlM_fuel_mono (fun F => innerF p F ρ r) (fun F F' x i y hF h => innerF_mono p ρ r F F' x y i hF h)
    _ A B F F' hF h

/-- Fuel monotonicity of `ExpandA`. -/
theorem ExpandA_mono (p : Spec.Params) (ρ : List UInt8) (F F' : Nat) (A : Vector (Vector Poly p.ℓ) p.k)
    (h : Spec.ExpandA p F ρ = some A) (hF : F ≤ F') : Spec.ExpandA p F' ρ = some A := by
  rw [expandA_eq] at h ⊢
  exact foldlM_fuel_mono (fun F => outerF p F ρ) (fun F F' x i y hF h => outerF_mono p ρ F F' x y i hF h)
    _ _ A F F' hF h

/-- Inner-loop invariant (columns `0 … s-1` of row `r` are filled). -/
def InnerInvU (sp : Spec.Params) {K L : Usize} (ρ : List UInt8) (r : Nat) (A : Vector (Vector Poly sp.ℓ) sp.k)
    (a : Array (Array (Array U32 256#usize) L) K) (s : Usize) : Prop :=
  s.val ≤ sp.ℓ ∧ ∃ F B, (List.range' 0 s.val).foldlM (innerF sp F ρ r) A = some B ∧ ReprMat a B

theorem inner_body_partial (sp : Spec.Params) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (r : Usize) (hr : r.val < sp.k)
    (A : Vector (Vector Poly sp.ℓ) sp.k)
    (a : Array (Array (Array U32 256#usize) L) K) (s : Usize) (hI : InnerInvU sp (bytesA rho) r.val A a s) :
    sampling.expand_a_loop0_loop0.body rho r a s ⦃ x =>
      match x with
      | .done y => ∃ F Af, outerF sp F (bytesA rho) A r.val = some Af ∧ ReprMat y Af
      | .cont (a', s') => InnerInvU sp (bytesA rho) r.val A a' s' ⦄div := by
  obtain ⟨hs, F, B, hB, ha⟩ := hI
  unfold sampling.expand_a_loop0_loop0.body
  split
  · rename_i hlt
    have hs' : s.val < sp.ℓ := by have : s.val < L.val := hlt; omega
    have hseed0 : bytesA (Array.repeat 34#usize 0#u8) = (bytesA rho).take (0#usize).val ++ List.replicate (34 - (0#usize).val) 0 := by
      simp [bytesA_repeat_zero]
    step*
    have hl : (bytesA rho).length = 32 := by simp
    have hseed3 : bytesA seed3 = pSeed (bytesA rho) r.val s.val := by
      rw [seed3_post, bytesA_set, seed2_post, bytesA_set, seed1_post, i_post, i1_post]
      unfold pSeed
      rw [integerToBytes_one, integerToBytes_one,
        List.set_append_right _ _ (by simp [hl]), List.set_append_right _ _ (by simp [hl])]
      simp [hl, UScalar.cast_val_eq, List.set]
    refine WP.dspec_bind' (rej_ntt_poly_partial_aux seed3) ?_
    rintro a1 ⟨a', F1, hrej, ha1⟩
    rw [hseed3] at hrej
    step*
    have hF : F ≤ max F F1 := le_max_left _ _
    have hF1 : F1 ≤ max F F1 := le_max_right _ _
    have hB' := foldlM_fuel_mono (fun F => innerF sp F (bytesA rho) r.val)
      (fun F F' x i y hF h => innerF_mono sp (bytesA rho) r.val F F' x y i hF h) _ A B F (max F F1) hF hB
    have hrej' := RejNTTPoly_mono _ F1 (max F F1) a' hrej hF1
    have hrk : r.val < sp.k := hr
    obtain ⟨a2, index_mut_back⟩ := a2
    dsimp only at a2_post2 a2_post3 ⊢
    step*
    have hrow : ReprVec a2 B[r.val] := by
      rw [a2_post2]; exact ha.elt r.val hrk
    have hrow' : ReprVec a3 (B[r.val]!.set! s.val a') := by
      rw [a3_post, getElem!_pos B r.val (by simpa using hrk)]
      exact ReprVec.set hrow s a1 a' ha1 hs'
    have hstep : innerF sp (max F F1) (bytesA rho) r.val B s.val = some (B.set! r.val (B[r.val]!.set! s.val a')) := by
      unfold innerF; rw [hrej']
    have hfold : (List.range' 0 (s.val + 1)).foldlM (innerF sp (max F F1) (bytesA rho) r.val) A =
        some (B.set! r.val (B[r.val]!.set! s.val a')) := by
      rw [List.range'_concat, List.foldlM_append, hB']
      simp [hstep]
    refine ⟨by omega, max F F1, _, by rw [s1_post]; exact hfold, ?_⟩
    rw [a2_post3]
    exact ReprMat.set' ha r a3 _ hrow' hrk
  · rename_i hlt
    have hs' : s.val = sp.ℓ := by have : ¬ s.val < L.val := hlt; omega
    simp only [WP.dspec_ok]
    rw [hs'] at hB
    exact ⟨F, B, by unfold outerF; exact hB, ha⟩

theorem inner_loop_partial (sp : Spec.Params) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) (r : Usize) (hr : r.val < sp.k)
    (A : Vector (Vector Poly sp.ℓ) sp.k)
    (a : Array (Array (Array U32 256#usize) L) K) (ha : ReprMat a A) :
    sampling.expand_a_loop0_loop0 rho a r 0#usize ⦃ x =>
      ∃ F Af, outerF sp F (bytesA rho) A r.val = some Af ∧ ReprMat x Af ⦄div := by
  unfold sampling.expand_a_loop0_loop0
  refine loop.dspec_inv _ (fun p : Array (Array (Array U32 256#usize) L) K × Usize =>
      InnerInvU sp (bytesA rho) r.val A p.1 p.2)
    (fun x => ∃ F Af, outerF sp F (bytesA rho) A r.val = some Af ∧ ReprMat x Af) ?_ (a, 0#usize)
    ⟨by simp, 0, A, by simp, ha⟩
  rintro ⟨a', s'⟩ hI
  dsimp only at hI ⊢
  refine WP.dspec_mono' (inner_body_partial sp hK hL rho r hr A a' s' hI) ?_
  rintro (⟨a'', s''⟩ | y) h
  · exact h
  · exact h

/-- Outer-loop invariant (rows `0 … r-1` are filled). -/
def OuterInvU (sp : Spec.Params) {K L : Usize} (ρ : List UInt8)
    (a : Array (Array (Array U32 256#usize) L) K) (r : Usize) : Prop :=
  r.val ≤ sp.k ∧ ∃ F B, (List.range' 0 r.val).foldlM (outerF sp F ρ)
    (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some B ∧ ReprMat a B

theorem outer_body_partial (sp : Spec.Params) {K L : Usize} (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize)
    (a : Array (Array (Array U32 256#usize) L) K) (r : Usize) (hI : OuterInvU sp (bytesA rho) a r) :
    sampling.expand_a_loop0.body rho a r ⦃ x =>
      match x with
      | .done y => ∃ F Af, (List.range' 0 sp.k).foldlM (outerF sp F (bytesA rho))
          (Vector.replicate sp.k (Vector.replicate sp.ℓ Poly.zero)) = some Af ∧ ReprMat y Af
      | .cont (a', r') => OuterInvU sp (bytesA rho) a' r' ⦄div := by
  obtain ⟨hr, F, B, hB, ha⟩ := hI
  unfold sampling.expand_a_loop0.body
  split
  · rename_i hlt
    have hr' : r.val < sp.k := by have : r.val < K.val := hlt; omega
    refine WP.dspec_bind' (inner_loop_partial sp hK hL rho r hr' B a ha) ?_
    rintro a1 ⟨F1, Af, hAf, hR⟩
    step*
    have hF : F ≤ max F F1 := le_max_left _ _
    have hF1 : F1 ≤ max F F1 := le_max_right _ _
    have hB' := foldlM_fuel_mono (fun F => outerF sp F (bytesA rho))
      (fun F F' x i y hF h => outerF_mono sp (bytesA rho) F F' x y i hF h) _ _ B F (max F F1) hF hB
    have hAf' := outerF_mono sp (bytesA rho) F1 (max F F1) B Af r.val hF1 hAf
    refine ⟨by omega, max F F1, Af, ?_, ?_⟩
    · rw [r1_post, List.range'_concat, List.foldlM_append, hB']
      simp [hAf']
    · exact hR
  · rename_i hlt
    have hr' : r.val = sp.k := by have : ¬ r.val < K.val := hlt; omega
    simp only [WP.dspec_ok]
    rw [hr'] at hB
    exact ⟨F, B, hB, ha⟩

theorem expand_a_partial_aux (sp : Spec.Params) (K L : Usize) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (rho : Array U8 32#usize) :
    sampling.expand_a K L rho ⦃ r => ∃ (A : Vector (Vector Poly sp.ℓ) sp.k) (F : Nat),
      Spec.ExpandA sp F (bytesA rho) = some A ∧ ReprMat r A ⦄div := by
  unfold sampling.expand_a
  simp only []
  unfold sampling.expand_a_loop0
  refine loop.dspec_inv _ (fun p : Array (Array (Array U32 256#usize) L) K × Usize =>
      OuterInvU sp (bytesA rho) p.1 p.2) ?_ ?_
    (Array.repeat K (Array.repeat L (Array.repeat 256#usize 0#u32)), 0#usize)
    ⟨by simp, 0, _, by simp, ReprMat_repeat_zero K L sp.k sp.ℓ hK hL⟩
  rintro ⟨a', r'⟩ hI
  dsimp only at hI ⊢
  refine WP.dspec_mono' (outer_body_partial sp hK hL rho a' r' hI) ?_
  rintro (⟨a'', r''⟩ | y) h
  · exact h
  · obtain ⟨F, Af, h1, h2⟩ := h
    refine ⟨Af, F, ?_, h2⟩
    rw [expandA_eq]; exact h1

end SampleA

theorem rej_ntt_poly_partial (ρ : Array U8 34#usize) :
    sampling.rej_ntt_poly ρ ⦃ r => ∃ (a : Spec.Poly) (F : Nat), Spec.RejNTTPoly F (bytesA ρ) = some a ∧
      Repr r a ⦄div :=
  SampleA.rej_ntt_poly_partial_aux ρ

/-- **ExpandA, partial correctness.** -/
theorem expand_a_partial (sp : Spec.Params) (K L : Usize) (hK : K.val = sp.k) (hL : L.val = sp.ℓ)
    (ρ : Array U8 32#usize) :
    sampling.expand_a K L ρ ⦃ r => ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (F : Nat),
      Spec.ExpandA sp F (bytesA ρ) = some A ∧ ReprMat r A ⦄div :=
  SampleA.expand_a_partial_aux sp K L hK hL ρ

end Proofs
