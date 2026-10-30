import Proofs.SampleBall

/-!
# Shape of the challenge polynomial (P4)

`Spec.SampleInBall` returns `c` with coefficients in `{-1, 0, 1}` and exactly `τ` nonzero coefficients
(`SampleInBall_weight`). The combined form `Ball τ c` is what the NTT bound `‖c·s₂‖∞ ≤ τη = β` consumes
(`SampleInBall_ball`).

Invariant of the outer loop of Algorithm 29, after processing `i = 256 - τ .. s - 1`: every coefficient at a
position `≥ s` is zero, and the number of nonzero coefficients is `s - (256 - τ)`. Step `i` reads `c[j]` with
`j ≤ i`, writes it to `c[i]` (which is `0` since `i ≥ s`), then writes `±1` at `j`: the count grows by one.
-/

open Spec
set_option maxRecDepth 8192

namespace Proofs.Corr
open Proofs

/-- The number of nonzero coefficients of `c`. -/
def nnz (c : RPoly) : Nat := (Finset.univ.filter (fun i : Fin 256 => c[i] ≠ 0)).card

/-- A challenge-shaped polynomial: coefficients in `{-1, 0, 1}` and at most `τ` of them nonzero. -/
def Ball (τ : Nat) (c : RPoly) : Prop :=
  (∀ i : Fin 256, c[i] = -1 ∨ c[i] = 0 ∨ c[i] = 1) ∧
    (Finset.univ.filter (fun i : Fin 256 => c[i] ≠ 0)).card ≤ τ

theorem nnz_replicate : nnz (Vector.replicate 256 0) = 0 := by
  unfold nnz
  simp

/-- One step changes the count of nonzero coefficients by exactly one. -/
theorem nnz_step (c : RPoly) (i j : Nat) (hi : i < 256) (hj : j ≤ i) (hci : c[i] = 0) (x : Int) (hx : x ≠ 0) :
    nnz ((c.set! i c[j]!).set! j x) = nnz c + 1 := by
  have hj' : j < 256 := by omega
  have hcj : c[j]! = c[j] := getElem!_pos _ _ (by simpa using hj')
  rw [hcj]
  unfold nnz
  have key : ∀ k : Fin 256, ((c.set! i c[j]).set! j x)[k] =
      if j = k.val then x else if i = k.val then c[j] else c[k] := by
    intro k
    show ((c.set! i c[j]).set! j x)[k.val]'k.isLt = _
    rw [set!_getElem _ _ _ _ k.isLt, set!_getElem _ _ _ _ k.isLt]
    rfl
  by_cases hij : j = i
  · subst hij
    have hjc : c[j] = 0 := hci
    have e : Finset.univ.filter (fun k : Fin 256 => ((c.set! j c[j]).set! j x)[k] ≠ 0) =
        insert ⟨j, hj'⟩ (Finset.univ.filter (fun k : Fin 256 => c[k] ≠ 0)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, key, Fin.ext_iff]
      by_cases hk : j = k.val
      · simp [hk, hx]
      · simp [hk, Ne.symm hk]
    rw [e, Finset.card_insert_of_notMem]
    simp [Fin.ext_iff, hjc]
  · have hlt : j < i := by omega
    by_cases hc : c[j] = 0
    · have e : Finset.univ.filter (fun k : Fin 256 => ((c.set! i c[j]).set! j x)[k] ≠ 0) =
          insert ⟨j, hj'⟩ (Finset.univ.filter (fun k : Fin 256 => c[k] ≠ 0)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, key, Fin.ext_iff]
        by_cases hk : j = k.val
        · simp [hk, hx]
        · by_cases hk2 : i = k.val
          · subst hk2; simp [hk, hc, hci, Ne.symm hk]
          · simp [hk, hk2, Ne.symm hk]
      rw [e, Finset.card_insert_of_notMem]
      simp [Fin.ext_iff, hc]
    · have e : Finset.univ.filter (fun k : Fin 256 => ((c.set! i c[j]).set! j x)[k] ≠ 0) =
          insert ⟨i, hi⟩ (Finset.univ.filter (fun k : Fin 256 => c[k] ≠ 0)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, key, Fin.ext_iff]
        by_cases hk : j = k.val
        · subst hk; simp [hx, hc, hij]
        · by_cases hk2 : i = k.val
          · subst hk2; simp [hk, hc, Ne.symm hk]
          · simp [hk, hk2, Ne.symm hk2, Ne.symm hk]
      rw [e, Finset.card_insert_of_notMem]
      simp [Fin.ext_iff, hci]

/-- Loop invariant: all coefficients at positions `≥ s` vanish, and `nnz c + (256 - τ) = s`. -/
def Inv (b s : Nat) (c : RPoly) : Prop := (∀ k (hk : k < 256), s ≤ k → c[k] = 0) ∧ nnz c + b = s

theorem sibStep_inv (S : List UInt8) (hb : List Bool) (τ fuel i : Nat) (hi : i < 256) (b : Nat)
    (st st' : RPoly × Nat) (h0 : Inv b i st.1) (h : sibStep S hb τ fuel st i = some st') :
    Inv b (i + 1) st'.1 := by
  unfold sibStep at h
  split at h
  · cases hf : sibFind S i fuel (st.2 + 1) ((S[st.2]?.getD default).toNat) with
    | none => rw [hf] at h; simp at h
    | some r =>
      obtain ⟨j, pos'⟩ := r
      rw [hf] at h
      simp only [Option.some.injEq] at h
      subst h
      have hj := sibFind_le S i _ _ _ _ _ hf
      obtain ⟨hz, hn⟩ := h0
      have hci : st.1[i] = 0 := hz i hi (le_refl _)
      have hx : (if hb[i + τ - 256]?.getD false = true then (-1 : Int) else 1) ≠ 0 := by split <;> simp
      refine ⟨?_, ?_⟩
      · intro k hk hik
        dsimp only
        rw [set!_getElem _ _ _ _ hk, set!_getElem _ _ _ _ hk]
        rw [if_neg (by omega), if_neg (by omega)]
        exact hz k hk (by omega)
      · dsimp only
        rw [nnz_step st.1 i j hi hj hci _ hx]
        omega
  · simp at h

theorem foldlM_inv (S : List UInt8) (hb : List Bool) (τ fuel b : Nat) :
    ∀ (n s : Nat) (st st' : RPoly × Nat), s + n ≤ 256 → Inv b s st.1 →
      (List.range' s n).foldlM (sibStep S hb τ fuel) st = some st' → Inv b (s + n) st'.1 := by
  intro n
  induction n with
  | zero => intro s st st' _ h hf; simp at hf; subst hf; simpa using h
  | succ n ih =>
    intro s st st' hs h hf
    rw [List.range'_succ, List.foldlM_cons] at hf
    cases h1 : sibStep S hb τ fuel st s with
    | none => rw [h1] at hf; simp at hf
    | some st1 =>
      rw [h1] at hf
      have := ih (s + 1) st1 st' (by omega) (sibStep_inv S hb τ fuel s (by omega) b st st1 h h1) hf
      rwa [show s + 1 + n = s + (n + 1) by omega] at this

/-- **Weight of `SampleInBall`**: exactly `τ` of the 256 coefficients are nonzero. -/
theorem SampleInBall_weight (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) (c : RPoly)
    (hs : Spec.SampleInBall p fuel ρ = some c) : nnz c = p.τ := by
  obtain ⟨pos, h⟩ := SampleInBall_model p hτ fuel ρ c hs
  unfold sibRun at h
  have h0 : Inv (256 - p.τ) (256 - p.τ) (Vector.replicate 256 (0 : Int), 8).1 := by
    refine ⟨?_, ?_⟩
    · intro k hk _; simp
    · simp [nnz_replicate]
  have := foldlM_inv (H ρ (8 + fuel)) (BytesToBits ((H ρ (8 + fuel)).take 8)) p.τ fuel (256 - p.τ) p.τ
    (256 - p.τ) _ _ (by omega) h0 h
  have h2 := this.2
  simp only at h2
  omega

/-- **Coefficients of `SampleInBall`** in `{-1, 0, 1}`, in `Fin 256` form. -/
theorem SampleInBall_ternary' (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) (c : RPoly)
    (hs : Spec.SampleInBall p fuel ρ = some c) : ∀ i : Fin 256, c[i] = -1 ∨ c[i] = 0 ∨ c[i] = 1 :=
  fun i => SampleInBall_ternary p hτ fuel ρ c hs i.val i.isLt

/-- **Shape of the challenge**: `SampleInBall`'s output is in `Ball τ` (ternary, exactly `τ`, hence at most
`τ`, nonzero coefficients). -/
theorem SampleInBall_ball (p : Spec.Params) (hτ : p.τ ≤ 256) (fuel : Nat) (ρ : List UInt8) (c : RPoly)
    (hs : Spec.SampleInBall p fuel ρ = some c) : Ball p.τ c :=
  ⟨SampleInBall_ternary' p hτ fuel ρ c hs, le_of_eq (SampleInBall_weight p hτ fuel ρ c hs)⟩

end Proofs.Corr
