import Proofs.PartialVerify
import Proofs.SampleS

/-!
# Partial correctness of RejBoundedPoly and ExpandS (FIPS 204 Algorithms 31 and 33)

See `Proofs/Partial.lean` for the technique. Here:

* `RejBoundedPoly_mono`: fuel monotonicity of the spec sampler (the first `k` iterations only read the first `k`
  stream bytes, so the stream length is irrelevant as long as it is `≥ k`).
* `rej_bounded_poly_partial`: `sampling.rej_bounded_poly ip ρ ⦃ r => ∃ a F, RejBoundedPoly sp F ρ = some a ∧
  ReprInt r a ⦄div`.
* `ExpandS_of_samplers`, `ExpandS_mono`: the converse of `ExpandS_some` and fuel monotonicity of `ExpandS`.
* `expand_s_partial`: `sampling.expand_s K L ip ρ ⦃ r => ∃ s₁ s₂ F, ExpandS sp F ρ = some (s₁, s₂) ∧ … ⦄div`
  (one fuel for all `ℓ + k` samples, the maximum of the per-sample fuels).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

namespace PartialSampleS

/-! ## Spec side: the stream prefix and fuel monotonicity -/

theorem rbRun_congr (η : Nat) (s1 s2 : List UInt8) (n : Nat) :
    ∀ (st : RPoly × Nat) (s : Nat), (∀ i, i < n → s1[s + i]! = s2[s + i]!) →
      rbRun η s1 st s n = rbRun η s2 st s n := by
  induction n with
  | zero => intro st s _; rfl
  | succ n ih =>
    intro st s h
    by_cases hj : st.2 ≥ 256
    · simp [rbRun, hj]
    · have h0 := h 0 (by omega)
      rw [Nat.add_zero] at h0
      simp only [rbRun, if_neg hj]
      rw [h0]
      exact ih _ _ (fun i hi => by
        have := h (i + 1) (by omega)
        rwa [show s + (i + 1) = s + 1 + i by omega] at this)

/-- A byte of the SHAKE256 stream does not depend on the stream length, as long as it is in range. -/
theorem H_getElem_mono (ρ : List UInt8) (k F F' : Nat) (hk : k < F) (hF : F ≤ F') :
    (H ρ F)[k]! = (H ρ F')[k]! := by
  have h1 := sponge_window 136 (by omega) ρ k 1 F (by omega)
  have h2 := sponge_window 136 (by omega) ρ k 1 F' (by omega)
  have hl1 : k < (H ρ F).length := by simp [H, SHAKE256_length]; exact hk
  have hl2 : k < (H ρ F').length := by simp [H, SHAKE256_length]; omega
  rw [← drop_take_one_get _ _ hl1, ← drop_take_one_get _ _ hl2]
  have : ((H ρ F).drop k).take 1 = ((H ρ F').drop k).take 1 := by
    have e1 : (H ρ F) = Spec.Keccak.sponge 136 ρ F := rfl
    have e2 : (H ρ F') = Spec.Keccak.sponge 136 ρ F' := rfl
    rw [e1, e2, ← h1, ← h2]
  rw [this]

/-- The first `k` iterations only read the first `k` stream bytes. -/
theorem rbS_fuel (η : Nat) (ρ : List UInt8) (k F F' : Nat) (hk : k ≤ F) (hF : F ≤ F') :
    rbS η F' ρ k = rbS η F ρ k := by
  unfold rbS
  apply rbRun_congr
  intro i hi
  rw [Nat.zero_add]
  exact (H_getElem_mono ρ i F F' (by omega) hF).symm

/-- Fuel monotonicity of `RejBoundedPoly`. -/
theorem RejBoundedPoly_mono (p : Params) (ρ : List UInt8) (F F' : Nat) (a : RPoly)
    (h : RejBoundedPoly p F ρ = some a) (hF : F ≤ F') : RejBoundedPoly p F' ρ = some a := by
  obtain ⟨rfl, hfull⟩ := RejBoundedPoly_some p F ρ a h
  have e1 : rbS p.η F' ρ F = rbS p.η F ρ F := rbS_fuel p.η ρ F F F' le_rfl hF
  have e2 : rbS p.η F' ρ F' = rbS p.η F' ρ F := by
    have := rbS_stable p.η F' ρ F (F' - F) (by rw [e1]; exact hfull)
    rwa [show F + (F' - F) = F' by omega] at this
  rw [RejBoundedPoly_eq]
  change (if (rbS p.η F' ρ F').2 < 256 then none else some (rbS p.η F' ρ F').1) = _
  rw [e2, e1, if_neg (by omega)]

theorem RejBoundedPoly_of_full (p : Params) (ρ : List UInt8) (n : Nat) (h : 256 ≤ (rbS p.η n ρ n).2) :
    RejBoundedPoly p n ρ = some (rbS p.η n ρ n).1 := by
  rw [RejBoundedPoly_eq]
  change (if (rbS p.η n ρ n).2 < 256 then none else some (rbS p.η n ρ n).1) = _
  rw [if_neg (by omega)]

/-! ## The Rust loop of `rej_bounded_poly` -/

/-- One iteration of `rej_bounded_poly_loop` from the state after `k` iterations of the model with stream length
`fuel > k` (the body of `rej_bounded_poly_loop_spec`, with the fuel as a parameter instead of a loop bound). -/
theorem rej_bounded_body_step {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (ρ : List UInt8) (fuel k : Nat)
    (hk : k ≤ fuel) (hkf : k < fuel) (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize)
    (hS : ShakeSqz ctx 136 ρ k) (hR : ReprInt a (rbS sp.η fuel ρ k).1)
    (hj : j.val = (rbS sp.η fuel ρ k).2) :
    sampling.rej_bounded_poly_loop.body ip a ctx j ⦃ r =>
      match r with
      | .done y => ReprInt y (rbS sp.η fuel ρ k).1 ∧ 256 ≤ (rbS sp.η fuel ρ k).2
      | .cont x' => k < fuel ∧ ShakeSqz x'.2.1 136 ρ (k + 1) ∧
          ReprInt x'.1 (rbS sp.η fuel ρ (k + 1)).1 ∧ x'.2.2.val = (rbS sp.η fuel ρ (k + 1)).2 ⦄ := by
  simp only [sampling.rej_bounded_poly_loop.body]
  split
  · rename_i hj256
    have hj256' : j.val < 256 := by scalar_tac
    have hlen : k < (H ρ fuel).length := by simp [H, SHAKE256_length]; exact hkf
    step*
    have hs1 : (↑s : List U8).length = 1 := by simp [s_post1]
    rw [hs1] at ctx1_post1 ctx1_post2
    have hw := sponge_window 136 (by omega) ρ k 1 fuel (by omega)
    have hb : bytes s1 = ((H ρ fuel).drop k).take 1 := by rw [ctx1_post2]; exact hw
    have hxv := byte_of _ s1 _ (H ρ fuel) k i_post2 (by rw [s_post2]) hb hlen
    have hi1 : i1.val = (H ρ fuel)[k]!.toNat % 16 := by
      rw [i1_post1, UScalar.val_and, hxv]
      show _ &&& 15 = _
      have := Nat.and_two_pow_sub_one_eq_mod (H ρ fuel)[k]!.toNat 4
      simpa using this
    have hi2 : i2.val = (H ρ fuel)[k]!.toNat / 16 := by
      rw [i2_post1, hxv, Nat.shiftRight_eq_div_pow]
    rw [hi1] at z0_post
    rw [hi2] at z1_post
    have hnext := rbS_succ sp.η fuel ρ k
    rw [if_neg (by omega)] at hnext
    obtain ⟨c1, c2, c3, c4⟩ := rbStep_cases sp.η (rbS sp.η fuel ρ k) (H ρ fuel)[k]!.toNat
    rcases z0 with _ | x0 <;> rcases z1 with _ | y0
    · have e0 := optCoeff_none z0_post
      have e1 := optCoeff_none z1_post
      have hn : rbS sp.η fuel ρ (k + 1) = rbS sp.η fuel ρ k := by rw [hnext]; exact c1 e0 e1
      refine (WP.spec_ok _).mpr ?_
      show k < fuel ∧ _
      rw [hn]
      exact ⟨hkf, ctx1_post1, hR, hj⟩
    · have e0 := optCoeff_none z0_post
      obtain ⟨d, e1, hrel⟩ := optCoeff_some z1_post
      have hn : rbS sp.η fuel ρ (k + 1) =
          (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 d, (rbS sp.η fuel ρ k).2 + 1) := by
        rw [hnext, c2 d e0 e1, if_pos (by omega)]
      have hset := ReprInt.set hR j y0 d hj256' hrel.1 hrel.2
      step*
    · obtain ⟨c, e0, hrel⟩ := optCoeff_some z0_post
      have e1 := optCoeff_none z1_post
      have hn : rbS sp.η fuel ρ (k + 1) =
          (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 c, (rbS sp.η fuel ρ k).2 + 1) := by
        rw [hnext, c3 c e0 e1]
      have hset := ReprInt.set hR j x0 c hj256' hrel.1 hrel.2
      step*
    · obtain ⟨c, e0, hr0⟩ := optCoeff_some z0_post
      obtain ⟨d, e1, hr1⟩ := optCoeff_some z1_post
      have hset := ReprInt.set hR j x0 c hj256' hr0.1 hr0.2
      have hn4 : rbS sp.η fuel ρ (k + 1) =
          (if (rbS sp.η fuel ρ k).2 + 1 < 256 then
            ((Vector.set! (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 c)
              ((rbS sp.η fuel ρ k).2 + 1) d), (rbS sp.η fuel ρ k).2 + 1 + 1)
           else (Vector.set! (rbS sp.η fuel ρ k).1 (rbS sp.η fuel ρ k).2 c, (rbS sp.η fuel ρ k).2 + 1)) := by
        rw [hnext, c4 c d e0 e1]
      step*
      subst_vars
      all_goals
        have hxlt : x.val < 256 := by scalar_tac
        have hlt : (rbS sp.η fuel ρ k).2 + 1 < 256 := by omega
        have hset2 := ReprInt.set hset x y0 d hxlt hr1.1 hr1.2
        refine ⟨hkf, ctx1_post1, ?_, ?_⟩
        · rw [hn4, if_pos hlt, ← hj]
          rw [x_post] at hset2
          exact hset2
        · rw [hn4, if_pos hlt, ← hj, j2_post, x_post]
  · rename_i hjn
    have h256 : 256 ≤ j.val := by scalar_tac
    refine (WP.spec_ok _).mpr ?_
    exact ⟨hR, by omega⟩

/-- Loop invariant of the partial proof: some `n` iterations have been done, with stream length `n`. -/
def RBInvU (sp : Spec.Params) (ρ : List UInt8) (x : Array U32 256#usize × keccak.Shake × Usize) : Prop :=
  ∃ n, ShakeSqz x.2.1 136 ρ n ∧ ReprInt x.1 (rbS sp.η n ρ n).1 ∧ x.2.2.val = (rbS sp.η n ρ n).2

theorem rej_bounded_loop_partial {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (ρ : List UInt8)
    (a : Array U32 256#usize) (ctx : keccak.Shake) (j : Usize) (h : RBInvU sp ρ (a, ctx, j)) :
    sampling.rej_bounded_poly_loop ip a ctx j ⦃ r =>
      ∃ (a' : RPoly) (F : Nat), Spec.RejBoundedPoly sp F ρ = some a' ∧ ReprInt r a' ⦄div := by
  unfold sampling.rej_bounded_poly_loop
  refine loop.dspec_inv _ (fun p : Array U32 256#usize × keccak.Shake × Usize => RBInvU sp ρ p)
    (fun r => ∃ (a' : RPoly) (F : Nat), Spec.RejBoundedPoly sp F ρ = some a' ∧ ReprInt r a') ?_
    (a, ctx, j) h
  rintro ⟨a, ctx, j⟩ ⟨n, hS, hR, hj⟩
  dsimp only at hS hR hj
  apply WP.spec_dspec
  have e : rbS sp.η (n + 1) ρ n = rbS sp.η n ρ n := rbS_fuel sp.η ρ n n (n + 1) le_rfl (by omega)
  apply WP.spec_mono (rej_bounded_body_step hp hη ρ (n + 1) n (by omega) (by omega) a ctx j hS
    (by rw [e]; exact hR) (by rw [e]; exact hj))
  rintro (⟨a', ctx', j'⟩ | y) h
  · obtain ⟨-, h1, h2, h3⟩ := h
    exact ⟨n + 1, h1, h2, h3⟩
  · obtain ⟨h1, h2⟩ := h
    rw [e] at h1 h2
    exact ⟨_, n, RejBoundedPoly_of_full sp ρ n h2, h1⟩

/-- **RejBoundedPoly, partial correctness.** The Rust function never panics, and if it returns `r` then `r`
represents the spec's answer at some fuel. -/
theorem rej_bounded_poly_partial {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (ρ : Array U8 66#usize) :
    sampling.rej_bounded_poly ip ρ ⦃ r =>
      ∃ (a : RPoly) (F : Nat), Spec.RejBoundedPoly sp F (bytesA ρ) = some a ∧ ReprInt r a ⦄div := by
  unfold sampling.rej_bounded_poly
  step*
  subst s_post
  have hc : ShakeSqz ctx2 136 (bytesA ρ) 0 := by
    rw [List.nil_append, bytes_to_slice] at ctx2_post
    exact ctx2_post
  exact rej_bounded_loop_partial hp hη (bytesA ρ) _ ctx2 0#usize ⟨0, hc, reprInt_zero, rfl⟩

/-! ## ExpandS: the spec side -/

theorem fill_forIn_fst_none {β : Type} {n : Nat} (f : Nat → Option RPoly) (m : Nat) :
    ∀ (s : Nat) (v : Vector RPoly n), (∀ i, i < m → (f (s + i)).isSome) →
      (forIn (m := Id) (List.range' s m) (⟨none, v⟩ : FS β n) (fillBody f)).fst = none := by
  induction m with
  | zero => intro s v _; rfl
  | succ m ih =>
    intro s v h
    obtain ⟨a, hf⟩ := Option.isSome_iff_exists.mp (h 0 (by omega))
    rw [Nat.add_zero] at hf
    have e : forIn (m := Id) (List.range' s (m + 1)) (⟨none, v⟩ : FS β n) (fillBody f) =
        forIn (m := Id) (List.range' (s + 1) m) (⟨none, v.set! s a⟩ : FS β n) (fillBody f) := by
      simp [List.range'_succ, List.forIn_cons, fillBody, hf]
      try rfl
    rw [e]
    exact ih (s + 1) _ (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show s + (i + 1) = s + 1 + i by omega] at this)

/-- The converse of `ExpandS_some`: if every sample succeeds at fuel `fuel`, so does `ExpandS`. -/
theorem ExpandS_of_samplers (p : Params) (fuel : Nat) (ρ : List UInt8) (s₁ : Vector RPoly p.ℓ)
    (s₂ : Vector RPoly p.k)
    (h1 : ∀ (i : Nat) (hi : i < p.ℓ), RejBoundedPoly p fuel (ρ ++ IntegerToBytes i 2) = some s₁[i])
    (h2 : ∀ (i : Nat) (hi : i < p.k), RejBoundedPoly p fuel (ρ ++ IntegerToBytes (i + p.ℓ) 2) = some s₂[i]) :
    ExpandS p fuel ρ = some (s₁, s₂) := by
  rw [ExpandS_eq]
  unfold expandSModel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have n1 := fill_forIn_fst_none (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) p.ℓ 0
    (Vector.replicate p.ℓ (Vector.replicate 256 0)) (fun i hi => by simp [h1 i hi])
  have n2 := fill_forIn_fst_none (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) p.k 0
    (Vector.replicate p.k (Vector.replicate 256 0)) (fun i hi => by simp [h2 i hi])
  obtain ⟨w1, hw1⟩ := fill_forIn (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes r 2)) p.ℓ 0
    (Vector.replicate p.ℓ (Vector.replicate 256 0))
  obtain ⟨w2, hw2⟩ := fill_forIn (β := Vector RPoly p.ℓ × Vector RPoly p.k)
    (fun r => RejBoundedPoly p fuel (ρ ++ IntegerToBytes (r + p.ℓ) 2)) p.k 0
    (Vector.replicate p.k (Vector.replicate 256 0))
  rcases hw1 with ⟨e1, q1, -⟩ | e1
  swap
  · rw [e1] at n1
    simp at n1
  rcases hw2 with ⟨e2, q2, -⟩ | e2
  swap
  · rw [e2] at n2
    simp at n2
  have hw1eq : w1 = s₁ := by
    apply Vector.ext
    intro i hi
    have := q1 i hi (by simpa using hi)
    simp only [Nat.zero_add] at this
    rw [h1 i hi] at this
    exact (Option.some.inj this).symm
  have hw2eq : w2 = s₂ := by
    apply Vector.ext
    intro i hi
    have := q2 i hi (by simpa using hi)
    simp only [Nat.zero_add] at this
    rw [h2 i hi] at this
    exact (Option.some.inj this).symm
  rw [e1, e2]
  simp [hw1eq, hw2eq]

/-- Fuel monotonicity of `ExpandS`. -/
theorem ExpandS_mono (p : Params) (ρ : List UInt8) (F F' : Nat) (s₁ : Vector RPoly p.ℓ) (s₂ : Vector RPoly p.k)
    (h : ExpandS p F ρ = some (s₁, s₂)) (hF : F ≤ F') : ExpandS p F' ρ = some (s₁, s₂) := by
  obtain ⟨h1, h2⟩ := ExpandS_some p F ρ s₁ s₂ h
  exact ExpandS_of_samplers p F' ρ s₁ s₂ (fun i hi => RejBoundedPoly_mono p _ F F' _ (h1 i hi) hF)
    (fun i hi => RejBoundedPoly_mono p _ F F' _ (h2 i hi) hF)

/-! ## The Rust loops of `expand_s` -/

/-- Invariant of `expand_s_loop1`: the seed buffer starts with `ρ`, and rows `0 … r-1` are the samples of the
spec at some fuel `F`. -/
def L1Inv (sp : Spec.Params) {L : Usize} (ρ : Array U8 64#usize)
    (p : Array (Array U32 256#usize) L × Array U8 66#usize × Usize) : Prop :=
  p.2.2.val ≤ L.val ∧ (∀ i, i < 64 → (bytesA p.2.1)[i]? = (bytesA ρ)[i]?) ∧
  ∃ F : Nat, ∀ i, i < p.2.2.val → ∃ a' : RPoly,
    RejBoundedPoly sp F (bytesA ρ ++ IntegerToBytes i 2) = some a' ∧ ∃ q, p.1.val[i]? = some q ∧ ReprInt q a'

theorem expand_s_loop1_partial {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (hKL : sp.k + sp.ℓ < 256)
    (ρ : Array U8 64#usize) (s1 : Array (Array U32 256#usize) L) (seed : Array U8 66#usize)
    (hseed : ∀ i, i < 64 → (bytesA seed)[i]? = (bytesA ρ)[i]?) :
    sampling.expand_s_loop1 ip s1 seed 0#usize ⦃ r =>
      (∀ i, i < 64 → (bytesA r.2)[i]? = (bytesA ρ)[i]?) ∧
      ∃ F : Nat, ∀ i, i < sp.ℓ → ∃ a' : RPoly,
        RejBoundedPoly sp F (bytesA ρ ++ IntegerToBytes i 2) = some a' ∧
          ∃ q, r.1.val[i]? = some q ∧ ReprInt q a' ⦄div := by
  have hρl : (bytesA ρ).length = 64 := by simp
  have hLl := hp.L_eq
  unfold sampling.expand_s_loop1
  refine loop.dspec_inv _ (L1Inv sp ρ) _ ?_ (s1, seed, 0#usize)
    ⟨by simp, hseed, 0, fun i hi => by simp at hi⟩
  rintro ⟨s1', sd, r⟩ ⟨h1, h2, F, h3⟩
  dsimp only at h1 h2 h3
  simp only [sampling.expand_s_loop1.body]
  split
  · rename_i hr
    have hr' : r.val < L.val := by scalar_tac
    have hrl : r.val < sp.ℓ := by omega
    have hrlt : r.val < 256 := by omega
    step*
    have hi : i.val = r.val := by rw [i_post]; simp [UScalar.cast_val_eq]; omega
    have hbytes : bytesA seed2 = bytesA ρ ++ IntegerToBytes r.val 2 := by
      rw [seed2_post, seed1_post, seed_set sd _ hρl h2, ofNat_nonce _ hrlt, hi]
      rfl
    refine WP.dspec_bind' (rej_bounded_poly_partial hp hη seed2) ?_
    rintro a ⟨a', F1, hrej, ha⟩
    rw [hbytes] at hrej
    step*
    refine ⟨by scalar_tac, ?_, max F F1, ?_⟩
    · rw [seed2_post, seed1_post]
      exact seed_set_P sd _ hρl h2 _ _
    · intro j hj
      have hlen : s1'.val.length = L.val := s1'.property
      have hj' : j < r.val + 1 := by scalar_tac
      by_cases hjr : r.val = j
      · subst hjr
        refine ⟨a', RejBoundedPoly_mono sp _ F1 _ _ hrej (le_max_right _ _), a, ?_, ha⟩
        rw [a1_post, Array.set_val_eq, List.getElem?_set, if_pos rfl, if_pos (by omega)]
      · obtain ⟨a'', h4, q, hq, hqr⟩ := h3 j (by omega)
        refine ⟨a'', RejBoundedPoly_mono sp _ F _ _ h4 (le_max_left _ _), q, ?_, hqr⟩
        rw [a1_post, Array.set_val_eq, List.getElem?_set, if_neg hjr]
        exact hq
  · rename_i hr
    have : r.val = L.val := by scalar_tac
    simp only [WP.dspec_ok]
    refine ⟨h2, F, fun i hi => h3 i (by omega)⟩

/-- Invariant of `expand_s_loop2`. -/
def L2Inv (sp : Spec.Params) {K : Usize} (ρ : Array U8 64#usize)
    (p : Array (Array U32 256#usize) K × Array U8 66#usize × Usize) : Prop :=
  p.2.2.val ≤ K.val ∧ (∀ i, i < 64 → (bytesA p.2.1)[i]? = (bytesA ρ)[i]?) ∧
  ∃ F : Nat, ∀ i, i < p.2.2.val → ∃ a' : RPoly,
    RejBoundedPoly sp F (bytesA ρ ++ IntegerToBytes (i + sp.ℓ) 2) = some a' ∧
      ∃ q, p.1.val[i]? = some q ∧ ReprInt q a'

theorem expand_s_loop2_partial {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (hKL : sp.k + sp.ℓ < 256)
    (ρ : Array U8 64#usize) (s2 : Array (Array U32 256#usize) K) (seed : Array U8 66#usize)
    (hseed : ∀ i, i < 64 → (bytesA seed)[i]? = (bytesA ρ)[i]?) :
    sampling.expand_s_loop2 L ip s2 seed 0#usize ⦃ r =>
      ∃ F : Nat, ∀ i, i < sp.k → ∃ a' : RPoly,
        RejBoundedPoly sp F (bytesA ρ ++ IntegerToBytes (i + sp.ℓ) 2) = some a' ∧
          ∃ q, r.val[i]? = some q ∧ ReprInt q a' ⦄div := by
  have hρl : (bytesA ρ).length = 64 := by simp
  have hKk := hp.K_eq
  have hLl := hp.L_eq
  unfold sampling.expand_s_loop2
  refine loop.dspec_inv _ (L2Inv sp ρ) _ ?_ (s2, seed, 0#usize)
    ⟨by simp, hseed, 0, fun i hi => by simp at hi⟩
  rintro ⟨s2', sd, r⟩ ⟨h1, h2, F, h3⟩
  dsimp only at h1 h2 h3
  simp only [sampling.expand_s_loop2.body]
  split
  · rename_i hr
    have hr' : r.val < K.val := by scalar_tac
    have hrl : r.val < sp.k := by omega
    have hrlt : r.val + L.val < 256 := by omega
    step*
    have hi : i1.val = r.val + sp.ℓ := by
      rw [i1_post]; simp [UScalar.cast_val_eq]; omega
    have hbytes : bytesA seed2 = bytesA ρ ++ IntegerToBytes (r.val + sp.ℓ) 2 := by
      rw [seed2_post, seed1_post, seed_set sd _ hρl h2, ofNat_nonce _ (by omega), hi]
      rfl
    refine WP.dspec_bind' (rej_bounded_poly_partial hp hη seed2) ?_
    rintro a ⟨a', F1, hrej, ha⟩
    rw [hbytes] at hrej
    step*
    refine ⟨by scalar_tac, ?_, max F F1, ?_⟩
    · rw [seed2_post, seed1_post]
      exact seed_set_P sd _ hρl h2 _ _
    · intro j hj
      have hlen : s2'.val.length = K.val := s2'.property
      have hj' : j < r.val + 1 := by scalar_tac
      by_cases hjr : r.val = j
      · subst hjr
        refine ⟨a', RejBoundedPoly_mono sp _ F1 _ _ hrej (le_max_right _ _), a, ?_, ha⟩
        rw [a1_post, Array.set_val_eq, List.getElem?_set, if_pos rfl, if_pos (by omega)]
      · obtain ⟨a'', h4, q, hq, hqr⟩ := h3 j (by omega)
        refine ⟨a'', RejBoundedPoly_mono sp _ F _ _ h4 (le_max_left _ _), q, ?_, hqr⟩
        rw [a1_post, Array.set_val_eq, List.getElem?_set, if_neg hjr]
        exact hq
  · rename_i hr
    have : r.val = K.val := by scalar_tac
    simp only [WP.dspec_ok]
    exact ⟨F, fun i hi => h3 i (by omega)⟩

end PartialSampleS

open PartialSampleS

/-- **RejBoundedPoly, partial correctness** (Algorithm 31). -/
theorem rej_bounded_poly_partial {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (ρ : Array U8 66#usize) :
    sampling.rej_bounded_poly ip ρ ⦃ r =>
      ∃ (a : RPoly) (F : Nat), Spec.RejBoundedPoly sp F (bytesA ρ) = some a ∧ ReprInt r a ⦄div :=
  PartialSampleS.rej_bounded_poly_partial hp hη ρ

/-- **ExpandS, partial correctness** (Algorithm 33). The Rust function never panics, and if it returns `(r₁, r₂)`
then they represent the spec's `(s₁, s₂)` at some fuel. (The older `expand_s_spec` is the converse.) -/
theorem expand_s_partial {ip : params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Valid ip K L sp) (hη : sp.η = 2 ∨ sp.η = 4) (hKL : sp.k + sp.ℓ < 256)
    (ρ : Array U8 64#usize) :
    sampling.expand_s K L ip ρ ⦃ r =>
      ∃ (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k) (F : Nat),
        Spec.ExpandS sp F (bytesA ρ) = some (s₁, s₂) ∧ ReprIntVec r.1 s₁ ∧ ReprIntVec r.2 s₂ ⦄div := by
  unfold sampling.expand_s
  refine dspec_bind_of_spec (expand_s_loop0_spec ρ _) ?_
  intro seed1 hseed1
  refine WP.dspec_bind' (expand_s_loop1_partial hp hη hKL ρ _ seed1 hseed1) ?_
  rintro ⟨s11, seed2⟩ ⟨h2, F1, h1⟩
  refine WP.dspec_bind' (expand_s_loop2_partial hp hη hKL ρ _ seed2 h2) ?_
  intro s21 ⟨F2, h3⟩
  simp only [WP.dspec_ok]
  choose f1 hf1 using h1
  choose f2 hf2 using h3
  let S₁ : Vector RPoly sp.ℓ := Vector.ofFn (fun i : Fin sp.ℓ => f1 i i.2)
  let S₂ : Vector RPoly sp.k := Vector.ofFn (fun i : Fin sp.k => f2 i i.2)
  have e1 : ∀ (i : Nat) (hi : i < sp.ℓ), S₁[i] = f1 i hi := fun i hi => by simp [S₁]
  have e2 : ∀ (i : Nat) (hi : i < sp.k), S₂[i] = f2 i hi := fun i hi => by simp [S₂]
  refine ⟨S₁, S₂, max F1 F2, ExpandS_of_samplers sp _ _ S₁ S₂ (fun i hi => ?_) (fun i hi => ?_), ?_, ?_⟩
  · rw [e1]
    exact RejBoundedPoly_mono sp _ F1 _ _ (hf1 i hi).1 (le_max_left _ _)
  · rw [e2]
    exact RejBoundedPoly_mono sp _ F2 _ _ (hf2 i hi).1 (le_max_right _ _)
  · refine ⟨hp.L_eq, fun i hi => ?_⟩
    obtain ⟨q, hq, hr⟩ := (hf1 i hi).2
    have hlt : i < s11.val.length := by have := s11.property; have := hp.L_eq; omega
    show ReprInt (s11.val[i]'hlt) _
    rw [getElem_of_getElem?_eq hlt hq, e1]
    exact hr
  · refine ⟨hp.K_eq, fun i hi => ?_⟩
    obtain ⟨q, hq, hr⟩ := (hf2 i hi).2
    have hlt : i < s21.val.length := by have := s21.property; have := hp.K_eq; omega
    show ReprInt (s21.val[i]'hlt) _
    rw [getElem_of_getElem?_eq hlt hq, e2]
    exact hr

end Proofs
