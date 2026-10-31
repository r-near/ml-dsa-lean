import XSpec.SignStep

/-!
# `Sign_internal` (Algorithm 7) against ocaml-pq's `signInternalMu`

One attempt (`attemptAt`) against ocaml-pq's `alg7Step`, then the loop (`loopRes` against `alg7Loop`), then the
top-level statements.
-/

open Spec

namespace XSpec

open OcamlPq.EndToEnd.MLDSA

namespace SGB

/-! ## The data of an attempt -/

/-- ocaml-pq's commitment hash `c̃` of an attempt, as it appears in `alg7Step`. -/
def alg7CT (F : OcamlPq.MLDSAAlg.SignFips) (P : OcamlPq.MLDSAAlg.Params) (lam : ℕ) (H : OcamlPq.MLDSAAlg.XOF)
    (A : OcamlPq.MLDSAAlg.PolyMat) (mu : OcamlPq.MLDSAAlg.Bytes) (y : OcamlPq.MLDSAAlg.PolyVec) :
    OcamlPq.MLDSAAlg.Bytes :=
  H.squeeze (mu ++ OcamlPq.MLDSAAlg.w1Encode F P
    (fun r i => F.highBits (F.NTTinv (F.mulMatVec A (fun i => F.NTT (y i)) r) i))) (lam / 4)

theorem alg7Step_unfold (F : OcamlPq.MLDSAAlg.SignFips) (P : OcamlPq.MLDSAAlg.Params) (lam : ℕ)
    (H : OcamlPq.MLDSAAlg.XOF) (A : OcamlPq.MLDSAAlg.PolyMat) (mu : OcamlPq.MLDSAAlg.Bytes)
    (y : OcamlPq.MLDSAAlg.PolyVec) :
    OcamlPq.MLDSAAlg.alg7Step F P lam H A mu y =
      match F.finish y (fun r => F.NTTinv (F.mulMatVec A (fun i => F.NTT (y i)) r))
          (F.NTT (OcamlPq.MLDSAAlg.sampleInBall P.tau (H (alg7CT F P lam H A mu y)))) with
      | some zh => some (F.sigEncode (alg7CT F P lam H A mu y) zh.1 zh.2)
      | none => none :=
  rfl

/-- The relation between the decoded data of Algorithm 7 (`P`) and ocaml-pq's inputs. -/
structure Rel (sp : Spec.Params) (P : SG.Pre sp) (key : OcamlPq.MLDSAAlg.ExpandedKey)
    (rho mu rhoPP : OcamlPq.MLDSAAlg.Bytes) : Prop where
  s1 : ∀ r, key.s1 r = rfn P.s₁[r]!
  s2 : ∀ r, key.s2 r = rfn P.s₂[r]!
  t0 : ∀ r, key.t0 r = rfn P.t₀[r]!
  A : ∀ r < sp.k, ∀ s < sp.ℓ, canon ((P.Â[r]!)[s]!) = OcamlPq.MLDSAAlg.expandA oursShake128 rho r s
  mu : u8ToBytes P.μ = mu
  rho : u8ToBytes P.ρ'' = rhoPP

/-- ocaml-pq's mask of the attempt with counter `κ`. -/
def mk (sp : Spec.Params) (rhoPP : OcamlPq.MLDSAAlg.Bytes) (κ : ℕ) : OcamlPq.MLDSAAlg.PolyVec :=
  fun r => OcamlPq.MLDSAAlg.expandMask oursShake256 (algParams sp) fipsBitUnpack rhoPP κ r

variable {sp : Spec.Params} {P : SG.Pre sp} {key : OcamlPq.MLDSAAlg.ExpandedKey}
  {rho mu rhoPP : OcamlPq.MLDSAAlg.Bytes}

theorem mask_rows (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (κ : ℕ) (r : ℕ) (hr : r < sp.ℓ) :
    mk sp rhoPP κ r = rfn ((ExpandMask sp P.ρ'' κ)[r]!) := by
  rw [expandMask_eq hp P.ρ'' κ r hr, h.rho]
  rfl

theorem commit_rows (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (κ : ℕ) (r : ℕ) (hr : r < sp.k) :
    fipsNTTinv (fipsMulMatVec (algParams sp).l (OcamlPq.MLDSAAlg.expandA oursShake128 rho)
        (fun i => fipsNTT (mk sp rhoPP κ i)) r) =
      canon ((SG.commitAt sp P κ)[r]!) := by
  unfold SG.commitAt
  rw [NTTInvVec_get _ r hr, ← fipsNTTinv_eq, matrixVectorNTT_eq _ _ r hr]
  congr 1
  refine fipsMulMatVec_local sp.ℓ _ _ _ _ r (fun s hs => (h.A r hr s hs).symm) (fun s hs => ?_)
  rw [mask_rows hp h κ s hs, SG.maskAt, NTTVec_get _ s hs, map_get!_lt _ _ s hs]
  exact fipsNTT_rfn _

theorem highBits_zero (γ2 : ℤ) (h : 0 < γ2) : OcamlPq.MLDSA.highBits γ2 0 = 0 := by
  unfold OcamlPq.MLDSA.highBits OcamlPq.MLDSA.decomposeSpec OcamlPq.MLDSA.modPM
  have h1 : ¬ ((0 : ℤ) > γ2) := by omega
  have h2 : ¬ ((0 : ℤ) = OcamlPq.MLDSA.q - 1) := by unfold OcamlPq.MLDSA.q; omega
  simp [h1, h2]

theorem w1_rows (hp : Std3 sp) (W : Vector Poly sp.k) (r : ℕ) (hr : r < sp.k) :
    (fun i => OcamlPq.MLDSA.highBits (sp.γ₂ : ℤ) (canon (W[r]!) i)) = rfn ((HighBitsVec sp W)[r]!) := by
  funext i
  by_cases hi : i < 256
  · simp only [rfn, canon]
    unfold HighBitsVec
    rw [map_get!_lt _ _ r hr, map_get!_lt _ _ i hi, highBits_eq]
  · have hi' : 256 ≤ i := by omega
    rw [canon_zero_of_ge _ hi']
    simp only [rfn]
    rw [getElem!_neg _ i (by simpa using hi)]
    have hg : 0 < (sp.γ₂ : ℤ) := by rcases hp with rfl | rfl | rfl <;> decide +kernel
    rw [highBits_zero _ hg]
    rfl

theorem ct_eq_gen (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (F : OcamlPq.MLDSAAlg.SignFips)
    (h1 : F.simpleBitPack = fipsSimpleBitPack) (h2 : F.NTT = fipsNTT) (h3 : F.NTTinv = fipsNTTinv)
    (h4 : F.mulMatVec = fipsMulMatVec (algParams sp).l)
    (h5 : F.highBits = OcamlPq.MLDSA.highBits (algParams sp).gamma2) (κ : ℕ) :
    alg7CT F (algParams sp) sp.lam oursShake256 (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu (mk sp rhoPP κ) =
      u8ToBytes (SG.ctildeAt sp P κ) := by
  have hw : OcamlPq.MLDSAAlg.w1Encode F (algParams sp)
      (fun r i => F.highBits (F.NTTinv (F.mulMatVec (OcamlPq.MLDSAAlg.expandA oursShake128 rho)
        (fun i => F.NTT (mk sp rhoPP κ i)) r) i)) =
      OcamlPq.MLDSAAlg.w1Encode F (algParams sp)
        (fun i => rfn ((HighBitsVec sp (SG.commitAt sp P κ))[i]!)) := by
    unfold OcamlPq.MLDSAAlg.w1Encode
    refine KG.foldl_range_congr _ _ _ (fun a r hr => ?_) _
    beta_reduce
    have hr' : r < sp.k := hr
    have e : (fun i => F.highBits (F.NTTinv (F.mulMatVec (OcamlPq.MLDSAAlg.expandA oursShake128 rho)
        (fun i => F.NTT (mk sp rhoPP κ i)) r) i)) = rfn ((HighBitsVec sp (SG.commitAt sp P κ))[r]!) := by
      funext i
      have := congrFun (w1_rows hp (SG.commitAt sp P κ) r hr') i
      rw [h2, h3, h4, h5]
      rw [commit_rows hp h κ r hr']
      exact this
    rw [e]
  unfold alg7CT SG.ctildeAt
  rw [H_eq, u8ToBytes_append, h.mu, w1Encode_eq hp F h1, hw]

theorem ct_eq (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (κ : ℕ) :
    alg7CT (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
        (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu (mk sp rhoPP κ) =
      u8ToBytes (SG.ctildeAt sp P κ) :=
  ct_eq_gen hp h _ (by simp only [signFips]) (by simp only [signFips]) (by simp only [signFips])
    (by simp only [signFips]) (by simp only [signFips]) κ

theorem respond_hw (y : Vector Poly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly) (zh)
    (h : SG.respond sp P y w c = some zh) : HintWeight zh.2 ≤ sp.ω := by
  rw [respond_eq'] at h
  split_ifs at h with h1 h2
  cases h
  push_neg at h2
  exact h2.2

/-- **One attempt, ours to theirs.**  Given the challenge `c` (with `rfn c` ocaml-pq's `SampleInBall` of `c̃`),
ocaml-pq's `alg7Step` is our `respond`, encoded. -/
theorem step_eq_gen (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (F : OcamlPq.MLDSAAlg.SignFips)
    (h1 : F.simpleBitPack = fipsSimpleBitPack) (h2 : F.NTT = fipsNTT) (h3 : F.NTTinv = fipsNTTinv)
    (h4 : F.mulMatVec = fipsMulMatVec (algParams sp).l)
    (h5 : F.highBits = OcamlPq.MLDSA.highBits (algParams sp).gamma2)
    (hFin : F.finish = fipsFinish (algParams sp) key) (hSig : F.sigEncode = fipsSigEncode (algParams sp))
    (κ : ℕ) (c : RPoly)
    (hc : rfn c = OcamlPq.MLDSAAlg.sampleInBall (algParams sp).tau (oursShake256 (u8ToBytes (SG.ctildeAt sp P κ)))) :
    OcamlPq.MLDSAAlg.alg7Step F (algParams sp) sp.lam oursShake256 (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu
        (mk sp rhoPP κ) =
      (SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c).map
        (fun zh => u8ToBytes (sigEncode sp (SG.ctildeAt sp P κ) (zh.1.map Poly.modPM) zh.2)) := by
  have hfin := respond_eq_fipsFinish P (ExpandMask sp P.ρ'' κ) (SG.commitAt sp P κ) c hp key h.s1 h.s2 h.t0
  rw [alg7Step_unfold, ct_eq_gen hp h F h1 h2 h3 h4 h5 κ, ← hc, h2, h3, h4, hFin, hSig]
  rw [fipsFinish_local (algParams sp) key (mk sp rhoPP κ) (fun r => rfn (ExpandMask sp P.ρ'' κ)[r]!) _
    (fun r => canon ((SG.commitAt sp P κ)[r]!)) _
    (fun s hs => mask_rows hp h κ s hs) (fun r hr => by
      funext i
      have := commit_rows hp h κ r hr
      exact congrFun this i)]
  have hfin' : fipsFinish (algParams sp) key (fun r => rfn (ExpandMask sp P.ρ'' κ)[r]!)
      (fun r => canon ((SG.commitAt sp P κ)[r]!)) (fipsNTT (rfn c)) =
      (SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c).map
        (fun x => ((fun r => rfn ((x.1.map Poly.modPM)[r]!)), hpoly x.2)) := hfin.symm
  rw [hfin']
  rcases hr : SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c with _ | ⟨z, hh⟩
  · rfl
  · have hw := respond_hw (P := P) _ _ c (z, hh) hr
    show some _ = some _
    exact congrArg some (sigEncode_eq hp _ (z.map Poly.modPM) hh hw).symm

theorem step_eq (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (κ : ℕ) (c : RPoly)
    (hc : rfn c = OcamlPq.MLDSAAlg.sampleInBall (algParams sp).tau (oursShake256 (u8ToBytes (SG.ctildeAt sp P κ)))) :
    OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
        (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu (mk sp rhoPP κ) =
      (SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c).map
        (fun zh => u8ToBytes (sigEncode sp (SG.ctildeAt sp P κ) (zh.1.map Poly.modPM) zh.2)) :=
  step_eq_gen hp h _ (by simp only [signFips]) (by simp only [signFips]) (by simp only [signFips])
    (by simp only [signFips]) (by simp only [signFips]) (by simp only [signFips]) (by simp only [signFips]) κ c hc

/-! ## The loop -/

variable (F : Spec.Fuel)

theorem loopRes_accept (P : SG.Pre sp) :
    ∀ n i ct z h, SG.loopRes sp F P n (i * sp.ℓ) = some (some (ct, z, h)) →
      ∃ j, i ≤ j ∧ j < i + n ∧ SG.attemptAt sp F P (j * sp.ℓ) = some (ct, some (z, h)) ∧
        ∀ j', i ≤ j' → j' < j → ∃ ct', SG.attemptAt sp F P (j' * sp.ℓ) = some (ct', none) := by
  intro n
  induction n with
  | zero => intro i ct z h hl; simp [SG.loopRes] at hl
  | succ n ih =>
    intro i ct z h hl
    unfold SG.loopRes at hl
    by_cases hg : 2 ^ 16 < i * sp.ℓ + sp.ℓ
    · rw [if_pos hg] at hl; simp at hl
    rw [if_neg hg] at hl
    rcases hat : SG.attemptAt sp F P (i * sp.ℓ) with _ | ⟨ct', _ | ⟨z', h'⟩⟩
    · rw [hat] at hl; simp at hl
    · rw [hat] at hl
      simp only [] at hl
      have hl' : SG.loopRes sp F P n ((i + 1) * sp.ℓ) = some (some (ct, z, h)) := by
        rw [Nat.add_one_mul]; exact hl
      obtain ⟨j, h1, h2, h3, h4⟩ := ih (i + 1) ct z h hl'
      refine ⟨j, by omega, by omega, h3, fun j' hj1 hj2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hj1 with rfl | hlt
      · exact ⟨ct', hat⟩
      · exact h4 j' hlt hj2
    · rw [hat] at hl
      simp only [Option.some.injEq] at hl
      obtain ⟨rfl, rfl, rfl⟩ : ct' = ct ∧ z' = z ∧ h' = h := by
        simpa using hl
      exact ⟨i, le_rfl, by omega, hat, fun j' h1 h2 => by omega⟩

theorem loopRes_none (P : SG.Pre sp) :
    ∀ n i, (∀ j, i ≤ j → j < i + n → (j + 1) * sp.ℓ ≤ 2 ^ 16 ∧ ∃ ct, SG.attemptAt sp F P (j * sp.ℓ) = some (ct, none)) →
      SG.loopRes sp F P n (i * sp.ℓ) = some none := by
  intro n
  induction n with
  | zero => intro i _; rfl
  | succ n ih =>
    intro i hall
    obtain ⟨hg, ct, hat⟩ := hall i le_rfl (by omega)
    unfold SG.loopRes
    have hg' : ¬ 2 ^ 16 < i * sp.ℓ + sp.ℓ := by rw [← Nat.add_one_mul]; omega
    rw [if_neg hg', hat]
    simp only []
    rw [← Nat.add_one_mul]
    exact ih (i + 1) (fun j h1 h2 => hall j (by omega) (by omega))

theorem loopRes_accept_of (P : SG.Pre sp) :
    ∀ n i j ct z h, i ≤ j → j < i + n →
      (∀ j', i ≤ j' → j' ≤ j → (j' + 1) * sp.ℓ ≤ 2 ^ 16) →
      (∀ j', i ≤ j' → j' < j → ∃ ct', SG.attemptAt sp F P (j' * sp.ℓ) = some (ct', none)) →
      SG.attemptAt sp F P (j * sp.ℓ) = some (ct, some (z, h)) →
      SG.loopRes sp F P n (i * sp.ℓ) = some (some (ct, z, h)) := by
  intro n
  induction n with
  | zero => intro i j ct z h h1 h2; omega
  | succ n ih =>
    intro i j ct z h h1 h2 hg hb ha
    unfold SG.loopRes
    have hg' : ¬ 2 ^ 16 < i * sp.ℓ + sp.ℓ := by
      rw [← Nat.add_one_mul]; have := hg i le_rfl h1; omega
    rw [if_neg hg']
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rw [ha]
    · obtain ⟨ct', hct'⟩ := hb i le_rfl hlt
      rw [hct']
      simp only []
      rw [← Nat.add_one_mul]
      exact ih (i + 1) j ct z h hlt (by omega) (fun j' a b => hg j' (by omega) b)
        (fun j' a b => hb j' (by omega) b) ha

/-! ## ocaml-pq's loop -/

theorem alg7Loop_eq_none {σ : Type} (l : ℕ) (em : ℕ → ℕ → OcamlPq.MLDSAAlg.Poly)
    (step : (ℕ → OcamlPq.MLDSAAlg.Poly) → Option σ) :
    ∀ fuel i, OcamlPq.MLDSAAlg.alg7Loop l em step fuel (i * l) = none ↔
      ∀ j, i ≤ j → j < i + fuel → step (em (j * l)) = none := by
  intro fuel
  induction fuel with
  | zero => intro i; simp [OcamlPq.MLDSAAlg.alg7Loop]; intro j h1 h2; omega
  | succ f ih =>
    intro i
    rw [OcamlPq.MLDSAAlg.alg7Loop]
    cases hs : step (em (i * l)) with
    | some s =>
      simp only []
      constructor
      · intro h; cases h
      · intro h; have := h i le_rfl (by omega); rw [hs] at this; cases this
    | none =>
      simp only []
      rw [← Nat.add_one_mul, ih (i + 1)]
      constructor
      · intro h j h1 h2
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact hs
        · exact h j hlt (by omega)
      · intro h j h1 h2
        exact h j (by omega) (by omega)

theorem alg7Loop_first {σ : Type} (l : ℕ) (em : ℕ → ℕ → OcamlPq.MLDSAAlg.Poly)
    (step : (ℕ → OcamlPq.MLDSAAlg.Poly) → Option σ) (j : ℕ) (s : σ)
    (hj : step (em (j * l)) = some s) (hb : ∀ j', j' < j → step (em (j' * l)) = none) :
    ∀ fuel i, i ≤ j → OcamlPq.MLDSAAlg.alg7Loop l em step fuel (i * l) = if j < i + fuel then some s else none := by
  intro fuel
  induction fuel with
  | zero => intro i hi; simp [OcamlPq.MLDSAAlg.alg7Loop]; omega
  | succ f ih =>
    intro i hi
    rw [OcamlPq.MLDSAAlg.alg7Loop]
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · rw [hj]; simp only []; rw [if_pos (by omega)]
    · rw [hb i hlt]
      simp only []
      rw [← Nat.add_one_mul, ih (i + 1) (by omega)]
      congr 1
      simp only [eq_iff_iff]
      omega

/-- ocaml-pq's attempt loop with `m` iterations, in terms of our `mk`. -/
noncomputable def thLoop (sp : Spec.Params) (key : OcamlPq.MLDSAAlg.ExpandedKey) (rho mu rhoPP : OcamlPq.MLDSAAlg.Bytes)
    (m : ℕ) : Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.alg7Loop (algParams sp).l (fun κ r => mk sp rhoPP κ r)
    (OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
      (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu) m 0

/-- One attempt of ocaml-pq's loop. -/
noncomputable def thStep (sp : Spec.Params) (key : OcamlPq.MLDSAAlg.ExpandedKey) (rho mu rhoPP : OcamlPq.MLDSAAlg.Bytes)
    (j : ℕ) : Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
    (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu (mk sp rhoPP (j * sp.ℓ))

theorem thLoop_none (m : ℕ) :
    thLoop sp key rho mu rhoPP m = none ↔ ∀ j, j < m → thStep sp key rho mu rhoPP j = none := by
  have := alg7Loop_eq_none (σ := OcamlPq.MLDSAAlg.Bytes) (algParams sp).l (fun κ r => mk sp rhoPP κ r)
    (OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
      (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu) m 0
  simp only [Nat.zero_mul, Nat.zero_add, Nat.zero_le, true_imp_iff] at this
  exact this

theorem thLoop_first (j : ℕ) (s : OcamlPq.MLDSAAlg.Bytes) (hj : thStep sp key rho mu rhoPP j = some s)
    (hb : ∀ j', j' < j → thStep sp key rho mu rhoPP j' = none) (m : ℕ) :
    thLoop sp key rho mu rhoPP m = if j < m then some s else none := by
  have := alg7Loop_first (σ := OcamlPq.MLDSAAlg.Bytes) (algParams sp).l (fun κ r => mk sp rhoPP κ r)
    (OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
      (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu) j s hj hb m 0 (Nat.zero_le _)
  simp only [Nat.zero_mul, Nat.zero_add] at this
  exact this

theorem thLoop_some (m : ℕ) (s : OcamlPq.MLDSAAlg.Bytes) (h : thLoop sp key rho mu rhoPP m = some s) :
    ∃ j, j < m ∧ thStep sp key rho mu rhoPP j = some s ∧ ∀ j', j' < j → thStep sp key rho mu rhoPP j' = none := by
  have := (OcamlPq.MLDSAAlg.alg7Loop_eq (algParams sp).l (fun κ r => mk sp rhoPP κ r)
    (OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
      (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu) m 0 s)
  simp only [Nat.zero_mul] at this
  obtain ⟨j, -, h2, h3, h4⟩ := this.mp h
  exact ⟨j, by omega, h3, fun j' hj => h4 j' (Nat.zero_le _) hj⟩

/-! ## Our attempt against ocaml-pq's step -/

theorem attemptAt_some {F : Spec.Fuel} {P : SG.Pre sp} {κ : ℕ} {ct : List UInt8} {r}
    (ha : SG.attemptAt sp F P κ = some (ct, r)) :
    ∃ c, Spec.SampleInBall sp F.sampleInBall (SG.ctildeAt sp P κ) = some c ∧ ct = SG.ctildeAt sp P κ ∧
      r = SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c := by
  unfold SG.attemptAt at ha
  rcases hsib : Spec.SampleInBall sp F.sampleInBall (SG.ctildeAt sp P κ) with _ | c
  · rw [hsib] at ha; simp at ha
  · rw [hsib] at ha
    simp only [Option.some.injEq, Prod.mk.injEq] at ha
    exact ⟨c, rfl, ha.1.symm, ha.2.symm⟩

theorem attemptAt_of {F : Spec.Fuel} {P : SG.Pre sp} {κ : ℕ} {c : RPoly}
    (h : Spec.SampleInBall sp F.sampleInBall (SG.ctildeAt sp P κ) = some c) :
    SG.attemptAt sp F P κ = some (SG.ctildeAt sp P κ, SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c) := by
  unfold SG.attemptAt
  rw [h]

theorem step_of_sib (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (κ : ℕ) (n : ℕ) (c : RPoly)
    (hc : Spec.SampleInBall sp n (SG.ctildeAt sp P κ) = some c) :
    OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
        (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu (mk sp rhoPP κ) =
      (SG.respond sp P (SG.maskAt sp P κ) (SG.commitAt sp P κ) c).map
        (fun zh => u8ToBytes (sigEncode sp (SG.ctildeAt sp P κ) (zh.1.map Poly.modPM) zh.2)) :=
  step_eq hp h κ c (SB.sampleInBall_ours_to_theirs hp _ n c hc).eq

theorem thStep_of_attempt (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) {F : Spec.Fuel} {κ : ℕ} {ct r}
    (ha : SG.attemptAt sp F P κ = some (ct, r)) :
    OcamlPq.MLDSAAlg.alg7Step (signFips (algParams sp) key) (algParams sp) sp.lam oursShake256
        (OcamlPq.MLDSAAlg.expandA oursShake128 rho) mu (mk sp rhoPP κ) =
      r.map (fun zh => u8ToBytes (sigEncode sp ct (zh.1.map Poly.modPM) zh.2)) := by
  obtain ⟨c, hc, rfl, rfl⟩ := attemptAt_some ha
  exact step_of_sib hp h κ _ c hc

/-- **The loop, ours to theirs.**  If our loop with `n` attempts accepts, it accepts at some attempt `a < n`, and
ocaml-pq's loop with `m` iterations gives the same signature exactly when `a < m`, and `none` otherwise. -/
theorem core_ours_to_theirs (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (F : Spec.Fuel) (n : ℕ) (σ : List UInt8)
    (hs : SG.encodeRes sp (SG.loopRes sp F P n 0) = some σ) :
    ∃ a, a < n ∧ ∀ m, thLoop sp key rho mu rhoPP m = if a < m then some (u8ToBytes σ) else none := by
  rcases hl : SG.loopRes sp F P n 0 with _ | _ | ⟨ct, z, hh⟩
  · rw [hl] at hs; simp [SG.encodeRes] at hs
  · rw [hl] at hs; simp [SG.encodeRes] at hs
  · rw [hl] at hs
    simp only [SG.encodeRes, Option.some.injEq] at hs
    subst hs
    have hl' : SG.loopRes sp F P n (0 * sp.ℓ) = some (some (ct, z, hh)) := by rw [Nat.zero_mul]; exact hl
    obtain ⟨j, -, hj2, hat, hbef⟩ := loopRes_accept F P n 0 ct z hh hl'
    have hstep : thStep sp key rho mu rhoPP j = some (u8ToBytes (sigEncode sp ct (z.map Poly.modPM) hh)) := by
      unfold thStep
      rw [thStep_of_attempt hp h hat]
      rfl
    have hb : ∀ j', j' < j → thStep sp key rho mu rhoPP j' = none := by
      intro j' hj'
      obtain ⟨ct', hat'⟩ := hbef j' (Nat.zero_le _) hj'
      unfold thStep
      rw [thStep_of_attempt hp h hat']
      rfl
    exact ⟨j, by omega, fun m => thLoop_first j _ hstep hb m⟩

/-- **The loop, theirs to ours (accepting).**  If ocaml-pq's loop with `m` iterations produces `s`, and every
`SampleInBall` call that the loop reaches returns on our side (for the fuel `F`), then our loop with
`n ≥ m` attempts accepts the same signature. -/
theorem core_theirs_to_ours (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (F : Spec.Fuel) (n m : ℕ) (hm : m ≤ n)
    (hg : m * sp.ℓ ≤ 2 ^ 16) (s : OcamlPq.MLDSAAlg.Bytes) (hs : thLoop sp key rho mu rhoPP m = some s)
    (hsamp : ∀ j, j < m → (∀ j', j' < j → thStep sp key rho mu rhoPP j' = none) →
      ∃ c, Spec.SampleInBall sp F.sampleInBall (SG.ctildeAt sp P (j * sp.ℓ)) = some c) :
    ∃ σ, SG.encodeRes sp (SG.loopRes sp F P n 0) = some σ ∧ u8ToBytes σ = s := by
  obtain ⟨j, hjm, hj, hb⟩ := thLoop_some m s hs
  have hgj : ∀ j', j' ≤ j → (j' + 1) * sp.ℓ ≤ 2 ^ 16 := by
    intro j' hj'
    have : (j' + 1) * sp.ℓ ≤ m * sp.ℓ := Nat.mul_le_mul_right _ (by omega)
    omega
  have hrej : ∀ j', j' < j → ∃ ct, SG.attemptAt sp F P (j' * sp.ℓ) = some (ct, none) := by
    intro j' hj'
    obtain ⟨c, hc⟩ := hsamp j' (by omega) (fun j'' hj'' => hb j'' (by omega))
    have ha := attemptAt_of (P := P) hc
    refine ⟨SG.ctildeAt sp P (j' * sp.ℓ), ?_⟩
    rw [ha]
    have hst := hb j' hj'
    unfold thStep at hst
    rw [thStep_of_attempt hp h ha] at hst
    simp only [Option.map_eq_none_iff] at hst
    rw [hst]
  obtain ⟨c, hc⟩ := hsamp j hjm (fun j'' hj'' => hb j'' hj'')
  have ha := attemptAt_of (P := P) hc
  have hst := hj
  unfold thStep at hst
  rw [thStep_of_attempt hp h ha] at hst
  obtain ⟨⟨z, hh⟩, hzh, hzs⟩ := Option.map_eq_some_iff.mp hst
  rw [hzh] at ha
  have hl := loopRes_accept_of F P n 0 j (SG.ctildeAt sp P (j * sp.ℓ)) z hh (Nat.zero_le _) (by omega)
    (fun j' _ h2 => hgj j' h2) (fun j' _ h2 => hrej j' h2) ha
  rw [Nat.zero_mul] at hl
  exact ⟨_, by rw [hl]; rfl, hzs⟩

/-- **The loop, theirs to ours (exhausted).**  If ocaml-pq's loop with `m` iterations returns `none`, and every
`SampleInBall` call returns on our side, then our loop with `m` attempts gives `none` too. -/
theorem core_theirs_to_ours_none (hp : Std3 sp) (h : Rel sp P key rho mu rhoPP) (F : Spec.Fuel) (m : ℕ)
    (hg : m * sp.ℓ ≤ 2 ^ 16) (hs : thLoop sp key rho mu rhoPP m = none)
    (hsamp : ∀ j, j < m → ∃ c, Spec.SampleInBall sp F.sampleInBall (SG.ctildeAt sp P (j * sp.ℓ)) = some c) :
    SG.encodeRes sp (SG.loopRes sp F P m 0) = none := by
  have hnone := (thLoop_none m).mp hs
  have := loopRes_none F P m 0 (fun j _ hj => by
    rw [Nat.zero_add] at hj
    refine ⟨?_, ?_⟩
    · have : (j + 1) * sp.ℓ ≤ m * sp.ℓ := Nat.mul_le_mul_right _ (by omega)
      omega
    · obtain ⟨c, hc⟩ := hsamp j hj
      have ha := attemptAt_of (P := P) hc
      refine ⟨SG.ctildeAt sp P (j * sp.ℓ), ?_⟩
      rw [ha]
      have hst := hnone j hj
      unfold thStep at hst
      rw [thStep_of_attempt hp h ha] at hst
      simp only [Option.map_eq_none_iff] at hst
      rw [hst])
  rw [Nat.zero_mul] at this
  rw [this]
  rfl

/-! ## The decoded key and the top level -/

/-- ocaml-pq's `ExpandedKey` for the key that our `skDecode` yields (`ρ`, `K`, `tr`, `s₁`, `s₂`, `t₀`). -/
def keyOfSk (sp : Spec.Params) (sk : List UInt8) : OcamlPq.MLDSAAlg.ExpandedKey where
  rho := u8ToBytes (Spec.skDecode sp sk).1
  key := u8ToBytes (Spec.skDecode sp sk).2.1
  tr := u8ToBytes (Spec.skDecode sp sk).2.2.1
  s1 := fun r => rfn (Spec.skDecode sp sk).2.2.2.1[r]!
  s2 := fun r => rfn (Spec.skDecode sp sk).2.2.2.2.1[r]!
  t0 := fun r => rfn (Spec.skDecode sp sk).2.2.2.2.2[r]!

/-- `μ = H(tr ‖ M′, 64)`, on ocaml-pq's side. -/
def muTh (sp : Spec.Params) (sk M' : List UInt8) : OcamlPq.MLDSAAlg.Bytes :=
  oursShake256.squeeze ((keyOfSk sp sk).tr ++ u8ToBytes M') 64

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`, on ocaml-pq's side. -/
def rppTh (sp : Spec.Params) (sk M' rnd : List UInt8) : OcamlPq.MLDSAAlg.Bytes :=
  oursShake256.squeeze ((keyOfSk sp sk).key ++ u8ToBytes rnd ++ muTh sp sk M') 64

/-- ocaml-pq's `signInternalMu` for our decoded key, the message representative `H(tr ‖ M′)` and `m` iterations. -/
noncomputable def thSignInternal (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) :
    Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.signInternalMu (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam oursShake256
    oursShake128 (keyOfSk sp sk).rho (keyOfSk sp sk).key (muTh sp sk M') (u8ToBytes rnd) m

theorem thSignInternal_eq (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) :
    thSignInternal sp sk M' rnd m =
      thLoop sp (keyOfSk sp sk) (keyOfSk sp sk).rho (muTh sp sk M') (rppTh sp sk M' rnd) m := by
  unfold thSignInternal OcamlPq.MLDSAAlg.signInternalMu thLoop mk rppTh
  simp only [signFips]

theorem pre_rel {sp : Spec.Params} (hp : Std3 sp) {F : Spec.Fuel} {sk M' rnd : List UInt8} {P : SG.Pre sp}
    (h : SG.pre sp F sk M' rnd = some P) :
    Rel sp P (keyOfSk sp sk) (keyOfSk sp sk).rho (muTh sp sk M') (rppTh sp sk M' rnd) := by
  unfold SG.pre at h
  rcases hd : Spec.skDecode sp sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  rw [hd] at h
  simp only [] at h
  rcases hA : Spec.ExpandA sp F.rejNTT ρ with _ | Â
  · rw [hA] at h; simp at h
  · rw [hA] at h
    simp only [Option.some.injEq] at h
    subst h
    have hmu : u8ToBytes (Spec.H (tr ++ M') 64) = muTh sp sk M' := by
      unfold muTh keyOfSk
      rw [hd]
      simp only [H_eq, u8ToBytes_append]
    refine ⟨fun r => ?_, fun r => ?_, fun r => ?_, fun r hr s hs => ?_, hmu, ?_⟩
    · unfold keyOfSk; rw [hd]
    · unfold keyOfSk; rw [hd]
    · unfold keyOfSk; rw [hd]
    · have := (expandA_ours_to_theirs sp F.rejNTT ρ Â hA).2 r hr s hs
      unfold keyOfSk
      rw [hd]
      exact this
    · unfold rppTh
      rw [← hmu]
      unfold keyOfSk
      rw [hd]
      simp only [H_eq, u8ToBytes_append]

/-- **`Sign_internal`, ours to theirs.**  If our loop (with at most `B` attempts) accepts, it accepts at some attempt
`a < B`, and ocaml-pq's `signInternalMu` (on the key that our decoder yields, `μ = H(tr ‖ M′)`) with `m` iterations
returns the same signature if `a < m` and `none` otherwise. -/
theorem signInternalBounded_ours_to_theirs {sp : Spec.Params} (hp : Std3 sp) (B : ℕ) (sk M' rnd : List UInt8)
    (F : Spec.Fuel) (σ : List UInt8) (h : Spec.Sign_internal_bounded sp B sk M' rnd F = some σ) :
    ∃ a, a < B ∧ ∀ m, thSignInternal sp sk M' rnd m = if a < m then some (u8ToBytes σ) else none := by
  rw [SG.Sign_internal_bounded_eq] at h
  rcases hpre : SG.pre sp F sk M' rnd with _ | P
  · rw [hpre] at h; simp at h
  · rw [hpre] at h
    obtain ⟨a, ha, hall⟩ := core_ours_to_theirs hp (pre_rel hp hpre) F B σ h
    exact ⟨a, ha, fun m => by rw [thSignInternal_eq]; exact hall m⟩

theorem pre_of_expandA (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8) (Â)
    (h : Spec.ExpandA sp F.rejNTT (Spec.skDecode sp sk).1 = some Â) : ∃ P, SG.pre sp F sk M' rnd = some P := by
  unfold SG.pre
  rcases hd : Spec.skDecode sp sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  rw [hd] at h
  simp only []
  rw [h]
  exact ⟨_, rfl⟩

/-- The `SampleInBall` calls that ocaml-pq's loop reaches (those after only rejected attempts, among the first
`m`) all terminate on ocaml-pq's side. -/
def SignTerm (sp : Spec.Params) (sk M' rnd : List UInt8) (m : ℕ) : Prop :=
  ∀ j, j < m →
    (∀ j', j' < j → thStep sp (keyOfSk sp sk) (keyOfSk sp sk).rho (muTh sp sk M') (rppTh sp sk M' rnd) j' = none) →
    ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns (algParams sp).tau
      (oursShake256 (alg7CT (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam oursShake256
        (OcamlPq.MLDSAAlg.expandA oursShake128 (keyOfSk sp sk).rho) (muTh sp sk M')
        (mk sp (rppTh sp sk M' rnd) (j * sp.ℓ)))) b

/-- For all large enough fuel, `pre` returns and the first `N` `SampleInBall` calls return. -/
theorem eventual_samples {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (hA : ExpandATerm sp (Spec.skDecode sp sk).1) (N : ℕ)
    (hT : ∀ j, j < N → ∃ b, OcamlPq.MLDSAAlg.SampleInBallReturns (algParams sp).tau
      (oursShake256 (alg7CT (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam oursShake256
        (OcamlPq.MLDSAAlg.expandA oursShake128 (keyOfSk sp sk).rho) (muTh sp sk M')
        (mk sp (rppTh sp sk M' rnd) (j * sp.ℓ)))) b) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ P, SG.pre sp F sk M' rnd = some P ∧
        ∀ j, j < N → ∃ c, Spec.SampleInBall sp F.sampleInBall (SG.ctildeAt sp P (j * sp.ℓ)) = some c := by
  obtain ⟨FA, hFA⟩ := expandA_theirs_to_ours sp _ hA
  obtain ⟨Â1, hÂ1⟩ := hFA FA le_rfl
  obtain ⟨P1, hP1⟩ := pre_of_expandA sp ({ rejNTT := FA } : Spec.Fuel) sk M' rnd Â1 hÂ1
  have hr1 := pre_rel hp hP1
  have hS : ∀ j, j < N → ∃ F0, ∀ F, F0 ≤ F →
      ∃ c, Spec.SampleInBall sp F (SG.ctildeAt sp P1 (j * sp.ℓ)) = some c := by
    intro j hj
    obtain ⟨b, hb⟩ := hT j hj
    rw [ct_eq hp hr1 (j * sp.ℓ)] at hb
    obtain ⟨F0, hF0⟩ := SB.sampleInBall_theirs_to_ours hp _ b hb
    exact ⟨F0, fun F hF => by obtain ⟨c, hc, -⟩ := hF0 F hF; exact ⟨c, hc⟩⟩
  obtain ⟨Fs, hFs⟩ := eventually_forall_lt (P := fun j F =>
    ∃ c, Spec.SampleInBall sp F (SG.ctildeAt sp P1 (j * sp.ℓ)) = some c) N hS
  refine ⟨max FA Fs, fun F h1 h2 => ?_⟩
  obtain ⟨Â, hÂ⟩ := hFA F.rejNTT (le_trans (le_max_left _ _) h1)
  obtain ⟨P, hP⟩ := pre_of_expandA sp F sk M' rnd Â hÂ
  have hr := pre_rel hp hP
  refine ⟨P, hP, fun j hj => ?_⟩
  have heq : SG.ctildeAt sp P (j * sp.ℓ) = SG.ctildeAt sp P1 (j * sp.ℓ) :=
    u8ToBytes_inj ((ct_eq hp hr _).symm.trans (ct_eq hp hr1 _))
  rw [heq]
  exact hFs F.sampleInBall (le_trans (le_max_right _ _) h2) j hj

/-- **`Sign_internal`, theirs to ours (accepting).**  If ocaml-pq's loop with `m ≤ B` iterations produces `s`,
`ExpandA` terminates on ocaml-pq's side and the `SampleInBall` calls that the loop reaches terminate, then for
every large enough fuel our loop with `B` attempts accepts the same signature. -/
theorem signInternalBounded_theirs_to_ours {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8) (B m : ℕ)
    (hm : m ≤ B) (hmℓ : m * sp.ℓ ≤ 2 ^ 16) (s : OcamlPq.MLDSAAlg.Bytes)
    (hs : thSignInternal sp sk M' rnd m = some s) (hA : ExpandATerm sp (Spec.skDecode sp sk).1)
    (hC : SignTerm sp sk M' rnd m) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ σ, Spec.Sign_internal_bounded sp B sk M' rnd F = some σ ∧ u8ToBytes σ = s := by
  rw [thSignInternal_eq] at hs
  obtain ⟨j0, hj0m, hj0, hb0⟩ := thLoop_some m s hs
  obtain ⟨F0, hF0⟩ := eventual_samples hp sk M' rnd hA (j0 + 1)
    (fun j hj => hC j (by omega) (fun j' hj' => hb0 j' (by omega)))
  refine ⟨F0, fun F h1 h2 => ?_⟩
  obtain ⟨P, hP, hsm⟩ := hF0 F h1 h2
  obtain ⟨σ, hσ, he⟩ := core_theirs_to_ours hp (pre_rel hp hP) F B m hm hmℓ s hs (fun j hj hprem => by
    by_cases hjj : j < j0 + 1
    · exact hsm j hjj
    · have := hprem j0 (by omega)
      rw [hj0] at this
      cases this)
  exact ⟨σ, by rw [SG.Sign_internal_bounded_eq, hP]; exact hσ, he⟩

/-- **`Sign_internal`, theirs to ours (exhausted).**  If ocaml-pq's loop with `m` iterations returns `none`
(under the same termination hypotheses), then for every large enough fuel our loop with `m` attempts returns
`none`; with more attempts it can only return a signature accepted at an attempt `a ≥ m`
(`signInternalBounded_ours_to_theirs`). -/
theorem signInternalBounded_theirs_to_ours_none {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8) (m : ℕ)
    (hmℓ : m * sp.ℓ ≤ 2 ^ 16) (hs : thSignInternal sp sk M' rnd m = none)
    (hA : ExpandATerm sp (Spec.skDecode sp sk).1) (hC : SignTerm sp sk M' rnd m) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      Spec.Sign_internal_bounded sp m sk M' rnd F = none := by
  rw [thSignInternal_eq] at hs
  have hnone := (thLoop_none m).mp hs
  obtain ⟨F0, hF0⟩ := eventual_samples hp sk M' rnd hA m (fun j hj => hC j hj (fun j' hj' => hnone j' (by omega)))
  refine ⟨F0, fun F h1 h2 => ?_⟩
  obtain ⟨P, hP, hsm⟩ := hF0 F h1 h2
  rw [SG.Sign_internal_bounded_eq, hP]
  exact core_theirs_to_ours_none hp (pre_rel hp hP) F m hmℓ hs hsm

/-! ## The three parameter sets: `Sign_internal` and `Sign` -/

theorem budget_of_std3 {sp : Spec.Params} (hp : Std3 sp) : 821 ≤ Spec.kappaBudget sp ∧ 821 * sp.ℓ ≤ 2 ^ 16 := by
  rcases hp with rfl | rfl | rfl <;> decide +kernel

/-- **`Sign_internal`, ours to theirs.**  If `Sign_internal` accepts, it does so at some attempt `a` below
`kappaBudget`; ocaml-pq's `signInternalMu` with its 821 iterations returns the same signature iff `a < 821`,
and `none` iff `821 ≤ a` (the only way the two can differ). -/
theorem signInternal_ours_to_theirs {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8) (F : Spec.Fuel)
    (σ : List UInt8) (h : Spec.Sign_internal sp sk M' rnd F = some σ) :
    ∃ a, a < Spec.kappaBudget sp ∧ (a < 821 → thSignInternal sp sk M' rnd 821 = some (u8ToBytes σ)) ∧
      (821 ≤ a → thSignInternal sp sk M' rnd 821 = none) := by
  obtain ⟨a, ha, hall⟩ := signInternalBounded_ours_to_theirs hp _ sk M' rnd F σ h
  refine ⟨a, ha, fun h1 => ?_, fun h1 => ?_⟩
  · rw [hall 821, if_pos h1]
  · rw [hall 821, if_neg (by omega)]

/-- **`Sign_internal`, theirs to ours** (accepting): for every large enough fuel. -/
theorem signInternal_theirs_to_ours {sp : Spec.Params} (hp : Std3 sp) (sk M' rnd : List UInt8)
    (s : OcamlPq.MLDSAAlg.Bytes) (hs : thSignInternal sp sk M' rnd 821 = some s)
    (hA : ExpandATerm sp (Spec.skDecode sp sk).1) (hC : SignTerm sp sk M' rnd 821) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ σ, Spec.Sign_internal sp sk M' rnd F = some σ ∧ u8ToBytes σ = s :=
  signInternalBounded_theirs_to_ours hp sk M' rnd _ 821 (budget_of_std3 hp).1 (budget_of_std3 hp).2 s hs hA hC

/-- ocaml-pq's `mldsaSign` (Algorithm 2 with Algorithm 7 bounded by 821 iterations) for our decoded key. -/
noncomputable def thSign (sp : Spec.Params) (sk M ctx rnd : List UInt8) : Option OcamlPq.MLDSAAlg.Bytes :=
  OcamlPq.MLDSAAlg.mldsaSign (signFips (algParams sp) (keyOfSk sp sk)) (algParams sp) sp.lam oursShake256
    oursShake128 (keyOfSk sp sk) (u8ToBytes M) (u8ToBytes ctx) (u8ToBytes rnd)

theorem thSign_of_ctx_gt (sp : Spec.Params) (sk M ctx rnd : List UInt8) (hc : ctx.length > 255) :
    thSign sp sk M ctx rnd = none := by
  unfold thSign OcamlPq.MLDSAAlg.mldsaSign
  have hc' : (u8ToBytes ctx).length > 255 := by simpa [u8ToBytes] using hc
  simp only [hc', if_true]

theorem thSign_of_ctx_le (sp : Spec.Params) (sk M ctx rnd : List UInt8) (hc : ctx.length ≤ 255) :
    thSign sp sk M ctx rnd =
      thSignInternal sp sk (IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M) rnd 821 := by
  unfold thSign OcamlPq.MLDSAAlg.mldsaSign thSignInternal muTh
  have hl : (u8ToBytes ctx).length = ctx.length := by simp [u8ToBytes]
  have hc' : ¬ (u8ToBytes ctx).length > 255 := by rw [hl]; omega
  simp only [hc', if_false]
  simp only [u8ToBytes_append, integerToBytes_alg_eq, hl, List.append_assoc]

theorem sign_of_ctx_gt (sp : Spec.Params) (sk M ctx rnd : List UInt8) (F : Spec.Fuel) (hc : ctx.length > 255) :
    Spec.Sign sp sk M ctx rnd F = none := by
  unfold Spec.Sign
  simp [Id.run, hc]
  rfl

theorem sign_of_ctx_le (sp : Spec.Params) (sk M ctx rnd : List UInt8) (F : Spec.Fuel) (hc : ctx.length ≤ 255) :
    Spec.Sign sp sk M ctx rnd F =
      Spec.Sign_internal sp sk (IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M) rnd F := by
  unfold Spec.Sign
  simp only [Id.run, show ¬ ctx.length > 255 by omega, if_false]
  rfl

/-- The formatted message `M′ = 0 ‖ |ctx| ‖ ctx ‖ M` of Algorithm 2 (step 10). -/
def mPrime (M ctx : List UInt8) : List UInt8 := IntegerToBytes 0 1 ++ IntegerToBytes ctx.length 1 ++ ctx ++ M

/-- **`Sign` (Algorithm 2), ours to theirs.**  If `Sign` returns a signature then `|ctx| ≤ 255` and it was accepted
at some attempt `a < kappaBudget`; ocaml-pq's `mldsaSign` (on the key that our decoder yields) returns the same
signature iff `a < 821`, and `none` iff `821 ≤ a`. -/
theorem sign_ours_to_theirs {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8) (F : Spec.Fuel)
    (σ : List UInt8) (h : Spec.Sign sp sk M ctx rnd F = some σ) :
    ctx.length ≤ 255 ∧ ∃ a, a < Spec.kappaBudget sp ∧
      (a < 821 → thSign sp sk M ctx rnd = some (u8ToBytes σ)) ∧ (821 ≤ a → thSign sp sk M ctx rnd = none) := by
  by_cases hc : ctx.length > 255
  · rw [sign_of_ctx_gt sp sk M ctx rnd F hc] at h; cases h
  · have hc' : ctx.length ≤ 255 := by omega
    rw [sign_of_ctx_le sp sk M ctx rnd F hc'] at h
    obtain ⟨a, ha, h1, h2⟩ := signInternal_ours_to_theirs hp sk _ rnd F σ h
    exact ⟨hc', a, ha, fun h => by rw [thSign_of_ctx_le sp sk M ctx rnd hc']; exact h1 h,
      fun h => by rw [thSign_of_ctx_le sp sk M ctx rnd hc']; exact h2 h⟩

/-- **`Sign`, theirs to ours** (accepting; `|ctx| ≤ 255`). -/
theorem sign_theirs_to_ours {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8) (hc : ctx.length ≤ 255)
    (s : OcamlPq.MLDSAAlg.Bytes) (hs : thSign sp sk M ctx rnd = some s)
    (hA : ExpandATerm sp (Spec.skDecode sp sk).1) (hC : SignTerm sp sk (mPrime M ctx) rnd 821) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      ∃ σ, Spec.Sign sp sk M ctx rnd F = some σ ∧ u8ToBytes σ = s := by
  rw [thSign_of_ctx_le sp sk M ctx rnd hc] at hs
  obtain ⟨F0, hF0⟩ := signInternal_theirs_to_ours hp sk _ rnd s hs hA hC
  exact ⟨F0, fun F h1 h2 => by
    obtain ⟨σ, h3, h4⟩ := hF0 F h1 h2
    exact ⟨σ, by rw [sign_of_ctx_le sp sk M ctx rnd F hc]; exact h3, h4⟩⟩

/-- **`Sign`, theirs to ours** (ocaml-pq's loop exhausted its 821 iterations): our loop with 821 attempts
returns `none` as well.  (Our `Sign` has more attempts and can still succeed at an attempt `a ≥ 821`, which is
the case excluded in `sign_ours_to_theirs`.) -/
theorem sign_theirs_to_ours_none {sp : Spec.Params} (hp : Std3 sp) (sk M ctx rnd : List UInt8) (hc : ctx.length ≤ 255)
    (hs : thSign sp sk M ctx rnd = none)
    (hA : ExpandATerm sp (Spec.skDecode sp sk).1) (hC : SignTerm sp sk (mPrime M ctx) rnd 821) :
    ∃ F0 : ℕ, ∀ F : Spec.Fuel, F0 ≤ F.rejNTT → F0 ≤ F.sampleInBall →
      Spec.Sign_internal_bounded sp 821 sk (mPrime M ctx) rnd F = none := by
  rw [thSign_of_ctx_le sp sk M ctx rnd hc] at hs
  exact signInternalBounded_theirs_to_ours_none hp sk _ rnd 821 (budget_of_std3 hp).2 hs hA hC

/-- A context of more than 255 bytes: both `Sign`s return `none`. -/
theorem sign_of_ctx_gt_both (sp : Spec.Params) (sk M ctx rnd : List UInt8) (F : Spec.Fuel) (hc : ctx.length > 255) :
    Spec.Sign sp sk M ctx rnd F = none ∧ thSign sp sk M ctx rnd = none :=
  ⟨sign_of_ctx_gt sp sk M ctx rnd F hc, thSign_of_ctx_gt sp sk M ctx rnd hc⟩

/-! ## The decoded key against ocaml-pq's decoder -/

theorem getD_toList_map {n : ℕ} (v : Vector RPoly n) (r : ℕ) (hr : r < n) :
    (v.toList.map Vector.toList).getD r [] = (v[r]!).toList := by
  rw [List.getD_eq_getElem?_getD, getElem!_pos v r (by simpa using hr)]
  simp [hr]

/-- On a key that ocaml-pq's decoder accepts (`skDecode_eq`: right length, `s₁`, `s₂` in `[-η, η]`), the key
`keyOfSk` is ocaml-pq's decoded key (`listsToVec` of the decoded lists), row by row. -/
theorem keyOfSk_s1 (sp : Spec.Params) (sk : List UInt8) (r : ℕ) (hr : r < sp.ℓ) :
    (keyOfSk sp sk).s1 r = listsToVec ((Spec.skDecode sp sk).2.2.2.1.toList.map Vector.toList) r := by
  unfold keyOfSk listsToVec
  simp only []
  rw [getD_toList_map _ r hr, listToPoly_rfn_toList]

theorem keyOfSk_s2 (sp : Spec.Params) (sk : List UInt8) (r : ℕ) (hr : r < sp.k) :
    (keyOfSk sp sk).s2 r = listsToVec ((Spec.skDecode sp sk).2.2.2.2.1.toList.map Vector.toList) r := by
  unfold keyOfSk listsToVec
  simp only []
  rw [getD_toList_map _ r hr, listToPoly_rfn_toList]

theorem keyOfSk_t0 (sp : Spec.Params) (sk : List UInt8) (r : ℕ) (hr : r < sp.k) :
    (keyOfSk sp sk).t0 r = listsToVec ((Spec.skDecode sp sk).2.2.2.2.2.toList.map Vector.toList) r := by
  unfold keyOfSk listsToVec
  simp only []
  rw [getD_toList_map _ r hr, listToPoly_rfn_toList]

end SGB

end XSpec
