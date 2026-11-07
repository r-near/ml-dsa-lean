import Proofs.CorrBall
import Proofs.CorrRound
import Proofs.CorrCodec
import Proofs.CorrNTT
import Proofs.NTTOps
import Proofs.MatrixVector
import Proofs.SampleS
import Proofs.StdParams
import Proofs.KeyGen
import Proofs.Verify
import Proofs.Sign
import Proofs.API

/-!
# Correctness: `Verify (Sign sk M) = true` for honestly generated keys (Phase 5)

## Results

* `correct_internal`: for `(pk, sk)` from `KeyGen_internal ξ` and a signature `σ` returned by
  `Sign_internal_bounded sk M′ rnd` (any attempt budget `B`, the same fuel `F` throughout),
  `Verify_internal pk M′ σ = some true`.
* `correct_external`: the same for Algorithms 1, 2, 3 (`KeyGen`, `Sign`, `Verify`) with a context string;
  `|ctx| ≤ 255` follows from the hypothesis that `Sign` returned `some`.
* `correct_44`, `correct_65`, `correct_87`: the transfer to the extracted Rust. If the spec's `KeyGen` and `Sign`
  return `some`, then running `api.keygen_NN`, then `api.sign_NN` on its secret key, then `api.verify_NN` on its
  public key and the returned signature yields `true`, and every step returns `ok`.

The only premise on the parameters is `StdParams sp`, the bundle proved for ML-DSA-44/65/87
(`stdParams_44/65/87`). The facts `2β < q`, `ω < 256`, `τ ≤ 256` are derived from it. The premises on the
inputs are exactly the spec-returns-`some` facts for `KeyGen` and `Sign` (`RejTerm` and the κ budget); that
`Verify` returns `some` is part of the conclusion.

## Layout

1. `Proofs.Corr`: the algebra that was missing: `NTT` and `NTT⁻¹` are additive and subtractive on vectors,
   `MatrixVectorNTT` and `ScalarVectorNTT` are linear, `MatrixVectorNTT` commutes with `ScalarVectorNTT`, and the
   resulting identity `w′_Approx = w − c s₂ + c t₀`.
2. `Proofs`: facts about the output of `KeyGen_internal` (round trips of the key codecs), the accepted attempt of
   `Sign_internal_bounded`, the assembly, the external and the Rust-level statements.
-/

set_option maxRecDepth 8192

namespace Proofs.Corr
open Spec

/-! ## Pointwise lemmas -/

theorem poly_sub_add (a b : Poly) : a - b + b = a := by
  apply poly_ext
  intro k _
  rw [get!_add, get!_sub]
  ring

theorem NTT_sub (a b : Poly) : NTT (a - b) = NTT a - NTT b := by
  apply poly_ext
  intro k _
  have h : NTT (a - b) + NTT b = NTT a := by rw [← NTT_add, poly_sub_add]
  have h2 : (NTT (a - b) + NTT b)[k]! = (NTT a)[k]! := by rw [h]
  rw [get!_add] at h2
  rw [get!_sub]
  linear_combination h2

theorem NTTInv_sub (a b : Poly) : NTTInv (a - b) = NTTInv a - NTTInv b := by
  apply poly_ext
  intro k _
  have h : NTTInv (a - b) + NTTInv b = NTTInv a := by rw [← NTTInv_add, poly_sub_add]
  have h2 : (NTTInv (a - b) + NTTInv b)[k]! = (NTTInv a)[k]! := by rw [h]
  rw [get!_add] at h2
  rw [get!_sub]
  linear_combination h2

/-! ## Vectors of polynomials, entrywise -/

theorem vec_ext' {n : Nat} (a b : Vector Poly n) (h : ∀ i, i < n → a[i]! = b[i]!) : a = b := by
  apply Vector.ext
  intro i hi
  have := h i hi
  rwa [vgetG a hi, vgetG b hi] at this

theorem vadd! {n : Nat} (u v : Vector Poly n) {i : Nat} (hi : i < n) : (u + v)[i]! = u[i]! + v[i]! := by
  rw [vgetG (u + v) hi, vgetG u hi, vgetG v hi]
  exact vec_add_getElem u v i hi

theorem vsub! {n : Nat} (u v : Vector Poly n) {i : Nat} (hi : i < n) : (u - v)[i]! = u[i]! - v[i]! := by
  rw [vgetG (u - v) hi, vgetG u hi, vgetG v hi]
  exact vec_sub_getElem u v i hi

theorem vadd2! {n : Nat} (u v : Vector Poly n) {i : Nat} (hi : i < n) {κ : Nat} :
    ((u + v)[i]!)[κ]! = (u[i]!)[κ]! + (v[i]!)[κ]! := by
  rw [vadd! u v hi, get!_add]

theorem vsub2! {n : Nat} (u v : Vector Poly n) {i : Nat} (hi : i < n) {κ : Nat} :
    ((u - v)[i]!)[κ]! = (u[i]!)[κ]! - (v[i]!)[κ]! := by
  rw [vsub! u v hi, get!_sub]

theorem NTTVec_get! {n : Nat} (v : Vector Poly n) {i : Nat} (hi : i < n) : (NTTVec v)[i]! = NTT v[i]! := by
  rw [vgetG (NTTVec v) hi, vgetG v hi]
  simp [NTTVec]

theorem NTTInvVec_get! {n : Nat} (v : Vector Poly n) {i : Nat} (hi : i < n) :
    (NTTInvVec v)[i]! = NTTInv v[i]! := by
  rw [vgetG (NTTInvVec v) hi, vgetG v hi]
  simp [NTTInvVec]

theorem NTTVec_add {n : Nat} (u v : Vector Poly n) : NTTVec (u + v) = NTTVec u + NTTVec v := by
  apply vec_ext'
  intro i hi
  rw [NTTVec_get! _ hi, vadd! u v hi, vadd! _ _ hi, NTTVec_get! _ hi, NTTVec_get! _ hi]
  exact NTT_add _ _

theorem NTTVec_sub {n : Nat} (u v : Vector Poly n) : NTTVec (u - v) = NTTVec u - NTTVec v := by
  apply vec_ext'
  intro i hi
  rw [NTTVec_get! _ hi, vsub! u v hi, vsub! _ _ hi, NTTVec_get! _ hi, NTTVec_get! _ hi]
  exact NTT_sub _ _

theorem NTTInvVec_add {n : Nat} (u v : Vector Poly n) : NTTInvVec (u + v) = NTTInvVec u + NTTInvVec v := by
  apply vec_ext'
  intro i hi
  rw [NTTInvVec_get! _ hi, vadd! u v hi, vadd! _ _ hi, NTTInvVec_get! _ hi, NTTInvVec_get! _ hi]
  exact NTTInv_add _ _

theorem NTTInvVec_sub {n : Nat} (u v : Vector Poly n) : NTTInvVec (u - v) = NTTInvVec u - NTTInvVec v := by
  apply vec_ext'
  intro i hi
  rw [NTTInvVec_get! _ hi, vsub! u v hi, vsub! _ _ hi, NTTInvVec_get! _ hi, NTTInvVec_get! _ hi]
  exact NTTInv_sub _ _

theorem NTTVec_NTTInvVec {n : Nat} (v : Vector Poly n) : NTTVec (NTTInvVec v) = v := by
  apply Vector.ext
  intro i hi
  simp only [NTTVec, NTTInvVec, Vector.getElem_map]
  exact NTT_NTTInv _

/-! ## `ScalarVectorNTT` -/

theorem SVN2! {ℓ : Nat} (c : Poly) (V : Vector Poly ℓ) {i : Nat} (hi : i < ℓ) {κ : Nat} (hκ : κ < 256) :
    ((ScalarVectorNTT c V)[i]!)[κ]! = c[κ]! * (V[i]!)[κ]! := by
  rw [vgetG (ScalarVectorNTT c V) hi, ScalarVectorNTT_get c V i hi, MultiplyNTT_get _ _ κ hκ, vgetG V hi]

/-- `ĉ ∘ (a + b − d) = ĉ ∘ a + ĉ ∘ b − ĉ ∘ d`. -/
theorem SVN_addsub {ℓ : Nat} (c : Poly) (a b d : Vector Poly ℓ) :
    ScalarVectorNTT c (a + b - d) = ScalarVectorNTT c a + ScalarVectorNTT c b - ScalarVectorNTT c d := by
  apply vec_ext'
  intro i hi
  apply poly_ext
  intro κ hκ
  simp only [vadd2! _ _ hi, vsub2! _ _ hi, SVN2! _ _ hi hκ]
  ring

/-! ## `MatrixVectorNTT`: linearity (the coefficient formula `MVN2!` is in `Proofs.MatrixVector`) -/

theorem MVN_add {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (u v : Vector Poly ℓ) :
    MatrixVectorNTT M (u + v) = MatrixVectorNTT M u + MatrixVectorNTT M v := by
  apply vec_ext'
  intro i hi
  apply poly_ext
  intro κ hκ
  rw [vadd2! _ _ hi, MVN2! _ _ hi hκ, MVN2! _ _ hi hκ, MVN2! _ _ hi hκ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [vadd2! u v (Finset.mem_range.mp hj)]
  ring

theorem MVN_SVN {k ℓ : Nat} (M : Vector (Vector Poly ℓ) k) (c : Poly) (V : Vector Poly ℓ) :
    MatrixVectorNTT M (ScalarVectorNTT c V) = ScalarVectorNTT c (MatrixVectorNTT M V) := by
  apply vec_ext'
  intro i hi
  apply poly_ext
  intro κ hκ
  rw [MVN2! _ _ hi hκ, SVN2! _ _ hi hκ, MVN2! _ _ hi hκ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [SVN2! _ _ (Finset.mem_range.mp hj) hκ]
  ring

/-! ## The identity `w′_Approx = w − c s₂ + c t₀` -/

theorem approx_eq {k ℓ : Nat} (A : Vector (Vector Poly ℓ) k) (y s1 : Vector Poly ℓ) (s2 t0 T t : Vector Poly k)
    (ĉ : Poly) (ht : t = NTTInvVec (MatrixVectorNTT A (NTTVec s1)) + s2) (hT : T + t0 = t) :
    NTTInvVec (MatrixVectorNTT A (NTTVec (y + NTTInvVec (ScalarVectorNTT ĉ (NTTVec s1)))) -
        ScalarVectorNTT ĉ (NTTVec T)) =
      NTTInvVec (MatrixVectorNTT A (NTTVec y)) - NTTInvVec (ScalarVectorNTT ĉ (NTTVec s2)) +
        NTTInvVec (ScalarVectorNTT ĉ (NTTVec t0)) := by
  have hT' : T = t - t0 := by
    apply vec_ext'
    intro i hi
    apply poly_ext
    intro κ _
    have h : ((T + t0)[i]!)[κ]! = (t[i]!)[κ]! := by rw [hT]
    rw [vadd2! _ _ hi] at h
    rw [vsub2! _ _ hi]
    linear_combination h
  have hN : NTTVec T = (MatrixVectorNTT A (NTTVec s1) + NTTVec s2) - NTTVec t0 := by
    rw [hT', NTTVec_sub, ht, NTTVec_add, NTTVec_NTTInvVec]
  rw [NTTVec_add, NTTVec_NTTInvVec, hN, MVN_add, MVN_SVN, SVN_addsub]
  generalize MatrixVectorNTT A (NTTVec y) = a
  generalize ScalarVectorNTT ĉ (MatrixVectorNTT A (NTTVec s1)) = b
  generalize ScalarVectorNTT ĉ (NTTVec s2) = c
  generalize ScalarVectorNTT ĉ (NTTVec t0) = d
  have e : a + b - (b + c - d) = a - c + d := by
    apply vec_ext'
    intro i hi
    apply poly_ext
    intro κ _
    simp only [vadd2! _ _ hi, vsub2! _ _ hi]
    ring
  rw [e, NTTInvVec_add, NTTInvVec_sub]

/-! ## Adapters -/

theorem map_modPM_toZq {n : Nat} (z : Vector Poly n) : (z.map Poly.modPM).map RPoly.toZq = z := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  exact toZq_modPM z[i]

/-- `‖z mod± q‖∞ ≤ ‖z‖∞`: the norm on the centered representatives is the norm on `Z_q`. -/
theorem infNorm_map_modPM {n : Nat} (z : Vector Poly n) (B : Nat) (h : ‖z‖∞ ≤ B) :
    ‖z.map Poly.modPM‖∞ ≤ B := by
  rw [infNorm_vec_le_iff] at h ⊢
  intro i hi
  have h1 := h i hi
  rw [infNorm_vec_le_iff] at h1 ⊢
  intro j hj
  have h2 := h1 j hj
  have e : (z.map Poly.modPM)[i][j] = Zq.modPM z[i][j] := by simp [Poly.modPM]
  show ((z.map Poly.modPM)[i][j]).natAbs ≤ B
  rw [e]
  exact h2

/-- A challenge-shaped polynomial, in the form `cs_norm_bound_params` wants. -/
theorem ball_facts {τ : Nat} {c : RPoly} (hb : Ball τ c) :
    (∀ i, i < 256 → c[i]! = 0 ∨ c[i]! = 1 ∨ c[i]! = -1) ∧
      ((Finset.range 256).filter (fun i => c[i]! ≠ 0)).card ≤ τ := by
  obtain ⟨h1, h2⟩ := hb
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [vgetG c hi]
    rcases h1 ⟨i, hi⟩ with h | h | h
    · right; right; exact h
    · left; exact h
    · right; left; exact h
  · refine le_trans (le_of_eq ?_) h2
    have himg : (Finset.univ.filter (fun i : Fin 256 => c[i] ≠ 0)).image Fin.val =
        (Finset.range 256).filter (fun i => c[i]! ≠ 0) := by
      ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        refine ⟨a.isLt, ?_⟩
        rw [vgetG c a.isLt]
        exact ha
      · rintro ⟨hi, hne⟩
        rw [vgetG c hi] at hne
        exact ⟨⟨i, hi⟩, hne, rfl⟩
    rw [← himg]
    exact Finset.card_image_of_injective _ Fin.val_injective

end Proofs.Corr

namespace Proofs
open Spec

/-! ## Parameter facts -/

theorem beta_two_lt {sp : Spec.Params} (hp : StdParams sp) : 2 * sp.β < Spec.q := by
  have h1 := hp.tau_le
  have hq : Spec.q = 8380417 := rfl
  rcases hp.eta with e | e <;> simp only [Spec.Params.β, e, hq] <;> omega

/-! ## What `KeyGen_internal` produces -/

/-- The honest key pair: `pk = pkEncode ρ t₁`, `sk = skEncode ρ K tr s₁ s₂ t₀` with `(t₁, t₀) = Power2Round(t)`,
`t = A s₁ + s₂`, `tr = H(pk, 64)`; both decode back (the codec round trips), and `‖s₁‖∞, ‖s₂‖∞ ≤ η`. -/
theorem keygen_facts {sp : Spec.Params} (hp : StdParams sp) (F : Spec.Fuel) (ξ pk sk : List UInt8)
    (hk : Spec.KeyGen_internal sp ξ F = some (pk, sk)) :
    ∃ (ρ K tr : List UInt8) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (s₁ : Vector RPoly sp.ℓ)
      (s₂ : Vector RPoly sp.k),
      Spec.ExpandA sp F.rejNTT ρ = some A ∧ ‖s₁‖∞ ≤ sp.η ∧ ‖s₂‖∞ ≤ sp.η ∧
      Spec.skDecode sp sk =
        (ρ, K, tr, s₁, s₂, (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).2) ∧
      Spec.pkDecode sp pk = (ρ, (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).1) ∧
      tr = H pk 64 := by
  obtain ⟨A, s₁, s₂, hA, hS, hpk, hsk⟩ := KeyGen.keygen_some sp F ξ pk sk hk
  have hH : (H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128).length = 128 := SHAKE256_length _ _
  generalize H (ξ ++ IntegerToBytes sp.k 1 ++ IntegerToBytes sp.ℓ 1) 128 = out at hH hA hS hpk hsk
  have hd := hp.d_eq
  have h32 : (slice out 0 32).length = 32 := by simp [slice, hH]
  have h32' : (slice out 96 32).length = 32 := by simp [slice, hH]
  obtain ⟨hr1, hr2⟩ := ExpandS_some sp F.rejBounded _ s₁ s₂ hS
  have hb1 : ∀ (i : Nat) (hi : i < sp.ℓ) (j : Nat) (hj : j < 256), ((s₁[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp F.rejBounded _ _ (hr1 i hi)
  have hb2 : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256), ((s₂[i])[j]'hj).natAbs ≤ sp.η :=
    fun i hi => RejBoundedPoly_bounded sp F.rejBounded _ _ (hr2 i hi)
  have hn1 : ‖s₁‖∞ ≤ sp.η :=
    (Corr.infNorm_vec_le_iff s₁ sp.η).mpr fun i hi =>
      (Corr.infNorm_vec_le_iff s₁[i] sp.η).mpr fun j hj => hb1 i hi j hj
  have hn2 : ‖s₂‖∞ ≤ sp.η :=
    (Corr.infNorm_vec_le_iff s₂ sp.η).mpr fun i hi =>
      (Corr.infNorm_vec_le_iff s₂[i] sp.η).mpr fun j hj => hb2 i hi j hj
  have e10 : (2 : Int) ^ 10 = 1024 := by norm_num
  subst hpk hsk
  refine ⟨slice out 0 32, slice out 96 32, _, A, s₁, s₂, hA, hn1, hn2, ?_, ?_, rfl⟩
  · apply Corr.skDecode_skEncode sp hd _ _ _ h32 h32' (SHAKE256_length _ _)
    · intro i hi j hj
      have := hb1 i hi j hj
      have := Int.natAbs_eq (s₁[i][j])
      omega
    · intro i hi j hj
      have := hb2 i hi j hj
      have := Int.natAbs_eq (s₂[i][j])
      omega
    · intro i hi j hj
      have := Corr.power2RoundVec_range sp hd (KeyGen.tVec sp A s₁ s₂) i hi j hj
      omega
  · apply Corr.pkDecode_pkEncode sp hd _ h32
    intro i hi j hj
    have := Corr.power2RoundVec_range sp hd (KeyGen.tVec sp A s₁ s₂) i hi j hj
    omega

/-! ## What an accepted attempt of `Sign_internal_bounded` gives -/

theorem loopRes_attempt (sp : Spec.Params) (F : Spec.Fuel) (P : Sign.Pre sp) :
    ∀ n κ ct z h, Sign.loopRes sp F P n κ = some (some (ct, z, h)) →
      ∃ κ', Sign.attemptAt sp F P κ' = some (ct, some (z, h)) := by
  intro n
  induction n with
  | zero => intro κ ct z h hh; simp [Sign.loopRes] at hh
  | succ n ih =>
    intro κ ct z h hh
    unfold Sign.loopRes at hh
    split_ifs at hh with hc
    · simp at hh
    · rcases hat : Sign.attemptAt sp F P κ with _ | ⟨ct', _ | ⟨z', h'⟩⟩
      · rw [hat] at hh; simp at hh
      · rw [hat] at hh
        exact ih _ _ _ _ hh
      · rw [hat] at hh
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl, rfl⟩ := hh
        exact ⟨κ, hat⟩

/-- The facts of an accepted attempt: the challenge `c`, the formulas for `z` and `h` and the four checks. -/
theorem attempt_facts (sp : Spec.Params) (F : Spec.Fuel) (P : Sign.Pre sp) (κ : Nat) (ct : List UInt8)
    (z : Vector Spec.Poly sp.ℓ) (h : Vector HintPoly sp.k)
    (hat : Sign.attemptAt sp F P κ = some (ct, some (z, h))) :
    ∃ c : RPoly,
      ct = H (P.μ ++ w1Encode sp (HighBitsVec sp
        (NTTInvVec (MatrixVectorNTT P.Â (NTTVec (Sign.maskAt sp P κ)))))) (sp.lam / 4) ∧
      Spec.SampleInBall sp F.sampleInBall ct = some c ∧
      z = Sign.maskAt sp P κ + NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (P.s₁.map RPoly.toZq))) ∧
      h = MakeHintVec sp (-NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (P.t₀.map RPoly.toZq))))
        (NTTInvVec (MatrixVectorNTT P.Â (NTTVec (Sign.maskAt sp P κ))) -
          NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (P.s₂.map RPoly.toZq))) +
          NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (P.t₀.map RPoly.toZq)))) ∧
      ‖z‖∞ < sp.γ₁ - sp.β ∧
      ‖LowBitsVec sp (NTTInvVec (MatrixVectorNTT P.Â (NTTVec (Sign.maskAt sp P κ))) -
          NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (P.s₂.map RPoly.toZq))))‖∞ < sp.γ₂ - sp.β ∧
      ‖NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (P.t₀.map RPoly.toZq)))‖∞ < sp.γ₂ ∧
      HintWeight h ≤ sp.ω := by
  unfold Sign.attemptAt at hat
  rcases hc : Spec.SampleInBall sp F.sampleInBall (Sign.ctildeAt sp P κ) with _ | c
  · simp [hc] at hat
  · simp only [hc, Option.some.injEq, Prod.mk.injEq] at hat
    obtain ⟨rfl, hr⟩ := hat
    refine ⟨c, rfl, hc, ?_⟩
    rw [Sign.respond_eq] at hr
    split at hr
    · simp at hr
    · rename_i h1
      split at hr
      · simp at hr
      · rename_i h2
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        rw [not_or, not_le, not_le] at h1
        rw [not_or, not_le, not_lt] at h2
        exact ⟨rfl, rfl, h1.1, h1.2, h2.1, h2.2⟩

/-! ## `w′_Approx` of the honest key pair -/

theorem wApprox_sign {sp : Spec.Params} (hp : StdParams sp) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k)
    (s₁ : Vector RPoly sp.ℓ) (s₂ : Vector RPoly sp.k) (c : RPoly) (y : Vector Spec.Poly sp.ℓ) :
    Verify.wApprox sp A
        ((y + NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (s₁.map RPoly.toZq)))).map Poly.modPM)
        (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).1 c =
      NTTInvVec (MatrixVectorNTT A (NTTVec y)) -
        NTTInvVec (ScalarVectorNTT (NTT c.toZq) (NTTVec (s₂.map RPoly.toZq))) +
        NTTInvVec (ScalarVectorNTT (NTT c.toZq)
          (NTTVec ((Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).2.map RPoly.toZq))) := by
  have ht : KeyGen.tVec sp A s₁ s₂ =
      NTTInvVec (MatrixVectorNTT A (NTTVec (s₁.map RPoly.toZq))) + s₂.map RPoly.toZq := rfl
  have hT := Corr.power2RoundVec_spec sp hp.d_eq (KeyGen.tVec sp A s₁ s₂)
  have h := Corr.approx_eq A y (s₁.map RPoly.toZq) (s₂.map RPoly.toZq) _ _ _ (NTT c.toZq) ht hT
  unfold Verify.wApprox
  rw [Corr.map_modPM_toZq]
  exact h

/-! ## Spec level, internal -/

set_option maxHeartbeats 4000000 in
/-- **Correctness, internal.** For `(pk, sk)` from `KeyGen_internal ξ` and a signature `σ` returned by
`Sign_internal_bounded` (any attempt budget `B`) at the same fuel `F`, `Verify_internal` accepts. -/
theorem correct_internal {sp : Spec.Params} (hp : StdParams sp) (B : Nat) (ξ M' rnd : List UInt8)
    (F : Spec.Fuel) (pk sk σ : List UInt8)
    (hk : Spec.KeyGen_internal sp ξ F = some (pk, sk))
    (hs : Spec.Sign_internal_bounded sp B sk M' rnd F = some σ) :
    Spec.Verify_internal sp pk M' σ F = some true := by
  obtain ⟨ρ, K, tr, A, s₁, s₂, hA, hη1, hη2, hdsk, hdpk, htr⟩ := keygen_facts hp F ξ pk sk hk
  have hlpk : pk.length = sp.pkLen := (API.keygen_lens sp hp.d_eq F ξ pk sk hk).1
  rw [Sign.Sign_internal_bounded_eq] at hs
  rcases hP : Sign.pre sp F sk M' rnd with _ | P
  · rw [hP] at hs; simp at hs
  rw [hP] at hs
  simp only [] at hs
  rcases hl : Sign.loopRes sp F P B 0 with _ | _ | ⟨ct, z, h⟩
  · rw [hl] at hs; simp [Sign.encodeRes] at hs
  · rw [hl] at hs; simp [Sign.encodeRes] at hs
  rw [hl] at hs
  simp only [Sign.encodeRes, Option.some.injEq] at hs
  -- the pre-loop values
  obtain ⟨Â, hÂ, hPeq⟩ := Sign.pre_some hP ρ K tr s₁ s₂ _ hdsk
  have hAA : Â = A := Option.some.inj (hÂ.symm.trans hA)
  rw [hAA] at hPeq
  have hPA : P.Â = A := by rw [hPeq]
  have hPs₁ : P.s₁ = s₁ := by rw [hPeq]
  have hPs₂ : P.s₂ = s₂ := by rw [hPeq]
  have hPt₀ : P.t₀ = (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).2 := by rw [hPeq]
  have hPμ : P.μ = H (tr ++ M') 64 := by rw [hPeq]
  -- the accepted attempt
  obtain ⟨κ, hat⟩ := loopRes_attempt sp F P B 0 ct z h hl
  obtain ⟨c, hct, hcs, hzE, hhE, hz1, hr0, hct0, hw⟩ := attempt_facts sp F P κ ct z h hat
  generalize Sign.maskAt sp P κ = y at hct hzE hhE hr0 hct0
  simp only [hPA, hPs₁, hPs₂, hPt₀, hPμ] at hct hzE hhE hr0 hct0
  -- bounds
  have hβ : 2 * sp.β < Spec.q := beta_two_lt hp
  obtain ⟨hc3, hcτ⟩ := Corr.ball_facts (Corr.SampleInBall_ball sp hp.tau_le_256 F.sampleInBall ct c hcs)
  have hcs2 := Corr.cs_norm_bound_params sp c s₂ hc3 hcτ hη2 hβ
  have hctlen : ct.length = sp.lam / 4 := by rw [hct]; exact SHAKE256_length _ _
  have hσlen : σ.length = sp.sigLen := by
    rw [← hs]; exact API.sigEncode_length sp hp.stdSig ct hctlen _ _
  have hzlt : ‖z‖∞ < sp.γ₁ := by omega
  have hω : sp.ω < 256 := by have := hp.omega_le; omega
  have hsd : Spec.sigDecode sp σ = some (ct, z.map Poly.modPM, h) := by
    rw [← hs]; exact Corr.sigDecode_sigEncode_modPM sp hp.gamma1 hω ct hctlen z h hzlt hw
  -- Verify returns `some`
  have hisSome : (Spec.Verify_internal sp pk M' σ F).isSome = true := by
    refine (Verify.verify_isSome_iff sp F pk M' σ hlpk hσlen).mpr ?_
    intro c' z' h' hsd'
    rw [hsd] at hsd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hsd'
    obtain ⟨rfl, rfl, rfl⟩ := hsd'
    refine ⟨?_, ?_⟩
    · rw [hdpk]; simp [hA]
    · rw [hcs]; rfl
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hisSome
  obtain ⟨A', c', hA', hc', hbEq⟩ :=
    Verify.verify_some sp F pk M' σ b hlpk hσlen ct (z.map Poly.modPM) h hsd hb
  rw [hdpk] at hA'
  have hAA' : A' = A := Option.some.inj (hA'.symm.trans hA)
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hcs)
  rw [hAA', hcc, hdpk] at hbEq
  -- `UseHint` recovers `HighBits w`
  have hU : Spec.UseHintVec sp h (Verify.wApprox sp A (z.map Poly.modPM)
      (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).1 c) =
      HighBitsVec sp (NTTInvVec (MatrixVectorNTT A (NTTVec y))) := by
    rw [hzE, hhE, wApprox_sign hp A s₁ s₂ c y]
    exact Corr.sign_verify_w1 sp hp.stdGamma2 _ _ _ hcs2 (not_le.mpr hr0) (not_le.mpr hct0)
  have hct' : ct = Verify.cTildePrime sp pk M'
      (HighBitsVec sp (NTTInvVec (MatrixVectorNTT A (NTTVec y)))) := by
    rw [hct, Verify.cTildePrime, htr]
  have hnorm : ‖z.map Poly.modPM‖∞ < sp.γ₁ - sp.β := by
    have := Corr.infNorm_map_modPM z (sp.γ₁ - sp.β - 1) (by omega)
    omega
  have hfinal : (decide (‖z.map Poly.modPM‖∞ < sp.γ₁ - sp.β) &&
      ct == Verify.cTildePrime sp pk M' (UseHintVec sp h (Verify.wApprox sp A (z.map Poly.modPM)
        (Power2RoundVec sp (KeyGen.tVec sp A s₁ s₂)).1 c))) = true := by
    rw [hU, ← hct']
    simp [hnorm]
  rw [hb, hbEq.trans hfinal]

/-! ## Spec level, external -/

/-- **Correctness, external (Algorithms 1, 2, 3).** If `KeyGen ξ` returns `(pk, sk)` and `Sign sk M ctx rnd`
returns `σ` (so `|ctx| ≤ 255`), then `Verify pk M σ ctx` returns `true`. All three at the same fuel `F`. -/
theorem correct_external {sp : Spec.Params} (hp : StdParams sp) (ξ M ctx rnd : List UInt8) (F : Spec.Fuel)
    (pk sk σ : List UInt8)
    (hk : Spec.KeyGen sp ξ F = some (pk, sk))
    (hs : Spec.Sign sp sk M ctx rnd F = some σ) :
    Spec.Verify sp pk M σ ctx F = some true := by
  have hl : ctx.length ≤ 255 := by
    by_contra hh
    rw [API.Sign_long sp sk M ctx rnd F (by omega)] at hs
    exact absurd hs (by simp)
  rw [API.Sign_short sp sk M ctx rnd F hl] at hs
  rw [API.Verify_short sp pk M σ ctx F hl]
  exact correct_internal hp _ ξ _ rnd F pk sk σ hk hs

/-! ## Transfer to the extracted Rust -/

open Aeneas Aeneas.Std RustM
open Impl

/-- **Correctness of the extracted ML-DSA-44.** If the spec's `KeyGen` and `Sign` return `some`, the Rust
`keygen_44`, then `sign_44` on its secret key, then `verify_44` on its public key and the returned signature all
return `ok`, the first two agree with the spec bytes, and the verdict is `true`. -/
theorem correct_44 (ξ : Array U8 32#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (pk₀ sk₀ σ₀ : List UInt8)
    (hk : Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (pk₀, sk₀))
    (hs : Spec.Sign Spec.ML_DSA_44 sk₀ (bytes m) (bytes ctx) (bytesA rnd) F = some σ₀) :
    ∃ (pk : Array U8 1312#usize) (sk : Array U8 2560#usize) (σ : Array U8 2420#usize),
      api.keygen_44 ξ = ok (pk, sk) ∧ bytesA pk = pk₀ ∧ bytesA sk = sk₀ ∧
      api.sign_44 sk m ctx rnd = ok (some σ) ∧ bytesA σ = σ₀ ∧
      api.verify_44 pk m ctx σ = ok true := by
  obtain ⟨⟨pk, sk⟩, hkg, hpk, hsk⟩ := WP.spec_imp_exists (keygen_44_correct ξ F pk₀ sk₀ hk)
  dsimp only at hpk hsk
  have hs' : Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ₀ := by
    rw [hsk]; exact hs
  obtain ⟨r2, hsg, σ, hr2, hσ⟩ := WP.spec_imp_exists (sign_44_correct_some sk m ctx rnd F σ₀ hs')
  subst hr2
  have hv : Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA σ) (bytes ctx) F = some true := by
    rw [hpk, hσ]; exact correct_external stdParams_44 _ _ _ _ F pk₀ sk₀ σ₀ hk hs
  obtain ⟨r3, hvf, hr3⟩ := WP.spec_imp_exists (verify_44_correct pk m ctx σ F true hv)
  exact ⟨pk, sk, σ, hkg, hpk, hsk, hsg, hσ, by rw [hvf, hr3]⟩

/-- **Correctness of the extracted ML-DSA-65.** See `correct_44`. -/
theorem correct_65 (ξ : Array U8 32#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (pk₀ sk₀ σ₀ : List UInt8)
    (hk : Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (pk₀, sk₀))
    (hs : Spec.Sign Spec.ML_DSA_65 sk₀ (bytes m) (bytes ctx) (bytesA rnd) F = some σ₀) :
    ∃ (pk : Array U8 1952#usize) (sk : Array U8 4032#usize) (σ : Array U8 3309#usize),
      api.keygen_65 ξ = ok (pk, sk) ∧ bytesA pk = pk₀ ∧ bytesA sk = sk₀ ∧
      api.sign_65 sk m ctx rnd = ok (some σ) ∧ bytesA σ = σ₀ ∧
      api.verify_65 pk m ctx σ = ok true := by
  obtain ⟨⟨pk, sk⟩, hkg, hpk, hsk⟩ := WP.spec_imp_exists (keygen_65_correct ξ F pk₀ sk₀ hk)
  dsimp only at hpk hsk
  have hs' : Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ₀ := by
    rw [hsk]; exact hs
  obtain ⟨r2, hsg, σ, hr2, hσ⟩ := WP.spec_imp_exists (sign_65_correct_some sk m ctx rnd F σ₀ hs')
  subst hr2
  have hv : Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA σ) (bytes ctx) F = some true := by
    rw [hpk, hσ]; exact correct_external stdParams_65 _ _ _ _ F pk₀ sk₀ σ₀ hk hs
  obtain ⟨r3, hvf, hr3⟩ := WP.spec_imp_exists (verify_65_correct pk m ctx σ F true hv)
  exact ⟨pk, sk, σ, hkg, hpk, hsk, hsg, hσ, by rw [hvf, hr3]⟩

/-- **Correctness of the extracted ML-DSA-87.** See `correct_44`. -/
theorem correct_87 (ξ : Array U8 32#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (pk₀ sk₀ σ₀ : List UInt8)
    (hk : Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (pk₀, sk₀))
    (hs : Spec.Sign Spec.ML_DSA_87 sk₀ (bytes m) (bytes ctx) (bytesA rnd) F = some σ₀) :
    ∃ (pk : Array U8 2592#usize) (sk : Array U8 4896#usize) (σ : Array U8 4627#usize),
      api.keygen_87 ξ = ok (pk, sk) ∧ bytesA pk = pk₀ ∧ bytesA sk = sk₀ ∧
      api.sign_87 sk m ctx rnd = ok (some σ) ∧ bytesA σ = σ₀ ∧
      api.verify_87 pk m ctx σ = ok true := by
  obtain ⟨⟨pk, sk⟩, hkg, hpk, hsk⟩ := WP.spec_imp_exists (keygen_87_correct ξ F pk₀ sk₀ hk)
  dsimp only at hpk hsk
  have hs' : Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ₀ := by
    rw [hsk]; exact hs
  obtain ⟨r2, hsg, σ, hr2, hσ⟩ := WP.spec_imp_exists (sign_87_correct_some sk m ctx rnd F σ₀ hs')
  subst hr2
  have hv : Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA σ) (bytes ctx) F = some true := by
    rw [hpk, hσ]; exact correct_external stdParams_87 _ _ _ _ F pk₀ sk₀ σ₀ hk hs
  obtain ⟨r3, hvf, hr3⟩ := WP.spec_imp_exists (verify_87_correct pk m ctx σ F true hv)
  exact ⟨pk, sk, σ, hkg, hpk, hsk, hsg, hσ, by rw [hvf, hr3]⟩

end Proofs
