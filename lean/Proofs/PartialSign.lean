import Proofs.Sign
import Proofs.PartialSample
import Proofs.PartialBall
import Proofs.PartialVerify
import Proofs.PartialAPI

/-!
# Partial correctness and panic-freedom of Sign (FIPS 204 Algorithms 7 and 2), `sign_NN` and `sign_internal_NN`

See `Proofs/Partial.lean` for the technique. Sign's rejection loop terminates (the Rust counter `kappa` is bounded
by `2^16`, the spec's budget is `kappaBudget`), so no new loop lemma is needed: only the samplers inside it call
for partial correctness. `ExpandA` (before the loop) is `expand_a_partial`; `SampleInBall` (one per attempt) is
`sample_in_ball_partial`; `ExpandMask` has no rejection.

* `attempt_partial`: one attempt never panics, and if it returns, the spec's `attemptAt` has the same outcome at
  some `SampleInBall` fuel.
* `sign_loop_partial`: the loop never panics, and its result is the spec's `loopRes` at some `SampleInBall` fuel.
  The fuels of the iterations are combined with `max`, which needs the fuel monotonicity of `SampleInBall`
  (`sampleInBall_fuel_mono`), `attemptAt` and `loopRes`.
* `sign_internal_partial`: `Rust sign_internal` never panics; if it returns `true` the output is the spec's
  signature at some fuel, and if it returns `false` the spec is `Exhausted` at some fuel (every one of the
  `kappaBudget` attempts ran within fuel and was rejected). This upgrades `sign_internal_NN_none_only_if` (the spec
  fails at every fuel) to an exact characterization of when the Rust returns `none`.
* `sign_NN_partial`, `sign_internal_NN_partial`: the same for the public API.
* `sign_NN_exact`, `sign_internal_NN_exact`: with the older `*_correct_some` / `_exhausted` / `_ctx_long` theorems
  the Rust agrees exactly with the unbounded FIPS 204 algorithm: never `fail`; the spec returning `some σ` at any
  fuel gives the Rust returning `some σ`; the Rust returning `some σ` gives the spec returning `some σ` at some
  fuel; and the Rust returns `none` exactly when `|ctx| > 255` or the spec is `Exhausted` at some fuel.

Premises: only the argument types (the slice-level `sign_internal_partial` takes `Params.Std` and the two length
hypotheses of `sign_internal_spec_some`; the API versions discharge them by the fixed array sizes).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

namespace PartialSign
open Sign

/-! ## Spec side: fuel monotonicity of the Sign loop in the `SampleInBall` fuel -/

theorem sampleInBall_fuel_mono (p : Spec.Params) (hτ : p.τ ≤ 256) (ρ : List UInt8) (F F' : Nat) (c : RPoly)
    (hF : F ≤ F') (h : Spec.SampleInBall p F ρ = some c) : Spec.SampleInBall p F' ρ = some c := by
  obtain ⟨pos, hpos⟩ := SampleInBall_model p hτ F ρ c h
  have hrun : runTo ρ p.τ F 256 = some (c, pos) := by
    unfold runTo
    have e : 256 - (256 - p.τ) = p.τ := by omega
    rw [e]
    unfold sibRun at hpos
    have hb : BytesToBits ((H ρ (8 + F)).take 8) = BytesToBits (Spec.SHAKE256 ρ 8) := by
      rw [show H ρ (8 + F) = Spec.SHAKE256 ρ (8 + F) from rfl, shake256_take ρ 8 (8 + F) (by omega)]
    rw [hb, show H ρ (8 + F) = Spec.SHAKE256 ρ (8 + F) from rfl] at hpos
    exact hpos
  exact SampleInBall_of_runTo p hτ ρ F' c pos (runTo_mono ρ p.τ F F' 256 hF _ hrun)

theorem attemptAt_fuel_mono (sp : Spec.Params) (hτ : sp.τ ≤ 256) (F F' : Spec.Fuel)
    (hF : F.sampleInBall ≤ F'.sampleInBall) (P : Pre sp) (κ : Nat) (r : List UInt8 × Out sp)
    (h : attemptAt sp F P κ = some r) : attemptAt sp F' P κ = some r := by
  unfold attemptAt at h ⊢
  rcases hS : Spec.SampleInBall sp F.sampleInBall (ctildeAt sp P κ) with _ | c
  · rw [hS] at h; simp at h
  · rw [hS] at h
    rw [sampleInBall_fuel_mono sp hτ _ _ _ c hF hS]
    exact h

theorem loopRes_fuel_mono (sp : Spec.Params) (hτ : sp.τ ≤ 256) (F F' : Spec.Fuel)
    (hF : F.sampleInBall ≤ F'.sampleInBall) (P : Pre sp) :
    ∀ (n κ : Nat) (T : Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k)),
      loopRes sp F P n κ = some T → loopRes sp F' P n κ = some T := by
  intro n
  induction n with
  | zero => intro κ T h; exact h
  | succ n ih =>
    intro κ T h
    simp only [loopRes] at h ⊢
    by_cases hc : 2 ^ 16 < κ + sp.ℓ
    · rw [if_pos hc] at h ⊢; exact h
    · rw [if_neg hc] at h ⊢
      rcases hA : attemptAt sp F P κ with _ | ⟨ct, _ | ⟨z, h'⟩⟩
      · simp [hA] at h
      · have hA' := attemptAt_fuel_mono sp hτ F F' hF P κ _ hA
        simp only [hA, hA'] at h ⊢
        exact ih _ T h
      · have hA' := attemptAt_fuel_mono sp hτ F F' hF P κ _ hA
        simp only [hA, hA'] at h ⊢
        exact h

theorem pre_of_decode {sp : Spec.Params} (F : Spec.Fuel) (sk M' rnd : List UInt8) (ρ K tr : List UInt8)
    (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hd : Spec.skDecode sp sk = (ρ, K, tr, s₁, s₂, t₀)) (Â : Vector (Vector Poly sp.ℓ) sp.k)
    (hA : Spec.ExpandA sp F.rejNTT ρ = some Â) :
    pre sp F sk M' rnd = some ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩ := by
  unfold pre
  rw [hd]
  dsimp only
  rw [hA]


/-! ## One attempt -/

theorem attempt_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (hb : SignBuf sp) (F : Spec.Fuel) (P : Pre sp)
    (a_hat : Array (Array (Array U32 256#usize) L) K) (hA : ReprMat a_hat P.Â)
    (s1_hat : Array (Array U32 256#usize) L) (hs1 : ReprVec s1_hat P.ŝ₁)
    (s2_hat : Array (Array U32 256#usize) K) (hs2 : ReprVec s2_hat P.ŝ₂)
    (t0_hat : Array (Array U32 256#usize) K) (ht0 : ReprVec t0_hat P.t₀hat)
    (mu : Array U8 64#usize) (hmu : bytesA mu = P.μ)
    (rho_pp : Array U8 64#usize) (hrho : bytesA rho_pp = P.ρ'')
    (kappa : U16) (hκ : kappa.val + sp.ℓ ≤ 2 ^ 16) :
    sign.attempt ip a_hat s1_hat s2_hat t0_hat mu rho_pp kappa ⦃ o =>
      ∃ F2 ct zh, attemptAt sp { F with sampleInBall := F2 } P kappa.val = some (ct, zh) ∧
        AttPost sp ct zh o ⦄div := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hg : StdGamma2 sp := hstd.stdGamma2
  obtain ⟨hβ1, hβ2⟩ := beta_lt_of_std hstd
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
  have hlam := hstd.lam_le
  unfold sign.attempt
  step with expand_mask_spec hv hstd.gamma₁ rho_pp kappa hκ as ⟨y, hy⟩
  rw [hrho] at hy
  have hY : ReprVec y (maskAt sp P kappa.val) := hy.repr
  step with ntt_vec_spec y _ hY as ⟨a, ha⟩
  step with matrix_vector_ntt_spec a_hat P.Â hA a _ ha as ⟨w_hat, hwhat⟩
  step with attempt_loop_spec ip sp hv hg w_hat _ hwhat (Array.repeat K (Array.repeat 256#usize 0#u32))
    (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (Rows.zero _ _) (Rows.zero _ _)
  rename' w11 => w2_post1
  obtain ⟨w2, w11⟩ := w2
  dsimp only at w2_post1 w2_post2 ⊢
  rw [hK] at w2_post1 w2_post2
  have hW : ReprVec w2 (commitAt sp P kappa.val) := Rows.reprVec w2_post1 hK
  have hw1 := Rows.hb_repr w2_post2 hK
  have hrng := Rows.hb_range w2_post2
  step*
  obtain ⟨s, to_slice_mut_back⟩ := s
  rename' to_slice_mut_back => s_post1
  try dsimp only at s_post1 s_post2 ⊢
  step with w1_encode_spec' ip sp hv w11 (HighBitsVec sp (commitAt sp P kappa.val)) hw1 hrng s
    (by rw [s_post1]; simpa [Array.repeat_val] using hb.w1_fits) as ⟨s1, hs1len, hs1b⟩
  step as ⟨h, h_post⟩
  step as ⟨s2, s2_post⟩
  step as ⟨h1, h1_post⟩
  have hmax : 4294967295 ≤ Usize.max := Usize.cMax_bound_concrete.1
  have hKm : K.val * 32 ≤ Usize.max := by
    have := hstd.k_le
    omega
  step as ⟨i, i_post⟩
  have hw1b : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hv.w1_bits
  have hmul : i.val * ip.w1_bits.val ≤ Usize.max := by
    have h1536 := hb.w1_fits
    rw [i_post, hK, hw1b]
    have e : sp.k * 32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) =
        32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by ring
    omega
  step as ⟨i1, i1_post⟩
  have hs1L : s1.val.length = 1536 := by rw [hs1len, s_post1]; simp [Array.repeat_val]
  have hbackv : (to_slice_mut_back s1).val = s1.val := by
    rw [s_post2]; exact Array.from_slice_val _ _ (by rw [hs1L]; rfl)
  have hback_len : ((to_slice_mut_back s1).to_slice).length = 1536 := by
    simp [Array.to_slice, Slice.length, hbackv, hs1L]
  have hi1_val : i1.val = sp.k * 32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by
    rw [i1_post, i_post, hK, hw1b]
  have hi1_le : i1.val ≤ 1536 := by
    have h1536 := hb.w1_fits
    have e : sp.k * 32 * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) =
        32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by ring
    omega
  have hctl : ip.c_tilde_len.val ≤ 64 := by rw [hcl]; exact hlam
  step*
  rename' index_mut_back => s4_post1
  obtain ⟨s4, index_mut_back⟩ := s4
  dsimp only at s4_post1 s4_post2 s4_post3 ⊢
  step*
  rename' s5 => s5_sq
  split_pair
  rename_i hx5 s5
  try dsimp only at s5_sq __post2
  try dsimp only
  rename' __post2 => s5_raw
  step*
  have hs2b : bytes s2 = P.μ := by rw [s2_post, bytes_to_slice, hmu]
  have hi1' : i1.val = 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by
    rw [hi1_val]; ring
  have hs3b : bytes s3 = w1Encode sp (HighBitsVec sp (commitAt sp P kappa.val)) := by
    have e : bytes s3 = (bytes s1).take i1.val := by
      simp [bytes, s3_post1, List.slice, Array.to_slice, hbackv, List.map_take]
    rw [e, hi1', hs1b]
  have hs4l : s4.val.length = sp.lam / 4 := by
    have h := s4_post2
    simp only [Slice.length] at h
    rw [h, hcl]
  have hs5b : bytes s5 = ctildeAt sp P kappa.val := by
    rw [s5_raw, List.drop_zero, Nat.zero_add, hs4l, hs2b, hs3b]
    unfold ctildeAt
    simp only [List.nil_append]
    rfl
  have hs5l : s5.val.length = sp.lam / 4 := by
    have h := congrArg List.length hs5b
    simp only [bytes, List.length_map] at h
    rw [h]
    unfold ctildeAt H
    exact SHAKE256_length _ _
  have hctp : (bytesA (index_mut_back s5)).take (sp.lam / 4) = ctildeAt sp P kappa.val := by
    have hn : s5.val.length ≤ (Array.repeat 64#usize 0#u8).val.length := by
      simp [hs5l]; omega
    have e := setSlice_zero (Array.repeat 64#usize 0#u8).val s5.val hn
    have hmap : bytesA (index_mut_back s5) =
        ((s5.val ++ (Array.repeat 64#usize 0#u8).val.drop s5.val.length).map
          fun x => UInt8.ofNat x.val) := by
      simp only [bytesA, s4_post3, e]
    rw [hmap, List.map_append, List.take_left' (by simp [hs5l])]
    exact hs5b
  have hs6b : bytes s6 = ctildeAt sp P kappa.val := by
    have e : bytes s6 = (bytesA (index_mut_back s5)).take ip.c_tilde_len.val := by
      simp [bytes, bytesA, s6_post1, List.slice, Array.to_slice, List.map_take]
    rw [e, hcl, hctp]
  refine WP.dspec_bind' (sample_in_ball_partial hv hstd.tau s6) ?_
  rintro cp ⟨c, F2, hC, hcp⟩
  rw [hs6b] at hC
  obtain ⟨zh, hzh⟩ : ∃ zh, respond sp P (maskAt sp P kappa.val) (commitAt sp P kappa.val) c = zh := ⟨_, rfl⟩
  have hatt : attemptAt sp { F with sampleInBall := F2 } P kappa.val = some (ctildeAt sp P kappa.val, zh) := by
    unfold attemptAt
    show (match Spec.SampleInBall sp F2 (ctildeAt sp P kappa.val) with
      | some c => some (ctildeAt sp P kappa.val, respond sp P (maskAt sp P kappa.val) (commitAt sp P kappa.val) c)
      | none => none) = _
    simp only [hC, hzh]
  step with ntt_spec cp hcp.canon as ⟨c_hat, hch1, hch2⟩
  have hchat : Repr c_hat (NTT c.toZq) := ⟨hch1, by rw [hch2, hcp.2]⟩
  refine dspec_bind_of_spec (response_spec ip sp hv hg y _ hY c_hat _ hchat s1_hat _ hs1 s2_hat _ hs2 w2 _ hW) ?_
  rintro ⟨z, wcs, r0⟩ ⟨hz, hwc, hr0⟩
  dsimp only at hz hwc hr0 ⊢
  have hg1v : ip.gamma1.val = sp.γ₁ := hv.gamma1
  have hg2v : ip.gamma2.val = sp.γ₂ := hv.gamma2
  have hbv : ip.beta.val = sp.β := hv.beta
  have hov : ip.omega.val = sp.ω := hv.omega
  step with vec_infinity_norm_spec_zq z _ hz as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hi3' : i3.val = sp.γ₁ - sp.β := by rw [hi3, hg1v, hbv]
  by_cases hc1 : i2 ≥ i3
  · rw [if_pos hc1]
    simp only [WP.dspec_ok]
    have h1 := (show i3.val ≤ i2.val by scalar_tac)
    rw [hi2, hi3'] at h1
    have hnone : zh = none := by rw [← hzh, respond_eq, if_pos (Or.inl h1)]
    refine ⟨F2, _, zh, hatt, ?_⟩
    rw [hnone]; simp [AttPost]
  rw [if_neg hc1]
  have h1 := (show i2.val < i3.val by scalar_tac)
  rw [hi2, hi3'] at h1
  step with vec_infinity_norm_lowbits_spec sp hg r0 _ hr0 as ⟨i4, hi4, hi4le⟩
  step as ⟨i5, hi5⟩
  have hi5' : i5.val = sp.γ₂ - sp.β := by rw [hi5, hg2v, hbv]
  by_cases hc2 : i4 ≥ i5
  · rw [if_pos hc2]
    simp only [WP.dspec_ok]
    have h2 := (show i5.val ≤ i4.val by scalar_tac)
    rw [hi4, hi5'] at h2
    have hnone : zh = none := by rw [← hzh, respond_eq, if_pos (Or.inr h2)]
    refine ⟨F2, _, zh, hatt, ?_⟩
    rw [hnone]; simp [AttPost]
  rw [if_neg hc2]
  have h2 := (show i4.val < i5.val by scalar_tac)
  rw [hi4, hi5'] at h2
  have hnot1 := not_or.2 ⟨not_le.2 h1, not_le.2 h2⟩
  refine dspec_bind_of_spec (hint_step_spec ip sp hv hg hstd.k_le c_hat _ hchat t0_hat _ ht0 wcs _ hwc) ?_
  rintro ⟨hint, ct0, ones⟩ ⟨hh, hct0, hones⟩
  dsimp only at hh hct0 hones ⊢
  step with vec_infinity_norm_spec_zq ct0 _ hct0 as ⟨i6, hi6⟩
  by_cases hc3 : i6 ≥ ip.gamma2
  · rw [if_pos hc3]
    simp only [WP.dspec_ok]
    have h3 := (show ip.gamma2.val ≤ i6.val by scalar_tac)
    rw [hi6, hg2v] at h3
    have hnone : zh = none := by rw [← hzh, respond_eq, if_neg hnot1, if_pos (Or.inl h3)]
    refine ⟨F2, _, zh, hatt, ?_⟩
    rw [hnone]; simp [AttPost]
  rw [if_neg hc3]
  have h3 := (show i6.val < ip.gamma2.val by scalar_tac)
  rw [hi6, hg2v] at h3
  by_cases hc4 : ones > ip.omega
  · rw [if_pos hc4]
    simp only [WP.dspec_ok]
    have h4 := (show ip.omega.val < ones.val by scalar_tac)
    rw [hones, hov] at h4
    have hnone : zh = none := by rw [← hzh, respond_eq, if_neg hnot1, if_pos (Or.inr h4)]
    refine ⟨F2, _, zh, hatt, ?_⟩
    rw [hnone]; simp [AttPost]
  rw [if_neg hc4]
  simp only [WP.dspec_ok]
  have h4 := (show ones.val ≤ ip.omega.val by scalar_tac)
  rw [hones, hov] at h4
  refine ⟨F2, _, zh, hatt, ?_⟩
  rw [← hzh, respond_eq, if_neg hnot1, if_neg (not_or.2 ⟨not_le.2 h3, not_lt.2 h4⟩)]
  exact ⟨_, _, _, rfl, hctp, hz, hh, h1, h4⟩

theorem kappaBudget_le_of (sp : Spec.Params) (hl : 1 ≤ sp.ℓ) (n : Nat) (hn : 2 ^ 16 ≤ n * sp.ℓ) :
    kappaBudget sp ≤ n := by
  unfold kappaBudget
  by_contra hlt
  have h1 : n ≤ (2 ^ 16 - sp.ℓ) / sp.ℓ := by omega
  have h2 : n * sp.ℓ ≤ (2 ^ 16 - sp.ℓ) / sp.ℓ * sp.ℓ := Nat.mul_le_mul_right _ h1
  have h3 := Nat.div_mul_le_self (2 ^ 16 - sp.ℓ) sp.ℓ
  have h4 : sp.ℓ ≤ 2 ^ 16 := by
    by_contra h5
    have : (2 ^ 16 - sp.ℓ) = 0 := by omega
    rw [this] at h1
    simp at h1
    subst h1
    omega
  omega


/-! ## The rejection loop -/

theorem sign_loop_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (hb : SignBuf sp) (F : Spec.Fuel) (P : Pre sp)
    (a_hat : Array (Array (Array U32 256#usize) L) K) (hA : ReprMat a_hat P.Â)
    (s1_hat : Array (Array U32 256#usize) L) (hs1 : ReprVec s1_hat P.ŝ₁)
    (s2_hat : Array (Array U32 256#usize) K) (hs2 : ReprVec s2_hat P.ŝ₂)
    (t0_hat : Array (Array U32 256#usize) K) (ht0 : ReprVec t0_hat P.t₀hat)
    (mu : Array U8 64#usize) (hmu : bytesA mu = P.μ)
    (rho_pp : Array U8 64#usize) (hrho : bytesA rho_pp = P.ρ'')
    (sig : Slice U8) (hsig : sig.length = sp.sigLen) (kappa : U32) (hk : kappa.val ≤ 2 ^ 16) :
    sign.sign_prepared_internal_loop ip a_hat s1_hat s2_hat t0_hat sig mu rho_pp kappa ⦃ r =>
      ∃ F2 n T, 2 ^ 16 ≤ kappa.val + n * sp.ℓ ∧
        loopRes sp { F with sampleInBall := F2 } P n kappa.val = some T ∧ LoopPost sp T sig r ⦄div := by
  obtain ⟨hv, hstd⟩ := hp
  have hp : Params.Std ip K L sp := ⟨hv, hstd⟩
  have hL : L.val = sp.ℓ := hv.L_eq
  have hl1 := hb.ell_pos
  have hl256 : sp.ℓ < 256 := by have := hstd.kl_lt; omega
  have hτ : sp.τ ≤ 256 := by have := hstd.tau_le; omega
  unfold sign.sign_prepared_internal_loop
  refine loop.dspec_rel _ (fun k : U32 => k.val ≤ 2 ^ 16)
    (fun k r => ∃ F2 n T, 2 ^ 16 ≤ k.val + n * sp.ℓ ∧
        loopRes sp { F with sampleInBall := F2 } P n k.val = some T ∧ LoopPost sp T sig r) ?_ kappa hk
  intro kappa hk
  simp only [sign.sign_prepared_internal_loop.body]
  step as ⟨i, hi⟩
  have hiv : i.val = sp.ℓ := by
    rw [hi]; simp [UScalar.cast_val_eq]
    have : L.val % 4294967296 = L.val := Nat.mod_eq_of_lt (by omega)
    omega
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  split
  · rename_i hc
    have hc' : kappa.val + sp.ℓ ≤ 2 ^ 16 := by
      have : i2.val ≤ 65535 := by scalar_tac
      omega
    have hklt : kappa.val < 2 ^ 16 := by omega
    have hlt : ¬ 2 ^ 16 < kappa.val + sp.ℓ := by omega
    step as ⟨i3, hi3⟩
    have hi3v : i3.val = kappa.val := by
      rw [hi3]; simp [UScalar.cast_val_eq]
      omega
    refine WP.dspec_bind' (attempt_partial hp hb F P a_hat hA s1_hat hs1 s2_hat hs2 t0_hat ht0 mu hmu rho_pp hrho i3
      (by omega)) ?_
    rintro o ⟨F2, ct, zh, hatt, ho⟩
    rw [hi3v] at hatt
    cases zh with
    | none =>
      simp only [AttPost] at ho
      rw [ho]
      dsimp only
      step as ⟨i4, hi4⟩
      have hi4v : i4.val = sp.ℓ := by
        rw [hi4]; simp [UScalar.cast_val_eq]
        have : L.val % 4294967296 = L.val := Nat.mod_eq_of_lt (by omega)
        omega
      step as ⟨kappa1, hk1⟩
      refine ⟨by omega, ?_⟩
      intro r F3 n T hn hT hpost
      have hk1v : kappa1.val = kappa.val + sp.ℓ := by omega
      rw [hk1v] at hn hT
      refine ⟨max F2 F3, n + 1, T, ?_, ?_, hpost⟩
      · have : (n + 1) * sp.ℓ = n * sp.ℓ + sp.ℓ := by ring
        omega
      · have hF2 : ({ F with sampleInBall := F2 } : Spec.Fuel).sampleInBall ≤
            ({ F with sampleInBall := max F2 F3 } : Spec.Fuel).sampleInBall := Nat.le_max_left _ _
        have hF3 : ({ F with sampleInBall := F3 } : Spec.Fuel).sampleInBall ≤
            ({ F with sampleInBall := max F2 F3 } : Spec.Fuel).sampleInBall := Nat.le_max_right _ _
        have hA' := attemptAt_fuel_mono sp hτ _ _ hF2 P kappa.val _ hatt
        have hT' := loopRes_fuel_mono sp hτ _ _ hF3 P n _ T hT
        simp only [loopRes]
        rw [if_neg hlt]
        simp only [hA']
        exact hT'
    | some zh' =>
      obtain ⟨z, h⟩ := zh'
      simp only [AttPost] at ho
      obtain ⟨ctb, zr, hr, he, hctb, hzr, hhr, hzn, hhw⟩ := ho
      rw [he]
      dsimp only
      step as ⟨s, hs⟩
      have hbs : bytes s = bytesA ctb := by rw [hs, bytes_to_slice]
      have hsl : sp.lam / 4 ≤ s.length := by
        have hl : ctb.val.length = 64 := ctb.property
        have : s.length = 64 := by rw [Slice.length, hs]; simpa [Array.to_slice] using hl
        have := hstd.lam_le
        omega
      refine dspec_bind_of_spec (sig_encode_signed_spec' ip sp hv hstd.stdSig s hsl zr z hzr hzn hr h hhr hhw sig hsig) ?_
      intro sig1 hsig1
      simp only [WP.dspec_ok]
      refine ⟨F2, 2 ^ 16, some (ct, z, h), ?_, ?_, rfl, ?_⟩
      · have : 2 ^ 16 ≤ 2 ^ 16 * sp.ℓ := Nat.le_mul_of_pos_right _ hl1
        omega
      · obtain ⟨n', hn'⟩ : ∃ n', 2 ^ 16 = n' + 1 := ⟨2 ^ 16 - 1, by omega⟩
        rw [hn']
        simp only [loopRes]
        rw [if_neg hlt]
        simp only [hatt]
      · show bytes sig1 = _
        rw [hsig1, hbs, hctb]
  · rename_i hc
    have hc' : 2 ^ 16 < kappa.val + sp.ℓ := by
      have : ¬ i2.val ≤ 65535 := by scalar_tac
      omega
    simp only [WP.dspec_ok]
    refine ⟨F.sampleInBall, 0 + 1, none, by omega, ?_, rfl, rfl⟩
    simp only [loopRes]
    rw [if_pos hc']


end PartialSign

open Sign PartialSign

/-! ## `sign_internal` -/

/-- **The key half of Sign, partial.** `prepare_sk` never fails; if it returns, `ps` holds ŝ₁, ŝ₂, t̂₀, K and tr as
`skDecode` gives them and Â = ExpandA(ρ) (at some fuel `F1` of the spec). It diverges exactly where ExpandA does. -/
theorem prepare_sk_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk : Slice U8) (hsk : sk.length = sp.skLen)
    (ρ Kk tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hd : Spec.skDecode sp (bytes sk) = (ρ, Kk, tr, s₁, s₂, t₀)) :
    sign.prepare_sk K L ip sk ⦃ ps =>
      ∃ (Â : Vector (Vector Poly sp.ℓ) sp.k) (F1 : Nat), Spec.ExpandA sp F1 ρ = some Â ∧
      ReprMat ps.a_hat Â ∧ ReprVec ps.s1_hat (NTTVec (s₁.map RPoly.toZq)) ∧
      ReprVec ps.s2_hat (NTTVec (s₂.map RPoly.toZq)) ∧ ReprVec ps.t0_hat (NTTVec (t₀.map RPoly.toZq)) ∧
      bytesA ps.key = Kk ∧ bytesA ps.tr = tr ⦄div := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  unfold sign.prepare_sk
  refine dspec_bind_of_spec (sk_decode_spec ip sp hv hstd.eta_lt sk hsk) ?_
  intro key ⟨hrho, hkey, htr, hs1, hs2, ht0⟩
  rw [hd] at hrho hkey htr hs1 hs2 ht0
  dsimp only at hrho hkey htr hs1 hs2 ht0
  refine dspec_bind_of_spec (ntt_vec_spec key.s1 _ hs1.repr) ?_
  intro s1_hat hs1h
  refine dspec_bind_of_spec (ntt_vec_spec key.s2 _ hs2.repr) ?_
  intro s2_hat hs2h
  refine dspec_bind_of_spec (ntt_vec_spec key.t0 _ ht0.repr) ?_
  intro t0_hat ht0h
  refine WP.dspec_bind' (expand_a_partial sp K L hK hL key.rho) ?_
  rintro a_hat ⟨Â, F1, hA, hAh⟩
  rw [hrho] at hA
  simp only [WP.dspec_ok]
  exact ⟨Â, F1, hA, hAh, hs1h, hs2h, ht0h, hkey, htr⟩

/-- **Steps 6-33 on a prepared key, partial.** For a prepared key holding the values of `skDecode skb`, Â =
ExpandA(ρ) at fuel `F1`, ŝ₁, ŝ₂, t̂₀: the Rust never returns `fail`; a `true` result is the spec's signature (budget
`kappaBudget`) at some fuel, a `false` result means the spec is `Exhausted` at some fuel and the buffer is untouched. -/
theorem sign_prepared_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (hb : SignBuf sp)
    (ps : sign.PreparedSk K L) (m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (hsig : sig.length = sp.sigLen)
    (skb : List UInt8) (ρ Kk tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hd : Spec.skDecode sp skb = (ρ, Kk, tr, s₁, s₂, t₀))
    (Â : Vector (Vector Poly sp.ℓ) sp.k) (F1 : Nat) (hA1 : Spec.ExpandA sp F1 ρ = some Â)
    (hAh : ReprMat ps.a_hat Â) (hs1h : ReprVec ps.s1_hat (NTTVec (s₁.map RPoly.toZq)))
    (hs2h : ReprVec ps.s2_hat (NTTVec (s₂.map RPoly.toZq))) (ht0h : ReprVec ps.t0_hat (NTTVec (t₀.map RPoly.toZq)))
    (hkey : bytesA ps.key = Kk) (htr : bytesA ps.tr = tr) :
    sign.sign_prepared_internal ip ps m_prefix m rnd sig ⦃ r =>
      (r.1 = true → ∃ F, Spec.Sign_internal_bounded sp (kappaBudget sp) skb
        (bytes m_prefix ++ bytes m) (bytesA rnd) F = some (bytes r.2)) ∧
      (r.1 = false → (∃ F, Exhausted sp F skb (bytes m_prefix ++ bytes m) (bytesA rnd)) ∧ r.2 = sig) ⦄div := by
  have hp' := hp
  obtain ⟨hv, hstd⟩ := hp
  unfold sign.sign_prepared_internal
  step*
  rename' to_slice_mut_back => s1_post1
  obtain ⟨s1, tsmb0⟩ := s1
  dsimp only at s1_post1 s1_post2 ⊢
  step*
  rename' s2 => s2_sq
  split_pair
  rename_i hx2 s2
  try dsimp only at s2_sq __post2
  try dsimp only
  rename' __post2 => s2_raw
  step*
  rename' to_slice_mut_back1 => s6_post1
  obtain ⟨s6, tsmb1⟩ := s6
  dsimp only at s6_post1 s6_post2 ⊢
  step*
  rename' s7 => s7_sq
  split_pair
  rename_i hx7 s7
  try dsimp only at s7_sq __post2
  try dsimp only
  rename' __post2 => s7_raw
  have hsb : bytes s = tr := by rw [s_post, bytes_to_slice, htr]
  have hs1l : s1.val.length = 64 := by rw [s1_post1]; simp
  have hs2b : bytes s2 = H (tr ++ (bytes m_prefix ++ bytes m)) 64 := by
    rw [s2_raw, List.drop_zero, Nat.zero_add, hs1l, hsb]
    simp only [List.nil_append, List.append_assoc]
    rfl
  have hs2l : s2.val.length = 64 := by
    have h := congrArg List.length hs2b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  have hmu : bytesA (tsmb0 s2) = H (tr ++ (bytes m_prefix ++ bytes m)) 64 := by
    rw [s1_post2, bytesA_from_slice _ _ hs2l, hs2b]
  have hs3b : bytes s3 = Kk := by rw [s3_post, bytes_to_slice, hkey]
  have hs4b : bytes s4 = bytesA rnd := by rw [s4_post, bytes_to_slice]
  have hs5b : bytes s5 = H (tr ++ (bytes m_prefix ++ bytes m)) 64 := by
    rw [s5_post, bytes_to_slice, hmu]
  have hs6l : s6.val.length = 64 := by rw [s6_post1]; simp
  have hs7b : bytes s7 = H (Kk ++ bytesA rnd ++ H (tr ++ (bytes m_prefix ++ bytes m)) 64) 64 := by
    rw [s7_raw, List.drop_zero, Nat.zero_add, hs6l, hs3b, hs4b, hs5b]
    simp only [List.nil_append]
    rfl
  have hs7l : s7.val.length = 64 := by
    have h := congrArg List.length hs7b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  have hrho' : bytesA (tsmb1 s7) =
      H (Kk ++ bytesA rnd ++ H (tr ++ (bytes m_prefix ++ bytes m)) 64) 64 := by
    rw [s6_post2, bytesA_from_slice _ _ hs7l, hs7b]
  have hpre : ∀ F : Spec.Fuel, F.rejNTT = F1 → pre sp F skb (bytes m_prefix ++ bytes m) (bytesA rnd) =
      some ⟨s₁, s₂, t₀, Â, H (tr ++ (bytes m_prefix ++ bytes m)) 64,
        H (Kk ++ bytesA rnd ++ H (tr ++ (bytes m_prefix ++ bytes m)) 64) 64⟩ := by
    intro F hF
    exact pre_of_decode F _ _ _ ρ Kk tr s₁ s₂ t₀ hd Â (by rw [hF]; exact hA1)
  have hl1 := hb.ell_pos
  refine WP.dspec_mono' (sign_loop_partial hp' hb { rejNTT := F1 } ⟨s₁, s₂, t₀, Â, H (tr ++ (bytes m_prefix ++ bytes m)) 64,
      H (Kk ++ bytesA rnd ++ H (tr ++ (bytes m_prefix ++ bytes m)) 64) 64⟩ ps.a_hat hAh ps.s1_hat hs1h ps.s2_hat hs2h ps.t0_hat ht0h
      (tsmb0 s2) hmu (tsmb1 s7) hrho' sig hsig 0#u32 (by simp)) ?_
  rintro r ⟨F2, n, T, hn, hT, hpost⟩
  have e0 : (0#u32).val = 0 := by simp
  rw [e0] at hn hT
  have hP' := hpre { rejNTT := F1, sampleInBall := F2 } rfl
  have hn' : 2 ^ 16 ≤ n * sp.ℓ := by omega
  have hkb : kappaBudget sp ≤ n := kappaBudget_le_of sp hl1 n hn'
  have hT' : loopRes sp ({ rejNTT := F1, sampleInBall := F2 } : Spec.Fuel) ⟨s₁, s₂, t₀, Â,
      H (tr ++ (bytes m_prefix ++ bytes m)) 64, H (Kk ++ bytesA rnd ++ H (tr ++ (bytes m_prefix ++ bytes m)) 64) 64⟩
      (kappaBudget sp) 0 = some T := by
    obtain ⟨j, rfl⟩ : ∃ j, n = kappaBudget sp + j := ⟨n - kappaBudget sp, by omega⟩
    rw [loopRes_cap sp _ _ (kappaBudget sp) 0 j (kappaBudget_cap sp hl1)] at hT
    exact hT
  rcases T with _ | ⟨ct, z, h⟩
  · obtain ⟨hr1, hr2⟩ := hpost
    refine ⟨fun h => by rw [hr1] at h; exact absurd h (by decide), fun _ => ⟨⟨{ rejNTT := F1, sampleInBall := F2 }, _, hP', hT'⟩, hr2⟩⟩
  · obtain ⟨hr1, hr2⟩ := hpost
    refine ⟨fun _ => ⟨{ rejNTT := F1, sampleInBall := F2 }, ?_⟩, fun h => by rw [hr1] at h; exact absurd h (by decide)⟩
    rw [Sign_internal_bounded_eq, hP']
    simp only [hT', encodeRes, hr2]

/-- **`sign_internal`, partial correctness and panic-freedom** (FIPS 204 Algorithm 7). The Rust never returns
`fail`. If it returns `true`, the output buffer holds the spec's signature (budget `kappaBudget`) at some fuel; if it
returns `false`, the spec is `Exhausted` at some fuel (`ExpandA` and every `SampleInBall` within fuel, all
`kappaBudget` attempts rejected) and the output buffer is untouched. -/
theorem sign_internal_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp)
    (sk m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (hsk : sk.length = sp.skLen) (hsig : sig.length = sp.sigLen) :
    sign.sign_internal K L ip sk m_prefix m rnd sig ⦃ r =>
      (r.1 = true → ∃ F, Spec.Sign_internal_bounded sp (kappaBudget sp) (bytes sk)
        (bytes m_prefix ++ bytes m) (bytesA rnd) F = some (bytes r.2)) ∧
      (r.1 = false → (∃ F, Exhausted sp F (bytes sk) (bytes m_prefix ++ bytes m) (bytesA rnd)) ∧ r.2 = sig) ⦄div := by
  have hb : SignBuf sp := StdParams.signBuf (Params.Std.params hp)
  rcases hd : Spec.skDecode sp (bytes sk) with ⟨ρ, Kk, tr, s₁, s₂, t₀⟩
  unfold sign.sign_internal
  refine WP.dspec_bind' (prepare_sk_partial hp sk hsk ρ Kk tr s₁ s₂ t₀ hd) ?_
  rintro ps ⟨Â, F1, hA1, hAh, hs1h, hs2h, ht0h, hkey, htr⟩
  exact sign_prepared_partial hp hb ps m_prefix m rnd sig hsig (bytes sk) ρ Kk tr s₁ s₂ t₀ hd Â F1 hA1 hAh hs1h hs2h
    ht0h hkey htr

/-! ## Public API bodies -/

theorem signInternalAPI_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m : Slice U8) (rnd : Array U8 32#usize) :
    APIInternal.signInternalAPI n N K L (ok ip) sk m rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign_internal_bounded sp (kappaBudget sp) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
      (r = none → ∃ F, Exhausted sp F (bytesA sk) (bytes m) (bytesA rnd)) ⦄div := by
  unfold APIInternal.signInternalAPI
  simp only [Std.bind_tc_ok]
  step*
  rename' to_slice_mut_back => s2_post1
  obtain ⟨s2, tsmb⟩ := s2
  dsimp only at s2_post1 s2_post2 ⊢
  have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
  have hls : s.length = sp.skLen := by
    have := congrArg List.length hbs
    simp only [bytes_length, bytesA_length] at this
    show s.val.length = _
    omega
  have hls2 : s2.length = sp.sigLen := by
    show s2.val.length = _
    rw [s2_post1]; simp [Array.repeat_val, hN]
  refine WP.dspec_bind' (sign_internal_partial hp s s1 m rnd s2 hls hls2) ?_
  rintro ⟨b1, s3⟩ ⟨H1, H2⟩
  dsimp only at H1 H2
  cases b1 with
  | false =>
    obtain ⟨⟨F, hF⟩, -⟩ := H2 rfl
    show WP.dspec (ok none) _
    rw [WP.dspec_ok]
    refine ⟨fun σ h => (by cases h), fun _ => ⟨F, ?_⟩⟩
    rw [hbs, s1_post, APIInternal.bytes_empty_prefix, List.nil_append] at hF
    exact hF
  | true =>
    obtain ⟨F, hF⟩ := H1 rfl
    show WP.dspec (ok (some (tsmb s3))) _
    rw [WP.dspec_ok]
    have hspec : Spec.Sign_internal_bounded sp (kappaBudget sp) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytes s3) := by
      rw [hbs, s1_post, APIInternal.bytes_empty_prefix, List.nil_append] at hF
      exact hF
    have hlenσ : (bytes s3).length = sp.sigLen :=
      API.sign_len sp (Params.Std.params hp).stdSig _ F _ _ _ _ hspec
    have hl3 : s3.val.length = N.val := by
      have := hlenσ
      simp only [bytes_length] at this
      omega
    refine ⟨fun σ h => ?_, fun h => by cases h⟩
    cases h
    refine ⟨F, ?_⟩
    rw [s2_post2, bytesA_from_slice _ _ hl3]
    exact hspec


theorem signAPI_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    API.signAPI n N K L (ok ip) sk m ctx rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign sp (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
      (r = none → 255 < (bytes ctx).length ∨ ∃ F, Exhausted sp F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) ⦄div := by
  unfold API.signAPI
  refine dspec_bind_of_spec (ctx_prefix_spec ctx) ?_
  intro o ho
  rcases o with _ | b'
  · have h' : 255 < (bytes ctx).length := by simp only [bytes_length]; exact ho
    simp only [WP.dspec_ok]
    exact ⟨fun σ h => (by cases h), fun _ => Or.inl h'⟩
  · obtain ⟨hl, htake, hdrop⟩ := ho
    simp only [Std.bind_tc_ok]
    step*
    rename' to_slice_mut_back => s2_post1
    obtain ⟨s2, tsmb⟩ := s2
    dsimp only at s2_post1 s2_post2 ⊢
    have hlen : ctx.len.val = ctx.val.length := by simp
    have hs1 : bytes s1 = [0, UInt8.ofNat ctx.val.length] ++ bytes ctx :=
      API.prefix_bytes ctx b' i1 s1 (by rw [i1_post, hlen]) s1_post1 htake
    have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
    have hls : s.length = sp.skLen := by
      have := congrArg List.length hbs
      simp only [bytes_length, bytesA_length] at this
      show s.val.length = _
      omega
    have hls2 : s2.length = sp.sigLen := by
      show s2.val.length = _
      rw [s2_post1]; simp [Array.repeat_val, hN]
    refine WP.dspec_bind' (sign_internal_partial hp s s1 m rnd s2 hls hls2) ?_
    rintro ⟨b1, s3⟩ ⟨H1, H2⟩
    dsimp only at H1 H2
    cases b1 with
    | false =>
      obtain ⟨⟨F, hF⟩, -⟩ := H2 rfl
      show WP.dspec (ok none) _
      rw [WP.dspec_ok]
      refine ⟨fun σ h => (by cases h), fun _ => Or.inr ⟨F, ?_⟩⟩
      rw [API.mprime_eq]
      rw [hbs, hs1] at hF
      simp only [bytes_length]
      exact hF
    | true =>
      obtain ⟨F, hF⟩ := H1 rfl
      show WP.dspec (ok (some (tsmb s3))) _
      rw [WP.dspec_ok]
      rw [hbs, hs1] at hF
      have hspec : Spec.Sign_internal_bounded sp (kappaBudget sp) (bytesA sk)
          ([0, UInt8.ofNat ctx.val.length] ++ bytes ctx ++ bytes m) (bytesA rnd) F = some (bytes s3) := hF
      have hlenσ : (bytes s3).length = sp.sigLen :=
        API.sign_len sp (Params.Std.params hp).stdSig _ F _ _ _ _ hspec
      have hl3 : s3.val.length = N.val := by
        have := hlenσ
        simp only [bytes_length] at this
        omega
      refine ⟨fun σ h => ?_, fun h => (by cases h)⟩
      cases h
      refine ⟨F, ?_⟩
      rw [API.Sign_short sp _ _ _ _ F (by simpa using hl)]
      simp only [bytes_length]
      rw [s2_post2, bytesA_from_slice _ _ hl3]
      exact hspec

/-! ## The six public functions -/

theorem sign_internal_44_dspec (sk : Array U8 2560#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_44 sk m rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_44 (kappaBudget Spec.ML_DSA_44) (bytesA sk) (bytes m)
        (bytesA rnd) F = some (bytesA σ)) ∧
      (r = none → ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd)) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [APIInternal.sign_internal_44_eq, hip]
  exact signInternalAPI_partial hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m rnd

theorem sign_44_dspec (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_44 sk m ctx rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F =
        some (bytesA σ)) ∧
      (r = none → 255 < (bytes ctx).length ∨ ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [API.sign_44_eq, hip]
  exact signAPI_partial hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m ctx rnd

theorem sign_internal_65_dspec (sk : Array U8 4032#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_65 sk m rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_65 (kappaBudget Spec.ML_DSA_65) (bytesA sk) (bytes m)
        (bytesA rnd) F = some (bytesA σ)) ∧
      (r = none → ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd)) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [APIInternal.sign_internal_65_eq, hip]
  exact signInternalAPI_partial hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m rnd

theorem sign_65_dspec (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_65 sk m ctx rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F =
        some (bytesA σ)) ∧
      (r = none → 255 < (bytes ctx).length ∨ ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [API.sign_65_eq, hip]
  exact signAPI_partial hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m ctx rnd

theorem sign_internal_87_dspec (sk : Array U8 4896#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_87 sk m rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_87 (kappaBudget Spec.ML_DSA_87) (bytesA sk) (bytes m)
        (bytesA rnd) F = some (bytesA σ)) ∧
      (r = none → ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd)) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [APIInternal.sign_internal_87_eq, hip]
  exact signInternalAPI_partial hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m rnd

theorem sign_87_dspec (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_87 sk m ctx rnd ⦃ r =>
      (∀ σ, r = some σ → ∃ F, Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F =
        some (bytesA σ)) ∧
      (r = none → 255 < (bytes ctx).length ∨ ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) ⦄div := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [API.sign_87_eq, hip]
  exact signAPI_partial hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m ctx rnd

/-! ## Headline statements -/

/-- **ML-DSA-44 `sign_internal`, partial correctness and panic-freedom** (Algorithm 7). The Rust never returns
`fail`; if it returns `some σ` then the spec (budget `kappaBudget`) returns `σ` at some fuel; if it returns `none`
then the spec is `Exhausted` at some fuel (every attempt within fuel and rejected). -/
theorem sign_internal_44_partial (sk : Array U8 2560#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_44 sk m rnd ≠ .fail e) ∧
    (∀ σ, api.sign_internal_44 sk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_44 (kappaBudget Spec.ML_DSA_44) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_44 sk m rnd = ok none →
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd)) :=
  ⟨dspec_not_fail (sign_internal_44_dspec sk m rnd),
    fun σ hσ => (WP.dspec_imp_forall (sign_internal_44_dspec sk m rnd) _ hσ).1 σ rfl,
    fun hn => (WP.dspec_imp_forall (sign_internal_44_dspec sk m rnd) _ hn).2 rfl⟩

/-- **ML-DSA-44 `sign`, partial correctness and panic-freedom** (Algorithm 2). The Rust never returns `fail`; if
it returns `some σ` then the spec returns `σ` at some fuel; if it returns `none` then `|ctx| > 255` or the spec is
`Exhausted` at some fuel for `M′ = 0 ‖ |ctx| ‖ ctx ‖ m`. -/
theorem sign_44_partial (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_44 sk m ctx rnd ≠ .fail e) ∧
    (∀ σ, api.sign_44 sk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_44 sk m ctx rnd = ok none → 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :=
  ⟨dspec_not_fail (sign_44_dspec sk m ctx rnd),
    fun σ hσ => (WP.dspec_imp_forall (sign_44_dspec sk m ctx rnd) _ hσ).1 σ rfl,
    fun hn => (WP.dspec_imp_forall (sign_44_dspec sk m ctx rnd) _ hn).2 rfl⟩

/-- **ML-DSA-65 `sign_internal`, partial correctness and panic-freedom** (Algorithm 7). The Rust never returns
`fail`; if it returns `some σ` then the spec (budget `kappaBudget`) returns `σ` at some fuel; if it returns `none`
then the spec is `Exhausted` at some fuel (every attempt within fuel and rejected). -/
theorem sign_internal_65_partial (sk : Array U8 4032#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_65 sk m rnd ≠ .fail e) ∧
    (∀ σ, api.sign_internal_65 sk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_65 (kappaBudget Spec.ML_DSA_65) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_65 sk m rnd = ok none →
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd)) :=
  ⟨dspec_not_fail (sign_internal_65_dspec sk m rnd),
    fun σ hσ => (WP.dspec_imp_forall (sign_internal_65_dspec sk m rnd) _ hσ).1 σ rfl,
    fun hn => (WP.dspec_imp_forall (sign_internal_65_dspec sk m rnd) _ hn).2 rfl⟩

/-- **ML-DSA-65 `sign`, partial correctness and panic-freedom** (Algorithm 2). The Rust never returns `fail`; if
it returns `some σ` then the spec returns `σ` at some fuel; if it returns `none` then `|ctx| > 255` or the spec is
`Exhausted` at some fuel for `M′ = 0 ‖ |ctx| ‖ ctx ‖ m`. -/
theorem sign_65_partial (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_65 sk m ctx rnd ≠ .fail e) ∧
    (∀ σ, api.sign_65 sk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_65 sk m ctx rnd = ok none → 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :=
  ⟨dspec_not_fail (sign_65_dspec sk m ctx rnd),
    fun σ hσ => (WP.dspec_imp_forall (sign_65_dspec sk m ctx rnd) _ hσ).1 σ rfl,
    fun hn => (WP.dspec_imp_forall (sign_65_dspec sk m ctx rnd) _ hn).2 rfl⟩

/-- **ML-DSA-87 `sign_internal`, partial correctness and panic-freedom** (Algorithm 7). The Rust never returns
`fail`; if it returns `some σ` then the spec (budget `kappaBudget`) returns `σ` at some fuel; if it returns `none`
then the spec is `Exhausted` at some fuel (every attempt within fuel and rejected). -/
theorem sign_internal_87_partial (sk : Array U8 4896#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_87 sk m rnd ≠ .fail e) ∧
    (∀ σ, api.sign_internal_87 sk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_87 (kappaBudget Spec.ML_DSA_87) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_87 sk m rnd = ok none →
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd)) :=
  ⟨dspec_not_fail (sign_internal_87_dspec sk m rnd),
    fun σ hσ => (WP.dspec_imp_forall (sign_internal_87_dspec sk m rnd) _ hσ).1 σ rfl,
    fun hn => (WP.dspec_imp_forall (sign_internal_87_dspec sk m rnd) _ hn).2 rfl⟩

/-- **ML-DSA-87 `sign`, partial correctness and panic-freedom** (Algorithm 2). The Rust never returns `fail`; if
it returns `some σ` then the spec returns `σ` at some fuel; if it returns `none` then `|ctx| > 255` or the spec is
`Exhausted` at some fuel for `M′ = 0 ‖ |ctx| ‖ ctx ‖ m`. -/
theorem sign_87_partial (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_87 sk m ctx rnd ≠ .fail e) ∧
    (∀ σ, api.sign_87 sk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_87 sk m ctx rnd = ok none → 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :=
  ⟨dspec_not_fail (sign_87_dspec sk m ctx rnd),
    fun σ hσ => (WP.dspec_imp_forall (sign_87_dspec sk m ctx rnd) _ hσ).1 σ rfl,
    fun hn => (WP.dspec_imp_forall (sign_87_dspec sk m ctx rnd) _ hn).2 rfl⟩

/-! ## Exactness: the Rust agrees with the unbounded FIPS 204 algorithm -/

/-- **ML-DSA-44 `sign_internal` is exactly the unbounded FIPS 204 Algorithm 7.** Never `fail`; if the spec
(any budget, any fuel) returns `σ`, the Rust returns `some σ'` with `σ'` holding `σ`; if the Rust returns
`some σ`, the spec (budget `kappaBudget`) returns `σ` at some fuel; the Rust returns `none` exactly when the spec is
`Exhausted` at some fuel. -/
theorem sign_internal_44_exact (sk : Array U8 2560#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_44 sk m rnd ≠ .fail e) ∧
    (∀ B F σ, Spec.Sign_internal_bounded Spec.ML_DSA_44 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_internal_44 sk m rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_internal_44 sk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_44 (kappaBudget Spec.ML_DSA_44) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_44 sk m rnd = ok none ↔
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd)) :=
  ⟨(sign_internal_44_partial sk m rnd).1,
    fun B F σ hs => by
      obtain ⟨r, hr, σ', rfl, h⟩ := WP.spec_imp_exists (sign_internal_44_correct_some sk m rnd B F σ hs)
      exact ⟨σ', hr, h⟩,
    (sign_internal_44_partial sk m rnd).2.1,
    ⟨(sign_internal_44_partial sk m rnd).2.2,
      fun ⟨F, hF⟩ => by
        obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_internal_44_correct_exhausted sk m rnd F hF)
        exact hr⟩⟩

/-- **ML-DSA-44 `sign` is exactly the unbounded FIPS 204 Algorithm 2.** Never `fail`; if the spec returns `σ` at
any fuel, the Rust returns `some σ'` with `σ'` holding `σ`; if the Rust returns `some σ`, the spec returns `σ` at some
fuel; the Rust returns `none` exactly when `|ctx| > 255` or the spec is `Exhausted` at some fuel. -/
theorem sign_44_exact (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_44 sk m ctx rnd ≠ .fail e) ∧
    (∀ F σ, Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_44 sk m ctx rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_44 sk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_44 sk m ctx rnd = ok none ↔ 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :=
  ⟨(sign_44_partial sk m ctx rnd).1,
    fun F σ hs => by
      obtain ⟨r, hr, σ', rfl, h⟩ := WP.spec_imp_exists (sign_44_correct_some sk m ctx rnd F σ hs)
      exact ⟨σ', hr, h⟩,
    (sign_44_partial sk m ctx rnd).2.1,
    ⟨(sign_44_partial sk m ctx rnd).2.2,
      fun hh => by
        rcases hh with hl | ⟨F, hF⟩
        · obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_44_correct_ctx_long sk m ctx rnd {} hl).2
          exact hr
        · obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_44_correct_exhausted sk m ctx rnd F hF)
          exact hr⟩⟩

/-- **ML-DSA-65 `sign_internal` is exactly the unbounded FIPS 204 Algorithm 7.** Never `fail`; if the spec
(any budget, any fuel) returns `σ`, the Rust returns `some σ'` with `σ'` holding `σ`; if the Rust returns
`some σ`, the spec (budget `kappaBudget`) returns `σ` at some fuel; the Rust returns `none` exactly when the spec is
`Exhausted` at some fuel. -/
theorem sign_internal_65_exact (sk : Array U8 4032#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_65 sk m rnd ≠ .fail e) ∧
    (∀ B F σ, Spec.Sign_internal_bounded Spec.ML_DSA_65 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_internal_65 sk m rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_internal_65 sk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_65 (kappaBudget Spec.ML_DSA_65) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_65 sk m rnd = ok none ↔
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd)) :=
  ⟨(sign_internal_65_partial sk m rnd).1,
    fun B F σ hs => by
      obtain ⟨r, hr, σ', rfl, h⟩ := WP.spec_imp_exists (sign_internal_65_correct_some sk m rnd B F σ hs)
      exact ⟨σ', hr, h⟩,
    (sign_internal_65_partial sk m rnd).2.1,
    ⟨(sign_internal_65_partial sk m rnd).2.2,
      fun ⟨F, hF⟩ => by
        obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_internal_65_correct_exhausted sk m rnd F hF)
        exact hr⟩⟩

/-- **ML-DSA-65 `sign` is exactly the unbounded FIPS 204 Algorithm 2.** Never `fail`; if the spec returns `σ` at
any fuel, the Rust returns `some σ'` with `σ'` holding `σ`; if the Rust returns `some σ`, the spec returns `σ` at some
fuel; the Rust returns `none` exactly when `|ctx| > 255` or the spec is `Exhausted` at some fuel. -/
theorem sign_65_exact (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_65 sk m ctx rnd ≠ .fail e) ∧
    (∀ F σ, Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_65 sk m ctx rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_65 sk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_65 sk m ctx rnd = ok none ↔ 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :=
  ⟨(sign_65_partial sk m ctx rnd).1,
    fun F σ hs => by
      obtain ⟨r, hr, σ', rfl, h⟩ := WP.spec_imp_exists (sign_65_correct_some sk m ctx rnd F σ hs)
      exact ⟨σ', hr, h⟩,
    (sign_65_partial sk m ctx rnd).2.1,
    ⟨(sign_65_partial sk m ctx rnd).2.2,
      fun hh => by
        rcases hh with hl | ⟨F, hF⟩
        · obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_65_correct_ctx_long sk m ctx rnd {} hl).2
          exact hr
        · obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_65_correct_exhausted sk m ctx rnd F hF)
          exact hr⟩⟩

/-- **ML-DSA-87 `sign_internal` is exactly the unbounded FIPS 204 Algorithm 7.** Never `fail`; if the spec
(any budget, any fuel) returns `σ`, the Rust returns `some σ'` with `σ'` holding `σ`; if the Rust returns
`some σ`, the spec (budget `kappaBudget`) returns `σ` at some fuel; the Rust returns `none` exactly when the spec is
`Exhausted` at some fuel. -/
theorem sign_internal_87_exact (sk : Array U8 4896#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_internal_87 sk m rnd ≠ .fail e) ∧
    (∀ B F σ, Spec.Sign_internal_bounded Spec.ML_DSA_87 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_internal_87 sk m rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_internal_87 sk m rnd = ok (some σ) →
      ∃ F, Spec.Sign_internal_bounded Spec.ML_DSA_87 (kappaBudget Spec.ML_DSA_87) (bytesA sk) (bytes m) (bytesA rnd) F =
        some (bytesA σ)) ∧
    (api.sign_internal_87 sk m rnd = ok none ↔
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd)) :=
  ⟨(sign_internal_87_partial sk m rnd).1,
    fun B F σ hs => by
      obtain ⟨r, hr, σ', rfl, h⟩ := WP.spec_imp_exists (sign_internal_87_correct_some sk m rnd B F σ hs)
      exact ⟨σ', hr, h⟩,
    (sign_internal_87_partial sk m rnd).2.1,
    ⟨(sign_internal_87_partial sk m rnd).2.2,
      fun ⟨F, hF⟩ => by
        obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_internal_87_correct_exhausted sk m rnd F hF)
        exact hr⟩⟩

/-- **ML-DSA-87 `sign` is exactly the unbounded FIPS 204 Algorithm 2.** Never `fail`; if the spec returns `σ` at
any fuel, the Rust returns `some σ'` with `σ'` holding `σ`; if the Rust returns `some σ`, the spec returns `σ` at some
fuel; the Rust returns `none` exactly when `|ctx| > 255` or the spec is `Exhausted` at some fuel. -/
theorem sign_87_exact (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    (∀ e, api.sign_87 sk m ctx rnd ≠ .fail e) ∧
    (∀ F σ, Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ →
      ∃ σ', api.sign_87 sk m ctx rnd = ok (some σ') ∧ bytesA σ' = σ) ∧
    (∀ σ, api.sign_87 sk m ctx rnd = ok (some σ) →
      ∃ F, Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some (bytesA σ)) ∧
    (api.sign_87 sk m ctx rnd = ok none ↔ 255 < (bytes ctx).length ∨
      ∃ F, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) :=
  ⟨(sign_87_partial sk m ctx rnd).1,
    fun F σ hs => by
      obtain ⟨r, hr, σ', rfl, h⟩ := WP.spec_imp_exists (sign_87_correct_some sk m ctx rnd F σ hs)
      exact ⟨σ', hr, h⟩,
    (sign_87_partial sk m ctx rnd).2.1,
    ⟨(sign_87_partial sk m ctx rnd).2.2,
      fun hh => by
        rcases hh with hl | ⟨F, hF⟩
        · obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_87_correct_ctx_long sk m ctx rnd {} hl).2
          exact hr
        · obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists (sign_87_correct_exhausted sk m ctx rnd F hF)
          exact hr⟩⟩

end Proofs
