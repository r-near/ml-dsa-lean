import Proofs.Verify
import Proofs.PartialSample
import Proofs.PartialBall

/-!
# Partial correctness of Verify (FIPS 204 Algorithms 8 and 3), `verify_NN` and `verify_internal_NN`

See `Proofs/Partial.lean` for the technique. For every input (pk, m, ctx, σ of the types of the API):

* the Rust never panics, and
* if it returns `b`, then there is a fuel `F` with `Spec.Verify … F = some b`.

The fuels of ExpandA and SampleInBall are independent fields of `Spec.Fuel`, so the two sampler fuels are
installed in the two fields. No premise other than the argument types.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open Proofs.Verify

theorem dspec_bind_of_spec {α β : Type} {m : RustM α} {k : α → RustM β} {P : α → Prop} {Q : β → Prop}
    (hm : m ⦃ P ⦄) (hk : ∀ x, P x → k x ⦃ Q ⦄div) : Std.bind m k ⦃ Q ⦄div :=
  WP.dspec_bind' (WP.spec_dspec _ _ _ hm) hk

/-- The converse of `verify_some`: if both samplers succeed (at their own fuels) on the seeds the spec uses,
then `Verify_internal` is `some` of the verdict computed from their outputs. -/
theorem verify_of_samplers (sp : Spec.Params) (F1 F2 : Nat) (pk M' σ : List UInt8)
    (hpk : pk.length = sp.pkLen) (hσ : σ.length = sp.sigLen)
    (c' : List UInt8) (z : Vector RPoly sp.ℓ) (h : Vector HintPoly sp.k)
    (hsd : Spec.sigDecode sp σ = some (c', z, h))
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (c : RPoly)
    (hA : Spec.ExpandA sp F1 (Spec.pkDecode sp pk).1 = some A)
    (hC : Spec.SampleInBall sp F2 c' = some c) :
    Spec.Verify_internal sp pk M' σ { rejNTT := F1, sampleInBall := F2 } =
      some (decide (‖z‖∞ < sp.γ₁ - sp.β) &&
        c' == cTildePrime sp pk M' (UseHintVec sp h (wApprox sp A z (Spec.pkDecode sp pk).2 c))) := by
  have hiff := (verify_isSome_iff sp { rejNTT := F1, sampleInBall := F2 } pk M' σ hpk hσ).2 (by
    intro c'' z'' h'' hsd''
    rw [hsd] at hsd''
    simp only [Option.some.injEq, Prod.mk.injEq] at hsd''
    obtain ⟨rfl, rfl, rfl⟩ := hsd''
    simp [hA, hC])
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hiff
  obtain ⟨A', c0, hA', hC', hb'⟩ := verify_some sp _ pk M' σ b hpk hσ c' z h hsd hb
  simp only [hA, Option.some.injEq] at hA'
  simp only [hC, Option.some.injEq] at hC'
  subst hA' hC'
  rw [hb, hb']

/-- **The key half, partial.** `prepare_vk` never fails; if it returns, `vk` holds Â = ExpandA(ρ) (at some
fuel `F1` of the spec), NTT(t₁ · 2^d) and tr = H(pk, 64). It diverges exactly where ExpandA does. -/
theorem prepare_vk_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk : Slice U8) (hpkLen : pk.val.length = 32 + 320 * sp.k) :
    verify.prepare_vk K L pk ⦃ vk =>
      ∃ (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (F1 : Nat),
        Spec.ExpandA sp F1 (Spec.pkDecode sp (bytes pk)).1 = some A ∧
        ReprMat vk.a_hat A ∧
        ReprVec vk.t1_2d_hat (NTTVec (((Spec.pkDecode sp (bytes pk)).2.map RPoly.toZq).map
          (·.map (· * (2 ^ sp.d : Zq))))) ∧
        bytesA vk.tr = H (bytes pk) 64 ⦄div := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hd := hstd.d_eq
  unfold verify.prepare_vk
  refine dspec_bind_of_spec (pk_decode_spec_range ip sp hv pk hpkLen) ?_
  rintro ⟨rho, t1⟩ ⟨hrho, ht1, ht1rng⟩
  refine WP.dspec_bind' (expand_a_partial sp K L hK hL rho) ?_
  rintro a_hat ⟨A, F1, hA, hahat⟩
  rw [hrho] at hA
  refine dspec_bind_of_spec (hash_pk_spec pk) ?_
  intro tr htr
  refine dspec_bind_of_spec (scale_vec_by_2d_pk_decode sp hd (bytes pk) t1 ht1) ?_
  intro a1 ha1
  refine dspec_bind_of_spec (ntt_vec_spec a1 _ ha1) ?_
  intro t1_2d_hat ht2d
  simp only [WP.dspec_ok]
  exact ⟨A, F1, hA, hahat, ht2d, htr⟩

/-- **Steps 8-13, partial.** For a decoded signature on which the spec's `sigDecode` succeeds, and a key whose
ExpandA the spec completes at `F1` (`Â` as in `vk`): the result is the spec's verdict at fuels
`F1` (ExpandA) and some `F2` (SampleInBall); it diverges exactly where SampleInBall does. -/
theorem verify_decoded_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (vk : verify.PreparedVk K L) (m_prefix m : Slice U8)
    (c_tilde : Array U8 64#usize) (z : Array (Array U32 256#usize) L) (h : Array (Array Bool 256#usize) K)
    (pkb σb : List UInt8) (hpkb : pkb.length = sp.pkLen) (hσb : σb.length = sp.sigLen)
    (A : Vector (Vector Spec.Poly sp.ℓ) sp.k) (F1 : Nat)
    (hA1 : Spec.ExpandA sp F1 (Spec.pkDecode sp pkb).1 = some A) (hA : ReprMat vk.a_hat A)
    (ht : ReprVec vk.t1_2d_hat (NTTVec (((Spec.pkDecode sp pkb).2.map RPoly.toZq).map
      (·.map (· * (2 ^ sp.d : Zq))))))
    (htr : bytesA vk.tr = H pkb 64)
    (c' : List UInt8) (z' : Vector RPoly sp.ℓ) (h' : Vector HintPoly sp.k)
    (hsd : Spec.sigDecode sp σb = some (c', z', h'))
    (hc1 : (bytesA c_tilde).take (sp.lam / 4) = c') (hz : ReprIntVec z z')
    (hzr : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.γ₁ : Int) + 1 ≤ (z'[i]'hi)[j]'hj ∧ (z'[i]'hi)[j]'hj ≤ (sp.γ₁ : Int))
    (hhh : ReprHintVec h h') :
    verify.verify_decoded ip vk m_prefix m c_tilde z h ⦃ r =>
      ∃ F, Spec.Verify_internal sp pkb (bytes m_prefix ++ bytes m) σb F = some r ⦄div := by
  have hv := hp.valid
  have hstd := hp.params
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
  have h64 : sp.lam / 4 ≤ 64 := hstd.lam_le
  unfold verify.verify_decoded
  refine dspec_bind_of_spec (hash_mu_spec vk.tr m_prefix m pkb htr) ?_
  intro mu hmu
  refine dspec_bind_of_spec (c_tilde_prefix_spec c_tilde ip.c_tilde_len (by omega)) ?_
  intro s hs
  have hs' : bytes s = c' := by rw [hs, hcl, hc1]
  refine WP.dspec_bind' (sample_in_ball_partial hv hstd.tau s) ?_
  rintro cp ⟨c, F2, hC, hcp⟩
  rw [hs'] at hC
  have hVb := verify_of_samplers sp F1 F2 pkb (bytes m_prefix ++ bytes m) σb hpkb hσb c' z' h' hsd A c hA1 hC
  dsimp only
  refine WP.dspec_mono' (WP.spec_dspec _ _ _ (verify_core_spec hp vk mu c_tilde cp z h pkb _ A hA ht hmu c' z' h'
    hc1 hz hzr hhh c hcp)) ?_
  intro r hr
  exact ⟨{ rejNTT := F1, sampleInBall := F2 }, by rw [hVb, hr]⟩

theorem verify_internal_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk σ m_prefix m : Slice U8) :
    verify.verify_internal K L ip pk m_prefix m σ ⦃ r =>
      ∃ F, Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F = some r ⦄div := by
  have hpkS := pk_len_spec hp
  have hsgS := sig_len_spec hp
  have hp' := hp
  obtain ⟨hv, hstd⟩ := hp
  have hd := hstd.d_eq
  unfold verify.verify_internal
  dsimp only
  -- Length guard (Rust: `pk.len() != pk_len(p) || sig.len() != sig_len(p)` returns false, as in FIPS 204 Verify)
  refine dspec_bind_of_spec hpkS ?_
  intro gk hgk
  by_cases hpk : pk.length = sp.pkLen
  swap
  · rw [if_pos ((len_bne_iff pk gk).2 (fun e => hpk (by show pk.val.length = _; omega)))]
    have hl : (bytes pk).length ≠ sp.pkLen ∨ (bytes σ).length ≠ sp.sigLen :=
      Or.inl (by rw [bytes_length]; exact hpk)
    simp only [WP.dspec_ok]
    exact ⟨{}, verify_of_length_ne sp {} _ _ _ hl⟩
  rw [if_neg (fun h => ((len_bne_iff pk gk).1 h) (by
    have : pk.val.length = sp.pkLen := hpk
    omega))]
  refine dspec_bind_of_spec hsgS ?_
  intro gs hgs
  by_cases hσ : σ.length = sp.sigLen
  swap
  · rw [if_pos ((len_bne_iff σ gs).2 (fun e => hσ (by show σ.val.length = _; omega)))]
    have hl : (bytes pk).length ≠ sp.pkLen ∨ (bytes σ).length ≠ sp.sigLen :=
      Or.inr (by rw [bytes_length]; exact hσ)
    simp only [WP.dspec_ok]
    exact ⟨{}, verify_of_length_ne sp {} _ _ _ hl⟩
  rw [if_neg (fun h => ((len_bne_iff σ gs).1 h) (by
    have : σ.val.length = sp.sigLen := hσ
    omega))]
  have hpkLen : pk.val.length = 32 + 320 * sp.k := by
    have : pk.val.length = sp.pkLen := hpk
    rw [this, KeyGen.pkLen_eq sp hd]
  refine dspec_bind_of_spec (sig_decode_spec ip sp hv hstd.stdSig σ hσ) ?_
  intro o ho
  rcases o with _ | ⟨c_tilde, z, h⟩
  · rcases hsd : Spec.sigDecode sp (bytes σ) with _ | ⟨c', z', h'⟩
    · simp only [WP.dspec_ok]
      exact ⟨{}, verify_of_sigDecode_none sp {} _ _ _ hsd⟩
    · rw [hsd] at ho
      exact ho.elim
  · rcases hsd : Spec.sigDecode sp (bytes σ) with _ | ⟨c', z', h'⟩
    · rw [hsd] at ho
      exact ho.elim
    · rw [hsd] at ho
      obtain ⟨hc1, hc2, hz, hzr, hhh⟩ := ho
      have hpkb : (bytes pk).length = sp.pkLen := by rw [bytes_length]; exact hpk
      have hσb : (bytes σ).length = sp.sigLen := by rw [bytes_length]; exact hσ
      dsimp only
      refine WP.dspec_bind' (prepare_vk_partial hp' pk hpkLen) ?_
      rintro vk ⟨A, F1, hA1, hvA, hvt, hvtr⟩
      exact verify_decoded_partial hp' vk m_prefix m c_tilde z h (bytes pk) (bytes σ) hpkb hσb A F1 hA1 hvA hvt
        hvtr c' z' h' hsd hc1 hz hzr hhh


end Proofs
