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

theorem verify_internal_partial {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (pk σ m_prefix m : Slice U8) :
    verify.verify_internal K L ip pk m_prefix m σ ⦃ r =>
      ∃ F, Spec.Verify_internal sp (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) F = some r ⦄div := by
  have hpkS := pk_len_spec hp
  have hsgS := sig_len_spec hp
  obtain ⟨hv, hstd⟩ := hp
  have hk8 : sp.k ≤ 8 := hstd.k_le_8
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hd := hstd.d_eq
  have hg := hstd.stdGamma2
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
  refine dspec_bind_of_spec (pk_decode_spec_range ip sp hv pk hpkLen) ?_
  rintro ⟨rho, t1⟩ ⟨hrho, ht1, ht1rng⟩
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
      refine WP.dspec_bind' (expand_a_partial sp K L hK hL rho) ?_
      rintro a_hat ⟨A, F1, hA, hahat⟩
      rw [hrho] at hA
      have hcl : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
      have h64 : sp.lam / 4 ≤ 64 := hstd.lam_le
      have hK8 : K.val ≤ 8 := by omega
      have hw1b : ip.w1_bits.val ≤ 6 := by rw [hv.w1_bits]; exact bitlen_m_le sp hg
      have hβ : ip.beta.val ≤ ip.gamma1.val := by
        rw [hv.beta, hv.gamma1]
        have : sp.β ≤ 256 := by
          have := hstd.tau_le
          rcases hstd.eta with e | e <;> simp only [Spec.Params.β, e] <;> omega
        rcases hstd.gamma1 with e | e <;> rw [e] <;> omega
      step*
      obtain ⟨s, to_slice_mut_back0⟩ := s
      rename' to_slice_mut_back => s_post1
      try dsimp only
      step*
      rename' s1 => s1_sq
      split_pair
      rename_i hx1 s1
      try dsimp only
      rename' __post2 => hs1raw_h
      step*
      obtain ⟨s3, to_slice_mut_back1⟩ := s3
      rename' to_slice_mut_back1 => s3_post1
      try dsimp only
      step*
      rename' s4 => s4_sq
      split_pair
      rename_i hx4 s4
      try dsimp only
      step*
      dsimp only at s_post1 s_post2 s1_sq hs1raw_h s3_post1 s3_post2 s4_sq __post2
      have hs1len : s.val.length = 64 := by rw [s_post1]; simp
      have hs1raw : bytes s1 = List.drop 0 (Keccak.sponge 136 ([] ++ bytes pk) (0 + s.val.length)) := by
        assumption
      have hs1b : bytes s1 = H (bytes pk) 64 := by
        rw [hs1raw, List.drop_zero, Nat.zero_add, hs1len, List.nil_append]; rfl
      have hs1l : s1.val.length = 64 := by
        have h := congrArg List.length hs1b
        simp only [bytes, List.length_map] at h
        rw [h]; exact SHAKE256_length _ _
      have hs2b : bytes s2 = H (bytes pk) 64 := by
        rw [s2_post, bytes_to_slice, s_post2, bytesA_from_slice _ _ hs1l, hs1b]
      have hs3len : s3.val.length = 64 := by rw [s3_post1]; simp
      have hmu : bytes s4 = H (H (bytes pk) 64 ++ (bytes m_prefix ++ bytes m)) 64 := by
        have e : ([] ++ H (bytes pk) 64 ++ bytes m_prefix ++ bytes m : List UInt8) =
            H (bytes pk) 64 ++ (bytes m_prefix ++ bytes m) := by simp
        rw [__post2, List.drop_zero, Nat.zero_add, hs3len, hs2b, e]; rfl
      have hs4l : s4.val.length = 64 := by
        have h := congrArg List.length hmu
        simp only [bytes, List.length_map] at h
        rw [h]; exact SHAKE256_length _ _
      have hs5 : bytes s5 = c' := by
        rw [← hc1]
        simp [bytes, bytesA, s5_post1, List.slice, Array.to_slice, hcl, List.map_take]
      refine WP.dspec_bind' (sample_in_ball_partial hv hstd.tau s5) ?_
      rintro cp ⟨c, F2, hC, hcp⟩
      rw [hs5] at hC
      have hVb := verify_of_samplers sp F1 F2 (bytes pk) (bytes m_prefix ++ bytes m) (bytes σ) hpkb hσb c' z' h' hsd
        A c hA hC
      refine dspec_bind_of_spec (ntt_vec_spec z _ hz.repr) ?_
      intro az0 haz0
      refine dspec_bind_of_spec (matrix_vector_ntt_spec a_hat A hahat az0 _ haz0) ?_
      intro az_hat haz
      refine dspec_bind_of_spec (ntt_spec cp hcp.canon) ?_
      rintro c_hat ⟨hch1, hch2⟩
      have hchat : Repr c_hat (NTT c.toZq) := ⟨hch1, by rw [hch2, hcp.2]⟩
      refine dspec_bind_of_spec (scale_vec_by_2d_pk_decode sp hd (bytes pk) t1 ht1) ?_
      intro a1 ha1
      refine dspec_bind_of_spec (ntt_vec_spec a1 _ ha1) ?_
      intro t1_2d_hat ht2d
      refine dspec_bind_of_spec (verify_loop_spec hv hg h h' hhh az_hat _ haz c_hat _ hchat t1_2d_hat _ ht2d
        (Array.repeat K (Array.repeat 256#usize 0#u32)) (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize
        (by simp) (Rows.zero _ _) (Rows.zero _ _)) ?_
      intro w11 hw11
      rw [hK] at hw11
      have hw11' : Rows w11 (W1Row sp (UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c))) sp.k :=
        hw11
      have hw11r : ReprIntVec w11 (UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c)) :=
        Rows.reprIntVec (Rows.mono hw11' fun r x hx => hx.1) hK
      have hrng : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256),
          0 ≤ ((UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c))[i]'hi)[j]'hj ∧
          ((UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c))[i]'hi)[j]'hj ≤
            (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int) := by
        intro i hi j hj
        obtain ⟨x, -, -, hr⟩ := hw11' i hi
        have := hr j hj
        rw [vget! _ i hi] at this
        have hpos : 0 < sp.m := hg.m_pos
        have hm' : (Spec.q - 1) / (2 * sp.γ₂) = sp.m := rfl
        rw [hm']
        omega
      step*
      obtain ⟨s6, to_slice_mut_back2⟩ := s6
      rename' to_slice_mut_back2 => s6_post1
      try dsimp only at s6_post1 s6_post2
      try dsimp only
      have hs6len : s6.val.length = 1536 := by rw [s6_post1]; simp
      have hbitsle : bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ 6 := bitlen_m_le sp hg
      have hL1 : 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ s6.val.length := by
        rw [hs6len]
        calc 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ 32 * 8 * 6 :=
              Nat.mul_le_mul (Nat.mul_le_mul_left _ hk8) hbitsle
          _ ≤ 1536 := by norm_num
      refine dspec_bind_of_spec (w1_encode_spec_long ip sp hv w11 _ hw11r hrng s6 hL1) ?_
      intro s7 hs7
      obtain ⟨hs7a, hs7len⟩ := hs7
      step*
      case h_fail =>
        have h1 : i4.val ≤ 256 := by scalar_tac
        have h2 : i4.val * ip.w1_bits.val ≤ 256 * 6 := Nat.mul_le_mul h1 hw1b
        scalar_tac
      case h =>
        show i5.val ≤ (to_slice_mut_back2 s7).to_slice.length
        have h1 : i4.val ≤ 256 := by scalar_tac
        have h2 : i5.val = i4.val * ip.w1_bits.val := i5_post
        have h3 : i4.val * ip.w1_bits.val ≤ 256 * 6 := Nat.mul_le_mul h1 hw1b
        have h4 : (to_slice_mut_back2 s7).to_slice.length = 1536 := by simp [Array.to_slice, Slice.length]
        omega
      obtain ⟨s10, index_mut_back⟩ := s10
      rename' index_mut_back => s10_post1
      try dsimp only at s10_post1 s10_post2 s10_post3
      try dsimp only
      step*
      rename' s11 => s11_sq
      split_pair
      rename_i hx11 s11
      try dsimp only at s11_sq __post2
      try dsimp only
      step*
      have hs8b : bytes s8 = H (H (bytes pk) 64 ++ (bytes m_prefix ++ bytes m)) 64 := by
        rw [s8_post, bytes_to_slice, s3_post2, bytesA_from_slice _ _ hs4l, hmu]
      have hwb : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hv.w1_bits
      have hi1v : i5.val = 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by
        rw [i5_post, i4_post, hK, hwb]; ring
      have he7 : bytesA (to_slice_mut_back2 s7) = bytes s7 := by
        rw [s6_post2, bytesA_from_slice _ _ (by simp [hs7len, hs6len])]
      have hs9b : bytes s9 = (bytes s7).take i5.val := by
        rw [← he7]
        simp [bytes, bytesA, s9_post1, List.slice, Array.to_slice, List.map_take]
      have hs9 : bytes s9 = w1Encode sp (UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c)) := by
        rw [hs9b, hi1v, hs7a]
      have hs10len : s10.val.length = sp.lam / 4 := by
        have h := s10_post2
        simp only [Slice.length] at h
        rw [h, hcl]
      have hs11b : bytes s11 = cTildePrime sp (bytes pk) (bytes m_prefix ++ bytes m)
          (UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c)) := by
        rw [__post2, List.drop_zero, Nat.zero_add, hs10len, hs8b, hs9]
        unfold cTildePrime
        rw [List.append_assoc, List.nil_append]
        rfl
      have hs11len : s11.val.length = sp.lam / 4 := by
        have h := congrArg List.length hs11b
        simp only [bytes, List.length_map, cTildePrime] at h
        rw [h]; exact SHAKE256_length _ _
      have hctp : (bytesA (index_mut_back s11)).take (sp.lam / 4) = bytes s11 := by
        have hn : s11.val.length ≤ (Array.repeat 64#usize 0#u8).val.length := by
          simp [hs11len]; omega
        have e := setSlice_zero (Array.repeat 64#usize 0#u8).val s11.val hn
        have hmap : bytesA (index_mut_back s11) =
            ((s11.val ++ (Array.repeat 64#usize 0#u8).val.drop s11.val.length).map
              fun x => UInt8.ofNat x.val) := by
          simp only [bytesA, s10_post3, e]
        rw [hmap, List.map_append, List.take_left' (by simp [hs11len])]
        rfl
      have hnorm : ‖z'‖∞ ≤ 4190208 := by
        rw [infNorm_le_iff]
        intro i hi
        rw [infNorm_le_iff]
        intro j hj
        have := hzr i hi j hj
        rw [infNorm_int]
        rcases hstd.gamma1 with e | e <;> rw [e] at this <;> norm_num at this <;> omega
      step with vec_infinity_norm_spec z z' hz hnorm as ⟨i2, hi2⟩
      step as ⟨i3, hi3⟩
      step with prefix_eq_spec c_tilde (index_mut_back s11) ip.c_tilde_len (by omega) as ⟨hok, hhok⟩
      have hi3' : i3.val = sp.γ₁ - sp.β := by rw [hi3, hv.gamma1, hv.beta]
      have hhok' : hok = decide (c' = cTildePrime sp (bytes pk) (bytes m_prefix ++ bytes m)
          (UseHintVec sp h' (wApprox sp A z' (pkDecode sp (bytes pk)).2 c))) := by
        rw [hhok, hcl, hc1, hctp, hs11b]
      by_cases hlt : i2 < i3
      · have hlt' : ‖z'‖∞ < sp.γ₁ - sp.β := by
          have : i2.val < i3.val := by scalar_tac
          rw [hi2, hi3'] at this
          exact this
        rw [if_pos hlt]
        simp only [WP.dspec_ok]
        refine ⟨{ rejNTT := F1, sampleInBall := F2 }, ?_⟩
        rw [hVb]
        congr 1
        symm
        rw [hhok']
        simp [hlt']
        rw [Bool.eq_iff_iff]
        simp
      · have hlt' : ¬ ‖z'‖∞ < sp.γ₁ - sp.β := by
          intro h
          apply hlt
          have : i2.val < i3.val := by rw [hi2, hi3']; exact h
          scalar_tac
        rw [if_neg hlt]
        simp only [WP.dspec_ok]
        refine ⟨{ rejNTT := F1, sampleInBall := F2 }, ?_⟩
        rw [hVb]
        congr 1
        simp [hlt']


end Proofs
