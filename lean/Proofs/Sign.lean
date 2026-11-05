import Spec.MLDSA
import Proofs.StdParams
import Proofs.EncodeKeys
import Proofs.SampleA
import Proofs.SampleBall
import Proofs.ExpandMask
import Proofs.NTTOps
import Proofs.Steps
import Proofs.Bridge
import Proofs.Keccak

/-!
# Sign_internal (Algorithm 7)

The spec side of the proof (this file, part 1): `Spec.Sign_internal_bounded` unfolded into the data of steps 1-7
(`Pre`, `pre`), one iteration of the loop (`attemptAt`) and the loop itself (`loopRes`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

namespace Sign

/-! ## Part 1: the specification, unfolded -/

/-- The values that Algorithm 7 computes before the loop (steps 1-7); `pre` is `none` if `ExpandA` runs out of
fuel (step 5). -/
structure Pre (sp : Spec.Params) where
  s₁ : Vector RPoly sp.ℓ
  s₂ : Vector RPoly sp.k
  t₀ : Vector RPoly sp.k
  Â : Vector (Vector Poly sp.ℓ) sp.k
  μ : List UInt8
  ρ'' : List UInt8

namespace Pre
variable {sp : Spec.Params}
/-- `ŝ₁` (step 2). -/
def ŝ₁ (P : Pre sp) : Vector Poly sp.ℓ := NTTVec (P.s₁.map RPoly.toZq)
/-- `ŝ₂` (step 3). -/
def ŝ₂ (P : Pre sp) : Vector Poly sp.k := NTTVec (P.s₂.map RPoly.toZq)
/-- `t̂₀` (step 4). -/
def t₀hat (P : Pre sp) : Vector Poly sp.k := NTTVec (P.t₀.map RPoly.toZq)
end Pre

/-- Steps 1-7 of Algorithm 7. -/
def pre (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8) : Option (Pre sp) :=
  match Spec.skDecode sp sk with
  | (ρ, K, tr, s₁, s₂, t₀) =>
    match Spec.ExpandA sp F.rejNTT ρ with
    | some Â => some ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩
    | none => none

/-- The accepted pair `(z, h)` of an attempt, or `none` if the attempt was rejected. -/
abbrev Out (sp : Spec.Params) : Type := Option (Vector Poly sp.ℓ × Vector HintPoly sp.k)

/-- Steps 17-30 once the challenge `c` is known: the response `z`, the hint `h`, and the two rejection tests. -/
def respond (sp : Spec.Params) (P : Pre sp) (y : Vector Poly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly) : Out sp :=
  let ĉ := NTT c.toZq
  let cs₁ := NTTInvVec (ScalarVectorNTT ĉ P.ŝ₁)
  let cs₂ := NTTInvVec (ScalarVectorNTT ĉ P.ŝ₂)
  let z := y + cs₁
  let r₀ := LowBitsVec sp (w - cs₂)
  if ‖z‖∞ ≥ sp.γ₁ - sp.β ∨ ‖r₀‖∞ ≥ sp.γ₂ - sp.β then none
  else
    let ct₀ := NTTInvVec (ScalarVectorNTT ĉ P.t₀hat)
    let h := MakeHintVec sp (-ct₀) (w - cs₂ + ct₀)
    if ‖ct₀‖∞ ≥ sp.γ₂ ∨ HintWeight h > sp.ω then none else some (z, h)

theorem respond_eq (sp : Spec.Params) (P : Pre sp) (y : Vector Poly sp.ℓ) (w : Vector Poly sp.k) (c : RPoly) :
    respond sp P y w c =
      if sp.γ₁ - sp.β ≤ ‖y + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₁)‖∞ ∨
          sp.γ₂ - sp.β ≤ ‖LowBitsVec sp (w - NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂))‖∞ then none
      else if sp.γ₂ ≤ ‖NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat)‖∞ ∨
          sp.ω < HintWeight (MakeHintVec sp (-NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat))
            (w - NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂) + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat)))
        then none
      else some (y + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₁),
        MakeHintVec sp (-NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat))
          (w - NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.ŝ₂) + NTTInvVec (ScalarVectorNTT (NTT c.toZq) P.t₀hat))) :=
  rfl

/-- The mask `y` of attempt `κ` (step 11). -/
def maskAt (sp : Spec.Params) (P : Pre sp) (κ : Nat) : Vector Poly sp.ℓ :=
  (ExpandMask sp P.ρ'' κ).map RPoly.toZq

/-- The commitment `w` of attempt `κ` (step 12). -/
def commitAt (sp : Spec.Params) (P : Pre sp) (κ : Nat) : Vector Poly sp.k :=
  NTTInvVec (MatrixVectorNTT P.Â (NTTVec (maskAt sp P κ)))

/-- The commitment hash `ct` of attempt `κ` (steps 13, 15). -/
def ctildeAt (sp : Spec.Params) (P : Pre sp) (κ : Nat) : List UInt8 :=
  H (P.μ ++ w1Encode sp (HighBitsVec sp (commitAt sp P κ))) (sp.lam / 4)

/-- One iteration of the loop body (steps 11-30) with counter `κ`. `none`: `SampleInBall` ran out of fuel.
`some (ct, none)`: the attempt is rejected. `some (ct, some (z, h))`: it is accepted. -/
def attemptAt (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (κ : Nat) : Option (List UInt8 × Out sp) :=
  match Spec.SampleInBall sp F.sampleInBall (ctildeAt sp P κ) with
  | some c => some (ctildeAt sp P κ, respond sp P (maskAt sp P κ) (commitAt sp P κ) c)
  | none => none

/-- The loop with `n` attempts left and counter `κ`. `some none`: no attempt was accepted (budget exhausted, or
the next attempt would need `κ + ℓ > 2^16`); `none`: a `SampleInBall` ran out of fuel first. -/
def loopRes (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) :
    Nat → Nat → Option (Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k))
  | 0, _ => some none
  | n + 1, κ =>
    if 2 ^ 16 < κ + sp.ℓ then some none
    else match attemptAt sp F P κ with
      | none => none
      | some (_, none) => loopRes sp F P n (κ + sp.ℓ)
      | some (ct, some (z, h)) => some (some (ct, z, h))

/-- Step 33: the signature of an accepted attempt. -/
def encodeRes (sp : Spec.Params) :
    Option (Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k)) → Option (List UInt8)
  | some (some (ct, z, h)) => some (sigEncode sp ct (z.map Poly.modPM) h)
  | _ => none

/-! ### The `for` loop as an iteration -/

/-- `n` rounds of a step function; a `done` ends the iteration. -/
def iterG {σ : Type} (g : σ → Id (ForInStep σ)) : Nat → σ → σ
  | 0, s => s
  | n + 1, s => match Id.run (g s) with
    | .done b => b
    | .yield b => iterG g n b

theorem forIn_list_const {σ : Type} (g : σ → Id (ForInStep σ)) (l : List Nat) (init : σ) :
    (forIn l init (fun _ r => g r) : Id σ) = iterG g l.length init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    simp only [List.forIn_cons, List.length_cons, iterG]
    show (match g init with
      | .done b => b
      | .yield b => (forIn l b (fun _ r => g r) : Id σ)) = _
    generalize g init = x
    cases x with
    | done b => rfl
    | yield b => exact ih b

theorem forIn_range_const {σ : Type} (g : σ → Id (ForInStep σ)) (B : Nat) (init : σ) :
    (forIn [0:B] init (fun _ r => g r) : Id σ) = iterG g B init := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_list_const]
  simp [Std.Legacy.Range.size]

/-- The state of the `for` loop of Algorithm 7 (as `do` notation packs it). -/
abbrev St (sp : Spec.Params) : Type :=
  MProd (Option (Option (List UInt8))) (MProd (List UInt8) (MProd (Out sp) Nat))

/-- What follows the loop in Algorithm 7 (the `return`, step 33). -/
def postSt (sp : Spec.Params) (r : St sp) : Option (List UInt8) :=
  match r.fst with
  | some a => a
  | none =>
    match r.snd.snd.fst with
    | some (z, h) => some (sigEncode sp r.snd.fst (z.map Poly.modPM) h)
    | none => none

theorem iterG_accepted (sp : Spec.Params) (_F : Spec.Fuel) (_P : Pre sp) (g : St sp → Id (ForInStep (St sp)))
    (hg2 : ∀ c x κ, Id.run (g ⟨none, c, some x, κ⟩) = .done ⟨none, c, some x, κ⟩) (c : List UInt8)
    (x : Vector Poly sp.ℓ × Vector HintPoly sp.k) (κ : Nat) :
    ∀ n, iterG g n ⟨none, c, some x, κ⟩ = ⟨none, c, some x, κ⟩ := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simp only [iterG, hg2]

theorem iterG_post (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (g : St sp → Id (ForInStep (St sp)))
    (hg1 : ∀ c κ, Id.run (g ⟨none, c, none, κ⟩) =
      if 2 ^ 16 < κ + sp.ℓ then .done ⟨some none, c, none, κ⟩
      else match attemptAt sp F P κ with
        | none => .done ⟨some none, ctildeAt sp P κ, none, κ⟩
        | some (ct, zh) => .yield ⟨none, ct, zh, κ + sp.ℓ⟩)
    (hg2 : ∀ c x κ, Id.run (g ⟨none, c, some x, κ⟩) = .done ⟨none, c, some x, κ⟩) :
    ∀ n κ c, postSt sp (iterG g n ⟨none, c, none, κ⟩) = encodeRes sp (loopRes sp F P n κ) := by
  intro n
  induction n with
  | zero => intro κ c; rfl
  | succ n ih =>
    intro κ c
    simp only [iterG, hg1, loopRes]
    by_cases hκ : 2 ^ 16 < κ + sp.ℓ
    · simp only [hκ, if_true]
      simp [postSt, encodeRes]
    · simp only [hκ, if_false]
      rcases hat : attemptAt sp F P κ with _ | ⟨ct, _ | ⟨z, h⟩⟩
      · simp [postSt, encodeRes]
      · simp only []
        exact ih _ _
      · simp only []
        rw [iterG_accepted sp F P g hg2]
        simp [postSt, encodeRes]

theorem iterG_post' (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (g : St sp → Id (ForInStep (St sp)))
    (hg1 : ∀ c κ, Id.run (g ⟨none, c, none, κ⟩) =
      if 2 ^ 16 < κ + sp.ℓ then .done ⟨some none, c, none, κ⟩
      else match attemptAt sp F P κ with
        | none => .done ⟨some none, ctildeAt sp P κ, none, κ⟩
        | some (ct, zh) => .yield ⟨none, ct, zh, κ + sp.ℓ⟩)
    (hg2 : ∀ c x κ, Id.run (g ⟨none, c, some x, κ⟩) = .done ⟨none, c, some x, κ⟩) (B : Nat) (I : St sp)
    (hI : iterG g B ⟨none, [], none, 0⟩ = I) :
    postSt sp I = encodeRes sp (loopRes sp F P B 0) := by
  subst hI
  exact iterG_post sp F P g hg1 hg2 B 0 []

theorem Sign_internal_bounded_eq (sp : Spec.Params) (B : Nat) (sk M' rnd : List UInt8) (F : Spec.Fuel) :
    Spec.Sign_internal_bounded sp B sk M' rnd F =
      match pre sp F sk M' rnd with
      | none => none
      | some P => encodeRes sp (loopRes sp F P B 0) := by
  unfold Spec.Sign_internal_bounded pre
  generalize Spec.skDecode sp sk = d
  obtain ⟨ρ, K, tr, s₁, s₂, t₀⟩ := d
  rcases hA : Spec.ExpandA sp F.rejNTT ρ with _ | Â
  · simp [hA]
  · simp only [hA]
    rw [forIn_range_const]
    generalize hI : iterG _ B (⟨none, [], none, 0⟩ : St sp) = I
    have key := iterG_post' sp F ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩ _
      (by
        intro c κ
        by_cases hκ : 2 ^ 16 < κ + sp.ℓ
        · simp only [hκ, if_true]
          simp
        · simp only [Option.isSome_none, Bool.false_eq_true, hκ, ↓reduceIte]
          dsimp only [attemptAt, ctildeAt, commitAt, maskAt, respond, Pre.ŝ₁, Pre.ŝ₂, Pre.t₀hat, Id.run]
          generalize SampleInBall sp F.sampleInBall _ = S
          cases S with
          | none => rfl
          | some c =>
            dsimp only
            split_ifs <;> rfl)
      (by intro c x κ; simp) B I hI
    rw [← key]
    rcases I with ⟨a, c, zh, κ⟩
    rcases a with _ | a <;> rcases zh with _ | ⟨z, h⟩ <;> rfl

/-! ## Part 2: the leaf specs for the buffers `sign_internal` passes

`attempt` hands `w1_encode` the whole 1536-byte buffer and `sig_encode` the whole 64-byte `c̃` buffer; the leaf specs
of `EncodeKeys` and `SigCodec` assume the exact lengths. These are the same proofs with `≤` in place of `=`. -/

theorem w1_encode_loop_spec' {K : Usize} (c n : Usize) (hn : n.val = 32 * c.val) (b : Nat) (hb : b < Spec.q)
    (hc : c.val = bitlen b) (k : Nat) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256, 0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (b : Int))
    (out0 : Slice U8) (hL : k * n.val ≤ out0.val.length)
    (out : Slice U8) (hlen0 : out.val.length = out0.val.length) (i1 : Usize) (hi1 : i1.val ≤ k)
    (hinv : (bytes out).take (i1.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) i1.val) :
    encode.w1_encode_loop c w1 out n i1 ⦃ out' => out'.val.length = out0.val.length ∧
      (bytes out').take (k * n.val) = flat (fun t => SimpleBitPack v[t]! b) k ⦄ := by
  have hKk := hv.len
  unfold encode.w1_encode_loop
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => k - p.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.val ≤ k ∧
      (bytes p.1).take (p.2.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) p.2.val)
  · rintro ⟨out, i1⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.w1_encode_loop.body]
    split
    · rename_i hi
      have hik : i1.val < k := by scalar_tac
      have hm1 : (i1.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have hm2 : i1.val * n.val ≤ k * n.val := Nat.mul_le_mul_right _ (by omega)
      have hlen := out.property
      step*
      have hFlen : ∀ t : Nat, (SimpleBitPack v[t]! b).length = n.val := fun t => by
        rw [SimpleBitPack_length, ← hc, hn]
      refine WP.spec_bind (bit_pack_spec_repr _ (v[i1.val]'hik) ?_ b hb (hrng _ hik) c hc s ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i4.val - i2.val := s_post2
        have e : (i1.val + 1) * n.val = i1.val * n.val + n.val := by ring
        rw [this, i4_post, i2_post, i3_post, e]; omega
      · intro s1 hs1
        simp only [WP.spec_ok]
        have hs1' : bytes s1 = SimpleBitPack v[i1.val]! b := by rw [hs1, vec_getElem!_eq v _ hik]
        obtain ⟨b1, b2⟩ := block_write_step out s1 index_mut_back i2 i4 0 n.val i1.val [] 
          (fun (t : Nat) => SimpleBitPack v[t]! b) hFlen rfl (by rw [i2_post]; ring)
          (by rw [i4_post, i3_post]; ring) s_post3 hs1' (by simpa using h3) (by rw [Nat.zero_add, h1]; exact le_trans hm1 hL)
        refine ⟨by rw [b1]; exact h1, by omega, ?_, by omega⟩
        show List.take (i3.val * n.val) (bytes (index_mut_back s1)) = flat _ i3.val
        rw [i3_post]
        simpa using b2
    · rename_i hi
      have hi' : i1.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      exact ⟨h1, h3⟩
  · exact ⟨hlen0, hi1, hinv⟩


/-- **`w1_encode` is `w1Encode`** (Algorithm 28): `w1` stores the integer vector `v` with coefficients in
`[0, (q-1)/(2γ₂) - 1]`, and `out` has `32·k·bitlen((q-1)/(2γ₂) - 1)` bytes. -/
theorem w1_encode_spec' {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly sp.k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int))
    (out : Slice U8) (hL : 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ out.val.length) :
    encode.w1_encode ip w1 out ⦃ out' => out'.val.length = out.val.length ∧
      (bytes out').take (32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) = Spec.w1Encode sp v ⦄ := by
  have hc : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hp.w1_bits
  have hb := hp.w1_b_lt
  have h23 := bitlen_lt_q hb
  unfold encode.w1_encode
  step*
  rw [w1Encode_eq]
  have hnk : sp.k * n.val = 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := by
    rw [n_post, hc]; ring
  refine WP.spec_mono (w1_encode_loop_spec' ip.w1_bits n (by rw [n_post]) _ hb hc sp.k w1 v hv hrng out
    (by rw [hnk]; exact hL) out rfl 0#usize (by simp) (by simp [flat_zero])) ?_
  intro out' h
  rw [← hnk]
  exact h



/-- The `c̃` copy loop of `sig_encode`: `out[0..λ/4) ← c̃`. -/
theorem sig_encode_loop0_spec' (ip : Impl.params.Params) (ct : Slice U8)
    (hct : ip.c_tilde_len.val ≤ ct.val.length) (out0 : Slice U8) (hL : ip.c_tilde_len.val ≤ out0.val.length)
    (out : Slice U8) (i : Usize) (hi : i.val ≤ ip.c_tilde_len.val) (hlen : out.val.length = out0.val.length)
    (hinv : ∀ k, (bytes out)[k]? = if k < i.val then (bytes ct)[k]? else (bytes out0)[k]?) :
    encode.sig_encode_loop0 ip ct out i ⦃ out' => out'.val.length = out0.val.length ∧
      ∀ k, (bytes out')[k]? = if k < ip.c_tilde_len.val then (bytes ct)[k]? else (bytes out0)[k]? ⦄ := by
  unfold encode.sig_encode_loop0
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => ip.c_tilde_len.val - p.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.val ≤ ip.c_tilde_len.val ∧
      ∀ k, (bytes p.1)[k]? = if k < p.2.val then (bytes ct)[k]? else (bytes out0)[k]?)
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.sig_encode_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < ip.c_tilde_len.val := by scalar_tac
      step*
      subst s_post2
      have hl3 : i.val < out.val.length := by omega
      refine ⟨by simp [h1], by omega, fun k => ?_, by omega⟩
      rw [bytes_set, List.getElem?_set, h3 k, i2_post]
      by_cases hk : i.val = k
      · subst hk
        have hq : ct.val[i.val]? = some (ct.val[i.val]'(by omega)) := List.getElem?_eq_getElem (by omega)
        simp [hl3, bytes_getElem?_eq, i1_post2, hq]
      · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = ip.c_tilde_len.val := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨h1, fun k => ?_⟩
      rw [h3 k, hi']
  · exact ⟨hlen, hi, hinv⟩


/-- **`sig_encode` is `sigEncode`** (Algorithm 26): `z` stores the integer vector `zv` with coefficients in
`[-γ₁ + 1, γ₁]` (`ReprIntVec`), `h` a hint of weight at most `ω`, `c̃` has `λ/4` bytes and `out` has `sigLen`. -/
theorem sig_encode_spec' {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hs : StdSig sp) (ct : Slice U8) (hct : sp.lam / 4 ≤ ct.length)
    (z : Array (Array U32 256#usize) L) (zv : Vector RPoly sp.ℓ) (hz : ReprIntVec z zv)
    (hzr : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.γ₁ : Int) + 1 ≤ (zv[i]'hi)[j]'hj ∧ (zv[i]'hi)[j]'hj ≤ (sp.γ₁ : Int))
    (h : Array (Array Bool 256#usize) K) (hv : Vector HintPoly sp.k) (hh : ReprHintVec h hv)
    (hw : HintWeight hv ≤ sp.ω) (out : Slice U8) (hout : out.length = sp.sigLen) :
    encode.sig_encode ip ct z h out ⦃ out' =>
      bytes out' = Spec.sigEncode sp ((bytes ct).take (sp.lam / 4)) zv hv ⦄ := by
  obtain ⟨hbl, hlt, hc2, hpow⟩ := hs.bitlen_eq
  have hγ : ip.gamma1.val = sp.γ₁ := hp.gamma1
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hp.c_tilde_len
  have hout' : out.val.length = sp.lam / 4 + sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1))) + (sp.ω + sp.k) := by
    have : out.val.length = sp.sigLen := hout
    rw [this]; unfold Spec.Params.sigLen; ring
  have hγ1 : 1 ≤ sp.γ₁ := by rcases hs.1 with e | e <;> rw [e] <;> decide +kernel
  have hq : Spec.q = 8380417 := rfl
  have hγq : sp.γ₁ - 1 + sp.γ₁ < Spec.q := by rcases hs.1 with e | e <;> rw [e] <;> decide +kernel
  have hb : ip.gamma1.val < Spec.q := by rw [hγ]; omega
  have hab : sp.γ₁ - 1 + ip.gamma1.val < Spec.q := by rw [hγ]; exact hγq
  have hc' : ip.gamma1_bits.val = bitlen (sp.γ₁ - 1 + ip.gamma1.val) := by rw [hp.gamma1_bits, hγ, hbl]
  have hrng : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -((sp.γ₁ - 1 : Nat) : Int) ≤ (zv[i]'hi)[j]'hj ∧ (zv[i]'hi)[j]'hj ≤ (ip.gamma1.val : Int) := by
    intro i hi j hj
    have := hzr i hi j hj
    rw [hγ]; omega
  rw [sigEncode_eq]
  unfold encode.sig_encode
  have hct' : ip.c_tilde_len.val ≤ ct.val.length := by rw [hcl]; exact hct
  refine WP.spec_bind (sig_encode_loop0_spec' ip ct hct' out (by omega) out 0#usize (by simp) rfl
    (by intro k; simp)) ?_
  rintro out1 ⟨hl1, hp1⟩
  have hgb : ip.gamma1_bits.val ≤ 20 := by rw [hp.gamma1_bits]; omega
  step as ⟨n, n_post⟩
  have hnv : n.val = 32 * (1 + bitlen (sp.γ₁ - 1)) := by rw [n_post, hp.gamma1_bits]
  have hLn : L.val * n.val = sp.ℓ * n.val := by rw [hp.L_eq]
  have hlenb := out.property
  have houtn : out.val.length = ip.c_tilde_len.val + sp.ℓ * n.val + (sp.ω + sp.k) := by rw [hout', hnv, hcl]
  have hpre : ((bytes ct).take ip.c_tilde_len.val).length = ip.c_tilde_len.val := by
    simp only [List.length_take, bytes_length]; omega
  have hprefix : (bytes out1).take (ip.c_tilde_len.val + 0 * n.val) = (bytes ct).take ip.c_tilde_len.val ++ flat (fun t =>
      Spec.BitPack zv[t]! (sp.γ₁ - 1) ip.gamma1.val) 0 := by
    rw [flat_zero, List.append_nil, Nat.zero_mul, Nat.add_zero]
    exact take_of_pointwise out1 ((bytes ct).take ip.c_tilde_len.val) _ hpre (by omega) (fun k => (bytes out)[k]?)
      (fun k => by
        rw [hp1 k]
        by_cases hk : k < ip.c_tilde_len.val <;> simp [hk])
  refine WP.spec_bind (sig_encode_loop1_spec ip ip.gamma1 ip.gamma1_bits (sp.γ₁ - 1) hb hab hc' n
    (by rw [hnv, hp.gamma1_bits]) sp.ℓ z zv hz hrng ((bytes ct).take ip.c_tilde_len.val) hpre out1
    (by rw [hl1, houtn]; omega) 0#usize (by simp) hprefix) ?_
  rintro out2 ⟨hl2, ht2⟩
  have hLn' : L.val * n.val ≤ Usize.max := by
    have : out2.val.length = out.val.length := by rw [hl2, hl1]
    have h2 := out2.property
    rw [hLn]; rw [houtn] at this; omega
  step as ⟨i, i_post⟩
  have hcn : ip.c_tilde_len.val + i.val ≤ Usize.max := by
    have : out2.val.length = out.val.length := by rw [hl2, hl1]
    have h2 := out2.property
    rw [i_post, hLn]; rw [houtn] at this; omega
  step as ⟨i1, i1_post⟩
  have hstart : i1.val = ip.c_tilde_len.val + sp.ℓ * n.val := by rw [i1_post, i_post, hLn]
  refine WP.spec_bind (slice_from_mut_spec out2 { start := i1 } (by simp; omega)) ?_
  rintro ⟨s, back⟩ ⟨hs1, hback⟩
  have hsl : s.val.length = out2.val.length - i1.val := by rw [hs1]; simp
  have hslen : s.length = sp.ω + sp.k := by
    show s.val.length = _
    rw [hsl, hl2, hl1, houtn, hstart]; omega
  refine WP.spec_bind (hint_bit_pack_spec ip sp hp h hv hh hw s hslen) ?_
  intro s1 hs1'
  simp only [WP.spec_ok]
  have hl : s1.val.length = out2.val.length - i1.val := by
    have := congrArg List.length hs1'
    simp only [bytes_length] at this
    have h3 : s.val.length = sp.ω + sp.k := hslen
    rw [this, HintBitPack_length]; omega
  have hbk : bytes (back s1) = (bytes out2).take i1.val ++ bytes s1 := by
    have this : (back s1).val = out2.val.take i1.val ++ s1.val := hback s1 hl
    simp only [bytes, this, List.map_append, List.map_take]
  rw [hbk, hstart, ht2, hs1', hγ, hcl]
  rfl

/-! ## `sig_decode` -/

/-- **`sig_encode` as Algorithm 7 step 33 calls it**: `z` is the canonical `Z_q` vector `zq` (`ReprVec`), whose
infinity norm is below `γ₁ - β` (the check of step 23), and the signature is `sigEncode … (z mod± q) …`. -/
theorem sig_encode_signed_spec' {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hs : StdSig sp) (ct : Slice U8) (hct : sp.lam / 4 ≤ ct.length)
    (z : Array (Array U32 256#usize) L) (zq : Vector Poly sp.ℓ) (hz : ReprVec z zq)
    (hnorm : ‖zq‖∞ < sp.γ₁ - sp.β)
    (h : Array (Array Bool 256#usize) K) (hv : Vector HintPoly sp.k) (hh : ReprHintVec h hv)
    (hw : HintWeight hv ≤ sp.ω) (out : Slice U8) (hout : out.length = sp.sigLen) :
    encode.sig_encode ip ct z h out ⦃ out' =>
      bytes out' = Spec.sigEncode sp ((bytes ct).take (sp.lam / 4)) (zq.map Poly.modPM) hv ⦄ := by
  have hz' : ReprIntVec z (zq.map Poly.modPM) := by
    refine ⟨hz.len, fun i hi => ?_⟩
    have := hz.elt i hi
    refine ⟨this.canon, ?_⟩
    rw [this.eq, Vector.getElem_map, toZq_modPM]
  have hn := (infNorm_le_iff zq (sp.γ₁ - sp.β - 1)).1 (by omega)
  refine sig_encode_spec' ip sp hp hs ct hct z (zq.map Poly.modPM) hz' ?_ h hv hh hw out hout
  intro i hi j hj
  have h1 := (infNorm_le_iff zq[i] (sp.γ₁ - sp.β - 1)).1 (hn i hi) j hj
  rw [Vector.getElem_map]
  simp only [Poly.modPM, Vector.getElem_map]
  have h2 : (Zq.modPM (zq[i][j])).natAbs ≤ sp.γ₁ - sp.β - 1 := h1
  omega

/-! ## Part 3: the `attempt` loop and `attempt` -/

theorem Rows.mono {α : Type} {n : Usize} {a : Array α n} {P Q : Nat → α → Prop} {i : Nat}
    (hPQ : ∀ r x, P r x → Q r x) (h : Rows a P i) : Rows a Q i :=
  fun r hr => by
    obtain ⟨x, hx, hp⟩ := h r hr
    exact ⟨x, hx, hPQ r x hp⟩

theorem highBitsVec_getElem! (sp : Spec.Params) {k : Nat} (X : Vector Poly k) (i : Nat) (hi : i < k) :
    (HighBitsVec sp X)[i]! = (X[i]!).map (HighBits sp) := by
  rw [vget! _ i hi, vget! X i hi]
  simp [Spec.HighBitsVec]

/-- Row `r` of `HighBitsVec sp W` is stored in `x`, with coefficients in `[0, m - 1]`. -/
def HBRow (sp : Spec.Params) {k : Nat} (W : Vector Poly k) (r : Nat) (x : Array U32 256#usize) : Prop :=
  ReprInt x (HighBitsVec sp W)[r]! ∧
  ∀ (j : Nat) (hj : j < 256), 0 ≤ ((HighBitsVec sp W)[r]!)[j]'hj ∧
    ((HighBitsVec sp W)[r]!)[j]'hj ≤ (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int)

theorem Rows.hb_repr {K : Usize} {k : Nat} {sp : Spec.Params} {a : Array (Array U32 256#usize) K}
    {W : Vector Poly k} (h : Rows a (fun r x => HBRow sp W r x) k) (hK : K.val = k) :
    ReprIntVec a (HighBitsVec sp W) :=
  Rows.reprIntVec (Rows.mono (fun _ _ hx => hx.1) h) hK

theorem Rows.hb_range {K : Usize} {k : Nat} {sp : Spec.Params} {a : Array (Array U32 256#usize) K}
    {W : Vector Poly k} (h : Rows a (fun r x => HBRow sp W r x) k) :
    ∀ (i : Nat) (hi : i < k) (j : Nat) (hj : j < 256),
      0 ≤ ((HighBitsVec sp W)[i]'hi)[j]'hj ∧
        ((HighBitsVec sp W)[i]'hi)[j]'hj ≤ (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int) := by
  intro i hi j hj
  obtain ⟨x, _, _, hr⟩ := h i hi
  have := hr j hj
  rwa [vget! _ i hi] at this

theorem attempt_loop_spec {K L : Usize} {k : Nat} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hg : StdGamma2 sp)
    (w_hat : Array (Array U32 256#usize) K) (Wh : Vector Poly k) (hwh : ReprVec w_hat Wh)
    (w w1 : Array (Array U32 256#usize) K) (i : Usize) (hi : i.val ≤ K.val)
    (h1 : Rows w (fun r x => Repr x (NTTInvVec Wh)[r]!) i.val)
    (h2 : Rows w1 (fun r x => HBRow sp (NTTInvVec Wh) r x) i.val) :
    sign.attempt_loop ip w_hat w w1 i ⦃ o =>
      Rows o.1 (fun r x => Repr x (NTTInvVec Wh)[r]!) K.val ∧
      Rows o.2 (fun r x => HBRow sp (NTTInvVec Wh) r x) K.val ⦄ := by
  have hN : K.val = k := hwh.len
  unfold sign.attempt_loop
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Array (Array U32 256#usize) K × Usize) => K.val - p.2.2.val)
    (fun p => p.2.2.val ≤ K.val ∧ Rows p.1 (fun r x => Repr x (NTTInvVec Wh)[r]!) p.2.2.val ∧
      Rows p.2.1 (fun r x => HBRow sp (NTTInvVec Wh) r x) p.2.2.val)
  · rintro ⟨w, w1, i⟩ ⟨hi1, h2', h3⟩
    dsimp only at hi1 h2' h3
    simp only [sign.attempt_loop.body]
    split
    · rename_i hi
      have hi' : i.val < K.val := hi
      have hik : i.val < k := by omega
      have hl : i.val < w.val.length := by rw [w.property]; exact hi'
      have hl1 : i.val < w1.val.length := by rw [w1.property]; exact hi'
      step with hwh.index_spec i hik as ⟨a, ha⟩
      step with ntt_inverse_spec a ha.canon as ⟨a1, ha1c, ha1⟩
      step as ⟨w2, hw2⟩
      step with arr_index_spec w2 i (by rw [hw2, Array.set_val_eq, List.length_set]; exact hl) as ⟨a2, ha2⟩
      have ha2e : a2 = a1 := by
        rw [ha2]; subst hw2; simp [Array.set_val_eq]
      have hr1 : Repr a1 (NTTInvVec Wh)[i.val]! := by
        refine ⟨ha1c, ?_⟩
        rw [ha1, ha.eq, nttInvVec_getElem! _ _ hik, vget! Wh _ hik]
      step with poly_high_bits_spec hp hg a2 (NTTInv Wh[i.val]) (by
        rw [ha2e]
        refine ⟨ha1c, ?_⟩
        rw [ha1, ha.eq]) as ⟨a3, ha3, ha3'⟩
      step*
      have e : i1.val = i.val + 1 := i1_post
      refine ⟨by omega, ?_, ?_, by omega⟩
      · rw [hw2, e]
        exact h2'.set i rfl hl a1 hr1
      · rw [a4_post, e]
        refine h3.set i rfl hl1 a3 ?_
        have hv : (HighBitsVec sp (NTTInvVec Wh))[i.val]! = (NTTInv Wh[i.val]).map (HighBits sp) := by
          rw [highBitsVec_getElem! sp _ _ hik, nttInvVec_getElem! _ _ hik, vget! Wh _ hik]
        unfold HBRow
        rw [hv]
        refine ⟨ha3, fun j hj => ?_⟩
        have := ha3' j hj
        rw [Vector.getElem_map]
        have hm : sp.m = (Spec.q - 1) / (2 * sp.γ₂) := rfl
        omega
    · rename_i hi
      have hi' : i.val = K.val := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h2' h3
      exact ⟨h2', h3⟩
  · exact ⟨hi, h1, h2⟩

/-! ## Part 4: one attempt -/

/-- Two parameter facts that `Params.Std` does not give but `sign_internal` needs: `ℓ ≥ 1` (the loop test
computes `κ + ℓ - 1` in `u32`) and that `w1Encode` fits the 1536-byte buffer of `attempt`
(`32·k·bitlen(m - 1) ≤ 1536`; with `m ∈ {16, 44}` this is `k ≤ 8`). Both hold for ML-DSA-44/65/87. -/
structure SignBuf (sp : Spec.Params) : Prop where
  ell_pos : 1 ≤ sp.ℓ
  w1_fits : 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) ≤ 1536

theorem signBuf_44 : SignBuf Spec.ML_DSA_44 := ⟨by decide +kernel, by decide +kernel⟩
theorem signBuf_65 : SignBuf Spec.ML_DSA_65 := ⟨by decide +kernel, by decide +kernel⟩
theorem signBuf_87 : SignBuf Spec.ML_DSA_87 := ⟨by decide +kernel, by decide +kernel⟩

/-- `SignBuf` follows from `StdParams`: γ₂ fixes the `w1` width at 6 or 4 bits, and `k ≤ 8`. -/
theorem _root_.Proofs.StdParams.signBuf {sp : Spec.Params} (h : StdParams sp) : SignBuf sp := by
  refine ⟨h.ell_pos, ?_⟩
  have hk := h.k_le_8
  rcases h.gamma2 with hg | hg <;> rw [hg]
  · have e : bitlen ((Spec.q - 1) / (2 * 95232) - 1) = 6 := by decide +kernel
    rw [e]; omega
  · have e : bitlen ((Spec.q - 1) / (2 * 261888) - 1) = 4 := by decide +kernel
    rw [e]; omega

theorem beta_lt_of_std {sp : Spec.Params} (h : StdParams sp) : sp.β < sp.γ₁ ∧ sp.β < sp.γ₂ := by
  have h1 := h.tau_le
  have h2 : sp.η ≤ 4 := by rcases h.eta with e | e <;> omega
  have h3 : sp.β ≤ 256 := by
    unfold Spec.Params.β
    calc sp.τ * sp.η ≤ 64 * 4 := Nat.mul_le_mul h1 h2
      _ = 256 := by norm_num
  rcases h.gamma1 with e | e <;> rcases h.gamma2 with e' | e' <;> rw [e, e'] <;> constructor <;> omega

/-- What `attempt` returns for the spec outcome `zh`: `none` if rejected, else a 64-byte `c̃` buffer (whose first
`λ/4` bytes are `c̃`), `z` and `h`. -/
def AttPost {K L : Usize} (sp : Spec.Params) (ct : List UInt8) (zh : Out sp)
    (o : Option (Array U8 64#usize × Array (Array U32 256#usize) L × Array (Array Bool 256#usize) K)) : Prop :=
  match zh with
  | none => o = none
  | some (z, h) => ∃ ctb zr hr, o = some (ctb, zr, hr) ∧ (bytesA ctb).take (sp.lam / 4) = ct ∧
      ReprVec zr z ∧ ReprHintVec hr h ∧ ‖z‖∞ < sp.γ₁ - sp.β ∧ HintWeight h ≤ sp.ω

theorem attempt_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (hb : SignBuf sp) (F : Spec.Fuel) (P : Pre sp)
    (a_hat : Array (Array (Array U32 256#usize) L) K) (hA : ReprMat a_hat P.Â)
    (s1_hat : Array (Array U32 256#usize) L) (hs1 : ReprVec s1_hat P.ŝ₁)
    (s2_hat : Array (Array U32 256#usize) K) (hs2 : ReprVec s2_hat P.ŝ₂)
    (t0_hat : Array (Array U32 256#usize) K) (ht0 : ReprVec t0_hat P.t₀hat)
    (mu : Array U8 64#usize) (hmu : bytesA mu = P.μ)
    (rho_pp : Array U8 64#usize) (hrho : bytesA rho_pp = P.ρ'')
    (kappa : U16) (hκ : kappa.val + sp.ℓ ≤ 2 ^ 16)
    (ct : List UInt8) (zh : Out sp) (hs : attemptAt sp F P kappa.val = some (ct, zh)) :
    sign.attempt ip a_hat s1_hat s2_hat t0_hat mu rho_pp kappa ⦃ o => AttPost sp ct zh o ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  have hg : StdGamma2 sp := hstd.stdGamma2
  obtain ⟨hβ1, hβ2⟩ := beta_lt_of_std hstd
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hv.c_tilde_len
  have hlam := hstd.lam_le
  unfold attemptAt at hs
  rcases hS : Spec.SampleInBall sp F.sampleInBall (ctildeAt sp P kappa.val) with _ | c
  · simp [hS] at hs
  simp only [hS, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨hct, hzh⟩ := hs
  unfold sign.attempt
  step with expand_mask_spec hv hstd.gamma₁ rho_pp kappa hκ as ⟨y, hy⟩
  rw [hrho] at hy
  have hY : ReprVec y (maskAt sp P kappa.val) := hy.repr
  step with ntt_vec_spec y _ hY as ⟨a, ha⟩
  step with matrix_vector_ntt_spec a_hat P.Â hA a _ ha as ⟨w_hat, hwhat⟩
  step with attempt_loop_spec ip sp hv hg w_hat _ hwhat (Array.repeat K (Array.repeat 256#usize 0#u32))
    (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (Rows.zero _ _) (Rows.zero _ _)
  rw [hK] at w2_post1 w2_post2
  have hW : ReprVec w2 (commitAt sp P kappa.val) := Rows.reprVec w2_post1 hK
  have hw1 := Rows.hb_repr w2_post2 hK
  have hrng := Rows.hb_range w2_post2
  step*
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
  have hs5b : bytes s5 = ct := by
    rw [__post2, List.drop_zero, Nat.zero_add, hs4l, hs2b, hs3b, ← hct]
    unfold ctildeAt
    simp only [List.nil_append]
    rfl
  have hs5l : s5.val.length = sp.lam / 4 := by
    have h := congrArg List.length hs5b
    simp only [bytes, List.length_map] at h
    rw [h, ← hct]
    unfold ctildeAt H
    exact SHAKE256_length _ _
  have hctp : (bytesA (index_mut_back s5)).take (sp.lam / 4) = ct := by
    have hn : s5.val.length ≤ (Array.repeat 64#usize 0#u8).val.length := by
      simp [hs5l]; omega
    have e := setSlice_zero (Array.repeat 64#usize 0#u8).val s5.val hn
    have hmap : bytesA (index_mut_back s5) =
        ((s5.val ++ (Array.repeat 64#usize 0#u8).val.drop s5.val.length).map
          fun x => UInt8.ofNat x.val) := by
      simp only [bytesA, s4_post3, e]
    rw [hmap, List.map_append, List.take_left' (by simp [hs5l])]
    exact hs5b
  have hs6b : bytes s6 = ct := by
    have e : bytes s6 = (bytesA (index_mut_back s5)).take ip.c_tilde_len.val := by
      simp [bytes, bytesA, s6_post1, List.slice, Array.to_slice, List.map_take]
    rw [e, hcl, hctp]
  step with sample_in_ball_spec hv hstd.tau s6 c F.sampleInBall (by rw [hs6b, ← hct]; exact hS) as ⟨cp, hcp⟩
  step with ntt_spec cp hcp.canon as ⟨c_hat, hch1, hch2⟩
  have hchat : Repr c_hat (NTT c.toZq) := ⟨hch1, by rw [hch2, hcp.2]⟩
  step with response_spec ip sp hv hg y _ hY c_hat _ hchat s1_hat _ hs1 s2_hat _ hs2 w2 _ hW
    as ⟨z, wcs, r0, hz, hwc, hr0⟩
  have hg1v : ip.gamma1.val = sp.γ₁ := hv.gamma1
  have hg2v : ip.gamma2.val = sp.γ₂ := hv.gamma2
  have hbv : ip.beta.val = sp.β := hv.beta
  have hov : ip.omega.val = sp.ω := hv.omega
  step with vec_infinity_norm_spec_zq z _ hz as ⟨i2, hi2⟩
  step as ⟨i3, hi3⟩
  have hi3' : i3.val = sp.γ₁ - sp.β := by rw [hi3, hg1v, hbv]
  by_cases hc1 : i2 ≥ i3
  · rw [if_pos hc1]
    simp only [WP.spec_ok]
    have h1 := (show i3.val ≤ i2.val by scalar_tac)
    rw [hi2, hi3'] at h1
    have hnone : zh = none := by rw [← hzh, respond_eq, if_pos (Or.inl h1)]
    rw [hnone]; simp [AttPost]
  rw [if_neg hc1]
  have h1 := (show i2.val < i3.val by scalar_tac)
  rw [hi2, hi3'] at h1
  step with vec_infinity_norm_lowbits_spec sp hg r0 _ hr0 as ⟨i4, hi4, hi4le⟩
  step as ⟨i5, hi5⟩
  have hi5' : i5.val = sp.γ₂ - sp.β := by rw [hi5, hg2v, hbv]
  by_cases hc2 : i4 ≥ i5
  · rw [if_pos hc2]
    simp only [WP.spec_ok]
    have h2 := (show i5.val ≤ i4.val by scalar_tac)
    rw [hi4, hi5'] at h2
    have hnone : zh = none := by rw [← hzh, respond_eq, if_pos (Or.inr h2)]
    rw [hnone]; simp [AttPost]
  rw [if_neg hc2]
  have h2 := (show i4.val < i5.val by scalar_tac)
  rw [hi4, hi5'] at h2
  have hnot1 := not_or.2 ⟨not_le.2 h1, not_le.2 h2⟩
  step with hint_step_spec ip sp hv hg hstd.k_le c_hat _ hchat t0_hat _ ht0 wcs _ hwc
    as ⟨hint, ct0, ones, hh, hct0, hones⟩
  step with vec_infinity_norm_spec_zq ct0 _ hct0 as ⟨i6, hi6⟩
  by_cases hc3 : i6 ≥ ip.gamma2
  · rw [if_pos hc3]
    simp only [WP.spec_ok]
    have h3 := (show ip.gamma2.val ≤ i6.val by scalar_tac)
    rw [hi6, hg2v] at h3
    have hnone : zh = none := by rw [← hzh, respond_eq, if_neg hnot1, if_pos (Or.inl h3)]
    rw [hnone]; simp [AttPost]
  rw [if_neg hc3]
  have h3 := (show i6.val < ip.gamma2.val by scalar_tac)
  rw [hi6, hg2v] at h3
  by_cases hc4 : ones > ip.omega
  · rw [if_pos hc4]
    simp only [WP.spec_ok]
    have h4 := (show ip.omega.val < ones.val by scalar_tac)
    rw [hones, hov] at h4
    have hnone : zh = none := by rw [← hzh, respond_eq, if_neg hnot1, if_pos (Or.inr h4)]
    rw [hnone]; simp [AttPost]
  rw [if_neg hc4]
  simp only [WP.spec_ok]
  have h4 := (show ones.val ≤ ip.omega.val by scalar_tac)
  rw [hones, hov] at h4
  rw [← hzh, respond_eq, if_neg hnot1, if_neg (not_or.2 ⟨not_le.2 h3, not_lt.2 h4⟩)]
  exact ⟨_, _, _, rfl, hctp, hz, hh, h1, h4⟩

/-! ## Part 5: the rejection loop -/

/-- What the loop returns, given the spec's loop result `T` and the input buffer `sig`: on acceptance the encoded
signature is written into the buffer; otherwise the buffer is returned untouched. -/
def LoopPost (sp : Spec.Params)
    (T : Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k)) (sig : Slice U8) (r : Bool × Slice U8) :
    Prop :=
  match T with
  | some (ct, z, h) => r.1 = true ∧ bytes r.2 = sigEncode sp ct (z.map Poly.modPM) h
  | none => r.1 = false ∧ r.2 = sig

/-- The loop guard `more_attempts L κ` of Sign (`κ + ℓ − 1 ≤ 0xFFFF`) holds exactly when another full attempt of
`ℓ` counter values still fits below `2^16`. -/
theorem more_attempts_spec {L : Usize} (kappa : U32) (hL : 1 ≤ L.val) (hL' : L.val < 256)
    (hk : kappa.val ≤ 2 ^ 16) :
    sign.more_attempts L kappa ⦃ b => (b = true ↔ kappa.val + L.val ≤ 2 ^ 16) ⦄ := by
  unfold sign.more_attempts
  step as ⟨i, hi⟩
  have hiv : i.val = L.val := by
    rw [hi]; simp [UScalar.cast_val_eq]
    have : L.val % 4294967296 = L.val := Nat.mod_eq_of_lt (by omega)
    omega
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  simp only [decide_eq_true_eq]
  scalar_tac

theorem sign_loop_spec {ip K L sp} (hp : Params.Std ip K L sp) (hb : SignBuf sp) (F : Spec.Fuel) (P : Pre sp)
    (a_hat : Array (Array (Array U32 256#usize) L) K) (hA : ReprMat a_hat P.Â)
    (s1_hat : Array (Array U32 256#usize) L) (hs1 : ReprVec s1_hat P.ŝ₁)
    (s2_hat : Array (Array U32 256#usize) K) (hs2 : ReprVec s2_hat P.ŝ₂)
    (t0_hat : Array (Array U32 256#usize) K) (ht0 : ReprVec t0_hat P.t₀hat)
    (mu : Array U8 64#usize) (hmu : bytesA mu = P.μ)
    (rho_pp : Array U8 64#usize) (hrho : bytesA rho_pp = P.ρ'')
    (sig : Slice U8) (hsig : sig.length = sp.sigLen)
    (T : Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k))
    (kappa : U32) (hk : kappa.val ≤ 2 ^ 16) (n : Nat) (hn : 2 ^ 16 ≤ n + kappa.val)
    (hT : loopRes sp F P n kappa.val = some T) :
    sign.sign_prepared_internal_loop ip a_hat s1_hat s2_hat t0_hat sig mu rho_pp kappa ⦃ r => LoopPost sp T sig r ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hp : Params.Std ip K L sp := ⟨hv, hstd⟩
  have hL : L.val = sp.ℓ := hv.L_eq
  have hl1 := hb.ell_pos
  have hl256 : sp.ℓ < 256 := by have := hstd.kl_lt; omega
  unfold sign.sign_prepared_internal_loop
  apply loop.spec_decr_nat
    (fun (k : U32) => 2 ^ 16 - k.val)
    (fun k => k.val ≤ 2 ^ 16 ∧ ∃ n, 2 ^ 16 ≤ n + k.val ∧ loopRes sp F P n k.val = some T)
  · rintro kappa ⟨hk, n, hn, hT⟩
    simp only [sign.sign_prepared_internal_loop.body]
    step with more_attempts_spec (L := L) kappa (by omega) (by omega) hk as ⟨b, hbm⟩
    split
    · rename_i hc
      have hc' : kappa.val + sp.ℓ ≤ 2 ^ 16 := by
        have := hbm.1 (by simpa using hc)
        omega
      have hklt : kappa.val < 2 ^ 16 := by omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hlt : ¬ 2 ^ 16 < kappa.val + sp.ℓ := by omega
      simp only [loopRes] at hT
      rw [if_neg hlt] at hT
      step as ⟨i3, hi3⟩
      have hi3v : i3.val = kappa.val := by
        rw [hi3]; simp [UScalar.cast_val_eq]
        omega
      rcases hAt : attemptAt sp F P kappa.val with _ | ⟨ct, zh⟩
      · rw [hAt] at hT; simp at hT
      rw [hAt] at hT
      have hatt := attempt_spec hp hb F P a_hat hA s1_hat hs1 s2_hat hs2 t0_hat ht0 mu hmu rho_pp hrho i3
        (by omega) ct zh (by rw [hi3v]; exact hAt)
      step with hatt as ⟨o, ho⟩
      cases zh with
      | none =>
        simp only [AttPost] at ho
        rw [ho]
        dsimp only
        simp only [] at hT
        step as ⟨i4, hi4⟩
        have hi4v : i4.val = sp.ℓ := by
          rw [hi4]; simp [UScalar.cast_val_eq]
          have : L.val % 4294967296 = L.val := Nat.mod_eq_of_lt (by omega)
          omega
        step as ⟨kappa1, hk1⟩
        refine ⟨by omega, ⟨n', by omega, ?_⟩, by omega⟩
        rw [show kappa1.val = kappa.val + sp.ℓ by omega]
        exact hT
      | some zh' =>
        obtain ⟨z, h⟩ := zh'
        simp only [AttPost] at ho
        obtain ⟨ctb, zr, hr, he, hctb, hzr, hhr, hzn, hhw⟩ := ho
        rw [he]
        dsimp only
        simp only [] at hT
        simp only [Option.some.injEq] at hT
        subst hT
        step as ⟨s, hs⟩
        have hbs : bytes s = bytesA ctb := by rw [hs, bytes_to_slice]
        have hsl : sp.lam / 4 ≤ s.length := by
          have hl : ctb.val.length = 64 := ctb.property
          have : s.length = 64 := by rw [Slice.length, hs]; simp [Array.to_slice]
          have := hstd.lam_le
          omega
        step with sig_encode_signed_spec' ip sp hv hstd.stdSig s hsl zr z hzr hzn hr h hhr hhw sig hsig as ⟨sig1, hsig1⟩
        refine ⟨rfl, ?_⟩
        show bytes sig1 = _
        rw [hsig1, hbs, hctb]
    · rename_i hc
      have hc' : 2 ^ 16 < kappa.val + sp.ℓ := by
        by_contra hcon
        exact hc (by simpa using hbm.2 (by omega))
      simp only [WP.spec_ok]
      have hTn : T = none := by
        cases n with
        | zero => simp [loopRes] at hT; exact hT.symm
        | succ n' =>
          simp only [loopRes] at hT
          rw [if_pos hc'] at hT
          simp at hT; exact hT.symm
      subst hTn
      exact ⟨rfl, rfl⟩
  · exact ⟨hk, n, hn, hT⟩

/-! ## Part 6: spec-side lemmas about `pre` and `loopRes` -/

theorem pre_some {sp : Spec.Params} {F : Spec.Fuel} {sk M' rnd : List UInt8} {P : Pre sp}
    (h : pre sp F sk M' rnd = some P) (ρ K tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hd : Spec.skDecode sp sk = (ρ, K, tr, s₁, s₂, t₀)) :
    ∃ Â, Spec.ExpandA sp F.rejNTT ρ = some Â ∧
      P = ⟨s₁, s₂, t₀, Â, H (tr ++ M') 64, H (K ++ rnd ++ H (tr ++ M') 64) 64⟩ := by
  unfold pre at h
  rw [hd] at h
  dsimp only at h
  rcases hA : Spec.ExpandA sp F.rejNTT ρ with _ | Â
  · rw [hA] at h; simp at h
  · rw [hA] at h
    simp only [Option.some.injEq] at h
    exact ⟨Â, rfl, h.symm⟩

theorem pre_isSome_iff (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8) :
    (pre sp F sk M' rnd).isSome = true ↔
      (Spec.ExpandA sp F.rejNTT (Spec.skDecode sp sk).1).isSome = true := by
  unfold pre
  rcases hd : Spec.skDecode sp sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  dsimp only
  rcases hA : Spec.ExpandA sp F.rejNTT ρ with _ | Â <;> simp

theorem attemptAt_isSome_iff (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) (κ : Nat) :
    (attemptAt sp F P κ).isSome = true ↔
      (Spec.SampleInBall sp F.sampleInBall (ctildeAt sp P κ)).isSome = true := by
  unfold attemptAt
  rcases Spec.SampleInBall sp F.sampleInBall (ctildeAt sp P κ) with _ | c <;> simp

/-- A spec result `some (some x)` persists when the attempt budget grows. -/
theorem loopRes_mono (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) :
    ∀ (n κ : Nat) (x : List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k),
      loopRes sp F P n κ = some (some x) → ∀ j, loopRes sp F P (n + j) κ = some (some x) := by
  intro n
  induction n with
  | zero => intro κ x h; simp [loopRes] at h
  | succ n ih =>
    intro κ x h j
    have e : n + 1 + j = (n + j) + 1 := by omega
    rw [e]
    simp only [loopRes] at h ⊢
    by_cases hc : 2 ^ 16 < κ + sp.ℓ
    · rw [if_pos hc] at h; simp at h
    · rw [if_neg hc] at h ⊢
      rcases hA : attemptAt sp F P κ with _ | ⟨ct, _ | ⟨z, h'⟩⟩
      · simp [hA] at h
      · simp only [hA] at h ⊢
        exact ih _ x h j
      · simp only [hA] at h ⊢
        exact h

/-- Once the counter has run out of room (`κ + n·ℓ + ℓ > 2^16`), a larger budget changes nothing. -/
theorem loopRes_cap (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) :
    ∀ (n κ j : Nat), 2 ^ 16 < κ + n * sp.ℓ + sp.ℓ → loopRes sp F P (n + j) κ = loopRes sp F P n κ := by
  intro n
  induction n with
  | zero =>
    intro κ j h
    rw [Nat.zero_add]
    cases j with
    | zero => rfl
    | succ j =>
      simp only [loopRes]
      have : 2 ^ 16 < κ + sp.ℓ := by simpa using h
      rw [if_pos this]
  | succ n ih =>
    intro κ j h
    have e : n + 1 + j = (n + j) + 1 := by omega
    rw [e]
    simp only [loopRes]
    by_cases hc : 2 ^ 16 < κ + sp.ℓ
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      rcases hA : attemptAt sp F P κ with _ | ⟨ct, _ | ⟨z, h'⟩⟩
      · simp
      · simp only []
        apply ih
        have : (n + 1) * sp.ℓ = n * sp.ℓ + sp.ℓ := by ring
        omega
      · simp

/-- Every attempt rejects (and every `SampleInBall` has enough fuel) from attempt `a` on for `n` attempts. -/
theorem loopRes_rejects (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) :
    ∀ (n a : Nat), (∀ i, a ≤ i → i < a + n → ∃ ct, attemptAt sp F P (i * sp.ℓ) = some (ct, none)) →
      loopRes sp F P n (a * sp.ℓ) = some none := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a H
    simp only [loopRes]
    by_cases hc : 2 ^ 16 < a * sp.ℓ + sp.ℓ
    · rw [if_pos hc]
    · rw [if_neg hc]
      obtain ⟨ct, hct⟩ := H a le_rfl (by omega)
      simp only [hct]
      have := ih (a + 1) (fun i h1 h2 => H i (by omega) (by omega))
      rwa [Nat.succ_mul] at this

/-- `kappaBudget` attempts exhaust the counter: `κ_final + ℓ > 2^16`. -/
theorem kappaBudget_cap (sp : Spec.Params) (hl : 1 ≤ sp.ℓ) :
    2 ^ 16 < 0 + kappaBudget sp * sp.ℓ + sp.ℓ := by
  unfold kappaBudget
  have h1 := Nat.div_add_mod (2 ^ 16 - sp.ℓ) sp.ℓ
  have h2 := Nat.mod_lt (2 ^ 16 - sp.ℓ) (show 0 < sp.ℓ by omega)
  have h3 : ((2 ^ 16 - sp.ℓ) / sp.ℓ + 1) * sp.ℓ = (2 ^ 16 - sp.ℓ) / sp.ℓ * sp.ℓ + sp.ℓ := by ring
  have h4 : sp.ℓ * ((2 ^ 16 - sp.ℓ) / sp.ℓ) = (2 ^ 16 - sp.ℓ) / sp.ℓ * sp.ℓ := Nat.mul_comm _ _
  omega

/-- Accepting runs of the spec loop, in terms of the attempts. -/
theorem loopRes_accept_iff (sp : Spec.Params) (F : Spec.Fuel) (P : Pre sp) :
    ∀ (n c : Nat), (∃ x, loopRes sp F P n (c * sp.ℓ) = some (some x)) ↔
      ∃ a, a < n ∧ (c + a) * sp.ℓ + sp.ℓ ≤ 2 ^ 16 ∧
        (∀ i, i < a → ∃ ct, attemptAt sp F P ((c + i) * sp.ℓ) = some (ct, none)) ∧
        ∃ ct z h, attemptAt sp F P ((c + a) * sp.ℓ) = some (ct, some (z, h)) := by
  intro n
  induction n with
  | zero =>
    intro c
    constructor
    · rintro ⟨x, hx⟩; simp [loopRes] at hx
    · rintro ⟨a, ha, _⟩; omega
  | succ n ih =>
    intro c
    simp only [loopRes]
    by_cases hc : 2 ^ 16 < c * sp.ℓ + sp.ℓ
    · rw [if_pos hc]
      constructor
      · rintro ⟨x, hx⟩; simp at hx
      · rintro ⟨a, _, h2, _⟩
        have : c * sp.ℓ ≤ (c + a) * sp.ℓ := Nat.mul_le_mul_right _ (by omega)
        omega
    · rw [if_neg hc]
      rcases hA : attemptAt sp F P (c * sp.ℓ) with _ | ⟨ct, _ | ⟨z, h'⟩⟩
      · simp only []
        constructor
        · rintro ⟨x, hx⟩; simp at hx
        · rintro ⟨a, _, _, hi, ct', z', h'', ha⟩
          cases a with
          | zero => simp [hA] at ha
          | succ a =>
            obtain ⟨ct0, h0⟩ := hi 0 (by omega)
            simp [hA] at h0
      · simp only []
        have ih' := ih (c + 1)
        rw [show c * sp.ℓ + sp.ℓ = (c + 1) * sp.ℓ by rw [Nat.succ_mul]]
        rw [ih']
        constructor
        · rintro ⟨a, ha, h2, hi, hr⟩
          refine ⟨a + 1, by omega, ?_, ?_, ?_⟩
          · rw [show c + (a + 1) = c + 1 + a by omega]; exact h2
          · intro i hi'
            cases i with
            | zero => exact ⟨ct, by simpa using hA⟩
            | succ i =>
              rw [show c + (i + 1) = c + 1 + i by omega]
              exact hi i (by omega)
          · rw [show c + (a + 1) = c + 1 + a by omega]; exact hr
        · rintro ⟨a, ha, h2, hi, ct', z', h'', hr⟩
          cases a with
          | zero => simp [hA] at hr
          | succ a =>
            refine ⟨a, by omega, ?_, ?_, ct', z', h'', ?_⟩
            · rw [show c + 1 + a = c + (a + 1) by omega]; exact h2
            · intro i hi'
              have := hi (i + 1) (by omega)
              rw [show c + (i + 1) = c + 1 + i by omega] at this
              exact this
            · rw [show c + 1 + a = c + (a + 1) by omega]; exact hr
      · simp only []
        constructor
        · intro _
          exact ⟨0, by omega, by simpa using hc, fun i hi => by omega, ct, z, h', by simpa using hA⟩
        · intro _
          exact ⟨_, rfl⟩

/-! ## Part 7: `sign_internal` -/

/-- The key half of Sign as `sign_internal` and `signing_key_NN` run it: `prepare_sk_into` on the all-zero
`PreparedSk` (the Rust `prepare_sk`, which is not itself extracted because nothing in the extraction closure calls
it). -/
def prepSk (K L : Usize) (p : Impl.params.Params) (sk : Slice U8) : RustM (sign.PreparedSk K L) := do
  let z ← sign.PreparedSk.zeroed K L
  sign.prepare_sk_into p sk z

/-- **The key half of Sign (steps 1-5).** `prepare_sk_into` returns, for any destination `out`, ŝ₁, ŝ₂, t̂₀ (the NTTs
of the decoded `s₁`, `s₂`, `t₀`), Â = ExpandA(ρ) (for any fuel at which the spec samples), K and tr, all as `skDecode`
of the key bytes gives them. -/
theorem prepare_sk_into_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk : Slice U8) (hsk : sk.length = sp.skLen) (out : sign.PreparedSk K L)
    (ρ Kk tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hd : Spec.skDecode sp (bytes sk) = (ρ, Kk, tr, s₁, s₂, t₀))
    (Â : Vector (Vector Poly sp.ℓ) sp.k) (F1 : Nat) (hA : Spec.ExpandA sp F1 ρ = some Â) :
    sign.prepare_sk_into ip sk out ⦃ ps =>
      ReprMat ps.a_hat Â ∧ ReprVec ps.s1_hat (NTTVec (s₁.map RPoly.toZq)) ∧
      ReprVec ps.s2_hat (NTTVec (s₂.map RPoly.toZq)) ∧ ReprVec ps.t0_hat (NTTVec (t₀.map RPoly.toZq)) ∧
      bytesA ps.key = Kk ∧ bytesA ps.tr = tr ⦄ := by
  obtain ⟨hv, hstd⟩ := hp
  have hK : K.val = sp.k := hv.K_eq
  have hL : L.val = sp.ℓ := hv.L_eq
  unfold sign.prepare_sk_into
  refine WP.spec_bind (sk_decode_into_spec ip sp hv hstd.eta_lt sk hsk _) ?_
  intro key ⟨hrho, hkey, htr, hs1, hs2, ht0⟩
  rw [hd] at hrho hkey htr hs1 hs2 ht0
  dsimp only at hrho hkey htr hs1 hs2 ht0
  refine WP.spec_bind (ntt_vec_into_spec key.s1 out.s1_hat _ hs1.repr) ?_
  intro s1_hat hs1h
  refine WP.spec_bind (ntt_vec_into_spec key.s2 out.s2_hat _ hs2.repr) ?_
  intro s2_hat hs2h
  refine WP.spec_bind (ntt_vec_into_spec key.t0 out.t0_hat _ ht0.repr) ?_
  intro t0_hat ht0h
  refine WP.spec_bind (expand_a_spec sp K L hK hL key.rho Â F1 (by rw [hrho]; exact hA)) ?_
  intro a_hat hAh
  simp only [WP.spec_ok]
  exact ⟨hAh, hs1h, hs2h, ht0h, hkey, htr⟩

/-- **The key half of Sign (steps 1-5), from the zero destination**: the same statement for `prepSk`. -/
theorem prepare_sk_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk : Slice U8) (hsk : sk.length = sp.skLen)
    (ρ Kk tr : List UInt8) (s₁ : Vector RPoly sp.ℓ) (s₂ t₀ : Vector RPoly sp.k)
    (hd : Spec.skDecode sp (bytes sk) = (ρ, Kk, tr, s₁, s₂, t₀))
    (Â : Vector (Vector Poly sp.ℓ) sp.k) (F1 : Nat) (hA : Spec.ExpandA sp F1 ρ = some Â) :
    prepSk K L ip sk ⦃ ps =>
      ReprMat ps.a_hat Â ∧ ReprVec ps.s1_hat (NTTVec (s₁.map RPoly.toZq)) ∧
      ReprVec ps.s2_hat (NTTVec (s₂.map RPoly.toZq)) ∧ ReprVec ps.t0_hat (NTTVec (t₀.map RPoly.toZq)) ∧
      bytesA ps.key = Kk ∧ bytesA ps.tr = tr ⦄ := by
  unfold prepSk
  simp only [sign.PreparedSk.zeroed, Std.bind_tc_ok]
  exact prepare_sk_into_spec hp sk hsk _ ρ Kk tr s₁ s₂ t₀ hd Â F1 hA

/-- `sign_internal` is `prepSk` followed by `sign_prepared_internal`. -/
theorem sign_internal_eq_prep {ip : Impl.params.Params} {K L : Usize}
    (sk m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8) :
    sign.sign_internal K L ip sk m_prefix m rnd sig =
      (do let ps ← prepSk K L ip sk; sign.sign_prepared_internal ip ps m_prefix m rnd sig) := by
  unfold sign.sign_internal prepSk
  simp only [sign.PreparedSk.zeroed, Std.bind_tc_ok]

/-- Steps 6-33 on a prepared key (the Rust `sign_prepared_internal`): if `ps` holds the spec's pre-loop values
(`P.Â`, `P.ŝ₁`, `P.ŝ₂`, `P.t̂₀`, with `P.μ = H(tr ‖ M′, 64)` and `P.ρ'' = H(K ‖ rnd ‖ μ, 64)` for the `K`, `tr` held in
`ps`) and the spec loop (with a budget large enough to cover the whole counter range) returns `T`, so does the Rust
function. -/
theorem sign_prepared_core {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (hb : SignBuf sp)
    (ps : sign.PreparedSk K L) (m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (hsig : sig.length = sp.sigLen) (F : Spec.Fuel) (P : Pre sp)
    (hA : ReprMat ps.a_hat P.Â) (hs1 : ReprVec ps.s1_hat P.ŝ₁) (hs2 : ReprVec ps.s2_hat P.ŝ₂)
    (ht0 : ReprVec ps.t0_hat P.t₀hat)
    (hmu : P.μ = H (bytesA ps.tr ++ (bytes m_prefix ++ bytes m)) 64)
    (hrho : P.ρ'' = H (bytesA ps.key ++ bytesA rnd ++ P.μ) 64)
    (T : Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k)) (n : Nat) (hn : 2 ^ 16 ≤ n)
    (hT : loopRes sp F P n 0 = some T) :
    sign.sign_prepared_internal ip ps m_prefix m rnd sig ⦃ r => LoopPost sp T sig r ⦄ := by
  have hp' := hp
  obtain ⟨hv, hstd⟩ := hp
  unfold sign.sign_prepared_internal
  step*
  have hsb : bytes s = bytesA ps.tr := by rw [s_post, bytes_to_slice]
  have hs1l : s1.val.length = 64 := by rw [s1_post1]; simp
  have hs2b : bytes s2 = H (bytesA ps.tr ++ (bytes m_prefix ++ bytes m)) 64 := by
    rw [‹bytes s2 = _›, List.drop_zero, Nat.zero_add, hs1l, hsb]
    simp only [List.nil_append, List.append_assoc]
    rfl
  have hs2l : s2.val.length = 64 := by
    have h := congrArg List.length hs2b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  have hmu' : bytesA (to_slice_mut_back s2) = P.μ := by
    rw [s1_post2, bytesA_from_slice _ _ hs2l, hs2b, hmu]
  have hs3b : bytes s3 = bytesA ps.key := by rw [s3_post, bytes_to_slice]
  have hs4b : bytes s4 = bytesA rnd := by rw [s4_post, bytes_to_slice]
  have hs5b : bytes s5 = P.μ := by
    rw [s5_post, bytes_to_slice, hmu']
  have hs6l : s6.val.length = 64 := by rw [s6_post1]; simp
  have hs7b : bytes s7 = H (bytesA ps.key ++ bytesA rnd ++ P.μ) 64 := by
    rw [‹bytes s7 = _›, List.drop_zero, Nat.zero_add, hs6l, hs3b, hs4b, hs5b]
    simp only [List.nil_append]
    rfl
  have hs7l : s7.val.length = 64 := by
    have h := congrArg List.length hs7b
    simp only [bytes, List.length_map] at h
    rw [h]; exact SHAKE256_length _ _
  have hrho' : bytesA (to_slice_mut_back1 s7) = P.ρ'' := by
    rw [s6_post2, bytesA_from_slice _ _ hs7l, hs7b, hrho]
  exact sign_loop_spec hp' hb F P ps.a_hat hA ps.s1_hat hs1 ps.s2_hat hs2 ps.t0_hat ht0 (to_slice_mut_back s2) hmu'
    (to_slice_mut_back1 s7) hrho' sig hsig T 0#u32 (by simp) n (by simp; omega) (by simpa using hT)

/-- The Rust prelude (steps 1-7) followed by the loop: if the spec's pre-loop values are `P` and the spec loop
(with a budget large enough to cover the whole counter range) returns `T`, so does the Rust function. -/
theorem sign_internal_core {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (hb : SignBuf sp)
    (sk m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (hsk : sk.length = sp.skLen) (hsig : sig.length = sp.sigLen) (F : Spec.Fuel)
    (P : Pre sp) (hP : pre sp F (bytes sk) (bytes m_prefix ++ bytes m) (bytesA rnd) = some P)
    (T : Option (List UInt8 × Vector Poly sp.ℓ × Vector HintPoly sp.k)) (n : Nat) (hn : 2 ^ 16 ≤ n)
    (hT : loopRes sp F P n 0 = some T) :
    sign.sign_internal K L ip sk m_prefix m rnd sig ⦃ r => LoopPost sp T sig r ⦄ := by
  rcases hd : Spec.skDecode sp (bytes sk) with ⟨ρ, Kk, tr, s₁, s₂, t₀⟩
  obtain ⟨Â, hA, rfl⟩ := pre_some hP ρ Kk tr s₁ s₂ t₀ hd
  rw [sign_internal_eq_prep]
  refine WP.spec_bind (prepare_sk_spec hp sk hsk ρ Kk tr s₁ s₂ t₀ hd Â F.rejNTT hA) ?_
  rintro ps ⟨hAh, hs1h, hs2h, ht0h, hkey, htr⟩
  exact sign_prepared_core hp hb ps m_prefix m rnd sig hsig F
    ⟨s₁, s₂, t₀, Â, H (tr ++ (bytes m_prefix ++ bytes m)) 64,
      H (Kk ++ bytesA rnd ++ H (tr ++ (bytes m_prefix ++ bytes m)) 64) 64⟩ hAh hs1h hs2h ht0h
    (by dsimp only; rw [htr]) (by dsimp only; rw [hkey]) T n hn hT

/-- **`Sign_internal` refinement, success case.** If the bounded spec (any attempt budget `B`) returns the
signature `σ`, the extracted Rust `sign_internal` returns `true` and writes exactly `σ` into the output buffer.
Premises: `Params.Std` (which gives the buffer facts `SignBuf`, see `StdParams.signBuf`), the buffer lengths and
the spec's `some`. -/
theorem sign_internal_spec_some {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp)
    (sk m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (hsk : sk.length = sp.skLen) (hsig : sig.length = sp.sigLen) (B : Nat) (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign_internal_bounded sp B (bytes sk) (bytes m_prefix ++ bytes m) (bytesA rnd) F = some σ) :
    sign.sign_internal K L ip sk m_prefix m rnd sig ⦃ r => r.1 = true ∧ bytes r.2 = σ ⦄ := by
  have hb : SignBuf sp := StdParams.signBuf (Params.Std.params hp)
  rw [Sign_internal_bounded_eq] at hs
  rcases hP : pre sp F (bytes sk) (bytes m_prefix ++ bytes m) (bytesA rnd) with _ | P
  · rw [hP] at hs; simp at hs
  rw [hP] at hs
  simp only [] at hs
  rcases hl : loopRes sp F P B 0 with _ | _ | ⟨ct, z, h⟩
  · rw [hl] at hs; simp [encodeRes] at hs
  · rw [hl] at hs; simp [encodeRes] at hs
  · rw [hl] at hs
    simp only [encodeRes, Option.some.injEq] at hs
    have hm := loopRes_mono sp F P B 0 (ct, z, h) hl (2 ^ 16)
    apply WP.spec_mono (sign_internal_core hp hb sk m_prefix m rnd sig hsk hsig F P hP (some (ct, z, h))
      (B + 2 ^ 16) (by omega) hm)
    intro r hr
    obtain ⟨h1, h2⟩ := hr
    exact ⟨h1, by rw [h2, hs]⟩

/-- The spec's failure outcome "the κ budget was exhausted": `ExpandA` succeeded, no `SampleInBall` ran out of
fuel, and no attempt among the first `kappaBudget sp` was accepted. -/
def Exhausted (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8) : Prop :=
  ∃ P, pre sp F sk M' rnd = some P ∧ loopRes sp F P (kappaBudget sp) 0 = some none

/-- `Exhausted` in terms of the attempts: every one of the `kappaBudget sp` attempts has enough `SampleInBall`
fuel and is rejected by the validity checks. -/
theorem exhausted_of_rejects (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8) (P : Pre sp)
    (hP : pre sp F sk M' rnd = some P)
    (hr : ∀ i, i < kappaBudget sp → ∃ ct, attemptAt sp F P (i * sp.ℓ) = some (ct, none)) :
    Exhausted sp F sk M' rnd := by
  refine ⟨P, hP, ?_⟩
  have := loopRes_rejects sp F P (kappaBudget sp) 0 (fun i _ h2 => hr i (by omega))
  rwa [Nat.zero_mul] at this

/-- `Exhausted` implies the spec returns `none` with the budget `kappaBudget sp`. -/
theorem exhausted_spec_none (sp : Spec.Params) (F : Spec.Fuel) (sk M' rnd : List UInt8)
    (h : Exhausted sp F sk M' rnd) :
    Spec.Sign_internal_bounded sp (kappaBudget sp) sk M' rnd F = none := by
  obtain ⟨P, hP, hl⟩ := h
  rw [Sign_internal_bounded_eq, hP]
  simp [hl, encodeRes]

/-- The spec's `none` conflates three situations: `ExpandA` ran out of fuel, a `SampleInBall` ran out of fuel
(`loopRes = none`), or the budget was exhausted (`loopRes = some none`, i.e. `Exhausted` when `B = kappaBudget sp`). -/
theorem sign_none_cases (sp : Spec.Params) (B : Nat) (F : Spec.Fuel) (sk M' rnd : List UInt8) :
    Spec.Sign_internal_bounded sp B sk M' rnd F = none ↔
      pre sp F sk M' rnd = none ∨
      ∃ P, pre sp F sk M' rnd = some P ∧ (loopRes sp F P B 0 = none ∨ loopRes sp F P B 0 = some none) := by
  rw [Sign_internal_bounded_eq]
  rcases hP : pre sp F sk M' rnd with _ | P
  · simp
  · rcases hl : loopRes sp F P B 0 with _ | _ | x <;> simp [hl, encodeRes]

/-- **`Sign_internal` refinement, exhaustion case.** If the spec's `ExpandA` and every `SampleInBall` had enough
fuel and all `kappaBudget sp` attempts were rejected, the Rust `sign_internal` returns `false` and leaves the
output buffer untouched (it writes `sig` only after an accepted attempt). The spec's plain `none` is not enough:
it also covers fuel failures, see `sign_none_cases`. -/
theorem sign_internal_spec_none {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp)
    (sk m_prefix m : Slice U8) (rnd : Array U8 32#usize) (sig : Slice U8)
    (hsk : sk.length = sp.skLen) (hsig : sig.length = sp.sigLen) (F : Spec.Fuel)
    (hex : Exhausted sp F (bytes sk) (bytes m_prefix ++ bytes m) (bytesA rnd)) :
    sign.sign_internal K L ip sk m_prefix m rnd sig ⦃ r => r.1 = false ∧ r.2 = sig ⦄ := by
  have hb : SignBuf sp := StdParams.signBuf (Params.Std.params hp)
  obtain ⟨P, hP, hl⟩ := hex
  have hcap := loopRes_cap sp F P (kappaBudget sp) 0 (2 ^ 16) (kappaBudget_cap sp hb.ell_pos)
  exact sign_internal_core hp hb sk m_prefix m rnd sig hsk hsig F P hP none (kappaBudget sp + 2 ^ 16)
    (by omega) (by rw [hcap, hl])

/-! ### Satisfiability of the `some` premise -/

/-- **Satisfiability reduction** for the premise of `sign_internal_spec_some` (the analogue of
`keygen_isSome_iff`): the bounded spec returns `some` exactly when `ExpandA` succeeds on `ρ` (see
`pre_isSome_iff`) and, for some `a < B` with `κ = a·ℓ` still inside the counter range, the attempts `0..a-1` are
rejected (their `SampleInBall` has enough fuel, `attemptAt_isSome_iff`) and attempt `a` is accepted. -/
theorem sign_isSome_iff (sp : Spec.Params) (B : Nat) (F : Spec.Fuel) (sk M' rnd : List UInt8) :
    (Spec.Sign_internal_bounded sp B sk M' rnd F).isSome = true ↔
      ∃ P, pre sp F sk M' rnd = some P ∧ ∃ a, a < B ∧ a * sp.ℓ + sp.ℓ ≤ 2 ^ 16 ∧
        (∀ i, i < a → ∃ ct, attemptAt sp F P (i * sp.ℓ) = some (ct, none)) ∧
        ∃ ct z h, attemptAt sp F P (a * sp.ℓ) = some (ct, some (z, h)) := by
  rw [Sign_internal_bounded_eq]
  rcases hP : pre sp F sk M' rnd with _ | P
  · simp
  · simp only [Option.some.injEq, exists_eq_left']
    have key : (encodeRes sp (loopRes sp F P B 0)).isSome = true ↔
        ∃ x, loopRes sp F P B (0 * sp.ℓ) = some (some x) := by
      rw [Nat.zero_mul]
      rcases loopRes sp F P B 0 with _ | _ | x <;> simp [encodeRes]
    rw [key, loopRes_accept_iff]
    simp only [Nat.zero_add]

end Sign
end Proofs
