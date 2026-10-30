import Proofs.API

/-!
# The internal wrappers `sign_internal_NN` / `verify_internal_NN` and the `none` direction of `sign_NN`

`Impl.api.sign_internal_NN (sk, M′, rnd)` and `verify_internal_NN (pk, M′, σ)` are Algorithms 7 and 8 with the
caller supplying `M′`. The Rust passes an empty `m_prefix` buffer, so `bytes m_prefix ++ bytes m = [] ++ bytes M′ = bytes M′`.

* `sign_internal_NN_correct_some`: if `Spec.Sign_internal_bounded … B (bytesA sk) (bytes M′) (bytesA rnd) F = some σ`
  (any budget `B`), the Rust returns `some σ'` with `bytesA σ' = σ`.
* `sign_internal_NN_correct_exhausted`: if the κ budget is exhausted (`Sign.Exhausted`), the Rust returns `none`.
* `sign_internal_NN_none_only_if`: if the Rust returns `none` then, for every fuel `F`, the spec (with the real
  budget `kappaBudget`) returns `none`, and that `none` is one of the spec's failure cases (`Sign.sign_none_cases`).
* `verify_internal_NN_correct`: if `Spec.Verify_internal … = some b`, the Rust returns `b`.
* `sign_NN_none_only_if`: the converse direction of `sign_NN_correct_some`. See the docstring there.

The premises are only the spec's `some` hypotheses; the fixed-size arrays and `ML_DSA_NN_std` discharge the rest.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open HintAux

namespace APIInternal
open API

/-- The body of `api.sign_internal_NN`, generic in the array sizes and the parameter record. -/
def signInternalAPI (n N : Usize) (K L : Usize) (P : RustM params.Params) (sk : Array U8 n) (m : Slice U8)
    (rnd : Array U8 32#usize) : RustM (Option (Array U8 N)) := do
  let p ← P
  let sig := Array.repeat N 0#u8
  let s ← lift (Array.to_slice sk)
  let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let (s2, to_slice_mut_back) ← lift (Array.to_slice_mut sig)
  let (b, s3) ← sign.sign_internal K L p s s1 m rnd s2
  if b
  then let sig1 := to_slice_mut_back s3
       ok (some sig1)
  else ok none

theorem sign_internal_44_eq : api.sign_internal_44 = signInternalAPI 2560#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem sign_internal_65_eq : api.sign_internal_65 = signInternalAPI 4032#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem sign_internal_87_eq : api.sign_internal_87 = signInternalAPI 4896#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 := rfl

/-- The body of `api.verify_internal_NN`. -/
def verifyInternalAPI (n N : Usize) (K L : Usize) (P : RustM params.Params) (pk : Array U8 n) (m : Slice U8)
    (sig : Array U8 N) : RustM Bool := do
  let p ← P
  let s ← lift (Array.to_slice pk)
  let s1 ← lift (Array.to_slice (Std.Array.empty Std.U8))
  let s2 ← lift (Array.to_slice sig)
  verify.verify_internal K L p s s1 m s2

theorem verify_internal_44_eq : api.verify_internal_44 = verifyInternalAPI 1312#usize 2420#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem verify_internal_65_eq : api.verify_internal_65 = verifyInternalAPI 1952#usize 3309#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem verify_internal_87_eq : api.verify_internal_87 = verifyInternalAPI 2592#usize 4627#usize 8#usize 7#usize params.ML_DSA_87 := rfl

/-- The empty prefix buffer contributes no bytes. -/
theorem bytesA_empty : bytesA (Std.Array.empty Std.U8) = [] := by
  simp [bytesA, Std.Array.empty]

theorem bytes_empty_prefix : bytes (Array.to_slice (Std.Array.empty Std.U8)) = [] := by
  rw [bytes_to_slice, bytesA_empty]

/-! ## Algorithm 8 (`Verify_internal`) -/

theorem verifyInternalAPI_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize)
    (pk : Array U8 n) (m : Slice U8) (sig : Array U8 N) (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify_internal sp (bytesA pk) (bytes m) (bytesA sig) F = some b) :
    verifyInternalAPI n N K L (ok ip) pk m sig ⦃ r => r = b ⦄ := by
  unfold verifyInternalAPI
  simp only [Std.bind_tc_ok]
  step*
  refine verify_internal_spec hp s s2 s1 m F b ?_
  rw [s_post, s2_post, s1_post]
  simp only [bytes_to_slice, bytesA_empty, List.nil_append]
  exact hs

/-! ## Algorithm 7 (`Sign_internal`) -/

theorem signInternalAPI_some {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m : Slice U8) (rnd : Array U8 32#usize) (B : Nat) (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign_internal_bounded sp B (bytesA sk) (bytes m) (bytesA rnd) F = some σ) :
    signInternalAPI n N K L (ok ip) sk m rnd ⦃ r => ∃ s, r = some s ∧ bytesA s = σ ⦄ := by
  unfold signInternalAPI
  simp only [Std.bind_tc_ok]
  step*
  have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
  have hls : s.length = sp.skLen := by
    have := congrArg List.length hbs
    simp only [bytes_length, bytesA_length] at this
    show s.val.length = _
    omega
  have hls2 : s2.length = sp.sigLen := by
    show s2.val.length = _
    rw [s2_post1]; simp [Array.repeat_val, hN]
  have hlenσ : σ.length = sp.sigLen :=
    sign_len sp (Params.Std.params hp).stdSig _ F _ _ _ σ hs
  have hspec : Spec.Sign_internal_bounded sp B (bytes s) (bytes s1 ++ bytes m) (bytesA rnd) F = some σ := by
    rw [hbs, s1_post, bytes_empty_prefix]; simpa using hs
  refine WP.spec_bind (Proofs.Sign.sign_internal_spec_some hp s s1 m rnd s2 hls hls2 B F σ hspec) ?_
  rintro ⟨b1, s3⟩ ⟨hb1, hs3⟩
  have hb1' : b1 = true := hb1
  have hs3' : bytes s3 = σ := hs3
  subst hb1'
  have hl3 : s3.val.length = N.val := by
    have := congrArg List.length hs3'
    simp only [bytes_length] at this
    omega
  refine (WP.spec_ok _).mpr ⟨_, rfl, ?_⟩
  rw [s2_post2, bytesA_from_slice _ _ hl3, hs3']

theorem signInternalAPI_exhausted {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m : Slice U8) (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted sp F (bytesA sk) (bytes m) (bytesA rnd)) :
    signInternalAPI n N K L (ok ip) sk m rnd ⦃ r => r = none ⦄ := by
  unfold signInternalAPI
  simp only [Std.bind_tc_ok]
  step*
  have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
  have hls : s.length = sp.skLen := by
    have := congrArg List.length hbs
    simp only [bytes_length, bytesA_length] at this
    show s.val.length = _
    omega
  have hls2 : s2.length = sp.sigLen := by
    show s2.val.length = _
    rw [s2_post1]; simp [Array.repeat_val, hN]
  have hex' : Proofs.Sign.Exhausted sp F (bytes s) (bytes s1 ++ bytes m) (bytesA rnd) := by
    rw [hbs, s1_post, bytes_empty_prefix]; simpa using hex
  refine WP.spec_bind (Proofs.Sign.sign_internal_spec_none hp s s1 m rnd s2 hls hls2 F hex') ?_
  rintro ⟨b1, s3⟩ hb1
  have hb1' : b1 = false := hb1.1
  subst hb1'
  exact (WP.spec_ok _).mpr rfl

/-- If the Rust `sign_internal` wrapper returns `none`, the spec (with the real budget) returns `none` for every
fuel. -/
theorem signInternalAPI_none_only_if {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m : Slice U8) (rnd : Array U8 32#usize)
    (h : signInternalAPI n N K L (ok ip) sk m rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign_internal_bounded sp (kappaBudget sp) (bytesA sk) (bytes m) (bytesA rnd) F = none := by
  by_contra hne
  obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists'.mp hne
  have := signInternalAPI_some hp n N hn hN sk m rnd _ F σ hσ
  rw [h] at this
  obtain ⟨s, hs, -⟩ := (WP.spec_ok _).mp this
  exact absurd hs (by simp)

/-! ## `sign_NN` returning `none` -/

/-- **The `none` direction of Algorithm 2.** If the Rust `sign` returns `none` (`= ok none`; the Rust may also
diverge, which this does not cover), then for every fuel `F` the spec's `Sign` is `none` too. This is the
contrapositive of `sign_NN_correct_some`: the Rust never rejects an input that the spec signs. -/
theorem signAPI_none_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n N : Usize) (hn : n.val = sp.skLen) (hN : N.val = sp.sigLen)
    (sk : Array U8 n) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (h : signAPI n N K L (ok ip) sk m ctx rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign sp (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none := by
  by_contra hne
  obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists'.mp hne
  have := signAPI_some hp n N hn hN sk m ctx rnd F σ hσ
  rw [h] at this
  obtain ⟨s, hs, -⟩ := (WP.spec_ok _).mp this
  exact absurd hs (by simp)

/-- The spec-side decomposition of `Sign = none` for `|ctx| ≤ 255`: the pre-computation (ExpandA) ran out of
fuel, or some attempt's `SampleInBall` did, or the κ budget was exhausted. -/
theorem sign_none_decomp (sp : Spec.Params) (F : Spec.Fuel) (sk M ctx rnd : List UInt8)
    (h : Spec.Sign sp sk M ctx rnd F = none) :
    255 < ctx.length ∨
      Proofs.Sign.pre sp F sk ([0, UInt8.ofNat ctx.length] ++ ctx ++ M) rnd = none ∨
      ∃ P, Proofs.Sign.pre sp F sk ([0, UInt8.ofNat ctx.length] ++ ctx ++ M) rnd = some P ∧
        (Proofs.Sign.loopRes sp F P (kappaBudget sp) 0 = none ∨
         Proofs.Sign.loopRes sp F P (kappaBudget sp) 0 = some none) := by
  by_cases hc : ctx.length ≤ 255
  · rw [Sign_short sp _ _ _ _ F hc] at h
    exact Or.inr ((Proofs.Sign.sign_none_cases sp _ F _ _ _).mp h)
  · exact Or.inl (by omega)


/-! ### ML-DSA-44 -/

/-- **Algorithm 7 (`Sign_internal`), ML-DSA-44, success.** If the spec returns `σ` (for any budget `B`), the
Rust `sign_internal_44` returns `some σ'` with `σ'` holding the bytes `σ`. -/
theorem _root_.Proofs.sign_internal_44_correct_some (sk : Array U8 2560#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (B : Nat) (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign_internal_bounded Spec.ML_DSA_44 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ) :
    api.sign_internal_44 sk m rnd ⦃ r => ∃ σ', r = some σ' ∧ bytesA σ' = σ ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_internal_44_eq, hip]
  exact signInternalAPI_some hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m rnd B F σ hs

/-- **Algorithm 7, ML-DSA-44, κ budget exhausted.** If every one of the `kappaBudget` attempts is rejected
(`Sign.Exhausted`), the Rust `sign_internal_44` returns `none`. -/
theorem _root_.Proofs.sign_internal_44_correct_exhausted (sk : Array U8 2560#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd)) :
    api.sign_internal_44 sk m rnd ⦃ r => r = none ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_internal_44_eq, hip]
  exact signInternalAPI_exhausted hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m rnd F hex

/-- **Algorithm 7, ML-DSA-44, `none` only if the spec fails.** If `sign_internal_44` returns `none`, then for
every fuel `F` the spec's `Sign_internal` (budget `kappaBudget`) is `none` as well, and by `Sign.sign_none_cases`
that is a fuel failure or exhaustion. -/
theorem _root_.Proofs.sign_internal_44_none_only_if (sk : Array U8 2560#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (h : api.sign_internal_44 sk m rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign_internal_bounded Spec.ML_DSA_44 (kappaBudget Spec.ML_DSA_44) (bytesA sk) (bytes m) (bytesA rnd) F = none ∧
      (Proofs.Sign.pre Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd) = none ∨
        ∃ P, Proofs.Sign.pre Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd) = some P ∧
          (Proofs.Sign.loopRes Spec.ML_DSA_44 F P (kappaBudget Spec.ML_DSA_44) 0 = none ∨
           Proofs.Sign.loopRes Spec.ML_DSA_44 F P (kappaBudget Spec.ML_DSA_44) 0 = some none)) := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_internal_44_eq, hip] at h
  have h0 := signInternalAPI_none_only_if hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m rnd h F
  exact ⟨h0, (Proofs.Sign.sign_none_cases _ _ F _ _ _).mp h0⟩

/-- **Algorithm 8 (`Verify_internal`), ML-DSA-44.** If the spec returns `b`, the Rust `verify_internal_44`
returns `b`. -/
theorem _root_.Proofs.verify_internal_44_correct (pk : Array U8 1312#usize) (m : Slice U8)
    (sig : Array U8 2420#usize) (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b) :
    api.verify_internal_44 pk m sig ⦃ r => r = b ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verify_internal_44_eq, hip]
  exact verifyInternalAPI_spec hp _ _ pk m sig F b hs

/-- **Algorithm 2 (`Sign`), ML-DSA-44, `none` only if the spec fails.** If `|ctx| ≤ 255` and the Rust `sign_44`
returns `none` (`= ok none`), then for every fuel `F` the spec's `Sign` is `none` too, and it is one of the
spec's failure cases for `M′ = 0 ‖ |ctx| ‖ ctx ‖ M`: `ExpandA` ran out of fuel, some `SampleInBall` did, or the κ
budget was exhausted (`Sign.sign_none_cases`). Together with `sign_44_correct_ctx_long` (`|ctx| > 255` gives
`none` on both sides) this is the contrapositive of `sign_44_correct_some`: the Rust only returns `none` where
the spec does. What is not provable: that the fuel-failure cases make the Rust return `none` (it may
diverge there; the triples are total correctness). The exhaustion case is `sign_44_correct_exhausted`. -/
theorem _root_.Proofs.sign_44_none_only_if (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (h : api.sign_44 sk m ctx rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none ∧
      (255 < (bytes ctx).length ∨
        Proofs.Sign.pre Spec.ML_DSA_44 F (bytesA sk) ([0, UInt8.ofNat (bytes ctx).length] ++ bytes ctx ++ bytes m) (bytesA rnd) = none ∨
        ∃ P, Proofs.Sign.pre Spec.ML_DSA_44 F (bytesA sk) ([0, UInt8.ofNat (bytes ctx).length] ++ bytes ctx ++ bytes m) (bytesA rnd) = some P ∧
          (Proofs.Sign.loopRes Spec.ML_DSA_44 F P (kappaBudget Spec.ML_DSA_44) 0 = none ∨
           Proofs.Sign.loopRes Spec.ML_DSA_44 F P (kappaBudget Spec.ML_DSA_44) 0 = some none)) := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sign_44_eq, hip] at h
  have h0 := signAPI_none_spec hp _ _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_44.sigLen = 2420 by decide +kernel]; rfl) sk m ctx rnd h F
  exact ⟨h0, sign_none_decomp _ F _ _ _ _ h0⟩

/-! ### ML-DSA-65 -/

/-- **Algorithm 7 (`Sign_internal`), ML-DSA-65, success.** If the spec returns `σ` (for any budget `B`), the
Rust `sign_internal_65` returns `some σ'` with `σ'` holding the bytes `σ`. -/
theorem _root_.Proofs.sign_internal_65_correct_some (sk : Array U8 4032#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (B : Nat) (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign_internal_bounded Spec.ML_DSA_65 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ) :
    api.sign_internal_65 sk m rnd ⦃ r => ∃ σ', r = some σ' ∧ bytesA σ' = σ ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_internal_65_eq, hip]
  exact signInternalAPI_some hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m rnd B F σ hs

/-- **Algorithm 7, ML-DSA-65, κ budget exhausted.** If every one of the `kappaBudget` attempts is rejected
(`Sign.Exhausted`), the Rust `sign_internal_65` returns `none`. -/
theorem _root_.Proofs.sign_internal_65_correct_exhausted (sk : Array U8 4032#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd)) :
    api.sign_internal_65 sk m rnd ⦃ r => r = none ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_internal_65_eq, hip]
  exact signInternalAPI_exhausted hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m rnd F hex

/-- **Algorithm 7, ML-DSA-65, `none` only if the spec fails.** If `sign_internal_65` returns `none`, then for
every fuel `F` the spec's `Sign_internal` (budget `kappaBudget`) is `none` as well, and by `Sign.sign_none_cases`
that is a fuel failure or exhaustion. -/
theorem _root_.Proofs.sign_internal_65_none_only_if (sk : Array U8 4032#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (h : api.sign_internal_65 sk m rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign_internal_bounded Spec.ML_DSA_65 (kappaBudget Spec.ML_DSA_65) (bytesA sk) (bytes m) (bytesA rnd) F = none ∧
      (Proofs.Sign.pre Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd) = none ∨
        ∃ P, Proofs.Sign.pre Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd) = some P ∧
          (Proofs.Sign.loopRes Spec.ML_DSA_65 F P (kappaBudget Spec.ML_DSA_65) 0 = none ∨
           Proofs.Sign.loopRes Spec.ML_DSA_65 F P (kappaBudget Spec.ML_DSA_65) 0 = some none)) := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_internal_65_eq, hip] at h
  have h0 := signInternalAPI_none_only_if hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m rnd h F
  exact ⟨h0, (Proofs.Sign.sign_none_cases _ _ F _ _ _).mp h0⟩

/-- **Algorithm 8 (`Verify_internal`), ML-DSA-65.** If the spec returns `b`, the Rust `verify_internal_65`
returns `b`. -/
theorem _root_.Proofs.verify_internal_65_correct (pk : Array U8 1952#usize) (m : Slice U8)
    (sig : Array U8 3309#usize) (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b) :
    api.verify_internal_65 pk m sig ⦃ r => r = b ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verify_internal_65_eq, hip]
  exact verifyInternalAPI_spec hp _ _ pk m sig F b hs

/-- **Algorithm 2 (`Sign`), ML-DSA-65, `none` only if the spec fails.** If `|ctx| ≤ 255` and the Rust `sign_65`
returns `none` (`= ok none`), then for every fuel `F` the spec's `Sign` is `none` too, and it is one of the
spec's failure cases for `M′ = 0 ‖ |ctx| ‖ ctx ‖ M`: `ExpandA` ran out of fuel, some `SampleInBall` did, or the κ
budget was exhausted (`Sign.sign_none_cases`). Together with `sign_65_correct_ctx_long` (`|ctx| > 255` gives
`none` on both sides) this is the contrapositive of `sign_65_correct_some`: the Rust only returns `none` where
the spec does. What is not provable: that the fuel-failure cases make the Rust return `none` (it may
diverge there; the triples are total correctness). The exhaustion case is `sign_65_correct_exhausted`. -/
theorem _root_.Proofs.sign_65_none_only_if (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (h : api.sign_65 sk m ctx rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none ∧
      (255 < (bytes ctx).length ∨
        Proofs.Sign.pre Spec.ML_DSA_65 F (bytesA sk) ([0, UInt8.ofNat (bytes ctx).length] ++ bytes ctx ++ bytes m) (bytesA rnd) = none ∨
        ∃ P, Proofs.Sign.pre Spec.ML_DSA_65 F (bytesA sk) ([0, UInt8.ofNat (bytes ctx).length] ++ bytes ctx ++ bytes m) (bytesA rnd) = some P ∧
          (Proofs.Sign.loopRes Spec.ML_DSA_65 F P (kappaBudget Spec.ML_DSA_65) 0 = none ∨
           Proofs.Sign.loopRes Spec.ML_DSA_65 F P (kappaBudget Spec.ML_DSA_65) 0 = some none)) := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sign_65_eq, hip] at h
  have h0 := signAPI_none_spec hp _ _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_65.sigLen = 3309 by decide +kernel]; rfl) sk m ctx rnd h F
  exact ⟨h0, sign_none_decomp _ F _ _ _ _ h0⟩

/-! ### ML-DSA-87 -/

/-- **Algorithm 7 (`Sign_internal`), ML-DSA-87, success.** If the spec returns `σ` (for any budget `B`), the
Rust `sign_internal_87` returns `some σ'` with `σ'` holding the bytes `σ`. -/
theorem _root_.Proofs.sign_internal_87_correct_some (sk : Array U8 4896#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (B : Nat) (F : Spec.Fuel) (σ : List UInt8)
    (hs : Spec.Sign_internal_bounded Spec.ML_DSA_87 B (bytesA sk) (bytes m) (bytesA rnd) F = some σ) :
    api.sign_internal_87 sk m rnd ⦃ r => ∃ σ', r = some σ' ∧ bytesA σ' = σ ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_internal_87_eq, hip]
  exact signInternalAPI_some hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m rnd B F σ hs

/-- **Algorithm 7, ML-DSA-87, κ budget exhausted.** If every one of the `kappaBudget` attempts is rejected
(`Sign.Exhausted`), the Rust `sign_internal_87` returns `none`. -/
theorem _root_.Proofs.sign_internal_87_correct_exhausted (sk : Array U8 4896#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (F : Spec.Fuel)
    (hex : Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd)) :
    api.sign_internal_87 sk m rnd ⦃ r => r = none ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_internal_87_eq, hip]
  exact signInternalAPI_exhausted hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m rnd F hex

/-- **Algorithm 7, ML-DSA-87, `none` only if the spec fails.** If `sign_internal_87` returns `none`, then for
every fuel `F` the spec's `Sign_internal` (budget `kappaBudget`) is `none` as well, and by `Sign.sign_none_cases`
that is a fuel failure or exhaustion. -/
theorem _root_.Proofs.sign_internal_87_none_only_if (sk : Array U8 4896#usize) (m : Slice U8)
    (rnd : Array U8 32#usize) (h : api.sign_internal_87 sk m rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign_internal_bounded Spec.ML_DSA_87 (kappaBudget Spec.ML_DSA_87) (bytesA sk) (bytes m) (bytesA rnd) F = none ∧
      (Proofs.Sign.pre Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd) = none ∨
        ∃ P, Proofs.Sign.pre Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd) = some P ∧
          (Proofs.Sign.loopRes Spec.ML_DSA_87 F P (kappaBudget Spec.ML_DSA_87) 0 = none ∨
           Proofs.Sign.loopRes Spec.ML_DSA_87 F P (kappaBudget Spec.ML_DSA_87) 0 = some none)) := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_internal_87_eq, hip] at h
  have h0 := signInternalAPI_none_only_if hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m rnd h F
  exact ⟨h0, (Proofs.Sign.sign_none_cases _ _ F _ _ _).mp h0⟩

/-- **Algorithm 8 (`Verify_internal`), ML-DSA-87.** If the spec returns `b`, the Rust `verify_internal_87`
returns `b`. -/
theorem _root_.Proofs.verify_internal_87_correct (pk : Array U8 2592#usize) (m : Slice U8)
    (sig : Array U8 4627#usize) (F : Spec.Fuel) (b : Bool)
    (hs : Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b) :
    api.verify_internal_87 pk m sig ⦃ r => r = b ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verify_internal_87_eq, hip]
  exact verifyInternalAPI_spec hp _ _ pk m sig F b hs

/-- **Algorithm 2 (`Sign`), ML-DSA-87, `none` only if the spec fails.** If `|ctx| ≤ 255` and the Rust `sign_87`
returns `none` (`= ok none`), then for every fuel `F` the spec's `Sign` is `none` too, and it is one of the
spec's failure cases for `M′ = 0 ‖ |ctx| ‖ ctx ‖ M`: `ExpandA` ran out of fuel, some `SampleInBall` did, or the κ
budget was exhausted (`Sign.sign_none_cases`). Together with `sign_87_correct_ctx_long` (`|ctx| > 255` gives
`none` on both sides) this is the contrapositive of `sign_87_correct_some`: the Rust only returns `none` where
the spec does. What is not provable: that the fuel-failure cases make the Rust return `none` (it may
diverge there; the triples are total correctness). The exhaustion case is `sign_87_correct_exhausted`. -/
theorem _root_.Proofs.sign_87_none_only_if (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize)
    (h : api.sign_87 sk m ctx rnd = ok none) (F : Spec.Fuel) :
    Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = none ∧
      (255 < (bytes ctx).length ∨
        Proofs.Sign.pre Spec.ML_DSA_87 F (bytesA sk) ([0, UInt8.ofNat (bytes ctx).length] ++ bytes ctx ++ bytes m) (bytesA rnd) = none ∨
        ∃ P, Proofs.Sign.pre Spec.ML_DSA_87 F (bytesA sk) ([0, UInt8.ofNat (bytes ctx).length] ++ bytes ctx ++ bytes m) (bytesA rnd) = some P ∧
          (Proofs.Sign.loopRes Spec.ML_DSA_87 F P (kappaBudget Spec.ML_DSA_87) 0 = none ∨
           Proofs.Sign.loopRes Spec.ML_DSA_87 F P (kappaBudget Spec.ML_DSA_87) 0 = some none)) := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sign_87_eq, hip] at h
  have h0 := signAPI_none_spec hp _ _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl)
    (by rw [show Spec.ML_DSA_87.sigLen = 4627 by decide +kernel]; rfl) sk m ctx rnd h F
  exact ⟨h0, sign_none_decomp _ F _ _ _ _ h0⟩

end APIInternal

end Proofs
