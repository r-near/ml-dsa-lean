import Proofs.PartialSign
import Proofs.PartialKeyGen
import Proofs.PkFromSk
import Proofs.PreparedVerify
import Proofs.PreparedSign

/-!
# Divergence corollaries

`RustM` has exactly three outcomes: `ok`, `fail` and `div`. The `_exact` theorems of `PartialAPI.lean`,
`PartialKeyGen.lean`, `PartialSign.lean` and `PkFromSk.lean` say, for each public function: it never returns
`fail`; the spec returning a value at some fuel gives `ok`; and `ok` gives the spec returning that value at some
fuel. So the only other outcome, `div`, happens exactly when the spec returns no value at any fuel. This file
spells that out (`rustM_div_iff`) for ML-DSA-44, -65 and -87:

* `verify_NN_div_iff`, `verify_internal_NN_div_iff`: `div ↔ ∀ F b, Spec.Verify … F ≠ some b`. In FIPS 204 terms:
  the unbounded `ExpandA` or `SampleInBall` never terminates.
* `keygen_NN_div_iff`: `div ↔ ∀ F pk sk, Spec.KeyGen … F ≠ some (pk, sk)`.
* `sign_internal_NN_div_iff`: `div ↔` (the spec with the real budget `kappaBudget` returns no signature at any
  fuel) `∧` (at no fuel is it `Exhausted`). Sign's κ loop is bounded, so it cannot diverge by itself; the spec's
  `none` is either exhaustion (all attempts within sampler fuel and rejected: the Rust returns `none`, not
  `div`) or a sampler running out of fuel. So `div` happens exactly when, at every fuel, the spec's `none` is a
  sampler fuel failure (`ExpandA`, or `SampleInBall` in some attempt).
* `sign_NN_div_iff`: the same, with `|ctx| ≤ 255` additionally required (for `|ctx| > 255` the Rust returns
  `none`).
* `pk_from_sk_NN_div_iff`: `div ↔ ∀ F o, skConsistentR … F ≠ some o`, i.e. the range check passes and `ExpandA`
  of the stored `ρ` never terminates.
* Prepared keys (last section): `verify_prepared_NN_div_iff`, `verify_internal_prepared_NN_div_iff`,
  `sign_prepared_NN_div_iff`, `sign_internal_prepared_NN_div_iff` are the statements above for the key `pk` / `sk` the
  object was built from (`verifying_key_NN pk = ok vk`); `verifying_key_NN_div_iff` and `signing_key_NN_div_iff`:
  `div ↔ ∀ F A, ExpandA … F ρ ≠ some A`, with ρ from `pkDecode pk` (resp. `skDecode sk`).

No premises beyond the argument types.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-- **Divergence from exactness.** If `x` never fails, every spec value (the proposition `P`) yields an `ok`,
and every `ok` yields a spec value, then `x` diverges exactly when there is no spec value. -/
theorem rustM_div_iff {α : Type} (x : RustM α) (P : Prop) (hnf : ∀ e, x ≠ .fail e)
    (h1 : P → ∃ a, x = ok a) (h2 : ∀ a, x = ok a → P) : x = .div ↔ ¬ P := by
  constructor
  · intro hx hP
    obtain ⟨a, ha⟩ := h1 hP
    rw [hx] at ha
    cases ha
  · intro hnP
    cases hx : x with
    | ok a => exact absurd (h2 a hx) hnP
    | fail e => exact absurd hx (hnf e)
    | div => rfl

/-! ## ML-DSA-44 -/

/-- **`verify_44` diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_44_div_iff (pk : Array U8 1312#usize) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_44 pk m ctx sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F ≠ some b := by
  obtain ⟨hnf, h1, h2⟩ := verify_44_exact pk m ctx sig
  have := rustM_div_iff (api.verify_44 pk m ctx sig)
    (∃ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) hnf
    (fun ⟨F, b, h⟩ => ⟨b, h1 F b h⟩) (fun b hb => let ⟨F, h⟩ := h2 b hb; ⟨F, b, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`verify_internal_44` diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_internal_44_div_iff (pk : Array U8 1312#usize) (m : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_internal_44 pk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  obtain ⟨hnf, h1, h2⟩ := verify_internal_44_exact pk m sig
  have := rustM_div_iff (api.verify_internal_44 pk m sig)
    (∃ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F = some b) hnf
    (fun ⟨F, b, h⟩ => ⟨b, h1 F b h⟩) (fun b hb => let ⟨F, h⟩ := h2 b hb; ⟨F, b, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`keygen_44` diverges iff the spec returns no key pair at any fuel.** -/
theorem keygen_44_div_iff (ξ : Array U8 32#usize) :
    api.keygen_44 ξ = .div ↔
      ∀ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F ≠ some (pk, sk) := by
  obtain ⟨hnf, h1, h2⟩ := keygen_44_exact ξ
  have := rustM_div_iff (api.keygen_44 ξ)
    (∃ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_44 (bytesA ξ) F = some (pk, sk)) hnf
    (fun ⟨F, pk, sk, h⟩ => let ⟨r, hr, _⟩ := h1 F pk sk h; ⟨r, hr⟩)
    (fun ⟨pk, sk⟩ hr => let ⟨F, h⟩ := h2 pk sk hr; ⟨F, _, _, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`sign_internal_44` diverges iff, at every fuel, the spec returns no signature and is not `Exhausted`**
(so its `none` is always a sampler running out of fuel; the κ loop itself is bounded). -/
theorem sign_internal_44_div_iff (sk : Array U8 2560#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_44 sk m rnd = .div ↔
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd) := by
  obtain ⟨hnf, h1, h2, h3⟩ := sign_internal_44_exact sk m rnd
  have := rustM_div_iff (api.sign_internal_44 sk m rnd)
    ((∃ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytesA rnd) F = some σ) ∨
      ∃ F : Spec.Fuel, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd)) hnf
    (fun h => by
      rcases h with ⟨F, σ, h⟩ | hE
      · obtain ⟨σ', hσ', _⟩ := h1 _ F σ h
        exact ⟨_, hσ'⟩
      · exact ⟨_, h3.mpr hE⟩)
    (fun a ha => by
      cases a with
      | some σ => exact Or.inl (let ⟨F, h⟩ := h2 σ ha; ⟨F, _, h⟩)
      | none => exact Or.inr (h3.mp ha))
  rw [this]
  simp only [not_or, not_exists, ne_eq]

/-- **`sign_44` diverges iff `|ctx| ≤ 255` and, at every fuel, the spec returns no signature and is not
`Exhausted`** for M′ = 0 ‖ |ctx| ‖ ctx ‖ M. -/
theorem sign_44_div_iff (sk : Array U8 2560#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_44 sk m ctx rnd = .div ↔
      ¬ 255 < (bytes ctx).length ∧
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd) := by
  obtain ⟨hnf, h1, h2, h3⟩ := sign_44_exact sk m ctx rnd
  have := rustM_div_iff (api.sign_44 sk m ctx rnd)
    ((∃ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) ∨
      255 < (bytes ctx).length ∨
      ∃ F : Spec.Fuel, Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) hnf
    (fun h => by
      rcases h with ⟨F, σ, h⟩ | hE
      · obtain ⟨σ', hσ', _⟩ := h1 F σ h
        exact ⟨_, hσ'⟩
      · exact ⟨_, h3.mpr hE⟩)
    (fun a ha => by
      cases a with
      | some σ => exact Or.inl (let ⟨F, h⟩ := h2 σ ha; ⟨F, _, h⟩)
      | none => exact Or.inr (h3.mp ha))
  rw [this]
  simp only [not_or, not_exists, ne_eq]
  exact and_left_comm

/-- **`pk_from_sk_44` diverges iff the range check passes and `ExpandA` of the stored ρ returns `none` at every
fuel** (`skConsistentR … F ≠ some o` for all `F`, `o`). -/
theorem pk_from_sk_44_div_iff (sk : Array U8 2560#usize) :
    api.pk_from_sk_44 sk = .div ↔
      ∀ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_44 (bytesA sk) F ≠ some o := by
  obtain ⟨hnf, h1, h2⟩ := pk_from_sk_44_exact sk
  have := rustM_div_iff (api.pk_from_sk_44 sk)
    (∃ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_44 (bytesA sk) F = some o) hnf
    (fun ⟨F, o, h⟩ => let ⟨r, hr, _⟩ := h1 F o h; ⟨r, hr⟩)
    (fun r hr => let ⟨F, h⟩ := h2 r hr; ⟨F, _, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-! ## ML-DSA-65 -/

/-- **`verify_65` diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_65_div_iff (pk : Array U8 1952#usize) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_65 pk m ctx sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F ≠ some b := by
  obtain ⟨hnf, h1, h2⟩ := verify_65_exact pk m ctx sig
  have := rustM_div_iff (api.verify_65 pk m ctx sig)
    (∃ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) hnf
    (fun ⟨F, b, h⟩ => ⟨b, h1 F b h⟩) (fun b hb => let ⟨F, h⟩ := h2 b hb; ⟨F, b, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`verify_internal_65` diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_internal_65_div_iff (pk : Array U8 1952#usize) (m : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_internal_65 pk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  obtain ⟨hnf, h1, h2⟩ := verify_internal_65_exact pk m sig
  have := rustM_div_iff (api.verify_internal_65 pk m sig)
    (∃ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F = some b) hnf
    (fun ⟨F, b, h⟩ => ⟨b, h1 F b h⟩) (fun b hb => let ⟨F, h⟩ := h2 b hb; ⟨F, b, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`keygen_65` diverges iff the spec returns no key pair at any fuel.** -/
theorem keygen_65_div_iff (ξ : Array U8 32#usize) :
    api.keygen_65 ξ = .div ↔
      ∀ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F ≠ some (pk, sk) := by
  obtain ⟨hnf, h1, h2⟩ := keygen_65_exact ξ
  have := rustM_div_iff (api.keygen_65 ξ)
    (∃ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_65 (bytesA ξ) F = some (pk, sk)) hnf
    (fun ⟨F, pk, sk, h⟩ => let ⟨r, hr, _⟩ := h1 F pk sk h; ⟨r, hr⟩)
    (fun ⟨pk, sk⟩ hr => let ⟨F, h⟩ := h2 pk sk hr; ⟨F, _, _, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`sign_internal_65` diverges iff, at every fuel, the spec returns no signature and is not `Exhausted`**
(so its `none` is always a sampler running out of fuel; the κ loop itself is bounded). -/
theorem sign_internal_65_div_iff (sk : Array U8 4032#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_65 sk m rnd = .div ↔
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd) := by
  obtain ⟨hnf, h1, h2, h3⟩ := sign_internal_65_exact sk m rnd
  have := rustM_div_iff (api.sign_internal_65 sk m rnd)
    ((∃ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytesA rnd) F = some σ) ∨
      ∃ F : Spec.Fuel, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd)) hnf
    (fun h => by
      rcases h with ⟨F, σ, h⟩ | hE
      · obtain ⟨σ', hσ', _⟩ := h1 _ F σ h
        exact ⟨_, hσ'⟩
      · exact ⟨_, h3.mpr hE⟩)
    (fun a ha => by
      cases a with
      | some σ => exact Or.inl (let ⟨F, h⟩ := h2 σ ha; ⟨F, _, h⟩)
      | none => exact Or.inr (h3.mp ha))
  rw [this]
  simp only [not_or, not_exists, ne_eq]

/-- **`sign_65` diverges iff `|ctx| ≤ 255` and, at every fuel, the spec returns no signature and is not
`Exhausted`** for M′ = 0 ‖ |ctx| ‖ ctx ‖ M. -/
theorem sign_65_div_iff (sk : Array U8 4032#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_65 sk m ctx rnd = .div ↔
      ¬ 255 < (bytes ctx).length ∧
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd) := by
  obtain ⟨hnf, h1, h2, h3⟩ := sign_65_exact sk m ctx rnd
  have := rustM_div_iff (api.sign_65 sk m ctx rnd)
    ((∃ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) ∨
      255 < (bytes ctx).length ∨
      ∃ F : Spec.Fuel, Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) hnf
    (fun h => by
      rcases h with ⟨F, σ, h⟩ | hE
      · obtain ⟨σ', hσ', _⟩ := h1 F σ h
        exact ⟨_, hσ'⟩
      · exact ⟨_, h3.mpr hE⟩)
    (fun a ha => by
      cases a with
      | some σ => exact Or.inl (let ⟨F, h⟩ := h2 σ ha; ⟨F, _, h⟩)
      | none => exact Or.inr (h3.mp ha))
  rw [this]
  simp only [not_or, not_exists, ne_eq]
  exact and_left_comm

/-- **`pk_from_sk_65` diverges iff the range check passes and `ExpandA` of the stored ρ returns `none` at every
fuel** (`skConsistentR … F ≠ some o` for all `F`, `o`). -/
theorem pk_from_sk_65_div_iff (sk : Array U8 4032#usize) :
    api.pk_from_sk_65 sk = .div ↔
      ∀ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_65 (bytesA sk) F ≠ some o := by
  obtain ⟨hnf, h1, h2⟩ := pk_from_sk_65_exact sk
  have := rustM_div_iff (api.pk_from_sk_65 sk)
    (∃ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_65 (bytesA sk) F = some o) hnf
    (fun ⟨F, o, h⟩ => let ⟨r, hr, _⟩ := h1 F o h; ⟨r, hr⟩)
    (fun r hr => let ⟨F, h⟩ := h2 r hr; ⟨F, _, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-! ## ML-DSA-87 -/

/-- **`verify_87` diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_87_div_iff (pk : Array U8 2592#usize) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_87 pk m ctx sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F ≠ some b := by
  obtain ⟨hnf, h1, h2⟩ := verify_87_exact pk m ctx sig
  have := rustM_div_iff (api.verify_87 pk m ctx sig)
    (∃ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F = some b) hnf
    (fun ⟨F, b, h⟩ => ⟨b, h1 F b h⟩) (fun b hb => let ⟨F, h⟩ := h2 b hb; ⟨F, b, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`verify_internal_87` diverges iff the spec returns no verdict at any fuel.** -/
theorem verify_internal_87_div_iff (pk : Array U8 2592#usize) (m : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_internal_87 pk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  obtain ⟨hnf, h1, h2⟩ := verify_internal_87_exact pk m sig
  have := rustM_div_iff (api.verify_internal_87 pk m sig)
    (∃ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F = some b) hnf
    (fun ⟨F, b, h⟩ => ⟨b, h1 F b h⟩) (fun b hb => let ⟨F, h⟩ := h2 b hb; ⟨F, b, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`keygen_87` diverges iff the spec returns no key pair at any fuel.** -/
theorem keygen_87_div_iff (ξ : Array U8 32#usize) :
    api.keygen_87 ξ = .div ↔
      ∀ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F ≠ some (pk, sk) := by
  obtain ⟨hnf, h1, h2⟩ := keygen_87_exact ξ
  have := rustM_div_iff (api.keygen_87 ξ)
    (∃ (F : Spec.Fuel) (pk sk : List UInt8), Spec.KeyGen Spec.ML_DSA_87 (bytesA ξ) F = some (pk, sk)) hnf
    (fun ⟨F, pk, sk, h⟩ => let ⟨r, hr, _⟩ := h1 F pk sk h; ⟨r, hr⟩)
    (fun ⟨pk, sk⟩ hr => let ⟨F, h⟩ := h2 pk sk hr; ⟨F, _, _, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- **`sign_internal_87` diverges iff, at every fuel, the spec returns no signature and is not `Exhausted`**
(so its `none` is always a sampler running out of fuel; the κ loop itself is bounded). -/
theorem sign_internal_87_div_iff (sk : Array U8 4896#usize) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_87 sk m rnd = .div ↔
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd) := by
  obtain ⟨hnf, h1, h2, h3⟩ := sign_internal_87_exact sk m rnd
  have := rustM_div_iff (api.sign_internal_87 sk m rnd)
    ((∃ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytesA rnd) F = some σ) ∨
      ∃ F : Spec.Fuel, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd)) hnf
    (fun h => by
      rcases h with ⟨F, σ, h⟩ | hE
      · obtain ⟨σ', hσ', _⟩ := h1 _ F σ h
        exact ⟨_, hσ'⟩
      · exact ⟨_, h3.mpr hE⟩)
    (fun a ha => by
      cases a with
      | some σ => exact Or.inl (let ⟨F, h⟩ := h2 σ ha; ⟨F, _, h⟩)
      | none => exact Or.inr (h3.mp ha))
  rw [this]
  simp only [not_or, not_exists, ne_eq]

/-- **`sign_87` diverges iff `|ctx| ≤ 255` and, at every fuel, the spec returns no signature and is not
`Exhausted`** for M′ = 0 ‖ |ctx| ‖ ctx ‖ M. -/
theorem sign_87_div_iff (sk : Array U8 4896#usize) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_87 sk m ctx rnd = .div ↔
      ¬ 255 < (bytes ctx).length ∧
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd) := by
  obtain ⟨hnf, h1, h2, h3⟩ := sign_87_exact sk m ctx rnd
  have := rustM_div_iff (api.sign_87 sk m ctx rnd)
    ((∃ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F = some σ) ∨
      255 < (bytes ctx).length ∨
      ∃ F : Spec.Fuel, Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd)) hnf
    (fun h => by
      rcases h with ⟨F, σ, h⟩ | hE
      · obtain ⟨σ', hσ', _⟩ := h1 F σ h
        exact ⟨_, hσ'⟩
      · exact ⟨_, h3.mpr hE⟩)
    (fun a ha => by
      cases a with
      | some σ => exact Or.inl (let ⟨F, h⟩ := h2 σ ha; ⟨F, _, h⟩)
      | none => exact Or.inr (h3.mp ha))
  rw [this]
  simp only [not_or, not_exists, ne_eq]
  exact and_left_comm

/-- **`pk_from_sk_87` diverges iff the range check passes and `ExpandA` of the stored ρ returns `none` at every
fuel** (`skConsistentR … F ≠ some o` for all `F`, `o`). -/
theorem pk_from_sk_87_div_iff (sk : Array U8 4896#usize) :
    api.pk_from_sk_87 sk = .div ↔
      ∀ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_87 (bytesA sk) F ≠ some o := by
  obtain ⟨hnf, h1, h2⟩ := pk_from_sk_87_exact sk
  have := rustM_div_iff (api.pk_from_sk_87 sk)
    (∃ (F : Nat) (o : Option (List UInt8)), skConsistentR Spec.ML_DSA_87 (bytesA sk) F = some o) hnf
    (fun ⟨F, o, h⟩ => let ⟨r, hr, _⟩ := h1 F o h; ⟨r, hr⟩)
    (fun r hr => let ⟨F, h⟩ := h2 r hr; ⟨F, _, h⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-! ## Prepared keys

The prepared-key API (`verifying_key_NN`, `verify_prepared_NN`, `verify_internal_prepared_NN`, `signing_key_NN`,
`sign_prepared_NN`, `sign_internal_prepared_NN`; `Proofs/PreparedVerify.lean`, `Proofs/PreparedSign.lean`).

* The four prepared functions per set do whatever the unprepared function does for the key the object was built from
  (`*_prepared_NN_eq`, which includes divergence), so their `div_iff` statements are those of the unprepared
  functions, under `verifying_key_NN pk = ok vk` (resp. `signing_key_NN sk = ok ssk`), about the same `pk` / `sk`.
* The constructors never fail (`*_not_fail`). `verifying_key_NN pk` diverges iff `ExpandA(ρ)` for `(ρ, t₁) =
  pkDecode pk` returns `none` at every fuel, i.e. iff FIPS 204's unbounded rejection sampler for Â never completes.
  `signing_key_NN sk` diverges iff `ExpandA(ρ)` for the ρ that `skDecode sk` yields returns `none` at every fuel.
  Nothing else in them can diverge: pkDecode, skDecode, the NTTs and the hashes are bounded loops, and a malformed
  key byte string has no failure mode (every string of the right length decodes).
-/

/-- A bind that returns a function of the first result diverges iff the first computation does. -/
theorem bind_ok_eq_div {α β : Type} (x : RustM α) (f : α → β) :
    (x >>= fun a => ok (f a)) = (.div : RustM β) ↔ x = (.div : RustM α) := by
  cases x <;> simp

/-- `prepare_vk` diverges iff `ExpandA` of the ρ in the public key returns `none` at every fuel. -/
theorem prepare_vk_div_iff {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n : Usize) (hn : n.val = sp.pkLen) (pk : Array U8 n) :
    verify.prepare_vk K L (Array.to_slice pk) = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k),
        Spec.ExpandA sp F (Spec.pkDecode sp (bytesA pk)).1 ≠ some A := by
  have hpkLen : (Array.to_slice pk).val.length = 32 + 320 * sp.k := by
    have := pk.property
    have h2 := KeyGen.pkLen_eq sp hp.params.d_eq
    simp only [Array.to_slice]
    omega
  have hpart := prepare_vk_partial' hp n hn pk
  have := rustM_div_iff (verify.prepare_vk K L (Array.to_slice pk))
    (∃ (F : Nat) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k),
      Spec.ExpandA sp F (Spec.pkDecode sp (bytesA pk)).1 = some A)
    (dspec_not_fail hpart)
    (fun ⟨F, A, hA⟩ => by
      have h := Proofs.Verify.prepare_vk_spec hp (Array.to_slice pk) hpkLen A F (by rw [bytes_to_slice]; exact hA)
      obtain ⟨r, hr, _⟩ := WP.spec_imp_exists h
      exact ⟨r, hr⟩)
    (fun vk hvk => by
      obtain ⟨A, F, hA, _⟩ := WP.dspec_imp_forall hpart vk hvk
      exact ⟨F, A, hA⟩)
  rw [this]
  simp only [not_exists, ne_eq]

/-- `prepSk` (the key half of Sign) diverges iff `ExpandA` of the ρ in the secret key returns `none` at every fuel. -/
theorem prepSk_div_iff {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n : Usize) (hn : n.val = sp.skLen) (sk : Array U8 n) :
    Proofs.Sign.prepSk K L ip (Array.to_slice sk) = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k),
        Spec.ExpandA sp F (Spec.skDecode sp (bytesA sk)).1 ≠ some A := by
  have hsk : (Array.to_slice sk).length = sp.skLen := by
    have := sk.property
    show (Array.to_slice sk).val.length = sp.skLen
    simp only [Array.to_slice]
    omega
  have hpart := prepare_sk_partial' hp n hn sk
  have := rustM_div_iff (Proofs.Sign.prepSk K L ip (Array.to_slice sk))
    (∃ (F : Nat) (A : Vector (Vector Spec.Poly sp.ℓ) sp.k),
      Spec.ExpandA sp F (Spec.skDecode sp (bytesA sk)).1 = some A)
    (dspec_not_fail hpart)
    (fun ⟨F, A, hA⟩ => by
      rcases hd : Spec.skDecode sp (bytes (Array.to_slice sk)) with ⟨ρ, Kk, tr, s₁, s₂, t₀⟩
      rw [bytes_to_slice] at hd
      rw [hd] at hA
      have h := Proofs.Sign.prepare_sk_spec hp (Array.to_slice sk) hsk ρ Kk tr s₁ s₂ t₀
        (by rw [bytes_to_slice]; exact hd) A F hA
      obtain ⟨r, hr, _⟩ := WP.spec_imp_exists h
      exact ⟨r, hr⟩)
    (fun ps hps => by
      obtain ⟨ρ, Kk, tr, s₁, s₂, t₀, A, F, hd, hA, _⟩ := WP.dspec_imp_forall hpart ps hps
      refine ⟨F, A, ?_⟩
      rw [hd]
      exact hA)
  rw [this]
  simp only [not_exists, ne_eq]

/-! ### ML-DSA-44 prepared keys -/

theorem verifying_key_44_eq_bind (pk : Array U8 1312#usize) :
    api.verifying_key_44 pk = (verify.prepare_vk 4#usize 4#usize (Array.to_slice pk) >>= fun ps =>
      ok ({ inner := ps } : api.VerifyingKey44)) := by
  rw [verifying_key_44_def]
  simp only [lift, Std.bind_tc_ok]

/-- **`verifying_key_44` diverges iff `ExpandA` of the ρ in `pk` returns `none` at every fuel** (the SHAKE output
never completes Â). -/
theorem verifying_key_44_div_iff (pk : Array U8 1312#usize) :
    api.verifying_key_44 pk = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly Spec.ML_DSA_44.ℓ) Spec.ML_DSA_44.k),
        Spec.ExpandA Spec.ML_DSA_44 F (Spec.pkDecode Spec.ML_DSA_44 (bytesA pk)).1 ≠ some A := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [verifying_key_44_eq_bind]
  exact (bind_ok_eq_div _ _).trans (prepare_vk_div_iff hp 1312#usize (by decide) pk)

/-- **`signing_key_44` diverges iff `ExpandA` of the ρ in `skDecode sk` returns `none` at every fuel.** -/
theorem signing_key_44_div_iff (sk : Array U8 2560#usize) :
    api.signing_key_44 sk = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly Spec.ML_DSA_44.ℓ) Spec.ML_DSA_44.k),
        Spec.ExpandA Spec.ML_DSA_44 F (Spec.skDecode Spec.ML_DSA_44 (bytesA sk)).1 ≠ some A := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [signing_key_44_eq, hip]
  simp only [Std.bind_tc_ok]
  exact (bind_ok_eq_div _ _).trans (prepSk_div_iff hp 2560#usize (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl) sk)

/-- **`verify_prepared_44` diverges iff the spec returns no verdict at any fuel**, for the key `vk` built from `pk`. -/
theorem verify_prepared_44_div_iff (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (hvk : api.verifying_key_44 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_prepared_44 vk m ctx sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F ≠ some b := by
  rw [verify_prepared_44_eq pk vk hvk m ctx sig]
  exact verify_44_div_iff pk m ctx sig

/-- **`verify_internal_prepared_44` diverges iff the spec returns no verdict at any fuel**, for the key `vk` built
from `pk`. -/
theorem verify_internal_prepared_44_div_iff (pk : Array U8 1312#usize) (vk : api.VerifyingKey44)
    (hvk : api.verifying_key_44 pk = ok vk) (m : Slice U8) (sig : Array U8 2420#usize) :
    api.verify_internal_prepared_44 vk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_44 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  rw [verify_internal_prepared_44_eq pk vk hvk m sig]
  exact verify_internal_44_div_iff pk m sig

/-- **`sign_prepared_44` diverges iff `|ctx| ≤ 255` and, at every fuel, the spec returns no signature and is not
`Exhausted`**, for the key `ssk` built from `sk` (see `sign_44_div_iff`). -/
theorem sign_prepared_44_div_iff (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (hssk : api.signing_key_44 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_44 ssk m ctx rnd = .div ↔
      ¬ 255 < (bytes ctx).length ∧
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd) := by
  rw [sign_prepared_44_eq sk ssk hssk m ctx rnd]
  exact sign_44_div_iff sk m ctx rnd

/-- **`sign_internal_prepared_44` diverges iff, at every fuel, the spec returns no signature and is not
`Exhausted`**, for the key `ssk` built from `sk` (see `sign_internal_44_div_iff`). -/
theorem sign_internal_prepared_44_div_iff (sk : Array U8 2560#usize) (ssk : api.SigningKey44)
    (hssk : api.signing_key_44 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_44 ssk m rnd = .div ↔
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_44 (bytesA sk) (bytes m) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_44 F (bytesA sk) (bytes m) (bytesA rnd) := by
  rw [sign_internal_prepared_44_eq sk ssk hssk m rnd]
  exact sign_internal_44_div_iff sk m rnd

/-! ### ML-DSA-65 prepared keys -/

theorem verifying_key_65_eq_bind (pk : Array U8 1952#usize) :
    api.verifying_key_65 pk = (verify.prepare_vk 6#usize 5#usize (Array.to_slice pk) >>= fun ps =>
      ok ({ inner := ps } : api.VerifyingKey65)) := by
  rw [verifying_key_65_def]
  simp only [lift, Std.bind_tc_ok]

/-- **`verifying_key_65` diverges iff `ExpandA` of the ρ in `pk` returns `none` at every fuel** (the SHAKE output
never completes Â). -/
theorem verifying_key_65_div_iff (pk : Array U8 1952#usize) :
    api.verifying_key_65 pk = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly Spec.ML_DSA_65.ℓ) Spec.ML_DSA_65.k),
        Spec.ExpandA Spec.ML_DSA_65 F (Spec.pkDecode Spec.ML_DSA_65 (bytesA pk)).1 ≠ some A := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [verifying_key_65_eq_bind]
  exact (bind_ok_eq_div _ _).trans (prepare_vk_div_iff hp 1952#usize (by decide) pk)

/-- **`signing_key_65` diverges iff `ExpandA` of the ρ in `skDecode sk` returns `none` at every fuel.** -/
theorem signing_key_65_div_iff (sk : Array U8 4032#usize) :
    api.signing_key_65 sk = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly Spec.ML_DSA_65.ℓ) Spec.ML_DSA_65.k),
        Spec.ExpandA Spec.ML_DSA_65 F (Spec.skDecode Spec.ML_DSA_65 (bytesA sk)).1 ≠ some A := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [signing_key_65_eq, hip]
  simp only [Std.bind_tc_ok]
  exact (bind_ok_eq_div _ _).trans (prepSk_div_iff hp 4032#usize (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl) sk)

/-- **`verify_prepared_65` diverges iff the spec returns no verdict at any fuel**, for the key `vk` built from `pk`. -/
theorem verify_prepared_65_div_iff (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (hvk : api.verifying_key_65 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_prepared_65 vk m ctx sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F ≠ some b := by
  rw [verify_prepared_65_eq pk vk hvk m ctx sig]
  exact verify_65_div_iff pk m ctx sig

/-- **`verify_internal_prepared_65` diverges iff the spec returns no verdict at any fuel**, for the key `vk` built
from `pk`. -/
theorem verify_internal_prepared_65_div_iff (pk : Array U8 1952#usize) (vk : api.VerifyingKey65)
    (hvk : api.verifying_key_65 pk = ok vk) (m : Slice U8) (sig : Array U8 3309#usize) :
    api.verify_internal_prepared_65 vk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_65 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  rw [verify_internal_prepared_65_eq pk vk hvk m sig]
  exact verify_internal_65_div_iff pk m sig

/-- **`sign_prepared_65` diverges iff `|ctx| ≤ 255` and, at every fuel, the spec returns no signature and is not
`Exhausted`**, for the key `ssk` built from `sk` (see `sign_65_div_iff`). -/
theorem sign_prepared_65_div_iff (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (hssk : api.signing_key_65 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_65 ssk m ctx rnd = .div ↔
      ¬ 255 < (bytes ctx).length ∧
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd) := by
  rw [sign_prepared_65_eq sk ssk hssk m ctx rnd]
  exact sign_65_div_iff sk m ctx rnd

/-- **`sign_internal_prepared_65` diverges iff, at every fuel, the spec returns no signature and is not
`Exhausted`**, for the key `ssk` built from `sk` (see `sign_internal_65_div_iff`). -/
theorem sign_internal_prepared_65_div_iff (sk : Array U8 4032#usize) (ssk : api.SigningKey65)
    (hssk : api.signing_key_65 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_65 ssk m rnd = .div ↔
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_65 (bytesA sk) (bytes m) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_65 F (bytesA sk) (bytes m) (bytesA rnd) := by
  rw [sign_internal_prepared_65_eq sk ssk hssk m rnd]
  exact sign_internal_65_div_iff sk m rnd

/-! ### ML-DSA-87 prepared keys -/

theorem verifying_key_87_eq_bind (pk : Array U8 2592#usize) :
    api.verifying_key_87 pk = (verify.prepare_vk 8#usize 7#usize (Array.to_slice pk) >>= fun ps =>
      ok ({ inner := ps } : api.VerifyingKey87)) := by
  rw [verifying_key_87_def]
  simp only [lift, Std.bind_tc_ok]

/-- **`verifying_key_87` diverges iff `ExpandA` of the ρ in `pk` returns `none` at every fuel** (the SHAKE output
never completes Â). -/
theorem verifying_key_87_div_iff (pk : Array U8 2592#usize) :
    api.verifying_key_87 pk = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly Spec.ML_DSA_87.ℓ) Spec.ML_DSA_87.k),
        Spec.ExpandA Spec.ML_DSA_87 F (Spec.pkDecode Spec.ML_DSA_87 (bytesA pk)).1 ≠ some A := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [verifying_key_87_eq_bind]
  exact (bind_ok_eq_div _ _).trans (prepare_vk_div_iff hp 2592#usize (by decide) pk)

/-- **`signing_key_87` diverges iff `ExpandA` of the ρ in `skDecode sk` returns `none` at every fuel.** -/
theorem signing_key_87_div_iff (sk : Array U8 4896#usize) :
    api.signing_key_87 sk = .div ↔
      ∀ (F : Nat) (A : Vector (Vector Spec.Poly Spec.ML_DSA_87.ℓ) Spec.ML_DSA_87.k),
        Spec.ExpandA Spec.ML_DSA_87 F (Spec.skDecode Spec.ML_DSA_87 (bytesA sk)).1 ≠ some A := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [signing_key_87_eq, hip]
  simp only [Std.bind_tc_ok]
  exact (bind_ok_eq_div _ _).trans (prepSk_div_iff hp 4896#usize (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl) sk)

/-- **`verify_prepared_87` diverges iff the spec returns no verdict at any fuel**, for the key `vk` built from `pk`. -/
theorem verify_prepared_87_div_iff (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (hvk : api.verifying_key_87 pk = ok vk) (m ctx : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_prepared_87 vk m ctx sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) (bytes ctx) F ≠ some b := by
  rw [verify_prepared_87_eq pk vk hvk m ctx sig]
  exact verify_87_div_iff pk m ctx sig

/-- **`verify_internal_prepared_87` diverges iff the spec returns no verdict at any fuel**, for the key `vk` built
from `pk`. -/
theorem verify_internal_prepared_87_div_iff (pk : Array U8 2592#usize) (vk : api.VerifyingKey87)
    (hvk : api.verifying_key_87 pk = ok vk) (m : Slice U8) (sig : Array U8 4627#usize) :
    api.verify_internal_prepared_87 vk m sig = .div ↔
      ∀ (F : Spec.Fuel) (b : Bool), Spec.Verify_internal Spec.ML_DSA_87 (bytesA pk) (bytes m) (bytesA sig) F ≠ some b := by
  rw [verify_internal_prepared_87_eq pk vk hvk m sig]
  exact verify_internal_87_div_iff pk m sig

/-- **`sign_prepared_87` diverges iff `|ctx| ≤ 255` and, at every fuel, the spec returns no signature and is not
`Exhausted`**, for the key `ssk` built from `sk` (see `sign_87_div_iff`). -/
theorem sign_prepared_87_div_iff (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (hssk : api.signing_key_87 sk = ok ssk) (m ctx : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_prepared_87 ssk m ctx rnd = .div ↔
      ¬ 255 < (bytes ctx).length ∧
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytes ctx) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk)
        (IntegerToBytes 0 1 ++ IntegerToBytes (bytes ctx).length 1 ++ bytes ctx ++ bytes m) (bytesA rnd) := by
  rw [sign_prepared_87_eq sk ssk hssk m ctx rnd]
  exact sign_87_div_iff sk m ctx rnd

/-- **`sign_internal_prepared_87` diverges iff, at every fuel, the spec returns no signature and is not
`Exhausted`**, for the key `ssk` built from `sk` (see `sign_internal_87_div_iff`). -/
theorem sign_internal_prepared_87_div_iff (sk : Array U8 4896#usize) (ssk : api.SigningKey87)
    (hssk : api.signing_key_87 sk = ok ssk) (m : Slice U8) (rnd : Array U8 32#usize) :
    api.sign_internal_prepared_87 ssk m rnd = .div ↔
      (∀ (F : Spec.Fuel) (σ : List UInt8),
        Spec.Sign_internal Spec.ML_DSA_87 (bytesA sk) (bytes m) (bytesA rnd) F ≠ some σ) ∧
      ∀ F : Spec.Fuel, ¬ Proofs.Sign.Exhausted Spec.ML_DSA_87 F (bytesA sk) (bytes m) (bytesA rnd) := by
  rw [sign_internal_prepared_87_eq sk ssk hssk m rnd]
  exact sign_internal_87_div_iff sk m rnd

end Proofs
