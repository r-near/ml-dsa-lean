import Proofs.PartialSign
import Proofs.PartialKeyGen
import Proofs.PkFromSk

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

end Proofs
