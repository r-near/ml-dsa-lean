import Proofs.Correctness
import Proofs.EncodeKeys
import Proofs.SigCodec
import Proofs.StdParams

/-!
# The optional secret-key check `sk_is_well_formed_NN`

FIPS 204 Algorithm 25 (skDecode) notes that the decoded `s₁` and `s₂` "may lie outside `[−η, η]` if the input is
malformed" and leaves `Sign` undefined there. `Spec.Sign` stays FIPS-literal (it signs with such a key, see
ISSUES E-4), so the range condition lives here, in `Proofs`, not in `Spec`:

* `PolyInEta η w`: every coefficient of the integer polynomial `w` lies in `[−η, η]`.
* `SkWF sp sk`: every coefficient of the `s₁` and `s₂` that `Spec.skDecode sp sk` returns does.
  (`t₀` is not part of it: its 13-bit field decodes to `4096 − z` with `z < 2¹³`, always within `[−4095, 4096]`.)
* `skWellFormed sp sk : Bool` is its decision.

Results:

* `sk_is_well_formed_NN_correct`: for every `sk : [u8; skLen]`, the extracted `api.sk_is_well_formed_NN sk` returns
  `skWellFormed Spec.ML_DSA_NN (bytesA sk)`. There is no premise beyond the array type (no sampler is involved).
* `skWellFormed_keygen`: the secret key of every `Spec.KeyGen_internal` result is well-formed (the premise is the
  spec's `some`, exactly as for `keygen_internal_correct`).
* `skWellFormed_zero_44` / `skWellFormed_bad_44`: concrete kernel witnesses that the predicate is satisfiable and
  falsifiable (the all-zero key; a key whose first `s₁` field is `7`, i.e. coefficient `−5`).

The Rust (`src/encode.rs`) decodes each of the `ℓ + k` η-blocks with `unpack_signed` (the same function
`sk_decode` uses) and checks the canonical residue `x` with `x ≤ η ∨ q ≤ x + η`; the proof shows that this is
`−η ≤ BitUnpack ≤ η` because `BitUnpack` coefficients lie in `(η − 2^c, η]` with `2^c ≤ 16`.
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## The spec-side predicate -/

/-- Every coefficient of the integer polynomial `w` lies in `[−η, η]`. -/
def PolyInEta (η : Nat) (w : RPoly) : Prop :=
  ∀ (j : Nat) (hj : j < 256), -(η : Int) ≤ w[j] ∧ w[j] ≤ η

instance (η : Nat) (w : RPoly) : Decidable (PolyInEta η w) := by
  unfold PolyInEta; infer_instance

/-- Every coefficient of the `s₁` and `s₂` returned by `Spec.skDecode` lies in `[−η, η]`. -/
def SkWF (sp : Spec.Params) (sk : List UInt8) : Prop :=
  (∀ (i : Nat) (hi : i < sp.ℓ), PolyInEta sp.η (Spec.skDecode sp sk).2.2.2.1[i]) ∧
  (∀ (i : Nat) (hi : i < sp.k), PolyInEta sp.η (Spec.skDecode sp sk).2.2.2.2.1[i])

instance (sp : Spec.Params) (sk : List UInt8) : Decidable (SkWF sp sk) := by
  unfold SkWF; infer_instance

/-- The decision of `SkWF`: `true` iff `s₁` and `s₂` of `skDecode sp sk` are within `[−η, η]`. -/
def skWellFormed (sp : Spec.Params) (sk : List UInt8) : Bool := decide (SkWF sp sk)

theorem skWellFormed_eq_true_iff (sp : Spec.Params) (sk : List UInt8) :
    skWellFormed sp sk = true ↔ SkWF sp sk := by
  unfold skWellFormed; exact decide_eq_true_iff

/-- The η-block `j` of `sk` (blocks `0..ℓ` are `s₁`, blocks `ℓ..ℓ+k` are `s₂`) decodes into `[−η, η]`. -/
def BlockOK (sp : Spec.Params) (sk : List UInt8) (j : Nat) : Prop :=
  PolyInEta sp.η (BitUnpack (slice sk (128 + j * (32 * bitlen (2 * sp.η))) (32 * bitlen (2 * sp.η))) sp.η sp.η)

theorem SkWF_iff_blocks (sp : Spec.Params) (sk : List UInt8) :
    SkWF sp sk ↔ ∀ j, j < sp.ℓ + sp.k → BlockOK sp sk j := by
  constructor
  · rintro ⟨h1, h2⟩ j hj
    by_cases hjl : j < sp.ℓ
    · have := h1 j hjl
      rw [skDecode_s1 sp sk j hjl] at this
      exact this
    · have hjk : j - sp.ℓ < sp.k := by omega
      have := h2 (j - sp.ℓ) hjk
      rw [skDecode_s2 sp sk (j - sp.ℓ) hjk] at this
      have hle : sp.ℓ ≤ j := by omega
      have e : 128 + sp.ℓ * (32 * bitlen (2 * sp.η)) + (j - sp.ℓ) * (32 * bitlen (2 * sp.η)) =
          128 + j * (32 * bitlen (2 * sp.η)) := by
        rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_cancel' hle]
      rw [e] at this
      exact this
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [skDecode_s1 sp sk i hi]
      exact h i (by omega)
    · rw [skDecode_s2 sp sk i hi]
      have := h (sp.ℓ + i) (by omega)
      unfold BlockOK at this
      have e : 128 + (sp.ℓ + i) * (32 * bitlen (2 * sp.η)) =
          128 + sp.ℓ * (32 * bitlen (2 * sp.η)) + i * (32 * bitlen (2 * sp.η)) := by
        ring
      rw [e] at this
      exact this

/-! ## Residues versus integers -/

/-- A canonical residue `x` stands for an integer in `[−η, η]` (for small `η` and a small integer). -/
def OkU (η x : Nat) : Prop := x ≤ η ∨ Spec.q ≤ x + η

/-- `OkU` of entry `j` of `w`; entries past the end count as `0` (true), which lets loop invariants quantify over
every `j` without bound proofs. -/
def OkAt (w : Array U32 256#usize) (η j : Nat) : Prop :=
  OkU η ((w.val[j]?.map fun x => x.val).getD 0)

theorem okAt_of_lt (w : Array U32 256#usize) (η j : Nat) (hj : j < 256) :
    OkAt w η j ↔ OkU η (w.val[j]'(by rw [len256 w]; exact hj)).val := by
  unfold OkAt
  rw [List.getElem?_eq_getElem (by rw [len256 w]; exact hj)]
  rfl

/-- For `w` representing the integer polynomial `V` whose coefficients lie in `(η − 16, η]` (`η ≤ 4`), the
residue test `OkU` is exactly `−η ≤ V[j] ≤ η`. -/
theorem okAt_iff (w : Array U32 256#usize) (V : RPoly) (hV : ReprInt w V) (η : Nat) (hη : η ≤ 4)
    (hr : ∀ (j : Nat) (hj : j < 256), (η : Int) - 16 < V[j] ∧ V[j] ≤ η) (j : Nat) (hj : j < 256) :
    OkAt w η j ↔ (-(η : Int) ≤ V[j] ∧ V[j] ≤ η) := by
  rw [okAt_of_lt w η j hj]
  have hc := hV.coeff j hj
  have hlt := canon_get hV.1 (show j < w.val.length by rw [len256 w]; exact hj)
  have hrj := hr j hj
  unfold OkU
  have hq : Spec.q = 8380417 := rfl
  rw [hq]
  rw [hq] at hc
  omega

/-! ## One polynomial: `poly_in_eta` -/

theorem poly_in_eta_loop_spec (w : Array U32 256#usize) (eta : U32) (hw : Canonical w)
    (hη : eta.val < 1000) (ok1 : Bool) (i : Usize) (hi : i.val ≤ 256) :
    encode.poly_in_eta_loop w eta ok1 i ⦃ r =>
      (r = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < 256 → OkAt w eta.val j) ⦄ := by
  have hQ : field.Q.val = 8380417 := by first | rfl | decide | simp [field.Q]
  have hqq : Spec.q = 8380417 := rfl
  unfold encode.poly_in_eta_loop
  apply loop.spec_decr_nat
    (fun (p : Bool × Usize) => 256 - p.2.val)
    (fun p => i.val ≤ p.2.val ∧ p.2.val ≤ 256 ∧
      (p.1 = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < p.2.val → OkAt w eta.val j))
  · rintro ⟨ok, i2⟩ ⟨h0, h1, h2⟩
    dsimp only at h0 h1 h2
    simp only [encode.poly_in_eta_loop.body]
    split
    · rename_i hlt
      have hlt' : i2.val < 256 := by scalar_tac
      have hl : i2.val < w.val.length := by rw [len256 w]; exact hlt'
      have hxq : (w.val[i2.val]'hl).val < Spec.q := canon_get hw hl
      have hOk : OkAt w eta.val i2.val ↔ OkU eta.val (w.val[i2.val]'hl).val := okAt_of_lt w eta.val i2.val hlt'
      -- extending the invariant by entry `i2`
      have hgood : OkAt w eta.val i2.val →
          (ok = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < i2.val + 1 → OkAt w eta.val j) := by
        intro hok
        rw [h2]
        constructor
        · rintro ⟨a, b⟩
          refine ⟨a, fun j hj1 hj2 => ?_⟩
          by_cases e : j = i2.val
          · subst e; exact hok
          · exact b j hj1 (by omega)
        · rintro ⟨a, b⟩
          exact ⟨a, fun j hj1 hj2 => b j hj1 (by omega)⟩
      have hbad : ¬ OkAt w eta.val i2.val →
          (false = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < i2.val + 1 → OkAt w eta.val j) := by
        intro hok
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨-, b⟩
          exact absurd (b i2.val h0 (by omega)) hok
      step with arr_index_spec w i2 hl as ⟨x, hx⟩
      have hxv : x.val = (w.val[i2.val]'hl).val := by rw [hx]
      have hxq' : x.val < Spec.q := by rw [hxv]; exact hxq
      by_cases hgt : x > eta
      · simp only [hgt, if_true]
        have hgt' : eta.val < x.val := by scalar_tac
        step as ⟨s, hs⟩
        by_cases hlq : s < field.Q
        · simp only [hlq, if_true]
          have hlq' : s.val < Spec.q := by scalar_tac
          have hnok : ¬ OkAt w eta.val i2.val := by
            rw [hOk, ← hxv]
            unfold OkU
            omega
          step as ⟨i3, hi3⟩
          refine ⟨by omega, by omega, by rw [hi3]; exact hbad hnok, by omega⟩
        · simp only [hlq, if_false]
          have hlq' : Spec.q ≤ s.val := by scalar_tac
          have hok : OkAt w eta.val i2.val := by
            rw [hOk, ← hxv]
            unfold OkU
            omega
          step as ⟨i3, hi3⟩
          refine ⟨by omega, by omega, by rw [hi3]; exact hgood hok, by omega⟩
      · simp only [hgt, if_false]
        have hgt' : x.val ≤ eta.val := by scalar_tac
        have hok : OkAt w eta.val i2.val := by
          rw [hOk, ← hxv]
          unfold OkU
          omega
        step as ⟨i3, hi3⟩
        refine ⟨by omega, by omega, by rw [hi3]; exact hgood hok, by omega⟩
    · rename_i hlt
      simp only [WP.spec_ok]
      have : i2.val = 256 := by scalar_tac
      rw [this] at h2
      exact h2
  · exact ⟨le_refl _, hi, fun h => ⟨h, fun j hj1 hj2 => by dsimp only at hj2; omega⟩, fun h => h.1⟩

/-- The decoded η-block lies in `[−η, η]`: `eta_block_in_range` decides `PolyInEta η (BitUnpack (bytes v) η η)`. -/
theorem eta_block_in_range_spec {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (v : Slice U8) (hlen : v.val.length = 32 * ip.eta_bits.val) :
    encode.eta_block_in_range ip v ⦃ r =>
      (r = true ↔ PolyInEta sp.η (BitUnpack (bytes v) sp.η sp.η)) ⦄ := by
  have hv := hp.valid
  have hη4 : sp.η = 2 ∨ sp.η = 4 := hp.params.eta
  have hb : ip.eta.val < Spec.q := by rw [hv.eta]; simp only [Spec.q]; omega
  have hc : ip.eta_bits.val = bitlen (sp.η + ip.eta.val) := by rw [hv.eta_bits, hv.eta, two_mul]
  have hbits : ip.eta_bits.val ≤ 22 := by
    rw [hv.eta_bits]; rcases hη4 with h | h <;> rw [h] <;> decide +kernel
  unfold encode.eta_block_in_range
  refine WP.spec_bind (unpack_signed_spec v ip.eta sp.η ip.eta_bits hb hc hbits hlen) ?_
  intro w hw
  unfold encode.poly_in_eta
  refine WP.spec_mono (poly_in_eta_loop_spec w ip.eta hw.1 (by rw [hv.eta]; omega) true 0#usize (by simp)) ?_
  intro r hr
  have hr' : (r = true ↔ ∀ j, j < 256 → OkAt w ip.eta.val j) := by
    rw [hr]; simp
  rw [hr', hv.eta]
  have hbl : 2 ^ bitlen (sp.η + ip.eta.val) ≤ 16 := by
    rw [hv.eta]; rcases hη4 with h | h <;> rw [h] <;> decide +kernel
  have hrange : ∀ (j : Nat) (hj : j < 256), (ip.eta.val : Int) - 16 < (BitUnpack (bytes v) sp.η ip.eta.val)[j] ∧
      (BitUnpack (bytes v) sp.η ip.eta.val)[j] ≤ ip.eta.val := by
    intro j hj
    have := BitUnpack_range (bytes v) sp.η ip.eta.val j hj
    have hh : (2 : Int) ^ bitlen (sp.η + ip.eta.val) ≤ 16 := by exact_mod_cast hbl
    constructor <;> omega
  have hη' : ip.eta.val ≤ 4 := by rw [hv.eta]; omega
  rw [hv.eta] at hw hrange hη'
  constructor
  · intro h j hj
    have := (okAt_iff w _ hw sp.η (by omega) hrange j hj).mp (h j hj)
    exact this
  · intro h j hj
    exact (okAt_iff w _ hw sp.η (by omega) hrange j hj).mpr (h j hj)

/-! ## All blocks: `sk_is_well_formed` -/

theorem sk_is_well_formed_loop_spec {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk : Slice U8) (hL : sk.val.length = sp.skLen)
    (n : Usize) (hn : n.val = 32 * bitlen (2 * sp.η)) (ok1 : Bool) (o i : Usize)
    (hi : i.val ≤ sp.ℓ + sp.k) (ho : o.val = 128 + i.val * n.val) :
    encode.sk_is_well_formed_loop K L ip.k ip.l ip.eta ip.eta_bits ip.tau ip.beta ip.gamma1 ip.gamma1_bits
      ip.gamma2 ip.w1_bits ip.omega ip.c_tilde_len ip.two_gamma2_shift ip.two_gamma2_mult
      ip.two_gamma2_div_mult sk n o ok1 i ⦃ r =>
      (r = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < sp.ℓ + sp.k → BlockOK sp (bytes sk) j) ⦄ := by
  have hv := hp.valid
  have hLen : sk.val.length = 128 + (sp.ℓ + sp.k) * n.val + sp.k * 416 := by
    rw [hL, skLen_eq sp hv.d_eq, hn]
  have hkl := hp.params.kl_lt
  have hnb : n.val = 32 * ip.eta_bits.val := by rw [hn, hv.eta_bits]
  unfold encode.sk_is_well_formed_loop
  apply loop.spec_decr_nat
    (fun (p : Usize × Bool × Usize) => sp.ℓ + sp.k - p.2.2.val)
    (fun p => i.val ≤ p.2.2.val ∧ p.2.2.val ≤ sp.ℓ + sp.k ∧ p.1.val = 128 + p.2.2.val * n.val ∧
      (p.2.1 = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < p.2.2.val → BlockOK sp (bytes sk) j))
  · rintro ⟨o2, ok, i2⟩ ⟨h0, h1, h2, h3⟩
    dsimp only at h0 h1 h2 h3
    simp only [encode.sk_is_well_formed_loop.body]
    have hLv := hv.L_eq
    have hKv := hv.K_eq
    step as ⟨i16, hi16⟩
    split
    · rename_i hlt
      have hik : i2.val < sp.ℓ + sp.k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ (sp.ℓ + sp.k) * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := sk.property
      have hbd : o2.val + n.val ≤ sk.val.length := by omega
      step as ⟨i17, hi17⟩
      step as ⟨s, hs1, hs2⟩
      have hslen : s.val.length = 32 * ip.eta_bits.val := by
        have : s.val.length = i17.val - o2.val := hs2
        rw [this, hi17]; omega
      have hsb0 := bytes_slice_of sk s o2.val i17.val n.val hs1 (by rw [hi17]; omega)
      have hsb : bytes s = slice (bytes sk) (128 + i2.val * n.val) n.val := by rw [hsb0, h2]
      refine WP.spec_bind (eta_block_in_range_spec hp s hslen) ?_
      intro b hb
      rw [hsb, hn] at hb
      have hblk : BlockOK sp (bytes sk) i2.val ↔ b = true := by
        unfold BlockOK
        exact hb.symm
      have hgood : BlockOK sp (bytes sk) i2.val →
          (ok = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < i2.val + 1 → BlockOK sp (bytes sk) j) := by
        intro hok
        rw [h3]
        constructor
        · rintro ⟨a, c⟩
          refine ⟨a, fun j hj1 hj2 => ?_⟩
          by_cases ej : j = i2.val
          · subst ej; exact hok
          · exact c j hj1 (by omega)
        · rintro ⟨a, c⟩
          exact ⟨a, fun j hj1 hj2 => c j hj1 (by omega)⟩
      have hbad : ¬ BlockOK sp (bytes sk) i2.val →
          (false = true ↔ ok1 = true ∧ ∀ j, i.val ≤ j → j < i2.val + 1 → BlockOK sp (bytes sk) j) := by
        intro hok
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨-, c⟩
          exact absurd (c i2.val h0 (by omega)) hok
      by_cases hbt : b = true
      · simp only [hbt, if_true]
        step as ⟨i18, hi18⟩
        refine ⟨by omega, by omega, by rw [hi18]; omega, by rw [hi18]; exact hgood (hblk.mpr hbt), by omega⟩
      · simp only [hbt, Bool.false_eq_true, if_false]
        step as ⟨i18, hi18⟩
        refine ⟨by omega, by omega, by rw [hi18]; omega, by rw [hi18]; exact hbad (fun h => hbt (hblk.mp h)), by omega⟩
    · rename_i hlt
      simp only [WP.spec_ok]
      have : i2.val = sp.ℓ + sp.k := by scalar_tac
      rw [this] at h3
      exact h3
  · exact ⟨le_refl _, hi, ho, fun h => ⟨h, fun j hj1 hj2 => by dsimp only at hj2; omega⟩, fun h => h.1⟩

/-- **`sk_is_well_formed` decides `skWellFormed`**, for every `sk` of length `skLen`. -/
theorem sk_is_well_formed_spec {K L : Usize} {ip : Impl.params.Params} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (sk : Slice U8) (hL : sk.val.length = sp.skLen) :
    encode.sk_is_well_formed K L ip sk ⦃ r => r = skWellFormed sp (bytes sk) ⦄ := by
  have hv := hp.valid
  have hbits : ip.eta_bits.val ≤ 22 := by
    rw [hv.eta_bits]; rcases hp.params.eta with h | h <;> rw [h] <;> decide +kernel
  unfold encode.sk_is_well_formed
  step as ⟨n, hn⟩
  have hnv : n.val = 32 * bitlen (2 * sp.η) := by
    have h1 := hv.eta_bits
    scalar_tac
  refine WP.spec_mono (sk_is_well_formed_loop_spec hp sk hL n hnv true 128#usize 0#usize (by simp) (by simp)) ?_
  intro r hr
  have hiff : r = true ↔ SkWF sp (bytes sk) := by
    rw [hr, SkWF_iff_blocks]
    simp
  by_cases hr1 : r = true
  · rw [hr1]
    exact ((skWellFormed_eq_true_iff _ _).mpr (hiff.mp hr1)).symm
  · have hr0 : r = false := by simpa using hr1
    rw [hr0]
    have : ¬ SkWF sp (bytes sk) := fun h => hr1 (hiff.mpr h)
    unfold skWellFormed
    exact (decide_eq_false this).symm

/-! ## The API wrappers -/

/-- The body of `api.sk_is_well_formed_NN`, generic in the array size and the parameter record. -/
def skWellFormedAPI (n : Usize) (K L : Usize) (P : RustM params.Params) (sk : Array U8 n) : RustM Bool := do
  let p ← P
  let s ← lift (Array.to_slice sk)
  encode.sk_is_well_formed K L p s

theorem sk_is_well_formed_44_eq :
    api.sk_is_well_formed_44 = skWellFormedAPI 2560#usize 4#usize 4#usize params.ML_DSA_44 := rfl
theorem sk_is_well_formed_65_eq :
    api.sk_is_well_formed_65 = skWellFormedAPI 4032#usize 6#usize 5#usize params.ML_DSA_65 := rfl
theorem sk_is_well_formed_87_eq :
    api.sk_is_well_formed_87 = skWellFormedAPI 4896#usize 8#usize 7#usize params.ML_DSA_87 := rfl

theorem skWellFormedAPI_spec {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (hp : Params.Std ip K L sp) (n : Usize) (hn : n.val = sp.skLen) (sk : Array U8 n) :
    skWellFormedAPI n K L (ok ip) sk ⦃ r => r = skWellFormed sp (bytesA sk) ⦄ := by
  unfold skWellFormedAPI
  simp only [Std.bind_tc_ok]
  step*
  have hbs : bytes s = bytesA sk := by rw [s_post, bytes_to_slice]
  have hls : s.val.length = sp.skLen := by
    have := congrArg List.length hbs
    simp only [bytes_length, bytesA_length] at this
    rw [this, hn]
  refine WP.spec_mono (sk_is_well_formed_spec hp s hls) ?_
  intro r hr
  rw [hr, hbs]

/-- **`api.sk_is_well_formed_44` is `skWellFormed Spec.ML_DSA_44`** on every secret key: the Rust returns `true`
iff every `s₁`, `s₂` coefficient of `skDecode sk` lies in `[−η, η]`. No premise beyond the array type. -/
theorem sk_is_well_formed_44_correct (sk : Array U8 2560#usize) :
    api.sk_is_well_formed_44 sk ⦃ r => r = skWellFormed Spec.ML_DSA_44 (bytesA sk) ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_44_std
  rw [sk_is_well_formed_44_eq, hip]
  exact skWellFormedAPI_spec hp _ (by rw [show Spec.ML_DSA_44.skLen = 2560 by decide +kernel]; rfl) sk

/-- **`api.sk_is_well_formed_65` is `skWellFormed Spec.ML_DSA_65`** on every secret key. -/
theorem sk_is_well_formed_65_correct (sk : Array U8 4032#usize) :
    api.sk_is_well_formed_65 sk ⦃ r => r = skWellFormed Spec.ML_DSA_65 (bytesA sk) ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_65_std
  rw [sk_is_well_formed_65_eq, hip]
  exact skWellFormedAPI_spec hp _ (by rw [show Spec.ML_DSA_65.skLen = 4032 by decide +kernel]; rfl) sk

/-- **`api.sk_is_well_formed_87` is `skWellFormed Spec.ML_DSA_87`** on every secret key. -/
theorem sk_is_well_formed_87_correct (sk : Array U8 4896#usize) :
    api.sk_is_well_formed_87 sk ⦃ r => r = skWellFormed Spec.ML_DSA_87 (bytesA sk) ⦄ := by
  obtain ⟨ip, hip, hp⟩ := ML_DSA_87_std
  rw [sk_is_well_formed_87_eq, hip]
  exact skWellFormedAPI_spec hp _ (by rw [show Spec.ML_DSA_87.skLen = 4896 by decide +kernel]; rfl) sk

/-! ## Meaning: honest keys are well-formed, and the predicate is neither trivial nor empty -/

/-- **Keys produced by `Spec.KeyGen_internal` are well-formed**: `s₁` and `s₂` of the honest secret key come from
`RejBoundedPoly`, so `‖s₁‖∞, ‖s₂‖∞ ≤ η`, and `skDecode` returns them unchanged (`skDecode_skEncode`). The premise is
the spec's `some`, as in `keygen_internal_correct`. -/
theorem skWellFormed_keygen {sp : Spec.Params} (hp : StdParams sp) (F : Spec.Fuel) (ξ pk sk : List UInt8)
    (hk : Spec.KeyGen_internal sp ξ F = some (pk, sk)) : skWellFormed sp sk = true := by
  obtain ⟨ρ, K, tr, A, s₁, s₂, -, hn1, hn2, hdec, -, -⟩ := keygen_facts hp F ξ pk sk hk
  rw [skWellFormed_eq_true_iff]
  have hb1 : ∀ (i : Nat) (hi : i < sp.ℓ) (j : Nat) (hj : j < 256), (s₁[i])[j].natAbs ≤ sp.η :=
    fun i hi j hj => ((Corr.infNorm_vec_le_iff s₁[i] sp.η).mp ((Corr.infNorm_vec_le_iff s₁ sp.η).mp hn1 i hi) j hj)
  have hb2 : ∀ (i : Nat) (hi : i < sp.k) (j : Nat) (hj : j < 256), (s₂[i])[j].natAbs ≤ sp.η :=
    fun i hi j hj => ((Corr.infNorm_vec_le_iff s₂[i] sp.η).mp ((Corr.infNorm_vec_le_iff s₂ sp.η).mp hn2 i hi) j hj)
  unfold SkWF
  rw [hdec]
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · intro j hj
    have := hb1 i hi j hj
    have := Int.natAbs_eq (s₁[i][j])
    dsimp only
    omega
  · intro j hj
    have := hb2 i hi j hj
    have := Int.natAbs_eq (s₂[i][j])
    dsimp only
    omega

/-- Satisfiable: the all-zero ML-DSA-44 key (every field `z = 0`, i.e. coefficient `+η`) is well-formed. -/
theorem skWellFormed_zero_44 : skWellFormed Spec.ML_DSA_44 (List.replicate 2560 0) = true := by
  decide +kernel

/-- Falsifiable: setting the first `s₁` field (bits 0..2 of byte 128) to `7` gives coefficient `2 - 7 = -5`,
outside `[−2, 2]`. -/
theorem skWellFormed_bad_44 :
    skWellFormed Spec.ML_DSA_44 (List.replicate 128 0 ++ [7] ++ List.replicate 2431 0) = false := by
  decide +kernel

end Proofs
