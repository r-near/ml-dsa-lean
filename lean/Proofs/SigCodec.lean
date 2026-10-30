import Proofs.Hint
import Proofs.EncodeKeys

/-!
# sigEncode / sigDecode (FIPS 204, Algorithms 26 and 27)

`sig_encode_spec` and `sig_decode_spec` relate `Impl.encode.sig_encode` / `sig_decode` to `Spec.sigEncode` /
`Spec.sigDecode`.

* `sig_decode_spec` holds for every byte string of length `sp.sigLen` (it runs on attacker data): it returns `none`
  exactly when the spec does (a malformed hint), and otherwise `c̃` (the first `λ/4` bytes of the 64-byte buffer, the
  rest being zero), `z` and `h` denote the spec's. It also gives the coefficient range of `z`,
  `-γ₁ + 1 ≤ z ≤ γ₁`, which is what Verify's norm check needs (`|z| ≤ (q-1)/2`).
* `sig_encode_spec` takes `z` with coefficients in `[-γ₁ + 1, γ₁]` and a hint of weight at most `ω`.
  `sig_encode_signed_spec` restates it for the way Sign calls it: `z` canonical (`< q`) with `z mod± q` of
  absolute value `< γ₁ - β` (so `Poly.modPM` of the residues is the integer value).

Premise `StdSig sp`: `γ₁ ∈ {2^17, 2^19}` and `λ/4 ≤ 64` (the size of the `c̃` buffer). `Params.Valid` alone
does not pin them; the three standard parameter sets satisfy it (`stdSig_44/65/87`).
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl
open HintAux

/-- The signature-specific parameter premise: `γ₁ ∈ {2^17, 2^19}`, `λ/4 ≤ 64`. -/
def StdSig (sp : Spec.Params) : Prop := (sp.γ₁ = 2 ^ 17 ∨ sp.γ₁ = 2 ^ 19) ∧ sp.lam / 4 ≤ 64

theorem stdSig_44 : StdSig Spec.ML_DSA_44 := ⟨Or.inl (by decide +kernel), by decide +kernel⟩
theorem stdSig_65 : StdSig Spec.ML_DSA_65 := ⟨Or.inr (by decide +kernel), by decide +kernel⟩
theorem stdSig_87 : StdSig Spec.ML_DSA_87 := ⟨Or.inr (by decide +kernel), by decide +kernel⟩

theorem StdSig.bitlen_eq {sp : Spec.Params} (h : StdSig sp) :
    bitlen (sp.γ₁ - 1 + sp.γ₁) = 1 + bitlen (sp.γ₁ - 1) ∧ sp.γ₁ - 1 + sp.γ₁ < 2 ^ (1 + bitlen (sp.γ₁ - 1)) ∧
    (1 + bitlen (sp.γ₁ - 1) = 18 ∨ 1 + bitlen (sp.γ₁ - 1) = 20) ∧
    2 ^ (1 + bitlen (sp.γ₁ - 1)) = 2 * sp.γ₁ := by
  rcases h.1 with e | e <;> rw [e] <;> decide +kernel

/-! ## The spec side as concatenations / pointwise -/

theorem sigEncode_eq (p : Params) (c : List UInt8) (z : Vector RPoly p.ℓ) (h : Vector HintPoly p.k) :
    sigEncode p c z h = c ++ ((List.range' 0 p.ℓ).map fun i => BitPack z[i]! (p.γ₁ - 1) p.γ₁).flatten ++
      HintBitPack p h := by
  unfold sigEncode
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]


/-! ## `HintBitPack` has `ω + k` bytes -/

theorem packRow_size (row : HintPoly) (st : MProd Nat (Array UInt8)) :
    (packRow row st).snd.size = st.snd.size := by
  unfold packRow
  suffices H : ∀ (l : List Nat) (st : MProd Nat (Array UInt8)),
      (l.foldl (fun b a => packRowF row a b) st).snd.size = st.snd.size from H _ _
  intro l
  induction l with
  | nil => intro st; rfl
  | cons a l ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih]
    unfold packRowF
    split <;> simp

theorem packModel_size (sp : Params) (h : Vector HintPoly sp.k) :
    (packModel sp h).length = sp.ω + sp.k := by
  unfold packModel
  suffices H : ∀ (l : List Nat) (st : MProd Nat (Array UInt8)),
      (l.foldl (fun b i => packRowsF sp.ω h i b) st).snd.size = st.snd.size by
    rw [Array.length_toList, H]; simp
  intro l
  induction l with
  | nil => intro st; rfl
  | cons a l ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih]
    unfold packRowsF
    simp [packRow_size]

theorem HintBitPack_length (sp : Params) (h : Vector HintPoly sp.k) :
    (HintBitPack sp h).length = sp.ω + sp.k := by
  rw [pack_eq]; exact packModel_size sp h

/-! ## `sig_encode` -/

/-- The `c̃` copy loop of `sig_encode`: `out[0..λ/4) ← c̃`. -/
theorem sig_encode_loop0_spec (ip : Impl.params.Params) (ct : Slice U8)
    (hct : ct.val.length = ip.c_tilde_len.val) (out0 : Slice U8) (hL : ip.c_tilde_len.val ≤ out0.val.length)
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

/-- The block loop of `sig_encode`: blocks `BitPack v[t] a b` at `λ/4 + t·n`. -/
theorem sig_encode_loop1_spec {L : Usize} (ip : Impl.params.Params) (bb : U32) (c : Usize) (ea : Nat)
    (hb : bb.val < Spec.q) (hab : ea + bb.val < Spec.q) (hc : c.val = bitlen (ea + bb.val)) (n : Usize)
    (hn : n.val = 32 * c.val) (k : Nat) (z : Array (Array U32 256#usize) L) (v : Vector RPoly k)
    (hv : ReprIntVec z v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256,
      -(ea : Int) ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (bb.val : Int))
    (pre : List UInt8) (hpre : pre.length = ip.c_tilde_len.val)
    (out0 : Slice U8) (hL : ip.c_tilde_len.val + k * n.val ≤ out0.val.length) (i2 : Usize) (hi2 : i2.val ≤ k)
    (hinv : (bytes out0).take (ip.c_tilde_len.val + i2.val * n.val) =
      pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) i2.val) :
    encode.sig_encode_loop1 ip bb c z out0 n i2 ⦃ r => r.val.length = out0.val.length ∧
      (bytes r).take (ip.c_tilde_len.val + k * n.val) =
        pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) k ⦄ := by
  have hKk := hv.len
  have hFlen : ∀ t : Nat, (Spec.BitPack v[t]! ea bb.val).length = n.val := fun t => by
    rw [BitPack_length, ← hc, hn]
  unfold encode.sig_encode_loop1
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => k - p.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.val ≤ k ∧
      (bytes p.1).take (ip.c_tilde_len.val + p.2.val * n.val) =
        pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) p.2.val)
  · rintro ⟨out, i2⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.sig_encode_loop1.body]
    split
    · rename_i hi
      have hik : i2.val < k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := out.property
      step*
      refine WP.spec_bind (pack_signed_spec _ (v[i2.val]'hik) ?_ bb ea c s hb hab hc (hrng _ hik) ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i7.val - i4.val := s_post2
        rw [this, i7_post, i4_post, i6_post, i5_post, i3_post]; omega
      · intro s2 hs2
        step*
        have hs1' : bytes s2 = Spec.BitPack v[i2.val]! ea bb.val := by rw [hs2, vec_getElem!_eq v _ hik]
        obtain ⟨b1, b2⟩ := block_write_step out s2 index_mut_back i4 i7 ip.c_tilde_len.val n.val i2.val pre
          (fun (t : Nat) => Spec.BitPack v[t]! ea bb.val) hFlen hpre (by rw [i4_post, i3_post])
          (by rw [i7_post, i6_post, i5_post]) s_post3 hs1' h3 (by omega)
        refine ⟨by rw [b1]; exact h1, by omega, ?_, by omega⟩
        show List.take (ip.c_tilde_len.val + i5.val * n.val) (bytes (index_mut_back s2)) = _
        rw [i5_post]
        exact b2
    · rename_i hi
      have hi' : i2.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      exact ⟨h1, h3⟩
  · exact ⟨rfl, hi2, hinv⟩

/-- **`sig_encode` is `sigEncode`** (Algorithm 26): `z` stores the integer vector `zv` with coefficients in
`[-γ₁ + 1, γ₁]` (`ReprIntVec`), `h` a hint of weight at most `ω`, `c̃` has `λ/4` bytes and `out` has `sigLen`. -/
theorem sig_encode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hs : StdSig sp) (ct : Slice U8) (hct : ct.length = sp.lam / 4)
    (z : Array (Array U32 256#usize) L) (zv : Vector RPoly sp.ℓ) (hz : ReprIntVec z zv)
    (hzr : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.γ₁ : Int) + 1 ≤ (zv[i]'hi)[j]'hj ∧ (zv[i]'hi)[j]'hj ≤ (sp.γ₁ : Int))
    (h : Array (Array Bool 256#usize) K) (hv : Vector HintPoly sp.k) (hh : ReprHintVec h hv)
    (hw : HintWeight hv ≤ sp.ω) (out : Slice U8) (hout : out.length = sp.sigLen) :
    encode.sig_encode ip ct z h out ⦃ out' => bytes out' = Spec.sigEncode sp (bytes ct) zv hv ⦄ := by
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
  have hct' : ct.val.length = ip.c_tilde_len.val := by rw [hcl]; exact hct
  refine WP.spec_bind (sig_encode_loop0_spec ip ct hct' out (by omega) out 0#usize (by simp) rfl
    (by intro k; simp)) ?_
  rintro out1 ⟨hl1, hp1⟩
  have hgb : ip.gamma1_bits.val ≤ 20 := by rw [hp.gamma1_bits]; omega
  step as ⟨n, n_post⟩
  have hnv : n.val = 32 * (1 + bitlen (sp.γ₁ - 1)) := by rw [n_post, hp.gamma1_bits]
  have hLn : L.val * n.val = sp.ℓ * n.val := by rw [hp.L_eq]
  have hlenb := out.property
  have houtn : out.val.length = ip.c_tilde_len.val + sp.ℓ * n.val + (sp.ω + sp.k) := by rw [hout', hnv, hcl]
  have hpre : (bytes ct).length = ip.c_tilde_len.val := by simpa using hct'
  have hprefix : (bytes out1).take (ip.c_tilde_len.val + 0 * n.val) = bytes ct ++ flat (fun t =>
      Spec.BitPack zv[t]! (sp.γ₁ - 1) ip.gamma1.val) 0 := by
    rw [flat_zero, List.append_nil, Nat.zero_mul, Nat.add_zero]
    exact take_of_pointwise out1 (bytes ct) _ hpre (by omega) _ (fun k => by rw [hp1 k])
  refine WP.spec_bind (sig_encode_loop1_spec ip ip.gamma1 ip.gamma1_bits (sp.γ₁ - 1) hb hab hc' n
    (by rw [hnv, hp.gamma1_bits]) sp.ℓ z zv hz hrng (bytes ct) hpre out1
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
  rw [hbk, hstart, ht2, hs1', hγ]
  rfl

/-! ## `sig_decode` -/

/-- The `z` component of `sigDecode`: block `i` is `BitUnpack` of bytes `[λ/4 + i·n, λ/4 + (i+1)·n)`. -/
def sigZ (p : Params) (σ : List UInt8) : Vector RPoly p.ℓ :=
  (List.range' 0 p.ℓ).foldl (fun (w : Vector RPoly p.ℓ) a => w.set! a
    (BitUnpack (slice σ (p.lam / 4 + a * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.γ₁ - 1) p.γ₁)) (Vector.replicate p.ℓ (Vector.replicate 256 0))

theorem sigZ_get (p : Params) (σ : List UInt8) (i : Nat) (hi : i < p.ℓ) :
    (sigZ p σ)[i] = BitUnpack (slice σ (p.lam / 4 + i * (32 * (1 + bitlen (p.γ₁ - 1))))
      (32 * (1 + bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁ := by
  unfold sigZ
  refine (vec_fold_gen (m := p.ℓ) (Vector.replicate 256 0) (fun a =>
    BitUnpack (slice σ (p.lam / 4 + a * (32 * (1 + bitlen (p.γ₁ - 1)))) (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.γ₁ - 1) p.γ₁) p.ℓ i hi).trans ?_
  rw [if_pos hi]

theorem sigDecode_eq (p : Params) (σ : List UInt8) :
    sigDecode p σ = (HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1))))
      (p.ω + p.k))).map (fun h => (slice σ 0 (p.lam / 4), sigZ p σ, h)) := by
  unfold sigDecode sigZ
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases hH : HintBitUnpack p (slice σ (p.lam / 4 + p.ℓ * (32 * (1 + bitlen (p.γ₁ - 1)))) (p.ω + p.k)) <;>
    simp [hH, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The range of the `BitUnpack` coefficients for `a = γ₁ - 1`, `b = γ₁`. -/
theorem BitUnpack_range (v : List UInt8) (a b i : Nat) (hi : i < 256) :
    (b : Int) - 2 ^ bitlen (a + b) < (BitUnpack v a b)[i] ∧ (BitUnpack v a b)[i] ≤ (b : Int) := by
  rw [BitUnpack_get v a b i hi]
  have h := BV_lt (byteBit v) (byteBit_le _) (bitlen (a + b) * i) (bitlen (a + b))
  have h' : ((BV (byteBit v) (bitlen (a + b) * i) (bitlen (a + b)) : Nat) : Int) <
      2 ^ bitlen (a + b) := by exact_mod_cast h
  constructor <;> omega

/-- The `c̃` copy loop of `sig_decode`. -/
theorem sig_decode_loop0_spec (ip : Impl.params.Params) (sig : Slice U8)
    (hL : ip.c_tilde_len.val ≤ sig.val.length) (hct : ip.c_tilde_len.val ≤ 64)
    (a0 a : Array U8 64#usize) (i : Usize) (hi : i.val ≤ ip.c_tilde_len.val)
    (ha : ∀ k, (bytesA a)[k]? = if k < i.val then (bytes sig)[k]? else (bytesA a0)[k]?) :
    encode.sig_decode_loop0 ip sig a i ⦃ r =>
      ∀ k, (bytesA r)[k]? = if k < ip.c_tilde_len.val then (bytes sig)[k]? else (bytesA a0)[k]? ⦄ := by
  unfold encode.sig_decode_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 64#usize × Usize) => ip.c_tilde_len.val - p.2.val)
    (fun p => p.2.val ≤ ip.c_tilde_len.val ∧
      ∀ k, (bytesA p.1)[k]? = if k < p.2.val then (bytes sig)[k]? else (bytesA a0)[k]?)
  · rintro ⟨a, i⟩ ⟨h2, h3⟩
    dsimp only at h2 h3
    simp only [encode.sig_decode_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < ip.c_tilde_len.val := by scalar_tac
      have hi64 : i.val < 64 := by omega
      step*
      subst a_post
      refine ⟨by omega, fun k => ?_, by omega⟩
      rw [bytesA_set, List.getElem?_set, h3 k, i2_post]
      by_cases hk : i.val = k
      · subst hk
        have hlt : i.val < (bytesA a).length := by simp; omega
        simp [hlt, hi', hi64, bytes_getElem?_eq, i1_post2, List.getElem?_eq_getElem (show i.val < sig.val.length from i1)]
      · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = ip.c_tilde_len.val := by scalar_tac
      simp only [WP.spec_ok]
      intro k
      rw [h3 k, hi']
  · exact ⟨hi, ha⟩

/-- The block loop of `sig_decode`: block `j` is `BitUnpack` of the bytes at `λ/4 + j·n`. -/
theorem sig_decode_loop1_spec {L : Usize} (ip : Impl.params.Params) (bb : U32) (c : Usize) (ea : Nat)
    (hb : bb.val < Spec.q) (hc : c.val = bitlen (ea + bb.val)) (hc22 : c.val ≤ 22) (n : Usize)
    (hn : n.val = 32 * c.val) (k : Nat) (hKk : L.val = k) (sig : Slice U8)
    (hL : ip.c_tilde_len.val + k * n.val ≤ sig.val.length)
    (arr : Array (Array U32 256#usize) L) (i2 : Usize) (hi2 : i2.val ≤ k)
    (hinv : ∀ j (hj : j < i2.val) (hj' : j < arr.val.length),
      ReprInt (arr.val[j]'hj')
        (BitUnpack (slice (bytes sig) (ip.c_tilde_len.val + j * n.val) n.val) ea bb.val)) :
    encode.sig_decode_loop1 ip bb c sig n arr i2 ⦃ r =>
      ∀ j (hj : j < k) (hj' : j < r.val.length),
        ReprInt (r.val[j]'hj')
          (BitUnpack (slice (bytes sig) (ip.c_tilde_len.val + j * n.val) n.val) ea bb.val) ⦄ := by
  unfold encode.sig_decode_loop1
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) L × Usize) => k - p.2.val)
    (fun p => p.2.val ≤ k ∧
      ∀ j (hj : j < p.2.val) (hj' : j < p.1.val.length),
        ReprInt (p.1.val[j]'hj')
          (BitUnpack (slice (bytes sig) (ip.c_tilde_len.val + j * n.val) n.val) ea bb.val))
  · rintro ⟨arr, i2⟩ ⟨h2, h3⟩
    dsimp only at h2 h3
    simp only [encode.sig_decode_loop1.body]
    split
    · rename_i hi
      have hik : i2.val < k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := sig.property
      have hlen2 := arr.property
      step*
      have hslen : s.val.length = 32 * c.val := by
        have : s.val.length = i7.val - i4.val := s_post2
        rw [this, i7_post, i4_post, i6_post, i5_post, i3_post]; omega
      refine WP.spec_bind (unpack_signed_spec s bb ea c hb hc hc22 hslen) ?_
      intro w hw
      step*
      have hsb0 := bytes_slice_of sig s i4.val i7.val n.val s_post1
        (by rw [i7_post, i4_post, i6_post, i5_post, i3_post]; omega)
      have hsb : bytes s = slice (bytes sig) (ip.c_tilde_len.val + i2.val * n.val) n.val := by
        rw [hsb0, i4_post, i3_post]
      subst a1_post
      refine ⟨by omega, ?_, by omega⟩
      intro j hj hj'
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rename_i hji
        subst hji
        rw [← hsb]; exact hw
      · exact h3 j (by omega) _
    · rename_i hi
      have hi' : i2.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      exact h3
  · exact ⟨hi2, hinv⟩

/-- **`sig_decode` is `sigDecode`** (Algorithm 27), for every byte string `σ` of length `sigLen`. It returns `none`
exactly when the spec does (malformed hint). Otherwise `c̃` is the first `λ/4` bytes (the rest of the 64-byte
buffer is zero), `z` denotes the spec's `z` (with the coefficient range `[-γ₁ + 1, γ₁]`) and `h` its hint. -/
theorem sig_decode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hs : StdSig sp) (σ : Slice U8) (hσ : σ.length = sp.sigLen) :
    encode.sig_decode K L ip σ ⦃ r =>
      match r, Spec.sigDecode sp (bytes σ) with
      | none, none => True
      | some (c, z, h), some (c', z', h') =>
          (bytesA c).take (sp.lam / 4) = c' ∧ (bytesA c).drop (sp.lam / 4) = List.replicate (64 - sp.lam / 4) 0 ∧
          ReprIntVec z z' ∧
          (∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
            -(sp.γ₁ : Int) + 1 ≤ (z'[i]'hi)[j]'hj ∧ (z'[i]'hi)[j]'hj ≤ (sp.γ₁ : Int)) ∧ ReprHintVec h h'
      | _, _ => False ⦄ := by
  obtain ⟨hbl, hlt, hc2, hpow⟩ := hs.bitlen_eq
  have hγ : ip.gamma1.val = sp.γ₁ := hp.gamma1
  have hcl : ip.c_tilde_len.val = sp.lam / 4 := hp.c_tilde_len
  have hσ' : σ.val.length = sp.lam / 4 + sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1))) + (sp.ω + sp.k) := by
    have : σ.val.length = sp.sigLen := hσ
    rw [this]; unfold Spec.Params.sigLen; ring
  have hq : Spec.q = 8380417 := rfl
  have hγ1 : 1 ≤ sp.γ₁ := by rcases hs.1 with e | e <;> rw [e] <;> decide +kernel
  have hγq : sp.γ₁ < 2 ^ 20 := by rcases hs.1 with e | e <;> rw [e] <;> decide +kernel
  have hb : ip.gamma1.val < Spec.q := by rw [hγ]; omega
  have hgb : ip.gamma1_bits.val ≤ 20 := by rw [hp.gamma1_bits]; omega
  have hc22 : ip.gamma1_bits.val ≤ 22 := by omega
  have hc' : ip.gamma1_bits.val = bitlen (sp.γ₁ - 1 + ip.gamma1.val) := by rw [hp.gamma1_bits, hγ, hbl]
  have hct64 : ip.c_tilde_len.val ≤ 64 := by rw [hcl]; exact hs.2
  have hlenb := σ.property
  unfold encode.sig_decode
  refine WP.spec_bind (sig_decode_loop0_spec ip σ (by omega) hct64 (Array.repeat 64#usize 0#u8) _ 0#usize
    (by simp) (by intro k; simp)) ?_
  intro c1 hc1
  step as ⟨n, n_post⟩
  have hnv : n.val = 32 * (1 + bitlen (sp.γ₁ - 1)) := by rw [n_post, hp.gamma1_bits]
  have hLn : L.val * n.val = sp.ℓ * n.val := by rw [hp.L_eq]
  have hσ'' : σ.val.length = ip.c_tilde_len.val + sp.ℓ * n.val + (sp.ω + sp.k) := by rw [hσ', hnv, hcl]
  refine WP.spec_bind (sig_decode_loop1_spec ip ip.gamma1 ip.gamma1_bits (sp.γ₁ - 1) hb hc' hc22 n n_post
    sp.ℓ hp.L_eq σ (by omega) _ 0#usize (by simp) (fun j hj => absurd hj (by simp))) ?_
  intro z1 hz1
  have hLn' : L.val * n.val ≤ Usize.max := by rw [hLn]; omega
  step as ⟨i, i_post⟩
  have hcn : ip.c_tilde_len.val + i.val ≤ Usize.max := by rw [i_post, hLn]; omega
  step as ⟨i1, i1_post⟩
  have hstart : i1.val = ip.c_tilde_len.val + sp.ℓ * n.val := by rw [i1_post, i_post, hLn]
  refine WP.spec_bind (slice_from_bytes σ { start := i1 } (by simp; omega)) ?_
  intro s hs'
  have hslen : s.length = sp.ω + sp.k := by
    have := congrArg List.length hs'
    simp only [bytes_length, List.length_drop] at this
    show s.val.length = _
    omega
  refine WP.spec_bind (hint_bit_unpack_spec ip sp hp s hslen) ?_
  intro o ho
  rw [sigDecode_eq]
  have hsl : slice (bytes σ) (sp.lam / 4 + sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1)))) (sp.ω + sp.k) = bytes s := by
    rw [hs']
    unfold slice
    have : (sp.lam / 4 + sp.ℓ * (32 * (1 + bitlen (sp.γ₁ - 1)))) = i1.val := by rw [hstart, hcl, hnv]
    rw [this]
    apply List.take_of_length_le
    simp only [bytes_length, List.length_drop]
    omega
  rw [hsl]
  rcases o with _ | h
  · simp only [WP.spec_ok]
    cases hH : HintBitUnpack sp (bytes s)
    · simp [hH]
    · rw [hH] at ho; exact ho.elim
  · cases hH : HintBitUnpack sp (bytes s)
    · rw [hH] at ho; exact ho.elim
    · rw [hH] at ho
      simp only [WP.spec_ok, hH, Option.map_some]
      have hzrepr : ReprIntVec z1 (sigZ sp (bytes σ)) := by
        refine ⟨hp.L_eq, fun i hi => ?_⟩
        have hj' : i < z1.val.length := by rw [z1.property, hp.L_eq]; exact hi
        have := hz1 i hi hj'
        rw [hcl, hnv, hγ] at this
        rw [sigZ_get sp (bytes σ) i hi]
        exact this
      refine ⟨?_, ?_, hzrepr, ?_, ho⟩
      · apply List.ext_getElem?
        intro k
        rw [List.getElem?_take, hc1 k, hcl]
        by_cases hk : k < sp.lam / 4 <;> simp [slice, List.getElem?_take, hk]
      · apply List.ext_getElem?
        intro k
        rw [List.getElem?_drop, hc1 (sp.lam / 4 + k), hcl, bytesA_repeat_zero, List.getElem?_replicate]
        by_cases hk : k < 64 - sp.lam / 4
        · simp [hk]; omega
        · simp [hk]; omega
      · intro i hi j hj
        rw [sigZ_get sp (bytes σ) i hi]
        have := BitUnpack_range (slice (bytes σ) (sp.lam / 4 + i * (32 * (1 + bitlen (sp.γ₁ - 1))))
          (32 * (1 + bitlen (sp.γ₁ - 1)))) (sp.γ₁ - 1) sp.γ₁ j hj
        have hpowI : (2 : Int) ^ (1 + bitlen (sp.γ₁ - 1)) = 2 * (sp.γ₁ : Int) := by exact_mod_cast hpow
        rw [hbl, hpowI] at this
        have e : ((2 * sp.γ₁ : Nat) : Int) = 2 * (sp.γ₁ : Int) := by push_cast; ring
        push_cast at this
        constructor <;> omega

/-! ## `sig_encode` as Sign uses it -/

/-- `RPoly.toZq (Poly.modPM w) = w`: the centered representative denotes the same residue. -/
theorem toZq_modPM (w : Poly) : RPoly.toZq (Poly.modPM w) = w := by
  apply Vector.ext
  intro k hk
  simp [RPoly.toZq, Poly.modPM, Zq.modPM_cast]

/-- **`sig_encode` as Algorithm 7 step 33 calls it**: `z` is the canonical `Z_q` vector `zq` (`ReprVec`), whose
infinity norm is below `γ₁ - β` (the check of step 23), and the signature is `sigEncode … (z mod± q) …`. -/
theorem sig_encode_signed_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hs : StdSig sp) (ct : Slice U8) (hct : ct.length = sp.lam / 4)
    (z : Array (Array U32 256#usize) L) (zq : Vector Poly sp.ℓ) (hz : ReprVec z zq)
    (hnorm : ‖zq‖∞ < sp.γ₁ - sp.β)
    (h : Array (Array Bool 256#usize) K) (hv : Vector HintPoly sp.k) (hh : ReprHintVec h hv)
    (hw : HintWeight hv ≤ sp.ω) (out : Slice U8) (hout : out.length = sp.sigLen) :
    encode.sig_encode ip ct z h out ⦃ out' =>
      bytes out' = Spec.sigEncode sp (bytes ct) (zq.map Poly.modPM) hv ⦄ := by
  have hz' : ReprIntVec z (zq.map Poly.modPM) := by
    refine ⟨hz.len, fun i hi => ?_⟩
    have := hz.elt i hi
    refine ⟨this.canon, ?_⟩
    rw [this.eq, Vector.getElem_map, toZq_modPM]
  have hn := (infNorm_le_iff zq (sp.γ₁ - sp.β - 1)).1 (by omega)
  refine sig_encode_spec ip sp hp hs ct hct z (zq.map Poly.modPM) hz' ?_ h hv hh hw out hout
  intro i hi j hj
  have h1 := (infNorm_le_iff zq[i] (sp.γ₁ - sp.β - 1)).1 (hn i hi) j hj
  rw [Vector.getElem_map]
  simp only [Poly.modPM, Vector.getElem_map]
  have h2 : (Zq.modPM (zq[i][j])).natAbs ≤ sp.γ₁ - sp.β - 1 := h1
  omega

/-- Satisfiability of the `sig_decode`/`sig_encode` premises: ML-DSA-44 parameters. -/
theorem sigcodec_hypotheses_ML_DSA_44 :
    ∃ ip, params.ML_DSA_44 = ok ip ∧ Params.Valid ip 4#usize 4#usize Spec.ML_DSA_44 ∧
      StdSig Spec.ML_DSA_44 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_44_valid
  exact ⟨ip, h, hv, stdSig_44⟩

theorem sigcodec_hypotheses_ML_DSA_65 :
    ∃ ip, params.ML_DSA_65 = ok ip ∧ Params.Valid ip 6#usize 5#usize Spec.ML_DSA_65 ∧
      StdSig Spec.ML_DSA_65 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_65_valid
  exact ⟨ip, h, hv, stdSig_65⟩

theorem sigcodec_hypotheses_ML_DSA_87 :
    ∃ ip, params.ML_DSA_87 = ok ip ∧ Params.Valid ip 8#usize 7#usize Spec.ML_DSA_87 ∧
      StdSig Spec.ML_DSA_87 := by
  obtain ⟨ip, h, hv⟩ := ML_DSA_87_valid
  exact ⟨ip, h, hv, stdSig_87⟩

end Proofs
