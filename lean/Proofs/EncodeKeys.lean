import Proofs.Encode

/-!
# w1Encode, pkEncode/pkDecode, skEncode/skDecode
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

/-! ## Concatenation of blocks -/

/-- `f 0 ++ ... ++ f (i-1)`. -/
def flat (f : Nat → List UInt8) (i : Nat) : List UInt8 := ((List.range' 0 i).map f).flatten

theorem flat_zero (f : Nat → List UInt8) : flat f 0 = [] := rfl

theorem flat_succ (f : Nat → List UInt8) (i : Nat) : flat f (i + 1) = flat f i ++ f i := by
  simp [flat, List.range'_concat]

theorem flat_length (f : Nat → List UInt8) (n : Nat) (h : ∀ t, (f t).length = n) :
    ∀ i, (flat f i).length = i * n := by
  intro i
  induction i with
  | zero => simp [flat]
  | succ i ih => rw [flat_succ, List.length_append, ih, h]; ring

theorem write_step (X new A : List UInt8) (P n : Nat) (hA : X.take P = A) (hAl : A.length = P)
    (hn : new.length = n) (hX : P + n ≤ X.length) :
    (X.take P ++ new ++ X.drop (P + n)).take (P + n) = A ++ new ∧
    (X.take P ++ new ++ X.drop (P + n)).length = X.length := by
  subst hA
  constructor
  · have : (X.take P ++ new).length = P + n := by simp [hn]; omega
    exact List.take_left' this
  · simp [hn]; omega

theorem SimpleBitPack_length (w : RPoly) (b : Nat) : (SimpleBitPack w b).length = 32 * bitlen b := by
  obtain ⟨g, _, _, h⟩ := SimpleBitPack_model w b
  rw [h]; simp

theorem BitPack_length (w : RPoly) (a b : Nat) : (BitPack w a b).length = 32 * bitlen (a + b) := by
  obtain ⟨g, _, _, h⟩ := BitPack_model w a b
  rw [h]; simp

theorem vec_getElem!_eq {α : Type} [Inhabited α] {m : Nat} (v : Vector α m) (i : Nat) (hi : i < m) :
    v[i]! = v[i] := by
  rw [getElem!_pos v i (by simpa using hi)]

theorem setSlice_bytes (out : Slice U8) (i : Nat) (s2 : List U8) (h : i + s2.length ≤ out.val.length) :
    bytes (out.setSlice! i s2) = (bytes out).take i ++ s2.map (fun x => UInt8.ofNat x.val) ++
      (bytes out).drop (i + s2.length) := by
  have hm : min s2.length (out.val.length - i) = s2.length := by omega
  simp [bytes, Slice.setSlice!, List.setSlice!, hm, List.map_take, List.map_drop]

/-- One iteration of a block-writing loop: the block `F i` replaces bytes `[o0 + i·n, o0 + (i+1)·n)`. -/
theorem block_write_step (out s1 : Slice U8) (back : Slice U8 → Slice U8) (i2 i4 : Usize)
    (o0 n i : Nat) (pre : List UInt8) (F : Nat → List UInt8)
    (hF : ∀ t, (F t).length = n) (hpre : pre.length = o0)
    (hi2 : i2.val = o0 + i * n) (hi4 : i4.val = o0 + (i + 1) * n)
    (hback : ∀ s2 : Slice U8, back s2 = out.setSlice! i2.val s2.val)
    (hs1 : bytes s1 = F i)
    (hinv : (bytes out).take (o0 + i * n) = pre ++ flat F i)
    (hbound : o0 + (i + 1) * n ≤ out.val.length) :
    (back s1).val.length = out.val.length ∧
    (bytes (back s1)).take (o0 + (i + 1) * n) = pre ++ flat F (i + 1) := by
  have e : (i + 1) * n = i * n + n := by ring
  have hs1len : s1.val.length = n := by
    have := congrArg List.length hs1
    simpa [hF] using this
  have hA : (pre ++ flat F i).length = o0 + i * n := by
    rw [List.length_append, flat_length F n hF, hpre]
  have hX : o0 + i * n + n ≤ (bytes out).length := by
    simp only [bytes_length]; omega
  obtain ⟨w1, w2⟩ := write_step (bytes out) (bytes s1) (pre ++ flat F i) (o0 + i * n) n hinv hA
    (by simpa using hs1len) hX
  have hb : bytes (back s1) = (bytes out).take (o0 + i * n) ++ bytes s1 ++
      (bytes out).drop (o0 + i * n + n) := by
    rw [hback, setSlice_bytes out i2.val s1.val (by omega), hi2, hs1len]
    rfl
  refine ⟨?_, ?_⟩
  · have := congrArg List.length hb
    simp only [bytes_length] at this w2
    rw [this]; exact w2
  · rw [hb, show o0 + (i + 1) * n = o0 + i * n + n by ring, w1, hs1, flat_succ, List.append_assoc]

/-! ## `w1_encode` -/

theorem w1_encode_loop_spec {K : Usize} (c n : Usize) (hn : n.val = 32 * c.val) (b : Nat) (hb : b < Spec.q)
    (hc : c.val = bitlen b) (k : Nat) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256, 0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (b : Int))
    (out : Slice U8) (hL : out.val.length = k * n.val) (i1 : Usize) (hi1 : i1.val ≤ k)
    (hinv : (bytes out).take (i1.val * n.val) = flat (fun t => SimpleBitPack v[t]! b) i1.val) :
    encode.w1_encode_loop c w1 out n i1 ⦃ out' => bytes out' = flat (fun t => SimpleBitPack v[t]! b) k ⦄ := by
  have hKk := hv.len
  unfold encode.w1_encode_loop
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => k - p.2.val)
    (fun p => p.1.val.length = k * n.val ∧ p.2.val ≤ k ∧
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
          (by rw [i4_post, i3_post]; ring) s_post3 hs1' (by simpa using h3) (by rw [h1] at *; simpa using hm1)
        refine ⟨by rw [b1]; exact h1, by omega, ?_, by omega⟩
        show List.take (i3.val * n.val) (bytes (index_mut_back s1)) = flat _ i3.val
        rw [i3_post]
        simpa using b2
    · rename_i hi
      have hi' : i1.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      rw [← h3, List.take_of_length_le (by simp [h1])]
  · exact ⟨hL, hi1, hinv⟩


theorem Params.Valid.w1_b_lt {ip : Impl.params.Params} {K L : Usize} {sp : Spec.Params}
    (_hp : Params.Valid ip K L sp) : (Spec.q - 1) / (2 * sp.γ₂) - 1 < Spec.q := by
  have := Nat.div_le_self (Spec.q - 1) (2 * sp.γ₂)
  have : Spec.q = 8380417 := rfl
  omega

/-- **`w1_encode` is `w1Encode`** (Algorithm 28): `w1` stores the integer vector `v` with coefficients in
`[0, (q-1)/(2γ₂) - 1]`, and `out` has `32·k·bitlen((q-1)/(2γ₂) - 1)` bytes. -/
theorem w1_encode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (w1 : Array (Array U32 256#usize) K) (v : Vector RPoly sp.k)
    (hv : ReprIntVec w1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (((Spec.q - 1) / (2 * sp.γ₂) - 1 : Nat) : Int))
    (out : Slice U8) (hL : out.val.length = 32 * sp.k * bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1)) :
    encode.w1_encode ip w1 out ⦃ out' => bytes out' = Spec.w1Encode sp v ⦄ := by
  have hc : ip.w1_bits.val = bitlen ((Spec.q - 1) / (2 * sp.γ₂) - 1) := hp.w1_bits
  have hb := hp.w1_b_lt
  have h23 := bitlen_lt_q hb
  unfold encode.w1_encode
  step*
  rw [w1Encode_eq]
  refine WP.spec_mono (w1_encode_loop_spec ip.w1_bits n (by rw [n_post]) _ hb hc sp.k w1 v hv hrng out
    (by rw [hL, n_post, hc]; ring) 0#usize (by simp) (by simp [flat_zero])) ?_
  intro out' h
  exact h


/-! ## Byte-copy loops -/

theorem take_of_pointwise (out : Slice U8) (R : List UInt8) (n : Nat) (hR : R.length = n)
    (_hL : n ≤ out.val.length) (X : Nat → Option UInt8)
    (h : ∀ k, (bytes out)[k]? = if k < n then R[k]? else X k) : (bytes out).take n = R := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_take, h k]
  by_cases hk : k < n
  · simp [hk]
  · simp [hk]
    omega

theorem bytesA_getElem? {n : Usize} (a : Array U8 n) (k : Nat) (hk : k < n.val) :
    (bytesA a)[k]? = some (UInt8.ofNat (a.val[k]'(by rw [a.property]; exact hk)).val) := by
  simp [bytesA, List.getElem?_eq_getElem (show k < a.val.length by rw [a.property]; exact hk)]

/-- The first loop of `pk_encode`: `out[0..32) ← ρ`. -/
theorem pk_encode_loop0_spec (rho : Array U8 32#usize) (out0 : Slice U8) (hL : 32 ≤ out0.val.length)
    (out : Slice U8) (i : Usize) (hi : i.val ≤ 32) (hlen : out.val.length = out0.val.length)
    (hinv : ∀ k, (bytes out)[k]? = if k < i.val then (bytesA rho)[k]? else (bytes out0)[k]?) :
    encode.pk_encode_loop0 rho out i ⦃ out' => out'.val.length = out0.val.length ∧
      ∀ k, (bytes out')[k]? = if k < 32 then (bytesA rho)[k]? else (bytes out0)[k]? ⦄ := by
  unfold encode.pk_encode_loop0
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => 32 - p.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.val ≤ 32 ∧
      ∀ k, (bytes p.1)[k]? = if k < p.2.val then (bytesA rho)[k]? else (bytes out0)[k]?)
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.pk_encode_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 32 := by scalar_tac
      step*
      subst s_post2
      refine ⟨by simp [h1], by omega, fun k => ?_, by omega⟩
      rw [bytes_set, List.getElem?_set, h3 k, i2_post]
      by_cases hk : i.val = k
      · subst hk
        have hlt : i.val < out.val.length := s_post1
        simp [hlt, bytesA_getElem? rho i.val (by simpa using hi'), i1_post2]
      · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨h1, fun k => ?_⟩
      rw [h3 k, hi']
  · exact ⟨hlen, hi, hinv⟩


/-! ## `pk_encode` -/

theorem pk_encode_loop1_spec {K : Usize} (b : Nat) (hb : b < Spec.q) (hc : bitlen b = 10) (k : Nat)
    (t1 : Array (Array U32 256#usize) K) (v : Vector RPoly k) (hv : ReprIntVec t1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256, 0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (b : Int))
    (pre : List UInt8) (hpre : pre.length = 32)
    (out : Slice U8) (hL : out.val.length = 32 + k * 320) (i : Usize) (hi : i.val ≤ k)
    (hinv : (bytes out).take (32 + i.val * 320) = pre ++ flat (fun (t : Nat) => SimpleBitPack v[t]! b) i.val) :
    encode.pk_encode_loop1 t1 out i ⦃ out' => bytes out' = pre ++ flat (fun (t : Nat) => SimpleBitPack v[t]! b) k ⦄ := by
  have hKk := hv.len
  have hFlen : ∀ t : Nat, (SimpleBitPack v[t]! b).length = 320 := fun t => by
    rw [SimpleBitPack_length, hc]
  unfold encode.pk_encode_loop1
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => k - p.2.val)
    (fun p => p.1.val.length = 32 + k * 320 ∧ p.2.val ≤ k ∧
      (bytes p.1).take (32 + p.2.val * 320) = pre ++ flat (fun (t : Nat) => SimpleBitPack v[t]! b) p.2.val)
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.pk_encode_loop1.body]
    split
    · rename_i hi
      have hik : i.val < k := by scalar_tac
      have hm1 : (i.val + 1) * 320 ≤ k * 320 := Nat.mul_le_mul_right _ hik
      have hlen := out.property
      step*
      refine WP.spec_bind (bit_pack_spec_repr _ (v[i.val]'hik) ?_ b hb (hrng _ hik) 10#usize (by simp [hc]) s ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i5.val - i2.val := s_post2
        rw [this, i5_post, i2_post, i4_post, i3_post, i1_post]; simp; omega
      · intro s1 hs1
        simp only [WP.spec_ok]
        have hs1' : bytes s1 = SimpleBitPack v[i.val]! b := by rw [hs1, vec_getElem!_eq v _ hik]
        obtain ⟨b1, b2⟩ := block_write_step out s1 index_mut_back i2 i5 32 320 i.val pre
          (fun (t : Nat) => SimpleBitPack v[t]! b) hFlen hpre (by rw [i2_post, i1_post])
          (by rw [i5_post, i4_post, i3_post]) s_post3 hs1' h3 (by rw [h1]; nlinarith)
        refine ⟨by rw [b1]; exact h1, by omega, ?_, by omega⟩
        show List.take (32 + i3.val * 320) (bytes (index_mut_back s1)) = _
        rw [i3_post]
        exact b2
    · rename_i hi
      have hi' : i.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      rw [← h3, List.take_of_length_le (by simp [h1])]
  · exact ⟨hL, hi, hinv⟩

theorem bitlen_q_sub_one : bitlen (Spec.q - 1) = 23 := by decide +kernel

theorem t1Bits_eq (sp : Spec.Params) (hd : sp.d = 13) : sp.t1Bits = 10 := by
  unfold Params.t1Bits; rw [hd, bitlen_q_sub_one]

/-- **`pk_encode` is `pkEncode`** (Algorithm 22): `t1` stores the integer vector `v` with coefficients in
`[0, 2^10 - 1]`, `out` has `32 + 320·k` bytes. -/
theorem pk_encode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (rho : Array U8 32#usize) (t1 : Array (Array U32 256#usize) K)
    (v : Vector RPoly sp.k) (hv : ReprIntVec t1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      0 ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (((2 ^ sp.t1Bits - 1 : Nat)) : Int))
    (out : Slice U8) (hL : out.val.length = 32 + 320 * sp.k) :
    encode.pk_encode rho t1 out ⦃ out' => bytes out' = Spec.pkEncode sp (bytesA rho) v ⦄ := by
  have ht := t1Bits_eq sp hp.d_eq
  rw [ht] at hrng
  have hb10 : (2 ^ 10 - 1 : Nat) < Spec.q := by decide +kernel
  have hc10 : bitlen (2 ^ 10 - 1) = 10 := by decide +kernel
  unfold encode.pk_encode
  refine WP.spec_bind (pk_encode_loop0_spec rho out (by omega) out 0#usize (by simp) rfl (by simp)) ?_
  rintro out1 ⟨hl1, hp1⟩
  rw [pkEncode_eq, ht]
  refine WP.spec_mono (pk_encode_loop1_spec (2 ^ 10 - 1) hb10 hc10 sp.k t1 v hv hrng (bytesA rho)
    (by simp) out1 (by rw [hl1, hL]; ring) 0#usize (by simp) ?_) ?_
  · show List.take (32 + 0 * 320) (bytes out1) = bytesA rho ++ flat _ 0
    rw [flat_zero, List.append_nil, Nat.zero_mul, Nat.add_zero]
    exact take_of_pointwise out1 (bytesA rho) 32 (by simp) (by omega) _ (by simpa using hp1)
  · intro out' h
    exact h


/-! ## `pk_decode` -/

theorem pk_decode_loop0_spec (pk : Slice U8) (hL : 32 ≤ pk.val.length) (rho0 : Array U8 32#usize)
    (rho : Array U8 32#usize) (i : Usize) (hi : i.val ≤ 32)
    (hinv : ∀ k, (bytesA rho)[k]? = if k < i.val then (bytes pk)[k]? else (bytesA rho0)[k]?) :
    encode.pk_decode_loop0 pk rho i ⦃ rho' =>
      ∀ k, (bytesA rho')[k]? = if k < 32 then (bytes pk)[k]? else (bytesA rho0)[k]? ⦄ := by
  unfold encode.pk_decode_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U8 32#usize × Usize) => 32 - p.2.val)
    (fun p => p.2.val ≤ 32 ∧
      ∀ k, (bytesA p.1)[k]? = if k < p.2.val then (bytes pk)[k]? else (bytesA rho0)[k]?)
  · rintro ⟨rho, i⟩ ⟨h2, h3⟩
    dsimp only at h2 h3
    simp only [encode.pk_decode_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 32 := by scalar_tac
      step*
      subst a_post
      refine ⟨by omega, fun k => ?_, by omega⟩
      rw [bytesA_set, List.getElem?_set, h3 k, i2_post]
      by_cases hk : i.val = k
      · subst hk
        have hlt : i.val < (bytesA rho).length := by simpa using hi'
        simp [hi', bytes_getElem?_eq, i1_post2, List.getElem?_eq_getElem (show i.val < pk.val.length from i1)]
      · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      intro k
      rw [h3 k, hi']
  · exact ⟨hi, hinv⟩


/-- The `i`-th block of a public key: bits `[32 + 320 i, 32 + 320 (i+1))`, decoded by `SimpleBitUnpack`. -/
def pkBlock (pk : List UInt8) (b i : Nat) : RPoly :=
  SimpleBitUnpack (slice pk (32 + i * 320) 320) b

theorem pk_decode_loop1_spec {K : Usize} (b : Nat) (hc : bitlen b = 10) (k : Nat) (hKk : K.val = k)
    (pk : Slice U8) (hL : pk.val.length = 32 + k * 320)
    (t1 : Array (Array U32 256#usize) K) (i : Usize) (hi : i.val ≤ k)
    (hinv : ∀ j (_hj : j < i.val) (hj' : j < t1.val.length), ReprInt (t1.val[j]'hj') (pkBlock (bytes pk) b j)) :
    encode.pk_decode_loop1 pk t1 i ⦃ t1' =>
      ∀ j (_hj : j < k) (hj' : j < t1'.val.length), ReprInt (t1'.val[j]'hj') (pkBlock (bytes pk) b j) ⦄ := by
  unfold encode.pk_decode_loop1
  apply loop.spec_decr_nat
    (fun (p : Array (Array U32 256#usize) K × Usize) => k - p.2.val)
    (fun p => p.2.val ≤ k ∧ ∀ j (hj : j < p.2.val) (hj' : j < p.1.val.length),
      ReprInt (p.1.val[j]'hj') (pkBlock (bytes pk) b j))
  · rintro ⟨t1, i⟩ ⟨h2, h3⟩
    dsimp only at h2 h3
    simp only [encode.pk_decode_loop1.body]
    split
    · rename_i hi
      have hik : i.val < k := by scalar_tac
      have hm1 : (i.val + 1) * 320 ≤ k * 320 := Nat.mul_le_mul_right _ hik
      have hlen := pk.property
      step*
      have hslen : s.val.length = 32 * (10#usize).val := by
        have : s.val.length = i5.val - i2.val := s_post2
        rw [this, i5_post, i2_post, i4_post, i3_post, i1_post]
        have e : (i.val + 1) * 320 = i.val * 320 + 320 := by ring
        rw [e]; simp; omega
      refine WP.spec_bind (bit_unpack_spec_repr s 10#usize b (by simp [hc]) (by simp) hslen) ?_
      intro a ha
      step*
      have hsb : bytes s = slice (bytes pk) (32 + i.val * 320) 320 := by
        have e1 : i5.val - i2.val = 320 := by
          rw [i5_post, i2_post, i4_post, i3_post, i1_post]
          have e : (i.val + 1) * 320 = i.val * 320 + 320 := by ring
          rw [e]; omega
        have hsv : s.val = (pk.val.drop (32 + i.val * 320)).take 320 := by
          rw [s_post1]; unfold List.slice; rw [e1, i2_post, i1_post]
        simp [bytes, hsv, slice, List.map_take, List.map_drop]
      subst a1_post
      refine ⟨by omega, ?_, by omega⟩
      intro j hj hj'
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rename_i hji
        subst hji
        have : pkBlock (bytes pk) b i.val = SimpleBitUnpack (bytes s) b := by rw [hsb]; rfl
        rw [this]; exact ha
      · exact h3 j (by omega) _
    · rename_i hi
      have hi' : i.val = k := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj hj'
      exact h3 j (by omega) _
  · exact ⟨hi, hinv⟩


/-- **`pk_decode` is `pkDecode`** (Algorithm 23), for *every* byte string `pk` of length `32 + 320·k`: the
decoder never fails, `ρ` is the first 32 bytes and `t1` denotes the spec's integer vector. -/
theorem pk_decode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (pk : Slice U8) (hL : pk.val.length = 32 + 320 * sp.k) :
    encode.pk_decode K pk ⦃ r => bytesA r.1 = (Spec.pkDecode sp (bytes pk)).1 ∧
      ReprIntVec r.2 (Spec.pkDecode sp (bytes pk)).2 ⦄ := by
  have ht := t1Bits_eq sp hp.d_eq
  have hc10 : bitlen (2 ^ 10 - 1) = 10 := by decide +kernel
  unfold encode.pk_decode
  refine WP.spec_bind (pk_decode_loop0_spec pk (by omega) (Array.repeat 32#usize 0#u8)
    (Array.repeat 32#usize 0#u8) 0#usize (by simp) (by intro k; simp)) ?_
  intro rho1 hrho1
  refine WP.spec_bind (pk_decode_loop1_spec (2 ^ 10 - 1) hc10 sp.k hp.K_eq pk (by omega)
    (Array.repeat K (Array.repeat 256#usize 0#u32)) 0#usize (by simp) (fun j hj => absurd hj (by simp))) ?_
  intro t11 ht11
  simp only [WP.spec_ok]
  refine ⟨?_, hp.K_eq, fun i hi => ?_⟩
  · rw [pkDecode_fst]
    apply List.ext_getElem?
    intro k
    rw [hrho1 k, List.getElem?_take]
    by_cases hk : k < 32
    · simp [hk]
    · simp only [hk, if_false]
      rw [List.getElem?_eq_none_iff.mpr (by simp; omega)]
  · rw [pkDecode_get sp (bytes pk) i hi, ht]
    have := ht11 i hi (by rw [t11.property, hp.K_eq]; exact hi)
    simpa [pkBlock] using this


/-! ## `sk_encode`: byte-copy loops -/

theorem sk_encode_loop0_spec (rho key : Array U8 32#usize) (out0 : Slice U8) (hL : 64 ≤ out0.val.length)
    (out : Slice U8) (i : Usize) (hi : i.val ≤ 32) (hlen : out.val.length = out0.val.length)
    (hinv : ∀ k, (bytes out)[k]? = if k < i.val then (bytesA rho)[k]?
      else if 32 ≤ k ∧ k < 32 + i.val then (bytesA key)[k - 32]? else (bytes out0)[k]?) :
    encode.sk_encode_loop0 rho key out i ⦃ out' => out'.val.length = out0.val.length ∧
      ∀ k, (bytes out')[k]? = if k < 32 then (bytesA rho)[k]?
        else if k < 64 then (bytesA key)[k - 32]? else (bytes out0)[k]? ⦄ := by
  unfold encode.sk_encode_loop0
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => 32 - p.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.val ≤ 32 ∧
      ∀ k, (bytes p.1)[k]? = if k < p.2.val then (bytesA rho)[k]?
        else if 32 ≤ k ∧ k < 32 + p.2.val then (bytesA key)[k - 32]? else (bytes out0)[k]?)
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.sk_encode_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 32 := by scalar_tac
      step*
      subst s_post2 out1_post2
      have hl1 : i.val < out.val.length := out1_post1
      have hl2 : i3.val < out.val.length := by
        have := s_post1; simpa using this
      refine ⟨by simp [h1], by omega, fun k => ?_, by omega⟩
      have hl3 : 32 + i.val < out.val.length := by omega
      rw [bytes_set, bytes_set, List.getElem?_set, List.getElem?_set, h3 k, i3_post, i4_post]
      have hr := bytesA_getElem? rho i.val (by simpa using hi')
      have hkk := bytesA_getElem? key i.val (by simpa using hi')
      by_cases hk1 : 32 + i.val = k
      · subst hk1
        simp [hl3, show ¬ (32 + i.val < i.val + 1) from by omega, i2_post2, hkk]
      · by_cases hk2 : i.val = k
        · subst hk2
          simp [hl1, i1_post2, hr]
        · rw [if_neg hk1, if_neg hk2]
          have : (k < i.val + 1) ↔ (k < i.val) := by omega
          have h4 : (32 ≤ k ∧ k < 32 + (i.val + 1)) ↔ (32 ≤ k ∧ k < 32 + i.val) := by omega
          simp only [this, h4]
    · rename_i hi
      have hi' : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨h1, fun k => ?_⟩
      rw [h3 k, hi']
      by_cases hk : k < 32
      · simp [hk]
      · by_cases hk2 : k < 64
        · simp [hk, hk2]
        · simp [hk, hk2]
  · exact ⟨hlen, hi, hinv⟩


/-- The block loop of `sk_encode` for the `s₁` vector: blocks `BitPack v[t] a b` at `o0 + t·n`. -/
theorem sk_encode_loop2_spec {L : Usize} (bb : U32) (c : Usize) (ea : Nat) (hb : bb.val < Spec.q)
    (hab : ea + bb.val < Spec.q) (hc : c.val = bitlen (ea + bb.val)) (n : Usize) (hn : n.val = 32 * c.val)
    (k : Nat) (s1 : Array (Array U32 256#usize) L) (v : Vector RPoly k) (hv : ReprIntVec s1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256,
      -(ea : Int) ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (bb.val : Int))
    (pre : List UInt8) (o0 : Nat) (hpre : pre.length = o0)
    (out0 : Slice U8) (hL : o0 + k * n.val ≤ out0.val.length) (o i2 : Usize) (hi2 : i2.val ≤ k)
    (ho : o.val = o0 + i2.val * n.val)
    (hinv : (bytes out0).take (o0 + i2.val * n.val) = pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) i2.val) :
    encode.sk_encode_loop2 bb c s1 out0 n o i2 ⦃ r => r.1.val.length = out0.val.length ∧
      r.2.val = o0 + k * n.val ∧
      (bytes r.1).take (o0 + k * n.val) = pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) k ⦄ := by
  have hKk := hv.len
  have hFlen : ∀ t : Nat, (Spec.BitPack v[t]! ea bb.val).length = n.val := fun t => by
    rw [BitPack_length, ← hc, hn]
  unfold encode.sk_encode_loop2
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize × Usize) => k - p.2.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.2.val ≤ k ∧ p.2.1.val = o0 + p.2.2.val * n.val ∧
      (bytes p.1).take (o0 + p.2.2.val * n.val) = pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) p.2.2.val)
  · rintro ⟨out, o, i2⟩ ⟨h1, h2, h2', h3⟩
    dsimp only at h1 h2 h2' h3
    simp only [encode.sk_encode_loop2.body]
    split
    · rename_i hi
      have hik : i2.val < k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := out.property
      have hbd : o.val + n.val ≤ out.val.length := by omega
      step*
      refine WP.spec_bind (pack_signed_spec _ (v[i2.val]'hik) ?_ bb ea c s hb hab hc (hrng _ hik) ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i3.val - o.val := s_post2
        rw [this, i3_post]; omega
      · intro s2 hs2
        step*
        have hs1' : bytes s2 = Spec.BitPack v[i2.val]! ea bb.val := by rw [hs2, vec_getElem!_eq v _ hik]
        obtain ⟨b1, b2⟩ := block_write_step out s2 index_mut_back o i3 o0 n.val i2.val pre
          (fun (t : Nat) => Spec.BitPack v[t]! ea bb.val) hFlen hpre h2' (by rw [i3_post]; omega) s_post3 hs1' h3
          (by omega)
        refine ⟨by rw [b1]; exact h1, by omega, by rw [i3_post, i4_post]; omega, ?_, by omega⟩
        show List.take (o0 + i4.val * n.val) (bytes (index_mut_back s2)) = _
        rw [i4_post]
        exact b2
    · rename_i hi
      have hi' : i2.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3 h2'
      exact ⟨h1, h2', h3⟩
  · exact ⟨rfl, hi2, ho, hinv⟩

/-- The block loop of `sk_encode` for the `s₂` vector: blocks `BitPack v[t] a b` at `o0 + t·n`. -/
theorem sk_encode_loop3_spec {L : Usize} (bb : U32) (c : Usize) (ea : Nat) (hb : bb.val < Spec.q)
    (hab : ea + bb.val < Spec.q) (hc : c.val = bitlen (ea + bb.val)) (n : Usize) (hn : n.val = 32 * c.val)
    (k : Nat) (s1 : Array (Array U32 256#usize) L) (v : Vector RPoly k) (hv : ReprIntVec s1 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256,
      -(ea : Int) ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (bb.val : Int))
    (pre : List UInt8) (o0 : Nat) (hpre : pre.length = o0)
    (out0 : Slice U8) (hL : o0 + k * n.val ≤ out0.val.length) (o i2 : Usize) (hi2 : i2.val ≤ k)
    (ho : o.val = o0 + i2.val * n.val)
    (hinv : (bytes out0).take (o0 + i2.val * n.val) = pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) i2.val) :
    encode.sk_encode_loop3 bb c s1 out0 n o i2 ⦃ r => r.1.val.length = out0.val.length ∧
      r.2.val = o0 + k * n.val ∧
      (bytes r.1).take (o0 + k * n.val) = pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) k ⦄ := by
  have hKk := hv.len
  have hFlen : ∀ t : Nat, (Spec.BitPack v[t]! ea bb.val).length = n.val := fun t => by
    rw [BitPack_length, ← hc, hn]
  unfold encode.sk_encode_loop3
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize × Usize) => k - p.2.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.2.val ≤ k ∧ p.2.1.val = o0 + p.2.2.val * n.val ∧
      (bytes p.1).take (o0 + p.2.2.val * n.val) = pre ++ flat (fun t => Spec.BitPack v[t]! ea bb.val) p.2.2.val)
  · rintro ⟨out, o, i2⟩ ⟨h1, h2, h2', h3⟩
    dsimp only at h1 h2 h2' h3
    simp only [encode.sk_encode_loop3.body]
    split
    · rename_i hi
      have hik : i2.val < k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := out.property
      have hbd : o.val + n.val ≤ out.val.length := by omega
      step*
      refine WP.spec_bind (pack_signed_spec _ (v[i2.val]'hik) ?_ bb ea c s hb hab hc (hrng _ hik) ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i3.val - o.val := s_post2
        rw [this, i3_post]; omega
      · intro s2 hs2
        step*
        have hs1' : bytes s2 = Spec.BitPack v[i2.val]! ea bb.val := by rw [hs2, vec_getElem!_eq v _ hik]
        obtain ⟨b1, b2⟩ := block_write_step out s2 index_mut_back o i3 o0 n.val i2.val pre
          (fun (t : Nat) => Spec.BitPack v[t]! ea bb.val) hFlen hpre h2' (by rw [i3_post]; omega) s_post3 hs1' h3
          (by omega)
        refine ⟨by rw [b1]; exact h1, by omega, by rw [i3_post, i4_post]; omega, ?_, by omega⟩
        show List.take (o0 + i4.val * n.val) (bytes (index_mut_back s2)) = _
        rw [i4_post]
        exact b2
    · rename_i hi
      have hi' : i2.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3 h2'
      exact ⟨h1, h2', h3⟩
  · exact ⟨rfl, hi2, ho, hinv⟩


/-- The `t₀` block loop of `sk_encode`: blocks `BitPack v[t] (2^12-1) 2^12` of 416 bytes. -/
theorem sk_encode_loop4_spec {K : Usize} (k : Nat) (t0 : Array (Array U32 256#usize) K)
    (v : Vector RPoly k) (hv : ReprIntVec t0 v)
    (hrng : ∀ i : Nat, ∀ hi : i < k, ∀ j : Nat, ∀ hj : j < 256,
      -(4095 : Int) ≤ (v[i]'hi)[j]'hj ∧ (v[i]'hi)[j]'hj ≤ (4096 : Int))
    (pre : List UInt8) (o0 : Nat) (hpre : pre.length = o0)
    (out0 : Slice U8) (hL : o0 + k * 416 ≤ out0.val.length) (o ii : Usize) (hi2 : ii.val ≤ k)
    (ho : o.val = o0 + ii.val * 416)
    (hinv : (bytes out0).take (o0 + ii.val * 416) = pre ++ flat (fun t => Spec.BitPack v[t]! 4095 4096) ii.val) :
    encode.sk_encode_loop4 t0 out0 o ii ⦃ r => r.val.length = out0.val.length ∧
      (bytes r).take (o0 + k * 416) = pre ++ flat (fun t => Spec.BitPack v[t]! 4095 4096) k ⦄ := by
  have hKk := hv.len
  have hFlen : ∀ t : Nat, (Spec.BitPack v[t]! 4095 4096).length = 416 := fun t => by
    rw [BitPack_length]; decide +kernel
  unfold encode.sk_encode_loop4
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize × Usize) => k - p.2.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.2.val ≤ k ∧ p.2.1.val = o0 + p.2.2.val * 416 ∧
      (bytes p.1).take (o0 + p.2.2.val * 416) = pre ++ flat (fun t => Spec.BitPack v[t]! 4095 4096) p.2.2.val)
  · rintro ⟨out, o, ii⟩ ⟨h1, h2, h2', h3⟩
    dsimp only at h1 h2 h2' h3
    simp only [encode.sk_encode_loop4.body]
    split
    · rename_i hi
      have hik : ii.val < k := by scalar_tac
      have hm1 : (ii.val + 1) * 416 ≤ k * 416 := Nat.mul_le_mul_right _ hik
      have e : (ii.val + 1) * 416 = ii.val * 416 + 416 := by ring
      have hlen := out.property
      have hbd : o.val + 416 ≤ out.val.length := by omega
      step*
      have hi1 : i1.val = 4096 := by simp [i1_post1, U32.size, U32.numBits]
      refine WP.spec_bind (pack_signed_spec _ (v[ii.val]'hik) ?_ i1 4095 13#usize s (by rw [hi1]; decide)
        (by rw [hi1]; decide) (by rw [hi1]; decide +kernel) (by intro j hj; have := hrng _ hik j hj; rw [hi1]; push_cast; exact this) ?_) ?_
      · rw [a_post2]; exact hv.elt _ hik
      · have : s.val.length = i2.val - o.val := s_post2
        rw [this, i2_post]; simp
      · intro s2 hs2
        step*
        have hs1' : bytes s2 = Spec.BitPack v[ii.val]! 4095 4096 := by rw [hs2, vec_getElem!_eq v _ hik, hi1]
        obtain ⟨b1, b2⟩ := block_write_step out s2 index_mut_back o i2 o0 416 ii.val pre
          (fun (t : Nat) => Spec.BitPack v[t]! 4095 4096) hFlen hpre h2' (by rw [i2_post]; omega) s_post3 hs1' h3
          (by omega)
        refine ⟨by rw [b1]; exact h1, by omega, by omega, ?_, by omega⟩
        show List.take (o0 + i3.val * 416) (bytes (index_mut_back s2)) = _
        rw [i3_post]
        exact b2
    · rename_i hi
      have hi' : ii.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      exact ⟨h1, h3⟩
  · exact ⟨rfl, hi2, ho, hinv⟩


/-- The `tr` copy loop of `sk_encode`: `out[64..128) ← tr`. -/
theorem sk_encode_loop1_spec (tr : Array U8 64#usize) (out0 : Slice U8) (hL : 128 ≤ out0.val.length)
    (out : Slice U8) (i : Usize) (hi : i.val ≤ 64) (hlen : out.val.length = out0.val.length)
    (hinv : ∀ k, (bytes out)[k]? = if 64 ≤ k ∧ k < 64 + i.val then (bytesA tr)[k - 64]? else (bytes out0)[k]?) :
    encode.sk_encode_loop1 tr out i ⦃ out' => out'.val.length = out0.val.length ∧
      ∀ k, (bytes out')[k]? = if 64 ≤ k ∧ k < 128 then (bytesA tr)[k - 64]? else (bytes out0)[k]? ⦄ := by
  unfold encode.sk_encode_loop1
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × Usize) => 64 - p.2.val)
    (fun p => p.1.val.length = out0.val.length ∧ p.2.val ≤ 64 ∧
      ∀ k, (bytes p.1)[k]? = if 64 ≤ k ∧ k < 64 + p.2.val then (bytesA tr)[k - 64]? else (bytes out0)[k]?)
  · rintro ⟨out, i⟩ ⟨h1, h2, h3⟩
    dsimp only at h1 h2 h3
    simp only [encode.sk_encode_loop1.body]
    split
    · rename_i hi
      have hi' : i.val < 64 := by scalar_tac
      step*
      subst s_post2
      have hl3 : 64 + i.val < out.val.length := by
        have := s_post1; simp at this; omega
      refine ⟨by simp [h1], by omega, fun k => ?_, by omega⟩
      rw [bytes_set, List.getElem?_set, h3 k, i2_post, i3_post]
      have hr := bytesA_getElem? tr i.val (by simpa using hi')
      by_cases hk1 : 64 + i.val = k
      · subst hk1
        simp [hl3, i1_post2, hr]
      · rw [if_neg hk1]
        have h4 : (64 ≤ k ∧ k < 64 + (i.val + 1)) ↔ (64 ≤ k ∧ k < 64 + i.val) := by omega
        simp only [h4]
    · rename_i hi
      have hi' : i.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨h1, fun k => ?_⟩
      rw [h3 k, hi']
  · exact ⟨hlen, hi, hinv⟩

theorem append3_getElem? (A B C : List UInt8) (hA : A.length = 32) (hB : B.length = 32) (k : Nat) :
    (A ++ B ++ C)[k]? = if k < 32 then A[k]? else if k < 64 then B[k - 32]? else C[k - 64]? := by
  rw [List.append_assoc]
  by_cases h1 : k < 32
  · rw [List.getElem?_append_left (by omega)]; simp [h1]
  · rw [List.getElem?_append_right (by omega)]
    by_cases h2 : k < 64
    · rw [List.getElem?_append_left (by omega)]; simp [h1, h2, hA]
    · rw [List.getElem?_append_right (by omega)]; simp [h1, h2, hA, hB]; try (congr 1)


theorem skLen_eq (sp : Spec.Params) (hd : sp.d = 13) :
    sp.skLen = 128 + (sp.ℓ + sp.k) * (32 * bitlen (2 * sp.η)) + sp.k * 416 := by
  unfold Spec.Params.skLen
  rw [hd]; ring

/-- **`sk_encode` is `skEncode`** (Algorithm 24), for `s₁, s₂` with coefficients in `[-η, η]`
(`2η < 2^22`, true of every FIPS 204 parameter set) and `t₀` with coefficients in `[-(2^12-1), 2^12]`. -/
theorem sk_encode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hη : 2 * sp.η < 2 ^ 22)
    (rho key : Array U8 32#usize) (tr : Array U8 64#usize)
    (s1 : Array (Array U32 256#usize) L) (s2 t0 : Array (Array U32 256#usize) K)
    (v1 : Vector RPoly sp.ℓ) (v2 v3 : Vector RPoly sp.k)
    (h1 : ReprIntVec s1 v1) (h2 : ReprIntVec s2 v2) (h3 : ReprIntVec t0 v3)
    (hr1 : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.η : Int) ≤ (v1[i]'hi)[j]'hj ∧ (v1[i]'hi)[j]'hj ≤ (sp.η : Int))
    (hr2 : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.η : Int) ≤ (v2[i]'hi)[j]'hj ∧ (v2[i]'hi)[j]'hj ≤ (sp.η : Int))
    (hr3 : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      -(4095 : Int) ≤ (v3[i]'hi)[j]'hj ∧ (v3[i]'hi)[j]'hj ≤ (4096 : Int))
    (out : Slice U8) (hL : out.val.length = sp.skLen) :
    encode.sk_encode ip rho key tr s1 s2 t0 out ⦃ out' =>
      bytes out' = Spec.skEncode sp (bytesA rho) (bytesA key) (bytesA tr) v1 v2 v3 ⦄ := by
  have hLen := skLen_eq sp hp.d_eq
  have hq : Spec.q = 8380417 := rfl
  have hη' : sp.η < Spec.q := by omega
  have hη2 : sp.η + sp.η < Spec.q := by omega
  have hc : ip.eta_bits.val = bitlen (sp.η + sp.η) := by rw [hp.eta_bits, two_mul]
  have hb : ip.eta.val < Spec.q := by rw [hp.eta]; exact hη'
  have hab : sp.η + ip.eta.val < Spec.q := by rw [hp.eta]; exact hη2
  have hc' : ip.eta_bits.val = bitlen (sp.η + ip.eta.val) := by rw [hp.eta]; exact hc
  rw [skEncode_eq]
  unfold encode.sk_encode
  refine WP.spec_bind (sk_encode_loop0_spec rho key out (by omega) out 0#usize (by simp) rfl
    (by intro k; simp)) ?_
  rintro out1 ⟨hl1, hp1⟩
  refine WP.spec_bind (sk_encode_loop1_spec tr out1 (by omega) out1 0#usize (by simp) rfl
    (by intro k; simp)) ?_
  rintro out2 ⟨hl2, hp2⟩
  have hbits : ip.eta_bits.val ≤ 22 := by rw [hp.eta_bits]; exact bitlen_le_of_lt hη
  step as ⟨n, n_post⟩
  have hnv : n.val = 32 * bitlen (2 * sp.η) := by rw [n_post, hp.eta_bits]
  have hLen' : out2.val.length = 128 + sp.ℓ * n.val + sp.k * n.val + sp.k * 416 := by
    rw [hl2, hl1, hL, hLen, hnv]; ring
  have h128 : 128 ≤ out2.val.length := by omega
  have hpre : (bytesA rho ++ bytesA key ++ bytesA tr).length = 128 := by simp
  have hprefix : (bytes out2).take 128 = bytesA rho ++ bytesA key ++ bytesA tr := by
    refine take_of_pointwise out2 _ 128 hpre h128 (fun k => (bytes out)[k]?) (fun k => ?_)
    rw [hp2 k, append3_getElem? _ _ _ (by simp) (by simp) k]
    have := hp1 k
    by_cases a1 : k < 32
    · simp [this, a1, (show ¬ 64 ≤ k by omega), (show k < 128 by omega)]
    · by_cases a2 : k < 64
      · simp [this, a1, a2, (show ¬ 64 ≤ k by omega), (show k < 128 by omega)]
      · by_cases a3 : k < 128
        · simp [a1, a2, a3, (show 64 ≤ k by omega)]
        · simp [this, a1, a2, a3]
  have hr1' : ∀ i : Nat, ∀ hi : i < sp.ℓ, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.η : Int) ≤ (v1[i]'hi)[j]'hj ∧ (v1[i]'hi)[j]'hj ≤ (ip.eta.val : Int) :=
    fun i hi j hj => by rw [hp.eta]; exact hr1 i hi j hj
  have hr2' : ∀ i : Nat, ∀ hi : i < sp.k, ∀ j : Nat, ∀ hj : j < 256,
      -(sp.η : Int) ≤ (v2[i]'hi)[j]'hj ∧ (v2[i]'hi)[j]'hj ≤ (ip.eta.val : Int) :=
    fun i hi j hj => by rw [hp.eta]; exact hr2 i hi j hj
  have hF1 : ∀ t : Nat, (Spec.BitPack v1[t]! sp.η ip.eta.val).length = n.val := fun t => by
    rw [BitPack_length, ← hc', n_post]
  have hF2 : ∀ t : Nat, (Spec.BitPack v2[t]! sp.η ip.eta.val).length = n.val := fun t => by
    rw [BitPack_length, ← hc', n_post]
  have hF3 : ∀ t : Nat, (Spec.BitPack v3[t]! 4095 4096).length = 416 := fun t => by
    rw [BitPack_length]; decide +kernel
  have hk1 : (sp.ℓ + 0) = sp.ℓ := rfl
  refine WP.spec_bind (sk_encode_loop2_spec ip.eta ip.eta_bits sp.η hb hab hc' n n_post sp.ℓ s1 v1 h1 hr1'
    _ 128 hpre out2 (by omega) 128#usize 0#usize (by simp) (by simp) ?_) ?_
  · simpa [flat_zero] using hprefix
  rintro ⟨out3, o⟩ ⟨hl3, ho3, ht3⟩
  dsimp only at hl3 ho3 ht3
  have hpre2 : (bytesA rho ++ bytesA key ++ bytesA tr ++
      flat (fun t => Spec.BitPack v1[t]! sp.η ip.eta.val) sp.ℓ).length = 128 + sp.ℓ * n.val := by
    rw [List.length_append, flat_length _ n.val hF1, hpre]
  refine WP.spec_bind (sk_encode_loop3_spec ip.eta ip.eta_bits sp.η hb hab hc' n n_post sp.k s2 v2 h2 hr2'
    _ (128 + sp.ℓ * n.val) hpre2 out3 (by omega) o 0#usize (by simp) (by simpa using ho3) ?_) ?_
  · simpa [flat_zero] using ht3
  rintro ⟨out4, o1⟩ ⟨hl4, ho4, ht4⟩
  dsimp only at hl4 ho4 ht4
  have hpre3 : (bytesA rho ++ bytesA key ++ bytesA tr ++
      flat (fun t => Spec.BitPack v1[t]! sp.η ip.eta.val) sp.ℓ ++
      flat (fun t => Spec.BitPack v2[t]! sp.η ip.eta.val) sp.k).length = 128 + sp.ℓ * n.val + sp.k * n.val := by
    rw [List.length_append, flat_length _ n.val hF2, hpre2]
  refine WP.spec_mono (sk_encode_loop4_spec sp.k t0 v3 h3 hr3 _ (128 + sp.ℓ * n.val + sp.k * n.val) hpre3
    out4 (by omega) o1 0#usize (by simp) (by simpa using ho4) ?_) ?_
  · simpa [flat_zero] using ht4
  rintro r ⟨hl5, ht5⟩
  have h4095 : 2 ^ (sp.d - 1) - 1 = 4095 := by rw [hp.d_eq]; rfl
  have h4096 : 2 ^ (sp.d - 1) = 4096 := by rw [hp.d_eq]; rfl
  rw [h4095, h4096]
  have htk : List.take (128 + sp.ℓ * n.val + sp.k * n.val + sp.k * 416) (bytes r) = bytes r :=
    List.take_of_length_le (by rw [bytes_length]; omega)
  rw [← htk, ht5, hp.eta]
  rfl


/-! ## `sk_decode` -/

theorem bytes_slice_of (sk s : Slice U8) (o e n : Nat) (hs : s.val = List.slice o e sk.val) (hn : e - o = n) :
    bytes s = slice (bytes sk) o n := by
  have hsv : s.val = (sk.val.drop o).take n := by rw [hs]; unfold List.slice; rw [hn]
  simp [bytes, hsv, slice, List.map_take, List.map_drop]

theorem bytesA_eq_slice {n : Usize} (a : Array U8 n) (sk : Slice U8) (off : Nat)
    (h : ∀ k, k < n.val → (bytesA a)[k]? = (bytes sk)[off + k]?) :
    bytesA a = slice (bytes sk) off n.val := by
  apply List.ext_getElem?
  intro k
  by_cases hk : k < n.val
  · rw [h k hk]
    simp [slice, List.getElem?_drop, hk]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [slice, hk]

theorem sk_decode_loop0_spec {K L : Usize} (sk : Slice U8) (out0 out : encode.SecretKey K L) (i : Usize)
    (hL : 64 ≤ sk.val.length) (hi : i.val ≤ 32)
    (hfr : { out with rho := out0.rho, key := out0.key } = out0)
    (ha : ∀ k, (bytesA out.rho)[k]? = if k < i.val then (bytes sk)[k]? else (bytesA out0.rho)[k]?)
    (hb : ∀ k, (bytesA out.key)[k]? = if k < i.val then (bytes sk)[32 + k]? else (bytesA out0.key)[k]?) :
    encode.sk_decode_into_loop0 sk out i ⦃ r =>
      { r with rho := out0.rho, key := out0.key } = out0 ∧
      (∀ k, (bytesA r.rho)[k]? = if k < 32 then (bytes sk)[k]? else (bytesA out0.rho)[k]?) ∧
      (∀ k, (bytesA r.key)[k]? = if k < 32 then (bytes sk)[32 + k]? else (bytesA out0.key)[k]?) ⦄ := by
  unfold encode.sk_decode_into_loop0
  apply loop.spec_decr_nat
    (fun (p : encode.SecretKey K L × Usize) => 32 - p.2.val)
    (fun p => p.2.val ≤ 32 ∧ { p.1 with rho := out0.rho, key := out0.key } = out0 ∧
      (∀ k, (bytesA p.1.rho)[k]? = if k < p.2.val then (bytes sk)[k]? else (bytesA out0.rho)[k]?) ∧
      (∀ k, (bytesA p.1.key)[k]? = if k < p.2.val then (bytes sk)[32 + k]? else (bytesA out0.key)[k]?))
  · rintro ⟨out, i⟩ ⟨h2, hf, h3, h4⟩
    dsimp only at h2 hf h3 h4
    simp only [encode.sk_decode_into_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 32 := by scalar_tac
      step*
      subst i1_post2 i3_post2 a_post a1_post
      have hq1 : sk.val[i.val]? = some (sk.val[i.val]'i1) := List.getElem?_eq_getElem i1
      have hq2 : sk.val[32 + i.val]? = some (sk.val[i2.val]'i3) := by
        rw [← i2_post]; exact List.getElem?_eq_getElem i3
      have hlt : i.val < (bytesA out.rho).length := by simpa using hi'
      have hlt2 : i.val < (bytesA out.key).length := by simpa using hi'
      refine ⟨by omega, hf, fun k => ?_, fun k => ?_, by omega⟩
      · rw [bytesA_set, List.getElem?_set, h3 k, i4_post]
        by_cases hk : i.val = k
        · subst hk; simp [hi', bytes_getElem?_eq, hq1]
        · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
      · rw [bytesA_set, List.getElem?_set, h4 k, i4_post]
        by_cases hk : i.val = k
        · subst hk; simp [hi', bytes_getElem?_eq, hq2]
        · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨hf, fun k => ?_, fun k => ?_⟩
      · rw [h3 k, hi']
      · rw [h4 k, hi']
  · exact ⟨hi, hfr, ha, hb⟩

theorem sk_decode_loop1_spec {K L : Usize} (sk : Slice U8) (out0 out : encode.SecretKey K L) (i : Usize)
    (hL : 128 ≤ sk.val.length) (hi : i.val ≤ 64)
    (hfr : { out with tr := out0.tr } = out0)
    (ha : ∀ k, (bytesA out.tr)[k]? = if k < i.val then (bytes sk)[64 + k]? else (bytesA out0.tr)[k]?) :
    encode.sk_decode_into_loop1 sk out i ⦃ r =>
      { r with tr := out0.tr } = out0 ∧
      ∀ k, (bytesA r.tr)[k]? = if k < 64 then (bytes sk)[64 + k]? else (bytesA out0.tr)[k]? ⦄ := by
  unfold encode.sk_decode_into_loop1
  apply loop.spec_decr_nat
    (fun (p : encode.SecretKey K L × Usize) => 64 - p.2.val)
    (fun p => p.2.val ≤ 64 ∧ { p.1 with tr := out0.tr } = out0 ∧
      ∀ k, (bytesA p.1.tr)[k]? = if k < p.2.val then (bytes sk)[64 + k]? else (bytesA out0.tr)[k]?)
  · rintro ⟨out, i⟩ ⟨h2, hf, h3⟩
    dsimp only at h2 hf h3
    simp only [encode.sk_decode_into_loop1.body]
    split
    · rename_i hi
      have hi' : i.val < 64 := by scalar_tac
      step*
      subst i2_post2 a_post
      have hq2 : sk.val[64 + i.val]? = some (sk.val[i1.val]'i2) := by
        rw [← i1_post]; exact List.getElem?_eq_getElem i2
      have hlt2 : i.val < (bytesA out.tr).length := by simpa using hi'
      refine ⟨by omega, hf, fun k => ?_, by omega⟩
      rw [bytesA_set, List.getElem?_set, h3 k, i3_post]
      by_cases hk : i.val = k
      · subst hk; simp [hi', bytes_getElem?_eq, hq2]
      · simp [hk, show (k < i.val + 1) ↔ (k < i.val) from by omega]
    · rename_i hi
      have hi' : i.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨hf, fun k => ?_⟩
      rw [h3 k, hi']
  · exact ⟨hi, hfr, ha⟩


theorem sk_decode_loop2_spec {K L : Usize} (bb : U32) (c : Usize) (ea : Nat) (hb : bb.val < Spec.q)
    (hc : c.val = bitlen (ea + bb.val)) (hc22 : c.val ≤ 22) (n : Usize) (hn : n.val = 32 * c.val)
    (k : Nat) (hKk : L.val = k) (sk : Slice U8) (o0 : Nat) (hL : o0 + k * n.val ≤ sk.val.length)
    (out0 out : encode.SecretKey K L) (o i2 : Usize)
    (hfr : { out with s1 := out0.s1 } = out0) (hi2 : i2.val ≤ k)
    (ho : o.val = o0 + i2.val * n.val)
    (hinv : ∀ j (_hj : j < i2.val) (hj' : j < out.s1.val.length),
      ReprInt (out.s1.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * n.val) n.val) ea bb.val)) :
    encode.sk_decode_into_loop2 bb c sk out n o i2 ⦃ r => { r.1 with s1 := out0.s1 } = out0 ∧ r.2.val = o0 + k * n.val ∧
      ∀ j (_hj : j < k) (hj' : j < r.1.s1.val.length),
        ReprInt (r.1.s1.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * n.val) n.val) ea bb.val) ⦄ := by
  unfold encode.sk_decode_into_loop2
  apply loop.spec_decr_nat
    (fun (p : encode.SecretKey K L × Usize × Usize) => k - p.2.2.val)
    (fun p => p.2.2.val ≤ k ∧ { p.1 with s1 := out0.s1 } = out0 ∧ p.2.1.val = o0 + p.2.2.val * n.val ∧
      ∀ j (hj : j < p.2.2.val) (hj' : j < p.1.s1.val.length),
        ReprInt (p.1.s1.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * n.val) n.val) ea bb.val))
  · rintro ⟨out, o, i2⟩ ⟨h2, hf, h2', h3⟩
    dsimp only at h2 hf h2' h3
    simp only [encode.sk_decode_into_loop2.body]
    split
    · rename_i hi
      have hik : i2.val < k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := sk.property
      have hlen2 := out.s1.property
      have hbd : o.val + n.val ≤ sk.val.length := by omega
      step*
      have hslen : s.val.length = 32 * c.val := by
        have : s.val.length = i3.val - o.val := s_post2
        rw [this, i3_post]; omega
      refine WP.spec_bind (unpack_signed_into_spec s bb ea c hb hc hc22 hslen _) ?_
      intro w hw
      step*
      have hsb0 := bytes_slice_of sk s o.val i3.val n.val s_post1 (by rw [i3_post]; omega)
      have hsb : bytes s = slice (bytes sk) (o0 + i2.val * n.val) n.val := by rw [hsb0, h2']
      subst a_post3
      refine ⟨by omega, hf, by rw [i3_post, i4_post]; omega, ?_, by omega⟩
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
      rw [hi'] at h2' h3
      exact ⟨hf, h2', h3⟩
  · exact ⟨hi2, hfr, ho, hinv⟩

theorem sk_decode_loop3_spec {K L : Usize} (bb : U32) (c : Usize) (ea : Nat) (hb : bb.val < Spec.q)
    (hc : c.val = bitlen (ea + bb.val)) (hc22 : c.val ≤ 22) (n : Usize) (hn : n.val = 32 * c.val)
    (k : Nat) (hKk : K.val = k) (sk : Slice U8) (o0 : Nat) (hL : o0 + k * n.val ≤ sk.val.length)
    (out0 out : encode.SecretKey K L) (o i2 : Usize)
    (hfr : { out with s2 := out0.s2 } = out0) (hi2 : i2.val ≤ k)
    (ho : o.val = o0 + i2.val * n.val)
    (hinv : ∀ j (_hj : j < i2.val) (hj' : j < out.s2.val.length),
      ReprInt (out.s2.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * n.val) n.val) ea bb.val)) :
    encode.sk_decode_into_loop3 bb c sk out n o i2 ⦃ r => { r.1 with s2 := out0.s2 } = out0 ∧ r.2.val = o0 + k * n.val ∧
      ∀ j (_hj : j < k) (hj' : j < r.1.s2.val.length),
        ReprInt (r.1.s2.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * n.val) n.val) ea bb.val) ⦄ := by
  unfold encode.sk_decode_into_loop3
  apply loop.spec_decr_nat
    (fun (p : encode.SecretKey K L × Usize × Usize) => k - p.2.2.val)
    (fun p => p.2.2.val ≤ k ∧ { p.1 with s2 := out0.s2 } = out0 ∧ p.2.1.val = o0 + p.2.2.val * n.val ∧
      ∀ j (hj : j < p.2.2.val) (hj' : j < p.1.s2.val.length),
        ReprInt (p.1.s2.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * n.val) n.val) ea bb.val))
  · rintro ⟨out, o, i2⟩ ⟨h2, hf, h2', h3⟩
    dsimp only at h2 hf h2' h3
    simp only [encode.sk_decode_into_loop3.body]
    split
    · rename_i hi
      have hik : i2.val < k := by scalar_tac
      have hm1 : (i2.val + 1) * n.val ≤ k * n.val := Nat.mul_le_mul_right _ hik
      have e : (i2.val + 1) * n.val = i2.val * n.val + n.val := by ring
      have hlen := sk.property
      have hlen2 := out.s2.property
      have hbd : o.val + n.val ≤ sk.val.length := by omega
      step*
      have hslen : s.val.length = 32 * c.val := by
        have : s.val.length = i3.val - o.val := s_post2
        rw [this, i3_post]; omega
      refine WP.spec_bind (unpack_signed_into_spec s bb ea c hb hc hc22 hslen _) ?_
      intro w hw
      step*
      have hsb0 := bytes_slice_of sk s o.val i3.val n.val s_post1 (by rw [i3_post]; omega)
      have hsb : bytes s = slice (bytes sk) (o0 + i2.val * n.val) n.val := by rw [hsb0, h2']
      subst a_post3
      refine ⟨by omega, hf, by rw [i3_post, i4_post]; omega, ?_, by omega⟩
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
      rw [hi'] at h2' h3
      exact ⟨hf, h2', h3⟩
  · exact ⟨hi2, hfr, ho, hinv⟩


theorem sk_decode_loop4_spec {K L : Usize} (k : Nat) (hKk : K.val = k) (sk : Slice U8) (o0 : Nat)
    (hL : o0 + k * 416 ≤ sk.val.length)
    (out0 out : encode.SecretKey K L) (o ii : Usize) (hi2 : ii.val ≤ k)
    (hfr : { out with t0 := out0.t0 } = out0)
    (ho : o.val = o0 + ii.val * 416)
    (hinv : ∀ j (hj : j < ii.val) (hj' : j < out.t0.val.length),
      ReprInt (out.t0.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * 416) 416) 4095 4096)) :
    encode.sk_decode_into_loop4 sk out o ii ⦃ r =>
      { r with t0 := out0.t0 } = out0 ∧ ∀ j (hj : j < k) (hj' : j < r.t0.val.length),
        ReprInt (r.t0.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * 416) 416) 4095 4096) ⦄ := by
  unfold encode.sk_decode_into_loop4
  apply loop.spec_decr_nat
    (fun (p : encode.SecretKey K L × Usize × Usize) => k - p.2.2.val)
    (fun p => p.2.2.val ≤ k ∧ { p.1 with t0 := out0.t0 } = out0 ∧ p.2.1.val = o0 + p.2.2.val * 416 ∧
      ∀ j (hj : j < p.2.2.val) (hj' : j < p.1.t0.val.length),
        ReprInt (p.1.t0.val[j]'hj') (BitUnpack (slice (bytes sk) (o0 + j * 416) 416) 4095 4096))
  · rintro ⟨out, o, ii⟩ ⟨h2, hf, h2', h3⟩
    dsimp only at h2 hf h2' h3
    simp only [encode.sk_decode_into_loop4.body]
    split
    · rename_i hi
      have hik : ii.val < k := by scalar_tac
      have hm1 : (ii.val + 1) * 416 ≤ k * 416 := Nat.mul_le_mul_right _ hik
      have e : (ii.val + 1) * 416 = ii.val * 416 + 416 := by ring
      have hlen := sk.property
      have hlen2 := out.t0.property
      have hbd : o.val + 416 ≤ sk.val.length := by omega
      step*
      have hi1 : i2.val = 4096 := by simp [i2_post1, U32.size, U32.numBits]
      have hslen : s.val.length = 32 * (13#usize).val := by
        have : s.val.length = i1.val - o.val := s_post2
        rw [this, i1_post]; simp
      refine WP.spec_bind (unpack_signed_into_spec s i2 4095 13#usize (by rw [hi1]; decide)
        (by rw [hi1]; decide +kernel) (by simp) hslen _) ?_
      intro w hw
      step*
      have hsb0 := bytes_slice_of sk s o.val i1.val 416 s_post1 (by rw [i1_post]; omega)
      have hsb : bytes s = slice (bytes sk) (o0 + ii.val * 416) 416 := by rw [hsb0, h2']
      subst a_post3
      refine ⟨by omega, hf, by rw [i1_post, i3_post]; omega, ?_, by omega⟩
      intro j hj hj'
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rename_i hji
        subst hji
        rw [← hsb, ← hi1]; exact hw
      · exact h3 j (by omega) _
    · rename_i hi
      have hi' : ii.val = k := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      exact ⟨hf, h3⟩
  · exact ⟨hi2, hfr, ho, hinv⟩


/-- **`sk_decode` is `skDecode`** (Algorithm 25), for *every* byte string `sk` of length `skLen`
(with `2η < 2^22`): the decoder never fails, `ρ, K, tr` are the corresponding byte ranges, and
`s₁, s₂, t₀` denote the spec's integer vectors modulo `q` (`ReprIntVec`), whatever the packed values. -/
theorem sk_decode_into_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hη : 2 * sp.η < 2 ^ 22) (sk : Slice U8) (hL : sk.val.length = sp.skLen)
    (out : encode.SecretKey K L) :
    encode.sk_decode_into ip sk out ⦃ r =>
      bytesA r.rho = (Spec.skDecode sp (bytes sk)).1 ∧
      bytesA r.key = (Spec.skDecode sp (bytes sk)).2.1 ∧
      bytesA r.tr = (Spec.skDecode sp (bytes sk)).2.2.1 ∧
      ReprIntVec r.s1 (Spec.skDecode sp (bytes sk)).2.2.2.1 ∧
      ReprIntVec r.s2 (Spec.skDecode sp (bytes sk)).2.2.2.2.1 ∧
      ReprIntVec r.t0 (Spec.skDecode sp (bytes sk)).2.2.2.2.2 ⦄ := by
  have hLen := skLen_eq sp hp.d_eq
  have hq : Spec.q = 8380417 := rfl
  have hη' : sp.η < Spec.q := by omega
  have hη2 : sp.η + sp.η < Spec.q := by omega
  have hc : ip.eta_bits.val = bitlen (sp.η + sp.η) := by rw [hp.eta_bits, two_mul]
  have hb : ip.eta.val < Spec.q := by rw [hp.eta]; exact hη'
  have hc' : ip.eta_bits.val = bitlen (sp.η + ip.eta.val) := by rw [hp.eta]; exact hc
  have hbits : ip.eta_bits.val ≤ 22 := by rw [hp.eta_bits]; exact bitlen_le_of_lt hη
  have hd := hp.d_eq
  unfold encode.sk_decode_into
  refine WP.spec_bind (sk_decode_loop0_spec sk out out 0#usize (by omega) (by simp) rfl
    (by intro k; simp) (by intro k; simp)) ?_
  intro out1 ⟨hf1, h9, h10⟩
  try dsimp only at hf1 h9 h10
  refine WP.spec_bind (sk_decode_loop1_spec sk out1 out1 0#usize (by omega) (by simp) rfl
    (by intro k; simp)) ?_
  intro out2 ⟨hf2, h11⟩
  try dsimp only at hf2 h11
  step as ⟨n, n_post⟩
  have hnv : n.val = 32 * bitlen (2 * sp.η) := by rw [n_post, hp.eta_bits]
  have hLen' : sk.val.length = 128 + sp.ℓ * n.val + sp.k * n.val + sp.k * 416 := by
    rw [hL, hLen, hnv]; ring
  refine WP.spec_bind (sk_decode_loop2_spec ip.eta ip.eta_bits sp.η hb hc' hbits n n_post sp.ℓ hp.L_eq sk 128
    (by omega) out2 out2 128#usize 0#usize rfl (by simp) (by simp) (fun j hj => absurd hj (by simp))) ?_
  rintro ⟨out3, o⟩ ⟨hf3, ho2, h12⟩
  try dsimp only at hf3 ho2 h12
  refine WP.spec_bind (sk_decode_loop3_spec ip.eta ip.eta_bits sp.η hb hc' hbits n n_post sp.k hp.K_eq sk
    (128 + sp.ℓ * n.val) (by omega) out3 out3 o 0#usize rfl (by simp) (by simpa using ho2)
    (fun j hj => absurd hj (by simp))) ?_
  rintro ⟨out4, o1⟩ ⟨hf4, ho3, h13⟩
  try dsimp only at hf4 ho3 h13
  refine WP.spec_mono (sk_decode_loop4_spec sp.k hp.K_eq sk (128 + sp.ℓ * n.val + sp.k * n.val) (by omega) out4
    out4 o1 0#usize (by simp) rfl (by simpa using ho3) (fun j hj => absurd hj (by simp))) ?_
  intro out5 ⟨hf5, h14⟩
  try dsimp only at hf5 h14
  obtain ⟨f1, f2, f3⟩ := skDecode_fst sp (bytes sk)
  have eRho : out5.rho = out1.rho := by
    have e5 : out5.rho = out4.rho := by have h := congrArg encode.SecretKey.rho hf5; exact h
    have e4 : out4.rho = out3.rho := by have h := congrArg encode.SecretKey.rho hf4; exact h
    have e3 : out3.rho = out2.rho := by have h := congrArg encode.SecretKey.rho hf3; exact h
    have e2 : out2.rho = out1.rho := by have h := congrArg encode.SecretKey.rho hf2; exact h
    rw [e5, e4, e3, e2]
  have eKey : out5.key = out1.key := by
    have e5 : out5.key = out4.key := by have h := congrArg encode.SecretKey.key hf5; exact h
    have e4 : out4.key = out3.key := by have h := congrArg encode.SecretKey.key hf4; exact h
    have e3 : out3.key = out2.key := by have h := congrArg encode.SecretKey.key hf3; exact h
    have e2 : out2.key = out1.key := by have h := congrArg encode.SecretKey.key hf2; exact h
    rw [e5, e4, e3, e2]
  have eTr : out5.tr = out2.tr := by
    have e5 : out5.tr = out4.tr := by have h := congrArg encode.SecretKey.tr hf5; exact h
    have e4 : out4.tr = out3.tr := by have h := congrArg encode.SecretKey.tr hf4; exact h
    have e3 : out3.tr = out2.tr := by have h := congrArg encode.SecretKey.tr hf3; exact h
    rw [e5, e4, e3]
  have eS1 : out5.s1 = out3.s1 := by
    have e5 : out5.s1 = out4.s1 := by have h := congrArg encode.SecretKey.s1 hf5; exact h
    have e4 : out4.s1 = out3.s1 := by have h := congrArg encode.SecretKey.s1 hf4; exact h
    rw [e5, e4]
  have eS2 : out5.s2 = out4.s2 := by have h := congrArg encode.SecretKey.s2 hf5; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f1, eRho]
    refine bytesA_eq_slice out1.rho sk 0 (fun k hk => ?_)
    have hk' : k < 32 := by simpa using hk
    rw [h9 k]; simp [hk']
  · rw [f2, eKey]
    refine bytesA_eq_slice out1.key sk 32 (fun k hk => ?_)
    have hk' : k < 32 := by simpa using hk
    rw [h10 k]; simp [hk']
  · rw [f3, eTr]
    refine bytesA_eq_slice out2.tr sk 64 (fun k hk => ?_)
    have hk' : k < 64 := by simpa using hk
    rw [h11 k]; simp [hk']
  · rw [eS1]
    refine ⟨hp.L_eq, fun i hi => ?_⟩
    rw [skDecode_s1 sp (bytes sk) i hi]
    have := h12 i hi (by rw [out3.s1.property, hp.L_eq]; exact hi)
    rw [hnv, hp.eta] at this
    exact this
  · rw [eS2]
    refine ⟨hp.K_eq, fun i hi => ?_⟩
    rw [skDecode_s2 sp (bytes sk) i hi]
    have := h13 i hi (by rw [out4.s2.property, hp.K_eq]; exact hi)
    rw [hnv, hp.eta] at this
    exact this
  · refine ⟨hp.K_eq, fun i hi => ?_⟩
    rw [skDecode_t0 sp (bytes sk) i hi, hd]
    have := h14 i hi (by rw [out5.t0.property, hp.K_eq]; exact hi)
    rw [hnv] at this
    have e : 128 + (sp.ℓ + sp.k) * (32 * bitlen (2 * sp.η)) + i * (32 * 13) =
        128 + sp.ℓ * (32 * bitlen (2 * sp.η)) + sp.k * (32 * bitlen (2 * sp.η)) + i * 416 := by ring
    rw [e]
    exact this

/-- **`sk_decode` is `skDecode`** (Algorithm 25), from the zero destination; see `sk_decode_into_spec`. -/
theorem sk_decode_spec {K L : Usize} (ip : Impl.params.Params) (sp : Spec.Params)
    (hp : Params.Valid ip K L sp) (hη : 2 * sp.η < 2 ^ 22) (sk : Slice U8) (hL : sk.val.length = sp.skLen) :
    encode.sk_decode K L ip sk ⦃ r =>
      bytesA r.rho = (Spec.skDecode sp (bytes sk)).1 ∧
      bytesA r.key = (Spec.skDecode sp (bytes sk)).2.1 ∧
      bytesA r.tr = (Spec.skDecode sp (bytes sk)).2.2.1 ∧
      ReprIntVec r.s1 (Spec.skDecode sp (bytes sk)).2.2.2.1 ∧
      ReprIntVec r.s2 (Spec.skDecode sp (bytes sk)).2.2.2.2.1 ∧
      ReprIntVec r.t0 (Spec.skDecode sp (bytes sk)).2.2.2.2.2 ⦄ := by
  unfold encode.sk_decode
  exact sk_decode_into_spec ip sp hp hη sk hL _

end Proofs
