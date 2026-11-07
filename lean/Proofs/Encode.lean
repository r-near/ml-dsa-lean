import Proofs.EncodeBits

/-!
# Bit packing: the Rust accumulator loops equal `SimpleBitPack` / `BitUnpack`
-/

open Aeneas Aeneas.Std RustM
open Spec
set_option maxRecDepth 8192

namespace Proofs
open Impl

theorem or_shift (a w n : Nat) (h : a < 2^n) : a ||| (w * 2^n) = a + w * 2^n := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  ring

theorem u64_size_gt : (2:Nat)^50 < U64.size := by
  simp [U64.size, U64.numBits]

/-! ## `bit_pack` -/

/-- Invariant of the inner loop and of the outer loop's head: `out[0..o)` are the bytes of the bit string
`g`, and `acc` holds the next `nbits` bits of `g` (those from position `8·o`). `T` is the total number of bits
consumed so far (`8·o + nbits`), constant along the inner loop. -/
def PackInv (g : Nat → Nat) (L T : Nat) (p : Slice U8 × U64 × Usize × Usize) : Prop :=
  p.1.val.length = L ∧ p.2.1.val = BV g (8 * p.2.2.2.val) p.2.2.1.val ∧
  8 * p.2.2.2.val + p.2.2.1.val = T ∧
  ∀ k (_hk : k < p.2.2.2.val) (hk' : k < p.1.val.length), (p.1.val[k]'hk').val = BV g (8*k) 8

theorem bit_pack_inner (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (L T : Nat) (hT : T ≤ 8 * L)
    (out : Slice U8) (acc : U64) (nbits o : Usize) (hinv : PackInv g L T (out, acc, nbits, o)) :
    encode.bit_pack_loop0_loop0 out acc nbits o ⦃ r => PackInv g L T r ∧ r.2.2.1.val < 8 ⦄ := by
  unfold encode.bit_pack_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × U64 × Usize × Usize) => p.2.2.1.val)
    (fun p => PackInv g L T p)
  · rintro ⟨out, acc, nbits, o⟩ hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    dsimp only at h1 h2 h3 h4
    simp only [encode.bit_pack_loop0_loop0.body]
    split
    · rename_i hn
      have hn' : 8 ≤ nbits.val := by scalar_tac
      step*
      have hb := BV_byte g hg (8*o.val) (nbits.val - 8)
      rw [show 8 + (nbits.val - 8) = nbits.val by omega, ← h2] at hb
      have hi : i.val = acc.val % 256 := by rw [i_post, UScalar.cast_val_eq]; simp
      subst s_post2
      dsimp only [PackInv]
      refine ⟨⟨by simp [h1], ?_, by omega, ?_⟩, by omega⟩
      · show acc1.val = BV g (8 * o1.val) nbits1.val
        rw [acc1_post1, Nat.shiftRight_eq_div_pow, o1_post, nbits1_post1,
          show 8 * (o.val + 1) = 8 * o.val + 8 by ring]
        norm_num
        exact hb.2
      · intro k hk hk'
        simp only [Slice.set_val_eq, List.getElem_set]
        split
        · rename_i hko
          subst hko
          rw [hi]; exact hb.1
        · rename_i hko
          exact h4 k (by omega) _
    · rename_i hn
      have hn' : nbits.val < 8 := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨⟨h1, h2, h3, h4⟩, hn'⟩
  · exact hinv

/-- Outer loop invariant: after `i` values, `c·i` bits have been consumed. -/
def PackOuterInv (g : Nat → Nat) (c L : Nat) (p : Slice U8 × U64 × Usize × Usize × Usize) : Prop :=
  PackInv g L (c * p.2.2.2.2.val) (p.1, p.2.1, p.2.2.1, p.2.2.2.1) ∧ p.2.2.1.val < 8 ∧ p.2.2.2.2.val ≤ 256

theorem bit_pack_core (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (w : Array U32 256#usize) (c : Usize)
    (hc : c.val ≤ 32) (out : Slice U8) (hL : out.val.length = 32 * c.val)
    (hw : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val = BV g (c.val * i) c.val) :
    encode.bit_pack w c out ⦃ out' => out'.val.length = 32 * c.val ∧
      ∀ k (hk : k < out'.val.length), (out'.val[k]).val = BV g (8*k) 8 ⦄ := by
  unfold encode.bit_pack encode.bit_pack_loop0
  apply loop.spec_decr_nat
    (fun (p : Slice U8 × U64 × Usize × Usize × Usize) => 256 - p.2.2.2.2.val)
    (fun p => PackOuterInv g c.val (32 * c.val) p)
  · rintro ⟨out, acc, nbits, o, i⟩ hp
    obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩ := hp
    dsimp only at h1 h2 h3 h4 h5 h6
    simp only [encode.bit_pack_loop0.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := by scalar_tac
      step*
      subst i1_post2
      have hwi := hw i.val hi'
      have hlt : BV g (c.val * i.val) c.val < 2 ^ c.val := BV_lt g hg _ _
      have h32 : 2 ^ c.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hc
      have hi2 : i2.val = BV g (c.val * i.val) c.val := by
        rw [i2_post, UScalar.cast_val_eq, hwi]
        exact Nat.mod_eq_of_lt (by
          have : (2:Nat)^32 < 2^UScalarTy.U64.numBits := by decide +kernel
          omega)
      have hacc_lt : acc.val < 2 ^ nbits.val := by rw [h2]; exact BV_lt g hg _ _
      have hi3 : i3.val = i2.val * 2 ^ nbits.val := by
        rw [i3_post1, Nat.shiftLeft_eq]
        apply Nat.mod_eq_of_lt
        have h64 : 2 ^ nbits.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : i2.val * 2 ^ nbits.val < 2 ^ 32 * 2 ^ 7 :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) h64 (by norm_num)
        have := u64_size_gt
        omega
      have hacc1 : acc1.val = BV g (8 * o.val) (nbits.val + c.val) := by
        rw [acc1_post1, UScalar.val_or, hi3, hi2, or_shift _ _ _ hacc_lt, BV_add, ← h2,
          show 8 * o.val + nbits.val = c.val * i.val by omega]
        ring
      have hT : c.val * (i.val + 1) ≤ 8 * (32 * c.val) := by nlinarith
      refine WP.spec_bind (bit_pack_inner g hg (32 * c.val) (c.val * (i.val + 1)) hT out acc1 nbits1 o
        ⟨h1, by rw [hacc1, nbits1_post], by rw [nbits1_post]; nlinarith, h4⟩) ?_
      rintro ⟨out1, acc2, nbits2, o1⟩ ⟨⟨k1, k2, k3, k4⟩, k5⟩
      dsimp only at k1 k2 k3 k4 k5
      step*
      simp only [PackOuterInv, PackInv]
      refine ⟨⟨⟨k1, k2, by rw [i4_post]; exact k3, k4⟩, k5, by omega⟩, by omega⟩
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      rw [hi'] at h3
      have ho : o.val = 32 * c.val := by omega
      refine ⟨by rw [h1], fun k hk => h4 k (by omega) hk⟩
  · refine ⟨⟨hL, ?_, by simp, by simp⟩, by simp, by simp⟩
    simp [BV]

/-! ## `bit_unpack` -/

/-- Inner loop invariant: `acc` holds the `nbits` bits of `g` from position `s`; `8·o` bits have been read. -/
def UnpackInv (g : Nat → Nat) (s c : Nat) (p : U64 × Usize × Usize) : Prop :=
  p.1.val = BV g s p.2.1.val ∧ s + p.2.1.val = 8 * p.2.2.val ∧ p.2.1.val < c + 8

theorem bit_unpack_inner (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (v : Slice U8) (c : Usize) (hc : c.val ≤ 32)
    (s : Nat) (hs : s + c.val ≤ 8 * v.val.length)
    (hbyte : ∀ o (h : o < v.val.length), BV g (8 * o) 8 = (v.val[o]'h).val)
    (acc : U64) (nbits o : Usize) (hinv : UnpackInv g s c.val (acc, nbits, o)) :
    encode.bit_unpack_loop0_loop0 v c acc nbits o ⦃ r => UnpackInv g s c.val r ∧ c.val ≤ r.2.1.val ⦄ := by
  unfold encode.bit_unpack_loop0_loop0
  apply loop.spec_decr_nat
    (fun (p : U64 × Usize × Usize) => c.val - p.2.1.val)
    (fun p => UnpackInv g s c.val p)
  · rintro ⟨acc, nbits, o⟩ hp
    obtain ⟨h1, h2, h3⟩ := hp
    dsimp only at h1 h2 h3
    simp only [encode.bit_unpack_loop0_loop0.body]
    split
    · rename_i hn
      have hn' : nbits.val < c.val := by scalar_tac
      have ho : o.val < v.val.length := by omega
      step*
      subst i_post2
      have hbv := hbyte o.val ho
      have hlt8 : BV g (8 * o.val) 8 < 2 ^ 8 := BV_lt g hg _ _
      have hi1 : i1.val = (v.val[o.val]).val := by
        rw [i1_post, UScalar.cast_val_eq, ← hbv]
        exact Nat.mod_eq_of_lt (by
          have : (2:Nat)^8 < 2^UScalarTy.U64.numBits := by decide +kernel
          omega)
      have hacc_lt : acc.val < 2 ^ nbits.val := by rw [h1]; exact BV_lt g hg _ _
      have hi2 : i2.val = i1.val * 2 ^ nbits.val := by
        rw [i2_post1, Nat.shiftLeft_eq]
        apply Nat.mod_eq_of_lt
        have h64 : 2 ^ nbits.val ≤ 2 ^ 39 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : i1.val * 2 ^ nbits.val < 2 ^ 8 * 2 ^ 39 :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) h64 (by norm_num)
        have := u64_size_gt
        omega
      have hacc1 : acc1.val = BV g s (nbits.val + 8) := by
        rw [acc1_post1, UScalar.val_or, hi2, hi1, ← hbv, or_shift _ _ _ hacc_lt, BV_add, ← h1,
          show s + nbits.val = 8 * o.val by omega]
        ring
      dsimp only [UnpackInv]
      refine ⟨⟨by rw [hacc1, nbits1_post], by omega, by omega⟩, by omega⟩
    · rename_i hn
      have hn' : c.val ≤ nbits.val := by scalar_tac
      simp only [WP.spec_ok]
      exact ⟨⟨h1, h2, h3⟩, hn'⟩
  · exact hinv

/-- Outer loop invariant of `bit_unpack`: `i` values have been decoded; `acc` holds the next `nbits` bits. -/
def UnpackOuterInv (g : Nat → Nat) (c : Nat)
    (p : Array U32 256#usize × U64 × Usize × Usize × Usize) : Prop :=
  p.2.1.val = BV g (c * p.2.2.2.2.val) p.2.2.1.val ∧
  c * p.2.2.2.2.val + p.2.2.1.val = 8 * p.2.2.2.1.val ∧ p.2.2.1.val < 8 ∧ p.2.2.2.2.val ≤ 256 ∧
  ∀ j (_hj : j < p.2.2.2.2.val) (hj' : j < p.1.val.length), (p.1.val[j]'hj').val = BV g (c * j) c

theorem bit_unpack_core (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (v : Slice U8) (c : Usize) (hc : c.val ≤ 32)
    (hlen : v.val.length = 32 * c.val)
    (hbyte : ∀ o (h : o < v.val.length), BV g (8 * o) 8 = (v.val[o]'h).val) :
    encode.bit_unpack v c ⦃ w => ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val
      = BV g (c.val * i) c.val ⦄ := by
  have hpow : ∀ i : U64, i.val = 1 <<< c.val % U64.size → i.val = 2 ^ c.val := by
    intro i hi
    rw [hi, Nat.shiftLeft_eq, one_mul]
    apply Nat.mod_eq_of_lt
    have h32 : 2 ^ c.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hc
    have := u64_size_gt
    omega
  unfold encode.bit_unpack
  step*
  · have := hpow i i_post1
    have := Nat.one_le_two_pow (n := c.val)
    simp
    omega
  · have hi2 := hpow i i_post1
    have hmask : mask.val = 2 ^ c.val - 1 := by omega
    unfold encode.bit_unpack_loop0
    apply loop.spec_decr_nat
      (fun (p : Array U32 256#usize × U64 × Usize × Usize × Usize) => 256 - p.2.2.2.2.val)
      (fun p => UnpackOuterInv g c.val p)
    · rintro ⟨w, acc, nbits, o, i⟩ hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := hp
      dsimp only at h1 h2 h3 h4 h5
      simp only [encode.bit_unpack_loop0.body]
      split
      · rename_i hi
        have hi' : i.val < 256 := by scalar_tac
        have hs : c.val * i.val + c.val ≤ 8 * v.val.length := by rw [hlen]; nlinarith
        refine WP.spec_bind (bit_unpack_inner g hg v c hc (c.val * i.val) hs hbyte acc nbits o
          ⟨h1, h2, by show nbits.val < c.val + 8; omega⟩) ?_
        rintro ⟨acc1, nbits1, o1⟩ ⟨⟨k1, k2, k3⟩, k4⟩
        dsimp only at k1 k2 k3 k4
        step*
        subst a_post
        have hsplit := BV_add g (c.val * i.val) c.val (nbits1.val - c.val)
        rw [show c.val + (nbits1.val - c.val) = nbits1.val by omega] at hsplit
        have hlt_c : BV g (c.val * i.val) c.val < 2 ^ c.val := BV_lt g hg _ _
        have hi1 : i1.val = BV g (c.val * i.val) c.val := by
          rw [i1_post1, UScalar.val_and, k1, hmask, Nat.and_two_pow_sub_one_eq_mod, hsplit,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_c]
        have hi2' : i2.val = i1.val := by
          rw [i2_post, UScalar.cast_val_eq]
          apply Nat.mod_eq_of_lt
          have h32 : 2 ^ c.val ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hc
          have : (2:Nat)^32 ≤ 2^UScalarTy.U32.numBits := by decide +kernel
          omega
        have hacc2 : acc2.val = BV g (c.val * i.val + c.val) (nbits1.val - c.val) := by
          rw [acc2_post1, Nat.shiftRight_eq_div_pow, k1, hsplit, Nat.add_mul_div_left _ _ (by positivity),
            Nat.div_eq_of_lt hlt_c, Nat.zero_add]
        have hci : c.val * i3.val = c.val * i.val + c.val := by rw [i3_post]; ring
        simp only [UnpackOuterInv]
        refine ⟨⟨?_, ?_, by omega, by omega, ?_⟩, by omega⟩
        · rw [hacc2, hci, nbits2_post1]
        · omega
        · intro j hj hj'
          simp only [Array.set_val_eq, List.getElem_set]
          split
          · rename_i hji
            subst hji
            rw [hi2', hi1]
          · rename_i hji
            exact h5 j (by omega) _
      · rename_i hi
        have hi' : i.val = 256 := by scalar_tac
        simp only [WP.spec_ok]
        intro j hj
        exact h5 j (by omega) _
    · refine ⟨by simp [BV], by simp, by simp, by simp, fun j hj => absurd hj (by simp)⟩

/-! ## Statements against the spec -/

/-- A slice whose bytes are given pointwise equals the corresponding `List.map`. -/
theorem bytes_eq_map (out : Slice U8) (f : Nat → Nat) (n : Nat) (hlen : out.val.length = n)
    (hk : ∀ k (h : k < out.val.length), (out.val[k]).val = f k) :
    bytes out = (List.range n).map (fun k => (f k).toUInt8) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro k h1 h2
    have h3 : k < out.val.length := by simpa using h1
    rw [bytes_getElem out k h1]
    simp [hk k h3, Nat.toUInt8]

theorem v_getElem!_eq (v : RPoly) (i : Nat) (hi : i < 256) : v[i]! = v[i] := by
  rw [getElem!_pos v i (by simpa using hi)]

/-- **`bit_pack` is `SimpleBitPack`.** `out` has `32·c` bytes, `c = bitlen b ≤ 32`, and the 256 coefficients
`w[i]` are the (nonnegative) integers `v[i]`, each below `2^c`. -/
theorem bit_pack_spec (w : Array U32 256#usize) (c : Usize) (out : Slice U8) (v : RPoly) (b : Nat)
    (hc : c.val = bitlen b) (hc32 : c.val ≤ 32) (hL : out.val.length = 32 * c.val)
    (hwv : ∀ i (hi : i < 256), ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) = v[i])
    (hlt : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val < 2 ^ c.val) :
    encode.bit_pack w c out ⦃ out' => bytes out' = Spec.SimpleBitPack v b ⦄ := by
  obtain ⟨g, hg, hwin, hSBP⟩ := SimpleBitPack_model v b
  have hcore := bit_pack_core g hg w c hc32 out hL (fun i hi => by
    have h := hwin i hi
    rw [← hc, v_getElem!_eq v i hi] at h
    rw [h, ← hwv i hi]
    simp only [Int.toNat_natCast]
    exact (Nat.mod_eq_of_lt (hlt i hi)).symm)
  apply WP.spec_mono hcore
  rintro out' ⟨hlen, hk⟩
  rw [hSBP, ← hc]
  exact bytes_eq_map out' (fun k => BV g (8 * k) 8) _ hlen hk

theorem bitlen_lt_q {b : Nat} (hb : b < Spec.q) : bitlen b ≤ 23 :=
  bitlen_le_of_lt (lt_of_lt_of_le hb (by decide))

theorem lt_pow_of_bitlen {x b : Nat} (hx : x ≤ b) : x < 2 ^ bitlen b :=
  lt_of_le_of_lt hx (lt_two_pow_bitlen b)

/-- **`bit_pack` on a `ReprInt` polynomial with coefficients in `[0, b]`** (the shape used by `w1_encode` and
`pk_encode`): the output is `SimpleBitPack v b`. -/
theorem bit_pack_spec_repr (w : Array U32 256#usize) (v : RPoly) (hw : ReprInt w v) (b : Nat)
    (hb : b < Spec.q) (hv : ∀ j : Nat, ∀ hj : j < 256, 0 ≤ v[j]'hj ∧ v[j]'hj ≤ (b : Int))
    (c : Usize) (hc : c.val = bitlen b) (out : Slice U8) (hL : out.val.length = 32 * c.val) :
    encode.bit_pack w c out ⦃ out' => bytes out' = Spec.SimpleBitPack v b ⦄ := by
  have hc23 := bitlen_lt_q hb
  have hcoef : ∀ i (hi : i < 256), ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) = v[i] := by
    intro i hi
    rw [hw.coeff i hi]
    exact Int.emod_eq_of_lt (hv i hi).1 (by have := (hv i hi).2; have hqv : Spec.q = 8380417 := rfl; rw [hqv]; omega)
  refine bit_pack_spec w c out v b hc (by omega) hL hcoef (fun i hi => ?_)
  have hle : ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) ≤ b := by
    rw [hcoef i hi]; exact (hv i hi).2
  rw [hc]
  exact lt_pow_of_bitlen (by exact_mod_cast hle)

/-! ### `bit_unpack` -/

theorem bytes_BV (v : Slice U8) (o : Nat) (h : o < v.val.length) :
    BV (byteBit (bytes v)) (8 * o) 8 = (v.val[o]'h).val := by
  rw [BV_byteBit (bytes v) o (by simpa using h), bytes_getElem v o (by simpa using h)]
  exact toNat_ofNat_val _

/-- **`bit_unpack` is `SimpleBitUnpack`**, for every byte string `v` of length `32·c` (total: no premise on the
byte contents). Coefficient `i` of the output is the `i`-th coefficient of the spec's result. -/
theorem bit_unpack_spec (v : Slice U8) (c : Usize) (b : Nat) (hc : c.val = bitlen b) (hc32 : c.val ≤ 32)
    (hlen : v.val.length = 32 * c.val) :
    encode.bit_unpack v c ⦃ w => ∀ i (hi : i < 256),
      ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int) = (Spec.SimpleBitUnpack (bytes v) b)[i] ⦄ := by
  apply WP.spec_mono (bit_unpack_core (byteBit (bytes v)) (byteBit_le _) v c hc32 hlen (bytes_BV v))
  intro w hw i hi
  rw [hw i hi, SimpleBitUnpack_get _ _ _ hi, hc]

/-- The same as a `ReprInt` statement: the output denotes the spec's integer polynomial (`c ≤ 22` keeps every
coefficient below `q`). -/
theorem bit_unpack_spec_repr (v : Slice U8) (c : Usize) (b : Nat) (hc : c.val = bitlen b) (hc22 : c.val ≤ 22)
    (hlen : v.val.length = 32 * c.val) :
    encode.bit_unpack v c ⦃ w => ReprInt w (Spec.SimpleBitUnpack (bytes v) b) ⦄ := by
  have h22 : (2:Nat) ^ 22 < Spec.q := by decide +kernel
  have hcore := bit_unpack_core (byteBit (bytes v)) (byteBit_le _) v c (by omega) hlen (bytes_BV v)
  apply WP.spec_mono hcore
  intro w hw
  have hw' : ∀ i (hi : i < 256), ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int)
      = (Spec.SimpleBitUnpack (bytes v) b)[i] := by
    intro i hi
    rw [hw i hi, SimpleBitUnpack_get _ _ _ hi, hc]
  have hlt : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val < Spec.q := by
    intro i hi
    rw [hw i hi]
    have := BV_lt (byteBit (bytes v)) (byteBit_le _) (c.val * i) c.val
    have : (2:Nat) ^ c.val ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hc22
    omega
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact hlt i (by simpa [len256 w] using hi)
  · apply Vector.ext
    intro k hk
    rw [toZq_get w k hk]
    simp only [RPoly.toZq, Vector.getElem_map]
    rw [← hw' k hk]
    simp

/-! ### `bit_unpack_pub` (the verify path: fixed-width unpacking for 10, 18 and 20 bits) -/

theorem BV_split (G : Nat → Nat) (hG : ∀ t, G t ≤ 1) (s n m : Nat) :
    BV G s (n + m) % 2 ^ n = BV G s n ∧ BV G s (n + m) / 2 ^ n = BV G (s + n) m := by
  have h := BV_add G s n m
  have hl := BV_lt G hG s n
  constructor
  · rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
  · rw [h, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hl, Nat.zero_add]

/-- The `c`-bit window at offset `a` of a longer window is the window at `s + a`. -/
theorem BV_win (G : Nat → Nat) (hG : ∀ t, G t ≤ 1) (s a c r : Nat) :
    BV G s (a + c + r) / 2 ^ a % 2 ^ c = BV G (s + a) c := by
  have h1 := (BV_split G hG s a (c + r)).2
  rw [show a + c + r = a + (c + r) by ring, h1]
  exact (BV_split G hG (s + a) c r).1


theorem blk_succ (G : Nat → Nat) (X m : Nat) :
    BV G (8 * X) (8 * (m + 1)) = BV G (8 * X) 8 + 2 ^ 8 * BV G (8 * (X + 1)) (8 * m) := by
  rw [show 8 * (m + 1) = 8 + 8 * m by ring, BV_add G (8 * X) 8 (8 * m), show 8 * X + 8 = 8 * (X + 1) by ring]

theorem blk5 (G : Nat → Nat) (X : Nat) :
    BV G (8 * X) 40 = BV G (8 * X) 8 + 256 * BV G (8 * (X + 1)) 8 + 65536 * BV G (8 * (X + 2)) 8 +
      16777216 * BV G (8 * (X + 3)) 8 + 4294967296 * BV G (8 * (X + 4)) 8 := by
  have h0 := blk_succ G X 4
  have h1 := blk_succ G (X + 1) 3
  have h2 := blk_succ G (X + 2) 2
  have h3 := blk_succ G (X + 3) 1
  have h4 := blk_succ G (X + 4) 0
  have z : ∀ s, BV G s 0 = 0 := fun s => rfl
  simp only [Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, z, Nat.mul_zero] at h0 h1 h2 h3 h4
  omega

theorem blk9 (G : Nat → Nat) (X : Nat) :
    BV G (8 * X) 72 = BV G (8 * X) 8 + 256 * BV G (8 * (X + 1)) 8 + 65536 * BV G (8 * (X + 2)) 8 +
      16777216 * BV G (8 * (X + 3)) 8 + 4294967296 * BV G (8 * (X + 4)) 8 +
      1099511627776 * BV G (8 * (X + 5)) 8 + 281474976710656 * BV G (8 * (X + 6)) 8 +
      72057594037927936 * BV G (8 * (X + 7)) 8 + 18446744073709551616 * BV G (8 * (X + 8)) 8 := by
  have h0 := blk_succ G X 8
  have h1 := blk_succ G (X + 1) 7
  have h2 := blk_succ G (X + 2) 6
  have h3 := blk_succ G (X + 3) 5
  have h4 := blk_succ G (X + 4) 4
  have h5 := blk_succ G (X + 5) 3
  have h6 := blk_succ G (X + 6) 2
  have h7 := blk_succ G (X + 7) 1
  have h8 := blk_succ G (X + 8) 0
  have z : ∀ s, BV G s 0 = 0 := fun s => rfl
  simp only [Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd, z, Nat.mul_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega


theorem u32_shl_mul (x i : U32) (n : Nat) (hx : x.val * 2 ^ n < 2 ^ 32) (h : i.val = x.val <<< n % U32.size) :
    i.val = x.val * 2 ^ n := by
  have hU : U32.size = 4294967296 := by scalar_tac
  rw [h, Nat.shiftLeft_eq, hU]; exact Nat.mod_eq_of_lt (by omega)

theorem u32_shr_div (x i : U32) (n : Nat) (h : i.val = x.val >>> n) : i.val = x.val / 2 ^ n := by
  rw [h, Nat.shiftRight_eq_div_pow]

theorem u32_and_mod (x m i : U32) (n : Nat) (hm : m.val = 2 ^ n - 1) (h : i.val = (x &&& m).val) :
    i.val = x.val % 2 ^ n := by
  rw [h, UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

theorem u32_or_mul (a i o : U32) (w n : Nat) (ha : a.val < 2 ^ n) (hi : i.val = w * 2 ^ n)
    (h : o.val = (a ||| i).val) : o.val = a.val + w * 2 ^ n := by
  rw [h, UScalar.val_or, hi, or_shift _ _ _ ha]

theorem u8_cast32 (i : U8) (b : U32) (h : b = UScalar.cast .U32 i) : b.val = i.val := by
  rw [h, UScalar.cast_val_eq]
  have hi : i.val < 256 := by scalar_tac
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hi (by decide +kernel : 256 ≤ 2 ^ UScalarTy.U32.numBits))

theorem arr256_set_get (a : Array U32 256#usize) (j : Usize) (z : U32) (hj : j.val < 256) (k : Nat) :
    (a.set j z).val[k]! = if j.val = k then z else a.val[k]! := by
  have hl : a.val.length = 256 := a.property
  by_cases hk : k < 256
  · rw [getElem!_pos (a.set j z).val k (by simp [Array.set_val_eq, hl]; omega), getElem!_pos a.val k (by omega)]
    simp only [Array.set_val_eq, List.getElem_set]
  · have hne : ¬ j.val = k := by omega
    rw [if_neg hne]
    rw [getElem!_neg, getElem!_neg] <;> simp [Array.set_val_eq, hl] <;> try omega

theorem bit_unpack_pub_loop0_spec (G : Nat → Nat) (hG : ∀ t, G t ≤ 1) (v : Slice U8) (hlen : v.val.length = 640)
    (hbyte : ∀ o (h : o < v.val.length), BV G (8 * o) 8 = (v.val[o]'h).val)
    (w : Array U32 256#usize) (g : Usize) (hg : g.val ≤ 128)
    (hinv : ∀ k, k < 2 * g.val → (w.val[k]!).val = BV G (20 * k) 20) :
    encode.bit_unpack_pub_loop0 w v g ⦃ r => ∀ k, k < 256 → (r.val[k]!).val = BV G (20 * k) 20 ⦄ := by
  unfold encode.bit_unpack_pub_loop0
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 128 - p.2.val)
    (fun p => p.2.val ≤ 128 ∧ ∀ k, k < 2 * p.2.val → (p.1.val[k]!).val = BV G (20 * k) 20)
  · rintro ⟨w, g⟩ ⟨hg, hI⟩
    dsimp only at hg hI
    simp only [encode.bit_unpack_pub_loop0.body]
    split
    · rename_i hlt
      have hg128 : g.val < 128 := by scalar_tac
      step*
      have hX : o.val = 5 * g.val := o_post
      have y0 : b0.val = BV G (8 * (5 * g.val)) 8 := by
        rw [u8_cast32 _ _ b0_post, i_post2, ← hX]; exact (hbyte o.val (by omega)).symm
      have y1 : b1.val = BV G (8 * (5 * g.val + 1)) 8 := by
        have := hbyte i1.val (by omega)
        rw [u8_cast32 _ _ b1_post, i2_post2, ← this, i1_post, hX]
      have y2 : b2.val = BV G (8 * (5 * g.val + 2)) 8 := by
        have := hbyte i3.val (by omega)
        rw [u8_cast32 _ _ b2_post, i4_post2, ← this, i3_post, hX]
      have y3 : b3.val = BV G (8 * (5 * g.val + 3)) 8 := by
        have := hbyte i5.val (by omega)
        rw [u8_cast32 _ _ b3_post, i6_post2, ← this, i5_post, hX]
      have y4 : b4.val = BV G (8 * (5 * g.val + 4)) 8 := by
        have := hbyte i7.val (by omega)
        rw [u8_cast32 _ _ b4_post, i8_post2, ← this, i7_post, hX]
      have l0 := BV_lt G hG (8 * (5 * g.val)) 8
      have l1 := BV_lt G hG (8 * (5 * g.val + 1)) 8
      have l2 := BV_lt G hG (8 * (5 * g.val + 2)) 8
      have l3 := BV_lt G hG (8 * (5 * g.val + 3)) 8
      have l4 := BV_lt G hG (8 * (5 * g.val + 4)) 8
      norm_num at l0 l1 l2 l3 l4
      have hN := blk5 G (5 * g.val)
      have w1 := BV_win G hG (8 * (5 * g.val)) 0 20 20
      have w2 := BV_win G hG (8 * (5 * g.val)) 20 20 0
      norm_num at w1 w2
      have z9 := u32_shl_mul b1 i9 8 (by omega) i9_post1
      have z10 := u32_or_mul b0 i9 i10 b1.val 8 (by omega) z9 i10_post1
      have z11 := u32_and_mod b2 15#u32 i11 4 (by rfl) i11_post1
      have z12 := u32_shl_mul i11 i12 16 (by omega) i12_post1
      have z14 := u32_or_mul i10 i12 i14 i11.val 16 (by omega) z12 i14_post1
      have z15 := u32_shr_div b2 i15 4 i15_post1
      have z16 := u32_shl_mul b3 i16 4 (by omega) i16_post1
      have z17 := u32_or_mul i15 i16 i17 b3.val 4 (by omega) z16 i17_post1
      have z18 := u32_shl_mul b4 i18 12 (by omega) i18_post1
      have z20 := u32_or_mul i17 i18 i20 b4.val 12 (by omega) z18 i20_post1
      refine ⟨by omega, ?_, by omega⟩
      intro k hk
      rw [a_post, arr256_set_get _ _ _ (by omega), w1_post, arr256_set_get _ _ _ (by omega)]
      split_ifs with h1 h2
      · have e : 20 * k = 8 * (5 * g.val) + 20 := by omega
        rw [e, ← w2]
        omega
      · have e : 20 * k = 8 * (5 * g.val) := by omega
        rw [e, ← w1]
        omega
      · exact hI k (by omega)
    · rename_i hge
      have : g.val = 128 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      exact hI k (by omega)
  · exact ⟨hg, hinv⟩


set_option maxHeartbeats 1600000 in
theorem bit_unpack_pub_loop1_spec (G : Nat → Nat) (hG : ∀ t, G t ≤ 1) (v : Slice U8) (hlen : v.val.length = 576)
    (hbyte : ∀ o (h : o < v.val.length), BV G (8 * o) 8 = (v.val[o]'h).val)
    (w : Array U32 256#usize) (g : Usize) (hg : g.val ≤ 64)
    (hinv : ∀ k, k < 4 * g.val → (w.val[k]!).val = BV G (18 * k) 18) :
    encode.bit_unpack_pub_loop1 w v g ⦃ r => ∀ k, k < 256 → (r.val[k]!).val = BV G (18 * k) 18 ⦄ := by
  unfold encode.bit_unpack_pub_loop1
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 64 - p.2.val)
    (fun p => p.2.val ≤ 64 ∧ ∀ k, k < 4 * p.2.val → (p.1.val[k]!).val = BV G (18 * k) 18)
  · rintro ⟨w, g⟩ ⟨hg, hI⟩
    dsimp only at hg hI
    simp only [encode.bit_unpack_pub_loop1.body]
    split
    · rename_i hlt
      have hg64 : g.val < 64 := by scalar_tac
      step*
      all_goals try scalar_tac
      have hX : o.val = 9 * g.val := o_post
      have y0 : b0.val = BV G (8 * (9 * g.val)) 8 := by
        rw [u8_cast32 _ _ b0_post, i_post2, ← hX]; exact (hbyte o.val (by omega)).symm
      have y1 : b1.val = BV G (8 * (9 * g.val + 1)) 8 := by
        have := hbyte i1.val (by omega)
        rw [u8_cast32 _ _ b1_post, i2_post2, ← this, i1_post, hX]
      have y2 : b2.val = BV G (8 * (9 * g.val + 2)) 8 := by
        have := hbyte i3.val (by omega)
        rw [u8_cast32 _ _ b2_post, i4_post2, ← this, i3_post, hX]
      have y3 : b3.val = BV G (8 * (9 * g.val + 3)) 8 := by
        have := hbyte i5.val (by omega)
        rw [u8_cast32 _ _ b3_post, i6_post2, ← this, i5_post, hX]
      have y4 : b4.val = BV G (8 * (9 * g.val + 4)) 8 := by
        have := hbyte i7.val (by omega)
        rw [u8_cast32 _ _ b4_post, i8_post2, ← this, i7_post, hX]
      have y5 : b5.val = BV G (8 * (9 * g.val + 5)) 8 := by
        have := hbyte i9.val (by omega)
        rw [u8_cast32 _ _ b5_post, i10_post2, ← this, i9_post, hX]
      have y6 : b6.val = BV G (8 * (9 * g.val + 6)) 8 := by
        have := hbyte i11.val (by omega)
        rw [u8_cast32 _ _ b6_post, i12_post2, ← this, i11_post, hX]
      have y7 : b7.val = BV G (8 * (9 * g.val + 7)) 8 := by
        have := hbyte i13.val (by omega)
        rw [u8_cast32 _ _ b7_post, i14_post2, ← this, i13_post, hX]
      have y8 : b8.val = BV G (8 * (9 * g.val + 8)) 8 := by
        have := hbyte i15.val (by omega)
        rw [u8_cast32 _ _ b8_post, i16_post2, ← this, i15_post, hX]
      have l0 := BV_lt G hG (8 * (9 * g.val)) 8
      have l1 := BV_lt G hG (8 * (9 * g.val + 1)) 8
      have l2 := BV_lt G hG (8 * (9 * g.val + 2)) 8
      have l3 := BV_lt G hG (8 * (9 * g.val + 3)) 8
      have l4 := BV_lt G hG (8 * (9 * g.val + 4)) 8
      have l5 := BV_lt G hG (8 * (9 * g.val + 5)) 8
      have l6 := BV_lt G hG (8 * (9 * g.val + 6)) 8
      have l7 := BV_lt G hG (8 * (9 * g.val + 7)) 8
      have l8 := BV_lt G hG (8 * (9 * g.val + 8)) 8
      norm_num at l0 l1 l2 l3 l4 l5 l6 l7 l8
      have hN := blk9 G (9 * g.val)
      have w0 := BV_win G hG (8 * (9 * g.val)) 0 18 54
      have w1 := BV_win G hG (8 * (9 * g.val)) 18 18 36
      have w2 := BV_win G hG (8 * (9 * g.val)) 36 18 18
      have w3 := BV_win G hG (8 * (9 * g.val)) 54 18 0
      norm_num at w0 w1 w2 w3
      have z17 := u32_shl_mul b1 i17 8 (by omega) i17_post1
      have z18 := u32_or_mul b0 i17 i18 b1.val 8 (by omega) z17 i18_post1
      have z19 := u32_and_mod b2 3#u32 i19 2 (by rfl) i19_post1
      have z20 := u32_shl_mul i19 i20 16 (by omega) i20_post1
      have z22 := u32_or_mul i18 i20 i22 i19.val 16 (by omega) z20 i22_post1
      have z23 := u32_shr_div b2 i23 2 i23_post1
      have z24 := u32_shl_mul b3 i24 6 (by omega) i24_post1
      have z25 := u32_or_mul i23 i24 i25 b3.val 6 (by omega) z24 i25_post1
      have z26 := u32_and_mod b4 15#u32 i26 4 (by rfl) i26_post1
      have z27 := u32_shl_mul i26 i27 14 (by omega) i27_post1
      have z29 := u32_or_mul i25 i27 i29 i26.val 14 (by omega) z27 i29_post1
      have z30 := u32_shr_div b4 i30 4 i30_post1
      have z31 := u32_shl_mul b5 i31 4 (by omega) i31_post1
      have z32 := u32_or_mul i30 i31 i32 b5.val 4 (by omega) z31 i32_post1
      have z33 := u32_and_mod b6 63#u32 i33 6 (by rfl) i33_post1
      have z34 := u32_shl_mul i33 i34 12 (by omega) i34_post1
      have z36 := u32_or_mul i32 i34 i36 i33.val 12 (by omega) z34 i36_post1
      have z37 := u32_shr_div b6 i37 6 i37_post1
      have z38 := u32_shl_mul b7 i38 2 (by omega) i38_post1
      have z39 := u32_or_mul i37 i38 i39 b7.val 2 (by omega) z38 i39_post1
      have z40 := u32_shl_mul b8 i40 10 (by omega) i40_post1
      have z42 := u32_or_mul i39 i40 i42 b8.val 10 (by omega) z40 i42_post1
      refine ⟨by omega, ?_, by omega⟩
      intro k hk
      rw [a_post, arr256_set_get _ _ _ (by omega), w3_post, arr256_set_get _ _ _ (by omega), w2_post, arr256_set_get _ _ _ (by omega), w1_post, arr256_set_get _ _ _ (by omega)]
      split_ifs with h1 h2 h3 h4
      · have e : 18 * k = 8 * (9 * g.val) + 54 := by omega
        rw [e]
        omega
      · have e : 18 * k = 8 * (9 * g.val) + 36 := by omega
        rw [e]
        omega
      · have e : 18 * k = 8 * (9 * g.val) + 18 := by omega
        rw [e]
        omega
      · have e : 18 * k = 8 * (9 * g.val) := by omega
        rw [e]
        omega
      · exact hI k (by omega)
    · rename_i hge
      have : g.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      exact hI k (by omega)
  · exact ⟨hg, hinv⟩

theorem bit_unpack_pub_loop2_spec (G : Nat → Nat) (hG : ∀ t, G t ≤ 1) (v : Slice U8) (hlen : v.val.length = 320)
    (hbyte : ∀ o (h : o < v.val.length), BV G (8 * o) 8 = (v.val[o]'h).val)
    (w : Array U32 256#usize) (g : Usize) (hg : g.val ≤ 64)
    (hinv : ∀ k, k < 4 * g.val → (w.val[k]!).val = BV G (10 * k) 10) :
    encode.bit_unpack_pub_loop2 w v g ⦃ r => ∀ k, k < 256 → (r.val[k]!).val = BV G (10 * k) 10 ⦄ := by
  unfold encode.bit_unpack_pub_loop2
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 64 - p.2.val)
    (fun p => p.2.val ≤ 64 ∧ ∀ k, k < 4 * p.2.val → (p.1.val[k]!).val = BV G (10 * k) 10)
  · rintro ⟨w, g⟩ ⟨hg, hI⟩
    dsimp only at hg hI
    simp only [encode.bit_unpack_pub_loop2.body]
    split
    · rename_i hlt
      have hg64 : g.val < 64 := by scalar_tac
      step*
      have hX : o.val = 5 * g.val := o_post
      have y0 : b0.val = BV G (8 * (5 * g.val)) 8 := by
        rw [u8_cast32 _ _ b0_post, i_post2, ← hX]; exact (hbyte o.val (by omega)).symm
      have y1 : b1.val = BV G (8 * (5 * g.val + 1)) 8 := by
        have := hbyte i1.val (by omega)
        rw [u8_cast32 _ _ b1_post, i2_post2, ← this, i1_post, hX]
      have y2 : b2.val = BV G (8 * (5 * g.val + 2)) 8 := by
        have := hbyte i3.val (by omega)
        rw [u8_cast32 _ _ b2_post, i4_post2, ← this, i3_post, hX]
      have y3 : b3.val = BV G (8 * (5 * g.val + 3)) 8 := by
        have := hbyte i5.val (by omega)
        rw [u8_cast32 _ _ b3_post, i6_post2, ← this, i5_post, hX]
      have y4 : b4.val = BV G (8 * (5 * g.val + 4)) 8 := by
        have := hbyte i7.val (by omega)
        rw [u8_cast32 _ _ b4_post, i8_post2, ← this, i7_post, hX]
      have l0 := BV_lt G hG (8 * (5 * g.val)) 8
      have l1 := BV_lt G hG (8 * (5 * g.val + 1)) 8
      have l2 := BV_lt G hG (8 * (5 * g.val + 2)) 8
      have l3 := BV_lt G hG (8 * (5 * g.val + 3)) 8
      have l4 := BV_lt G hG (8 * (5 * g.val + 4)) 8
      norm_num at l0 l1 l2 l3 l4
      have hN := blk5 G (5 * g.val)
      have w0 := BV_win G hG (8 * (5 * g.val)) 0 10 30
      have w1 := BV_win G hG (8 * (5 * g.val)) 10 10 20
      have w2 := BV_win G hG (8 * (5 * g.val)) 20 10 10
      have w3 := BV_win G hG (8 * (5 * g.val)) 30 10 0
      norm_num at w0 w1 w2 w3
      have z9 := u32_and_mod b1 3#u32 i9 2 (by rfl) i9_post1
      have z10 := u32_shl_mul i9 i10 8 (by omega) i10_post1
      have z12 := u32_or_mul b0 i10 i12 i9.val 8 (by omega) z10 i12_post1
      have z13 := u32_shr_div b1 i13 2 i13_post1
      have z14 := u32_and_mod b2 15#u32 i14 4 (by rfl) i14_post1
      have z15 := u32_shl_mul i14 i15 6 (by omega) i15_post1
      have z17 := u32_or_mul i13 i15 i17 i14.val 6 (by omega) z15 i17_post1
      have z18 := u32_shr_div b2 i18 4 i18_post1
      have z19 := u32_and_mod b3 63#u32 i19 6 (by rfl) i19_post1
      have z20 := u32_shl_mul i19 i20 4 (by omega) i20_post1
      have z22 := u32_or_mul i18 i20 i22 i19.val 4 (by omega) z20 i22_post1
      have z23 := u32_shr_div b3 i23 6 i23_post1
      have z24 := u32_shl_mul b4 i24 2 (by omega) i24_post1
      have z26 := u32_or_mul i23 i24 i26 b4.val 2 (by omega) z24 i26_post1
      refine ⟨by omega, ?_, by omega⟩
      intro k hk
      rw [a_post, arr256_set_get _ _ _ (by omega), w3_post, arr256_set_get _ _ _ (by omega), w2_post, arr256_set_get _ _ _ (by omega), w1_post, arr256_set_get _ _ _ (by omega)]
      split_ifs with h1 h2 h3 h4
      · have e : 10 * k = 8 * (5 * g.val) + 30 := by omega
        rw [e]
        omega
      · have e : 10 * k = 8 * (5 * g.val) + 20 := by omega
        rw [e]
        omega
      · have e : 10 * k = 8 * (5 * g.val) + 10 := by omega
        rw [e]
        omega
      · have e : 10 * k = 8 * (5 * g.val) := by omega
        rw [e]
        omega
      · exact hI k (by omega)
    · rename_i hge
      have : g.val = 64 := by scalar_tac
      simp only [WP.spec_ok]
      intro k hk
      exact hI k (by omega)
  · exact ⟨hg, hinv⟩


theorem bit_unpack_pub_core (g : Nat → Nat) (hg : ∀ t, g t ≤ 1) (v : Slice U8) (c : Usize) (hc : c.val ≤ 32)
    (hlen : v.val.length = 32 * c.val)
    (hbyte : ∀ o (h : o < v.val.length), BV g (8 * o) 8 = (v.val[o]'h).val) :
    encode.bit_unpack_pub v c ⦃ w => ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val
      = BV g (c.val * i) c.val ⦄ := by
  have conv : ∀ (v1 : Slice U8) (n : Nat), v1.val = v.val → v.val.length = n →
      (∀ o (h : o < v1.val.length), BV g (8 * o) 8 = (v1.val[o]'h).val) := by
    intro v1 n h1 _ o ho
    have ho' : o < v.val.length := by rw [← h1]; exact ho
    rw [hbyte o ho']
    simp [h1]
  unfold encode.bit_unpack_pub
  by_cases h20 : c = 20#usize
  · have hc20 : c.val = 20 := by rw [h20]; rfl
    simp only [if_pos h20]
    refine WP.spec_bind (slice_to_spec v ⟨640#usize⟩ (by show (640 : Nat) ≤ _; omega)) ?_
    intro v1 hv1
    have hv1' : v1.val = v.val := by
      rw [hv1]; exact List.take_of_length_le (by show v.val.length ≤ 640; omega)
    have hl1 : v1.val.length = 640 := by rw [hv1']; omega
    apply WP.spec_mono (bit_unpack_pub_loop0_spec g hg v1 hl1 (conv v1 640 hv1' (by omega)) _ 0#usize (by simp)
      (by intro k hk; exfalso; have : (0#usize).val = 0 := rfl; omega))
    intro w hw i hi
    rw [hc20]
    have := hw i hi
    rwa [getElem!_pos w.val i (by rw [len256 w]; exact hi)] at this
  · by_cases h18 : c = 18#usize
    · have hc18 : c.val = 18 := by rw [h18]; rfl
      simp only [if_neg h20, if_pos h18]
      refine WP.spec_bind (slice_to_spec v ⟨576#usize⟩ (by show (576 : Nat) ≤ _; omega)) ?_
      intro v1 hv1
      have hv1' : v1.val = v.val := by
        rw [hv1]; exact List.take_of_length_le (by show v.val.length ≤ 576; omega)
      have hl1 : v1.val.length = 576 := by rw [hv1']; omega
      apply WP.spec_mono (bit_unpack_pub_loop1_spec g hg v1 hl1 (conv v1 576 hv1' (by omega)) _ 0#usize (by simp)
        (by intro k hk; exfalso; have : (0#usize).val = 0 := rfl; omega))
      intro w hw i hi
      rw [hc18]
      have := hw i hi
      rwa [getElem!_pos w.val i (by rw [len256 w]; exact hi)] at this
    · by_cases h10 : c = 10#usize
      · have hc10 : c.val = 10 := by rw [h10]; rfl
        simp only [if_neg h20, if_neg h18, if_pos h10]
        refine WP.spec_bind (slice_to_spec v ⟨320#usize⟩ (by show (320 : Nat) ≤ _; omega)) ?_
        intro v1 hv1
        have hv1' : v1.val = v.val := by
          rw [hv1]; exact List.take_of_length_le (by show v.val.length ≤ 320; omega)
        have hl1 : v1.val.length = 320 := by rw [hv1']; omega
        apply WP.spec_mono (bit_unpack_pub_loop2_spec g hg v1 hl1 (conv v1 320 hv1' (by omega)) _ 0#usize (by simp)
          (by intro k hk; exfalso; have : (0#usize).val = 0 := rfl; omega))
        intro w hw i hi
        rw [hc10]
        have := hw i hi
        rwa [getElem!_pos w.val i (by rw [len256 w]; exact hi)] at this
      · simp only [if_neg h20, if_neg h18, if_neg h10]
        exact bit_unpack_core g hg v c hc hlen hbyte


/-- The same as `bit_unpack_spec_repr` for the verify-path `bit_unpack_pub`. -/
theorem bit_unpack_pub_spec_repr (v : Slice U8) (c : Usize) (b : Nat) (hc : c.val = bitlen b) (hc22 : c.val ≤ 22)
    (hlen : v.val.length = 32 * c.val) :
    encode.bit_unpack_pub v c ⦃ w => ReprInt w (Spec.SimpleBitUnpack (bytes v) b) ⦄ := by
  have h22 : (2:Nat) ^ 22 < Spec.q := by decide +kernel
  have hcore := bit_unpack_pub_core (byteBit (bytes v)) (byteBit_le _) v c (by omega) hlen (bytes_BV v)
  apply WP.spec_mono hcore
  intro w hw
  have hw' : ∀ i (hi : i < 256), ((w.val[i]'(by rw [len256 w]; exact hi)).val : Int)
      = (Spec.SimpleBitUnpack (bytes v) b)[i] := by
    intro i hi
    rw [hw i hi, SimpleBitUnpack_get _ _ _ hi, hc]
  have hlt : ∀ i (hi : i < 256), (w.val[i]'(by rw [len256 w]; exact hi)).val < Spec.q := by
    intro i hi
    rw [hw i hi]
    have := BV_lt (byteBit (bytes v)) (byteBit_le _) (c.val * i) c.val
    have : (2:Nat) ^ c.val ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hc22
    omega
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact hlt i (by simpa [len256 w] using hi)
  · apply Vector.ext
    intro k hk
    rw [toZq_get w k hk]
    simp only [RPoly.toZq, Vector.getElem_map]
    rw [← hw' k hk]
    simp

/-! ## `pack_signed` / `unpack_signed` -/

theorem pack_signed_loop_spec (w : Array U32 256#usize) (v : RPoly) (hw : ReprInt w v) (b : U32) (a : Nat)
    (hb : b.val < Spec.q) (hab : a + b.val < Spec.q)
    (hv : ∀ j : Nat, ∀ hj : j < 256, -(a : Int) ≤ v[j]'hj ∧ v[j]'hj ≤ (b.val : Int))
    (t : Array U32 256#usize) (i : Usize) (hi : i.val ≤ 256)
    (ht : ∀ j (_hj : j < i.val) (hj' : j < t.val.length),
      (t.val[j]'hj').val = ((b.val : Int) - v[j]!).toNat) :
    encode.pack_signed_loop w b t i ⦃ t' => ∀ j (hj : j < 256),
      (t'.val[j]'(by rw [len256 t']; exact hj)).val = ((b.val : Int) - v[j]!).toNat ⦄ := by
  unfold encode.pack_signed_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ ∀ j (hj : j < p.2.val) (hj' : j < p.1.val.length),
      (p.1.val[j]'hj').val = ((b.val : Int) - v[j]!).toNat)
  · rintro ⟨t, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [encode.pack_signed_loop.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := by scalar_tac
      step
      have hs := ReprInt.sub_signed hw i.val hi' b a hb (hv _ hi').1 (hv _ hi').2 hab
      rw [← i1_post2] at hs
      refine WP.spec_bind hs ?_
      intro y hy
      step*
      subst a_post
      refine ⟨by omega, ?_, by omega⟩
      intro j hj hj'
      simp only [Array.set_val_eq, List.getElem_set]
      split
      · rename_i hji
        subst hji
        rw [hy, v_getElem!_eq v _ hi']
      · rename_i hji
        exact h2 j (by omega) _
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj
      exact h2 j (by omega) _
  · exact ⟨hi, ht⟩

/-- **`pack_signed` is `BitPack`** (Algorithm 17) with `(a, b)` the bounds of the spec: a polynomial
with coefficients in `[-a, b]` is packed as `b - w[i]` in `c = bitlen (a + b)` bits. -/
theorem pack_signed_spec (w : Array U32 256#usize) (v : RPoly) (hw : ReprInt w v) (b : U32) (a : Nat)
    (c : Usize) (out : Slice U8) (hb : b.val < Spec.q) (hab : a + b.val < Spec.q)
    (hc : c.val = bitlen (a + b.val))
    (hv : ∀ j : Nat, ∀ hj : j < 256, -(a : Int) ≤ v[j]'hj ∧ v[j]'hj ≤ (b.val : Int))
    (hL : out.val.length = 32 * c.val) :
    encode.pack_signed w b c out ⦃ out' => bytes out' = Spec.BitPack v a b.val ⦄ := by
  unfold encode.pack_signed
  refine WP.spec_bind (pack_signed_loop_spec w v hw b a hb hab hv _ 0#usize (by simp)
    (fun j hj => absurd hj (by simp))) ?_
  intro t ht
  obtain ⟨g, hg, hwin, hBP⟩ := BitPack_model v a b.val
  have hc23 : c.val ≤ 23 := hc ▸ bitlen_lt_q hab
  have hcore := bit_pack_core g hg t c (by omega) out hL (fun i hi => by
    have h := hwin i hi
    rw [← hc] at h
    rw [h, ht i hi]
    refine (Nat.mod_eq_of_lt ?_).symm
    rw [hc]
    refine lt_pow_of_bitlen ?_
    have := hv i hi
    rw [v_getElem!_eq v i hi]
    omega)
  apply WP.spec_mono hcore
  rintro out' ⟨hlen, hk⟩
  rw [hBP, ← hc]
  exact bytes_eq_map out' _ _ hlen hk

theorem unpack_signed_into_loop_spec (b : U32) (hb : b.val < Spec.q) (z : Array U32 256#usize)
    (hz : Canonical z) (w : Array U32 256#usize) (i : Usize) (hi : i.val ≤ 256)
    (hw : ∀ j (_hj : j < i.val) (hj' : j < w.val.length) (hj'' : j < z.val.length),
      (w.val[j]'hj').val < Spec.q ∧
      (((w.val[j]'hj').val : Nat) : Zq) = ((b.val : Nat) : Zq) - (((z.val[j]'hj'').val : Nat) : Zq)) :
    encode.unpack_signed_into_loop b w z i ⦃ w' => ∀ j (_hj : j < 256) (hj' : j < w'.val.length)
      (hj'' : j < z.val.length),
      (w'.val[j]'hj').val < Spec.q ∧
      (((w'.val[j]'hj').val : Nat) : Zq) = ((b.val : Nat) : Zq) - (((z.val[j]'hj'').val : Nat) : Zq) ⦄ := by
  unfold encode.unpack_signed_into_loop
  apply loop.spec_decr_nat
    (fun (p : Array U32 256#usize × Usize) => 256 - p.2.val)
    (fun p => p.2.val ≤ 256 ∧ ∀ j (hj : j < p.2.val) (hj' : j < p.1.val.length)
      (hj'' : j < z.val.length),
      (p.1.val[j]'hj').val < Spec.q ∧
      (((p.1.val[j]'hj').val : Nat) : Zq) = ((b.val : Nat) : Zq) - (((z.val[j]'hj'').val : Nat) : Zq))
  · rintro ⟨w, i⟩ ⟨h1, h2⟩
    dsimp only at h1 h2
    simp only [encode.unpack_signed_into_loop.body]
    split
    · rename_i hi
      have hi' : i.val < 256 := by scalar_tac
      step*
      · rw [i1_post2]; exact hz _ (List.getElem_mem _)
      · subst a_post
        refine ⟨by omega, ?_, by omega⟩
        intro j hj hj' hj''
        simp only [Array.set_val_eq, List.getElem_set]
        split
        · rename_i hji
          subst hji
          refine ⟨i2_post1, ?_⟩
          rw [i2_post2, i1_post2]
        · rename_i hji
          exact h2 j (by omega) _ _
    · rename_i hi
      have hi' : i.val = 256 := by scalar_tac
      simp only [WP.spec_ok]
      intro j hj hj' hj''
      exact h2 j (by omega) _ _
  · exact ⟨hi, hw⟩

/-- **`unpack_signed_into` is `BitUnpack`** (Algorithm 19), for every byte string of length `32·c` (no premise on the
bytes) and every destination `w0` (all 256 entries are overwritten): the output denotes the spec's integer polynomial
`b - (unsigned value)` (modulo `q`; the integers need not lie in `[-a, b]` for a malformed input). `c = bitlen (a + b) ≤ 22`. -/
theorem unpack_signed_into_spec (v : Slice U8) (b : U32) (a : Nat) (c : Usize) (hb : b.val < Spec.q)
    (hc : c.val = bitlen (a + b.val)) (hc22 : c.val ≤ 22) (hlen : v.val.length = 32 * c.val)
    (w0 : Array U32 256#usize) :
    encode.unpack_signed_into v b c w0 ⦃ w => ReprInt w (Spec.BitUnpack (bytes v) a b.val) ⦄ := by
  have h22 : (2:Nat) ^ 22 < Spec.q := by decide +kernel
  unfold encode.unpack_signed_into
  refine WP.spec_bind (bit_unpack_core (byteBit (bytes v)) (byteBit_le _) v c (by omega) hlen
    (bytes_BV v)) ?_
  intro z hz
  have hzc : Canonical z := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 256 := by simpa [len256 z] using hi
    rw [hz i hi']
    have := BV_lt (byteBit (bytes v)) (byteBit_le _) (c.val * i) c.val
    have : (2:Nat) ^ c.val ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hc22
    omega
  refine WP.spec_mono (unpack_signed_into_loop_spec b hb z hzc w0 0#usize (by simp)
    (fun j hj => absurd hj (by simp))) ?_
  intro w hw
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 256 := by simpa [len256 w] using hi
    exact (hw i hi' hi (by rw [len256 z]; exact hi')).1
  · apply Vector.ext
    intro k hk
    rw [toZq_get w k hk]
    simp only [RPoly.toZq, Vector.getElem_map]
    rw [(hw k hk (by rw [len256 w]; exact hk) (by rw [len256 z]; exact hk)).2]
    have hzk := hz k hk
    have hbu : (Spec.BitUnpack (bytes v) a b.val)[k] = (b.val : Int) -
        ((BV (byteBit (bytes v)) (bitlen (a + b.val) * k) (bitlen (a + b.val)) : Nat) : Int) :=
      BitUnpack_get _ _ _ _ hk
    rw [hbu, ← hc, hzk]
    push_cast
    ring

/-- The verify path's `unpack_signed_loop` is `unpack_signed_into_loop` with the arguments reordered (same body). -/
theorem unpack_signed_loop_eq (b : U32) (z w : Array U32 256#usize) (i : Usize) :
    encode.unpack_signed_loop b z w i = encode.unpack_signed_into_loop b w z i := rfl

/-- **`unpack_signed` is `BitUnpack`** (Algorithm 19), for every byte string of length `32·c` (no premise on the
bytes): the output denotes the spec's integer polynomial `b - (unsigned value)` (modulo `q`; the integers
need not lie in `[-a, b]` for a malformed input). `c = bitlen (a + b) ≤ 22`. The verify path: `bit_unpack_pub`. -/
theorem unpack_signed_spec (v : Slice U8) (b : U32) (a : Nat) (c : Usize) (hb : b.val < Spec.q)
    (hc : c.val = bitlen (a + b.val)) (hc22 : c.val ≤ 22) (hlen : v.val.length = 32 * c.val) :
    encode.unpack_signed v b c ⦃ w => ReprInt w (Spec.BitUnpack (bytes v) a b.val) ⦄ := by
  have h22 : (2:Nat) ^ 22 < Spec.q := by decide +kernel
  unfold encode.unpack_signed
  refine WP.spec_bind (bit_unpack_pub_core (byteBit (bytes v)) (byteBit_le _) v c (by omega) hlen
    (bytes_BV v)) ?_
  intro z hz
  have hzc : Canonical z := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 256 := by simpa [len256 z] using hi
    rw [hz i hi']
    have := BV_lt (byteBit (bytes v)) (byteBit_le _) (c.val * i) c.val
    have : (2:Nat) ^ c.val ≤ 2 ^ 22 := Nat.pow_le_pow_right (by norm_num) hc22
    omega
  have hloop := unpack_signed_into_loop_spec b hb z hzc (Array.repeat 256#usize 0#u32) 0#usize (by simp)
    (fun j hj => absurd hj (by simp))
  rw [← unpack_signed_loop_eq] at hloop
  refine WP.spec_mono hloop ?_
  intro w hw
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i < 256 := by simpa [len256 w] using hi
    exact (hw i hi' hi (by rw [len256 z]; exact hi')).1
  · apply Vector.ext
    intro k hk
    rw [toZq_get w k hk]
    simp only [RPoly.toZq, Vector.getElem_map]
    rw [(hw k hk (by rw [len256 w]; exact hk) (by rw [len256 z]; exact hk)).2]
    have hzk := hz k hk
    have hbu : (Spec.BitUnpack (bytes v) a b.val)[k] = (b.val : Int) -
        ((BV (byteBit (bytes v)) (bitlen (a + b.val) * k) (bitlen (a + b.val)) : Nat) : Int) :=
      BitUnpack_get _ _ _ _ hk
    rw [hbu, ← hc, hzk]
    push_cast
    ring

end Proofs
