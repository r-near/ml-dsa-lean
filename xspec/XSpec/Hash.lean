import XSpec.Sig

/-!
# Hashing (`G = SHAKE128`, `H = SHAKE256`) and `IntegerToBytes` on `MLDSAAlg` types

ocaml-pq's `MLDSAAlg` treats SHAKE as an abstract extendable-output function `XOF = Bytes -> N -> Byte`; its
end-to-end layer instantiates it twice, with its own Keccak transcription (`ocamlShake*`, `fipsShake*`).  This
file instantiates it a third time, with our `Spec.SHAKE128` / `Spec.SHAKE256`, through ocaml-pq's own
construction `keccakXOF`.  Every algorithm equivalence below that involves hashing is then stated for ocaml-pq's
algorithms *instantiated with our SHAKE*; the remaining gap is the equality of the two Keccak implementations
(`oursShake* = ocamlShake*`), which is a separate theorem about Keccak-f[1600] and is not proved here.
-/

open Spec

namespace XSpec

open OcamlPq.MLDSAAlg
open OcamlPq.EndToEnd.MLDSA

/-- Our `SHAKE128` (the `G` of FIPS 204) as an `MLDSAAlg.XOF`. -/
def oursShake128 : XOF := keccakXOF (fun L M => Spec.SHAKE128 M L)

/-- Our `SHAKE256` (the `H` of FIPS 204) as an `MLDSAAlg.XOF`. -/
def oursShake256 : XOF := keccakXOF (fun L M => Spec.SHAKE256 M L)

/-- `XOF.squeeze oursShake128 x L` is our `SHAKE128` on the same bytes. -/
theorem oursShake128_squeeze (input : Bytes) (L : ℕ) :
    oursShake128.squeeze input L = u8ToBytes (Spec.SHAKE128 (bytesToU8 input) L) :=
  keccakXOF_squeeze (fun L M => Spec.SHAKE128 M L) (fun L M => Spec.SHAKE128_length M L)
    (fun L L' M h => by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
      exact Spec.SHAKE128_prefix M L e) input L

/-- `XOF.squeeze oursShake256 x L` is our `SHAKE256` on the same bytes. -/
theorem oursShake256_squeeze (input : Bytes) (L : ℕ) :
    oursShake256.squeeze input L = u8ToBytes (Spec.SHAKE256 (bytesToU8 input) L) :=
  keccakXOF_squeeze (fun L M => Spec.SHAKE256 M L) (fun L M => Spec.SHAKE256_length M L)
    (fun L L' M h => by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
      exact Spec.SHAKE256_prefix M L e) input L

/-- `G(M, L)` of ours on `List UInt8` against the `XOF` on `Bytes`. -/
theorem G_eq (M : List UInt8) (L : ℕ) :
    u8ToBytes (Spec.G M L) = oursShake128.squeeze (u8ToBytes M) L := by
  rw [oursShake128_squeeze, bytesToU8_u8ToBytes]; rfl

/-- `H(M, L)` of ours on `List UInt8` against the `XOF` on `Bytes`. -/
theorem H_eq (M : List UInt8) (L : ℕ) :
    u8ToBytes (Spec.H M L) = oursShake256.squeeze (u8ToBytes M) L := by
  rw [oursShake256_squeeze, bytesToU8_u8ToBytes]; rfl

theorem integerToBytes_alg (x α : ℕ) :
    OcamlPq.MLDSAAlg.integerToBytes x α = natToBytes (OcamlPq.Encoding.Spec.integerToBytes x α) := by
  induction α generalizing x with
  | zero => simp [OcamlPq.MLDSAAlg.integerToBytes, OcamlPq.Encoding.Spec.integerToBytes_eq, natToBytes]
  | succ α ih =>
    rw [OcamlPq.MLDSAAlg.integerToBytes, ih (x / 256)]
    simp only [OcamlPq.Encoding.Spec.integerToBytes_eq, natToBytes, List.map_map, List.range_succ_eq_map,
      List.map_cons, List.map_map]
    congr 1
    · simp [byteOfNat]
    · apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.pow_succ]
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]

/-- `IntegerToBytes` (Algorithm 11) on `List UInt8` against `MLDSAAlg.integerToBytes`. -/
theorem integerToBytes_alg_eq (x α : ℕ) :
    u8ToBytes (Spec.IntegerToBytes x α) = OcamlPq.MLDSAAlg.integerToBytes x α := by
  rw [u8ToBytes_eq_natToBytes, integerToBytes_eq, integerToBytes_alg]


/-- Byte `i` of the stream `oursShake128 (u8ToBytes ρ)` is byte `i` of `SHAKE128 ρ L` for any `L > i`. -/
theorem oursShake128_val (ρ : List UInt8) (L i : ℕ) (hi : i < L) :
    (oursShake128 (u8ToBytes ρ) i).val = ((Spec.SHAKE128 ρ L).getD i 0).toNat := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have h : i + e + 1 = (i + 1) + e := by omega
  simp only [oursShake128, keccakXOF, bytesToU8_u8ToBytes, u8ToByte, byteOfNat]
  rw [h, Spec.SHAKE128_prefix ρ (i + 1) e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rw [if_pos (by omega)]
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt _)

/-- The same for SHAKE256. -/
theorem oursShake256_val (ρ : List UInt8) (L i : ℕ) (hi : i < L) :
    (oursShake256 (u8ToBytes ρ) i).val = ((Spec.SHAKE256 ρ L).getD i 0).toNat := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hi
  have h : i + e + 1 = (i + 1) + e := by omega
  simp only [oursShake256, keccakXOF, bytesToU8_u8ToBytes, u8ToByte, byteOfNat]
  rw [h, Spec.SHAKE256_prefix ρ (i + 1) e]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rw [if_pos (by omega)]
  exact Nat.mod_eq_of_lt (UInt8.toNat_lt _)

/-! ## `ExpandMask` (Algorithm 34) -/

theorem ExpandMask_get (p : Spec.Params) (ρ : List UInt8) (μ i : ℕ) (hi : i < p.ℓ) :
    (Spec.ExpandMask p ρ μ)[i] =
      BitUnpack (Spec.H (ρ ++ IntegerToBytes (μ + i) 2) (32 * (1 + Spec.bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁ := by
  have h : Spec.ExpandMask p ρ μ = (List.range' 0 p.ℓ).foldl (fun (w : Vector RPoly p.ℓ) a => w.set! a
      (BitUnpack (Spec.H (ρ ++ IntegerToBytes (μ + a) 2) (32 * (1 + Spec.bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁))
      (Vector.replicate p.ℓ (Vector.replicate 256 0)) := by
    unfold Spec.ExpandMask
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [h]
  refine (EB.vec_fold_gen (m := p.ℓ) (Vector.replicate 256 0) (fun a =>
    BitUnpack (Spec.H (ρ ++ IntegerToBytes (μ + a) 2) (32 * (1 + Spec.bitlen (p.γ₁ - 1)))) (p.γ₁ - 1) p.γ₁)
    p.ℓ i hi).trans ?_
  rw [if_pos hi]

theorem Std3.bitlen_gamma1 {p : Spec.Params} (h : Std3 p) :
    Spec.bitlen (p.γ₁ - 1) = OcamlPq.MLDSAAlg.bitlen ((algParams p).gamma1 - 1) := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- `ExpandMask` (Algorithm 34), entry `r`, against ocaml-pq's `expandMask` with the FIPS `BitUnpack` and
our SHAKE256 as `H`.  No bound on `μ + r` is needed: both sides keep `μ + r mod 2^16`. -/
theorem expandMask_eq {p : Spec.Params} (hp : Std3 p) (ρ : List UInt8) (μ r : ℕ) (hr : r < p.ℓ) :
    rfn ((Spec.ExpandMask p ρ μ)[r]!) =
      expandMask oursShake256 (algParams p) fipsBitUnpack (u8ToBytes ρ) μ r := by
  rw [getElem!_pos _ r (by simpa using hr), ExpandMask_get p ρ μ r hr]
  unfold expandMask
  rw [← hp.bitlen_gamma1]
  simp only []
  rw [← integerToBytes_alg_eq, ← u8ToBytes_append, ← H_eq]
  exact bu_corr _ _ _

end XSpec
