import OcamlPq
import Std.Data.HashMap

/-!
# Executable shadow of ocaml-pq's top-level FIPS 204 specification

Why a shadow.  ocaml-pq states Algorithms 6 / 7 / 8 (`keyGenInternal`, `signInternalMu`, `verifyInternal`, ...)
parametrically in "bundles" of building blocks (`KeyFips`, `SignFips`, `VerifyFips`) and an abstract `XOF`.
Three of the building blocks, `rejNTTPoly`, `rejBoundedPoly` and `sampleInBall`, are `Classical.choose`
totalizations of the fuel loops `rejNTTPolyLoop`, `rejBoundedLoop`, `sampleInBallFuel`, so everything above them
is `noncomputable`.  In addition the specification is written with index functions `ℕ → ℤ`
(`Function.update` chains in the NTT).  Compiled, a definition whose result type is a function type is
eta-expanded by type, so `fipsNTT p` recomputes the whole transform for every index it is applied to
(measured: a 256-index tabulation of one definition costs 256 recomputations; we found no way to keep a shared
intermediate behind a function-typed definition).  A verbatim run is therefore impractical.

This file contains a SHADOW: the same algorithms, with the same order of operations and the same call of
ocaml-pq's own functions for every pointwise step (`power2RoundSpec`, `highBits`, `useHintSpec`, `fipsMulMatVec`,
`fipsMulNTT`, `fipsAddPoly`, `fipsSubPoly`, `fipsSimpleBitPack`, `pkEncode`, `skEncode`, `fipsSigEncode`,
`fipsSigDecode`, `signAttemptSpec`, ...), with exactly these changes:

* polynomials are `Array ℤ` of length 256 (`AP`) between steps (converted with `fnOf`/`apOf`), so every
  intermediate is computed once;
* `nttA` / `invNttA` are Algorithms 41 / 42 on an array (the loops of `MLDSA.nttSpec` / `invNttSpec` with
  `Function.update` replaced by array writes).  ocaml-pq's `fipsNTT` itself cannot be run compiled: one
  coefficient took more than 25 minutes (each `Function.update` value and each function-typed intermediate
  is recomputed on every application), and strict-update variants with tabulated layers were still above 15
  minutes per coefficient.  So the NTT lines of the differential compare OUR `NTT` / `NTTInv` with this
  transcription, not with `fipsNTT`;
* `rejNTTPoly`, `rejBoundedPoly`, `sampleInBall` are the fuel loops with fuel `FUEL`; `none` gives the zero
  polynomial, as the `Classical.choose` version does when the sampler does not terminate;
* `fipsBitUnpackX`, `fipsPkDecodeX` are `fipsBitUnpack`, `fipsPkDecode` with the unpacked list kept as an array;
* the key-dependent NTTs `ŝ1`, `ŝ2`, `t̂0` of Algorithm 7 are computed once per signature, not per attempt;
* `verifyFormattedX` adds the length check of the OCaml wrapper `verifyFormatted` (`verify_wrong_length` in
  ocaml-pq), which ocaml-pq's `verifyInternal` does not contain;
* the XOF is the Hash area's lane-level Keccak model (`Keccak.shake128/256`, proved equal to the bit-level
  FIPS 202 transcription by ocaml-pq's `fipsShake128_eq` / `fipsShake256_eq`), cached per input (the bit-level
  transcription itself cannot be evaluated: its state is a closure over `Fin 5 → Fin 5 → Fin 64 → Bool`).

Nothing here is a statement about ocaml-pq's definitions; it is an executable stand-in used only for the
differential run.  The final-gate results therefore read "our spec agrees with the shadow of theirs".
-/

namespace XSpecDiff.Shadow

open OcamlPq OcamlPq.MLDSAAlg OcamlPq.EndToEnd.MLDSA

/-! ## Arrays and index functions (all cheap per index) -/

abbrev AP := Array ℤ

def fnOf (a : AP) : Poly := fun i => a.getD i 0
def apOf (p : Poly) : AP := (Array.range 256).map p
def fnV (v : Array AP) : PolyVec := fun r => fnOf (v.getD r #[])
def apV (n : ℕ) (v : PolyVec) : Array AP := (Array.range n).map fun r => apOf (v r)
def fnM (m : Array (Array AP)) : PolyMat := fun r s => fnOf ((m.getD r #[]).getD s #[])

/-! ## The XOF: Keccak model with a per-input cache -/

initialize xofCache : IO.Ref (Std.HashMap (Nat × Nat × List UInt8) (Array UInt8)) ← IO.mkRef {}

/-- `N` bytes of SHAKE `w` (128 or 256) of `input`, computed once per distinct `(w, N, input)`. -/
unsafe def shakeCachedImpl (w N : Nat) (input : List UInt8) : Array UInt8 :=
  unsafeBaseIO do
    let c ← xofCache.get
    match c.get? (w, N, input) with
    | some a => pure a
    | none =>
      let a := (if w == 128 then Hash.Keccak.shake128 N input else Hash.Keccak.shake256 N input).toArray
      xofCache.set (c.insert (w, N, input) a)
      pure a

@[implemented_by shakeCachedImpl]
def shakeCached (w N : Nat) (input : List UInt8) : Array UInt8 :=
  (if w == 128 then Hash.Keccak.shake128 N input else Hash.Keccak.shake256 N input).toArray

def clearCache : IO Unit := xofCache.set {}

/-- The stream of the first `N` bytes (zeros beyond, which no run reaches). -/
def xofOf (w N : Nat) : XOF := fun input i =>
  if i < N then u8ToByte ((shakeCached w N (bytesToU8 input)).getD i 0) else u8ToByte 0

def G : XOF := xofOf 128 3300
def H : XOF := xofOf 256 2200

/-! ## Samplers as fuel loops -/

def FUEL : ℕ := 1000

def rejNTTPolyA (s : ℕ → Byte) : AP :=
  match rejNTTPolyLoop s FUEL 0 0 (fun _ => 0) with
  | some a => apOf a
  | none => Array.replicate 256 0

def rejBoundedPolyA (eta : ℕ) (s : ℕ → Byte) : AP :=
  match rejBoundedLoop eta s FUEL 0 (0, fun _ => 0) with
  | some a => apOf a
  | none => Array.replicate 256 0

def sampleInBallA (tau : ℕ) (s : ℕ → Byte) : AP :=
  match sampleInBallFuel tau s FUEL with
  | some a => apOf a
  | none => Array.replicate 256 0

/-- `expandA` of `MLDSAAlg/Expand.lean` (one entry) with the fuel-loop sampler. -/
def expandAA (G : XOF) (rho : Bytes) (r s : ℕ) : AP :=
  rejNTTPolyA (G (rho ++ integerToBytes s 1 ++ integerToBytes r 1))

def matA (G : XOF) (P : Params) (rho : Bytes) : Array (Array AP) :=
  (Array.range P.k).map fun r => (Array.range P.l).map fun s => expandAA G rho r s

/-- `expandS` of `MLDSAAlg/Expand.lean` with the fuel-loop sampler. -/
def expandSA (H : XOF) (P : Params) (rho : Bytes) : Array AP × Array AP :=
  ((Array.range P.l).map fun r => rejBoundedPolyA P.eta (H (rho ++ integerToBytes r 2)),
   (Array.range P.k).map fun r => rejBoundedPolyA P.eta (H (rho ++ integerToBytes (r + P.l) 2)))

/-- `BitUnpack` (Algorithm 19) as `fipsBitUnpack`, as an array. -/
def fipsBitUnpackA (v : Bytes) (a b : ℕ) : AP :=
  let L : List ℤ := Encoding.Spec.bitUnpack (bytesToNat v) a b
  (Array.range 256).map fun i => L.getD i 0

/-- `expandMask` of `MLDSAAlg/Expand.lean`: `y[r]` for `r < ℓ`. -/
def expandMaskA (H : XOF) (P : Params) (rho : Bytes) (mu : ℕ) : Array AP :=
  (Array.range P.l).map fun r =>
    let c := 1 + bitlen (P.gamma1 - 1)
    let x := integerToBytes (mu + r) 2
    let v := H.squeeze (rho ++ x) (32 * c)
    fipsBitUnpackA v (P.gamma1 - 1) P.gamma1

/-- `fipsPkDecode` (Algorithm 23): `t1` as arrays. -/
def fipsPkDecodeA (P : Params) (pk : Bytes) : Bytes × Array AP :=
  let c := bitlen (q - 1) - d
  (pk.take 32, (Array.range P.k).map fun r =>
    let L : List ℕ := Encoding.Spec.simpleBitUnpack
      (bytesToNat ((pk.drop (32 + r * (32 * c))).take (32 * c))) (2 ^ c - 1)
    (Array.range 256).map fun i => ((L.getD i 0 : ℕ) : ℤ))

/-! ## NTT and NTT⁻¹ on arrays (Algorithms 41, 42) -/

def nttA (a : AP) : AP := Id.run do
  let mut w : Array MLDSA.Zq := (Array.range 256).map fun i => ((a.getD i 0 : ℤ) : MLDSA.Zq)
  let mut m := 0
  let mut len := 128
  while len ≥ 1 do
    let mut start := 0
    while start < 256 do
      m := m + 1
      let z := MLDSA.zetaSpec m
      for i in [0:len] do
        let j := start + i
        let t := z * w.getD (j + len) 0
        w := w.set! (j + len) (w.getD j 0 - t)
        w := w.set! j (w.getD j 0 + t)
      start := start + 2 * len
    len := len / 2
  return w.map fun x => (x.val : ℤ)

def invNttA (a : AP) : AP := Id.run do
  let mut w : Array MLDSA.Zq := (Array.range 256).map fun i => ((a.getD i 0 : ℤ) : MLDSA.Zq)
  let mut m := 256
  let mut len := 1
  while len < 256 do
    let mut start := 0
    while start < 256 do
      m := m - 1
      let z := -MLDSA.zetaSpec m
      for i in [0:len] do
        let j := start + i
        let t := w.getD j 0
        w := w.set! j (t + w.getD (j + len) 0)
        w := w.set! (j + len) (t - w.getD (j + len) 0)
        w := w.set! (j + len) (z * w.getD (j + len) 0)
      start := start + 2 * len
    len := 2 * len
  let f : MLDSA.Zq := 8347681
  return w.map fun x => ((f * x).val : ℤ)


/-- `fipsProduct ĉ v̂` for `v̂` already in the NTT domain: `NTT⁻¹(ĉ ∘ v̂)`. -/
def productA (cHat vHat : AP) : AP := invNttA (apOf (fipsMulNTT (fnOf cHat) (fnOf vHat)))

/-! ## Algorithm 6 -/

def keyGenInternalA (P : Params) (H G : XOF) (xi : Bytes) : Bytes × Bytes :=
  let out := H.squeeze (xi ++ integerToBytes P.k 1 ++ integerToBytes P.l 1) 128
  let rho := out.take 32
  let rhoPrime := (out.drop 32).take 64
  let K := out.drop 96
  let s := expandSA H P rhoPrime
  let A := matA G P rho
  let s1h := s.1.map nttA
  let t : Array AP := (Array.range P.k).map fun r =>
    let prod := apOf (fipsMulMatVec P.l (fnM A) (fnV s1h) r)
    apOf (fipsAddPoly (fnOf (invNttA prod)) (fnOf (s.2.getD r #[])))
  let t1 : Array AP := t.map fun p => p.map fun x => (MLDSA.power2RoundSpec x).1
  let t0 : Array AP := t.map fun p => p.map fun x => (MLDSA.power2RoundSpec x).2
  let F := keyFips P
  let pk := pkEncode F P rho (fnV t1)
  let tr := H.squeeze pk 64
  (pk, skEncode F P rho K tr (fnV s.1) (fnV s.2) (fnV t0))

/-! ## Algorithms 7 and 2 -/

/-- One iteration of the loop of Algorithm 7 (lines 11-30 and 33): `alg7Step` with `fipsFinish` inlined. -/
def alg7StepA (P : Params) (lam : ℕ) (H : XOF) (A : Array (Array AP)) (s1h s2h t0h : Array AP)
    (mu : Bytes) (y : Array AP) : Option Bytes :=
  let yh := y.map nttA
  let w : Array AP := (Array.range P.k).map fun r =>
    invNttA (apOf (fipsMulMatVec P.l (fnM A) (fnV yh) r))
  let w1 : Array AP := w.map fun p => p.map fun x => MLDSA.highBits (P.gamma2 : ℤ) x
  let w1bytes := (List.range P.k).foldl
    (fun acc i => acc ++ fipsSimpleBitPack (fnOf (w1.getD i #[])) ((q - 1) / (2 * P.gamma2) - 1)) []
  let cTilde := H.squeeze (mu ++ w1bytes) (lam / 4)
  let c := sampleInBallA P.tau (H cTilde)
  let cHat := nttA c
  let cs1 : Array AP := s1h.map (productA cHat)
  let cs2 : Array AP := s2h.map (productA cHat)
  let ct0 : Array AP := t0h.map (productA cHat)
  let z := (List.range P.l).map fun r => (List.range 256).map fun i =>
    (y.getD r #[]).getD i 0 + (cs1.getD r #[]).getD i 0
  let rows := (List.range P.k).map fun r => (List.range 256).map fun i =>
    (((w.getD r #[]).getD i 0, (cs2.getD r #[]).getD i 0, (ct0.getD r #[]).getD i 0) : ℤ × ℤ × ℤ)
  match (MLDSA.signAttemptSpec P.gamma1 P.gamma2 P.beta P.omega z rows).map fun zh =>
      (listsToVec (zh.1.map (List.map fun x => MLDSA.modPM x MLDSA.q)), listsToVec zh.2) with
  | some zh => some (fipsSigEncode P cTilde zh.1 zh.2)
  | none => none

def alg7LoopA (P : Params) (lam : ℕ) (H : XOF) (A : Array (Array AP)) (s1h s2h t0h : Array AP)
    (mu rhoPP : Bytes) : ℕ → ℕ → Option Bytes
  | 0, _ => none
  | fuel + 1, kappa =>
    match alg7StepA P lam H A s1h s2h t0h mu (expandMaskA H P rhoPP kappa) with
    | some sig => some sig
    | none => alg7LoopA P lam H A s1h s2h t0h mu rhoPP fuel (kappa + P.l)

/-- Algorithm 7 (`Sign_internal`) from `M'`: `μ = H(tr ‖ M', 64)`, then the loop (821 iterations). -/
def signInternalA (P : Params) (lam : ℕ) (key : ExpandedKey) (M' rnd : Bytes) : Option Bytes :=
  let mu := H.squeeze (key.tr ++ M') 64
  let A := matA G P key.rho
  let rhoPP := H.squeeze (key.key ++ rnd ++ mu) 64
  let s1h := (apV P.l key.s1).map nttA
  let s2h := (apV P.k key.s2).map nttA
  let t0h := (apV P.k key.t0).map nttA
  alg7LoopA P lam H A s1h s2h t0h mu rhoPP 821 0

/-- `mldsaSign` of `MLDSAAlg/SignVerify.lean` (Algorithm 2). -/
def mldsaSignA (P : Params) (lam : ℕ) (key : ExpandedKey) (M ctx rnd : Bytes) : Option Bytes :=
  if ctx.length > 255 then none
  else signInternalA P lam key (integerToBytes 0 1 ++ integerToBytes ctx.length 1 ++ ctx ++ M) rnd

/-! ## Algorithms 8 and 3 -/

/-- `verifyInternal` of `MLDSAAlg/SignVerify.lean` with the `verifyFips` building blocks. -/
def verifyInternalA (P : Params) (lam : ℕ) (H G : XOF) (pk M' sig : Bytes) : Bool :=
  let pd := fipsPkDecodeA P pk
  let rho := pd.1
  let t1 := pd.2
  match fipsSigDecode P sig with
  | none => false
  | some (cTilde, z0, h) =>
    let z := apV P.l z0
    let A := matA G P rho
    let tr := H.squeeze pk 64
    let mu := H.squeeze (tr ++ M') 64
    let c := sampleInBallA P.tau (H cTilde)
    let zh := z.map nttA
    let ch := nttA c
    let t1s : Array AP := t1.map fun p => nttA (p.map fun x => x * 2 ^ d)
    let wApprox : Array AP := (Array.range P.k).map fun r =>
      invNttA (apOf (fipsSubPoly (fipsMulMatVec P.l (fnM A) (fnV zh) r)
        (fipsMulNTT (fnOf ch) (fnOf (t1s.getD r #[])))))
    let w1' : Array AP := (Array.range P.k).map fun r =>
      (Array.range 256).map fun i =>
        MLDSA.useHintSpec P.gamma2 (h r i) ((wApprox.getD r #[]).getD i 0)
    let cTilde' := H.squeeze (mu ++ (List.range P.k).foldl
      (fun acc i => acc ++ fipsSimpleBitPack (fnOf (w1'.getD i #[])) ((q - 1) / (2 * P.gamma2) - 1)) []) (lam / 4)
    fipsZNormOk P (fnV z) && decide (cTilde = cTilde')

/-- Algorithm 8 with the length check of the OCaml wrapper (`verify_wrong_length`). -/
def verifyFormattedA (P : Params) (lam : ℕ) (pk M' sig : Bytes) : Bool :=
  if pk.length ≠ P.verificationKeySize ∨ sig.length ≠ P.signatureSize then false
  else verifyInternalA P lam H G pk M' sig

/-- `mldsaVerify` of `MLDSAAlg/SignVerify.lean` (Algorithm 3) with that length check. -/
def mldsaVerifyA (P : Params) (lam : ℕ) (pk M sig ctx : Bytes) : Bool :=
  if ctx.length > 255 then false
  else verifyFormattedA P lam pk (integerToBytes 0 1 ++ integerToBytes ctx.length 1 ++ ctx ++ M) sig

end XSpecDiff.Shadow
