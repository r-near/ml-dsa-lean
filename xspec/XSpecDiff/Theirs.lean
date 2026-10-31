import OcamlPq
import XSpecDiff.Common
import XSpecDiff.Shadow

/-!
# Differential: ocaml-pq's side

Leaves are ocaml-pq's FIPS 204 transcriptions called directly (`MLDSA.power2RoundSpec`, `Encoding.Spec.*`,
`EndToEnd.MLDSA.fipsNTT`, ...); the samplers are their fuel loops on the stream of the Hash area's Keccak model;
the top-level algorithms are the shadow of `XSpecDiff/Shadow.lean`.
-/

open DiffCommon

namespace XSpecDiff.Theirs

open OcamlPq OcamlPq.MLDSAAlg OcamlPq.EndToEnd.MLDSA

def pOf : Nat → Params
  | 44 => mldsa44
  | 65 => mldsa65
  | _ => mldsa87

def lamOf : Nat → Nat
  | 44 => 128
  | 65 => 192
  | _ => 256

def toP (a : Array Int) : Poly := fun i => a.getD i 0
def toPN (a : Array Nat) : Poly := fun i => ((a.getD i 0 : Nat) : Int)
def ofP (p : Poly) : Array Int := (Array.range 256).map fun i => p i
def toPV (a : Array (Array Int)) : PolyVec := fun r => toP (a.getD r #[])
def ofPV (n : Nat) (v : PolyVec) : Array (Array Int) := (Array.range n).map fun r => ofP (v r)
def hintPV (rows : HintRows) : PolyVec := fun r c => if (rows.getD r #[]).contains c then 1 else 0
def hintVec (rows : HintRows) : Encoding.Hint.HintVec := fun r c =>
  if (rows.getD r #[]).contains c then 1 else 0
def ofHintPV (k : Nat) (h : PolyVec) : HintRows :=
  (Array.range k).map fun r => ((List.range 256).filter fun c => h r c ≠ 0).toArray
def ofHintVec (k : Nat) (h : Encoding.Hint.HintVec) : HintRows :=
  (Array.range k).map fun r => ((List.range 256).filter fun c => h r c ≠ 0).toArray
def listsToArr (l : List (List Int)) : Array (Array Int) := l.toArray.map List.toArray

def dummyKey : ExpandedKey := ⟨[], [], [], fun _ _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- The key of `sk` as ocaml-pq's decoder of expanded signing keys returns it. -/
def keyOf (s : Nat) (sk : List UInt8) : Option ExpandedKey :=
  let P := pOf s
  (Encoding.Mldsa.decodeSk (encParams P) (sk.map UInt8.toNat)).map fun (rho, key, tr, s1, s2, t0) =>
    { rho := natToBytes rho, key := natToBytes key, tr := natToBytes tr,
      s1 := listsToVec s1, s2 := listsToVec s2, t0 := listsToVec t0 }

/-- A stream of `N` bytes of SHAKE `w` (zeros beyond `N`). -/
def streamOf (w N : Nat) (rho : List UInt8) : ℕ → Byte :=
  let a := Shadow.shakeCached w N rho
  fun i => u8ToByte (a.getD i 0)

def impl : Impl where
  p2r r := MLDSA.power2RoundSpec (r : Int)
  dec s r :=
    let g : Int := (pOf s).gamma2
    (MLDSA.decomposeSpec g r, MLDSA.highBits g r, MLDSA.lowBits g r)
  mh s z r := MLDSA.makeHintSpec ((pOf s).gamma2 : Int) z r == 1
  uh s h r := MLDSA.useHintSpec ((pOf s).gamma2 : Int) (if h then 1 else 0) r
  ntt a := (Shadow.nttA (a.map Int.ofNat)).map Int.toNat
  intt a := (Shadow.invNttA (a.map Int.ofNat)).map Int.toNat
  mul a b := (ofP (fipsMulNTT (toPN a) (toPN b))).map Int.toNat
  sbp b w := bytesToU8 (fipsSimpleBitPack (toP w) b)
  sbu b bs := ofP (natListToPoly (Encoding.Spec.simpleBitUnpack (bs.map UInt8.toNat) b)) |>.map canon
  bp a b w := bytesToU8 (fipsBitPack (toP w) a b)
  bu a b bs := (ofP (fipsBitUnpack (u8ToBytes bs) a b)).map canon
  hbp s rows :=
    let P := pOf s
    (Encoding.Hint.hintBitPack P.k P.omega (hintVec rows)).map Nat.toUInt8
  hbu s y :=
    let P := pOf s
    (Encoding.Hint.hintBitUnpack P.k P.omega (y.map UInt8.toNat)).map (ofHintVec P.k)
  pke s rho t1 := let P := pOf s; bytesToU8 (pkEncode (keyFips P) P (u8ToBytes rho) (toPV t1))
  pkd s pk :=
    let P := pOf s
    -- The body of `fipsPkDecode` with each row's list computed once (the closure form recomputes the
    -- whole unpacking per coefficient); see the header of Shadow.lean.
    let b := u8ToBytes pk
    let c := bitlen (q - 1) - d
    (bytesToU8 (b.take 32), (Array.range P.k).map fun r =>
      ofP (natListToPoly (Encoding.Spec.simpleBitUnpack
        (bytesToNat ((b.drop (32 + r * (32 * c))).take (32 * c))) (2 ^ c - 1))))
  ske s rho K tr s1 s2 t0 :=
    let P := pOf s
    bytesToU8 (skEncode (keyFips P) P (u8ToBytes rho) (u8ToBytes K) (u8ToBytes tr) (toPV s1) (toPV s2)
      (toPV t0))
  skd s sk :=
    let P := pOf s
    (Encoding.Mldsa.decodeSk (encParams P) (sk.map UInt8.toNat)).map fun (rho, key, tr, s1, s2, t0) =>
      (rho.map Nat.toUInt8, key.map Nat.toUInt8, tr.map Nat.toUInt8, listsToArr s1, listsToArr s2,
        listsToArr t0)
  sge s ct z h :=
    let P := pOf s
    bytesToU8 (fipsSigEncode P (u8ToBytes ct) (toPV z) (hintPV h))
  sgd s sg :=
    let P := pOf s
    (fipsSigDecode P (u8ToBytes sg)).map fun (ct, z, h) =>
      (bytesToU8 ct, ofPV P.l z, ofHintPV P.k h)
  w1e s w := let P := pOf s; bytesToU8 (w1Encode (signFips P dummyKey) P (toPV w))
  c3b a b c := coeffFromThreeBytes a b c
  chb e b := coeffFromHalfByte e b
  shake w m d := if w == 128 then Hash.Keccak.shake128 d m else Hash.Keccak.shake256 d m
  rntt f rho :=
    (rejNTTPolyLoop (streamOf 128 (3 * (f + 1) + 3) rho) (f + 1) 0 0 (fun _ => 0)).map ofP
  rbnd s f rho :=
    (rejBoundedLoop (pOf s).eta (streamOf 256 (f + 3) rho) (f + 1) 0 (0, fun _ => 0)).map ofP
  sib s f rho :=
    (sampleInBallFuel (pOf s).tau (streamOf 256 (f + 40) rho) f).map ofP
  expa s _ rho :=
    let P := pOf s
    some <| (Array.range P.k).flatMap fun r => (Array.range P.l).map fun c =>
      Shadow.expandAA Shadow.G (u8ToBytes rho) r c
  exps s _ rho :=
    let P := pOf s
    let (s1, s2) := Shadow.expandSA Shadow.H P (u8ToBytes rho)
    some <| s1 ++ s2
  expm s rho kappa :=
    let P := pOf s
    Shadow.expandMaskA Shadow.H P (u8ToBytes rho) kappa
  kgi s xi :=
    let P := pOf s
    let (pk, sk) := Shadow.keyGenInternalA P Shadow.H Shadow.G (u8ToBytes xi)
    some (bytesToU8 pk, bytesToU8 sk)
  sgi s sk m rnd :=
    match keyOf s sk with
    | none => none
    | some key =>
      (Shadow.signInternalA (pOf s) (lamOf s) key (u8ToBytes m) (u8ToBytes rnd)).map bytesToU8
  sgn s sk m ctx rnd :=
    match keyOf s sk with
    | none => none
    | some key =>
      (Shadow.mldsaSignA (pOf s) (lamOf s) key (u8ToBytes m) (u8ToBytes ctx) (u8ToBytes rnd)).map bytesToU8
  vri s pk m sg := some (Shadow.verifyFormattedA (pOf s) (lamOf s) (u8ToBytes pk) (u8ToBytes m) (u8ToBytes sg))
  vrf s pk m sg ctx :=
    some (Shadow.mldsaVerifyA (pOf s) (lamOf s) (u8ToBytes pk) (u8ToBytes m) (u8ToBytes sg) (u8ToBytes ctx))

end XSpecDiff.Theirs
