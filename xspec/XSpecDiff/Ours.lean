import Spec
import XSpecDiff.Common

/-!
# Differential: our side (`lean/Spec`, vendored as `Spec`)

Adapters: parameter sets 44 / 65 / 87 select `ML_DSA_44` / `ML_DSA_65` / `ML_DSA_87`; a number `n` is the `Zq`
element `(n : Zq)`; a signed integer polynomial is an `RPoly`; a hint vector is a list of index lists per row.
-/

open Spec DiffCommon

namespace XSpecDiff.Ours

def pOf : Nat → Params
  | 44 => ML_DSA_44
  | 65 => ML_DSA_65
  | _ => ML_DSA_87

def zq (n : Nat) : Zq := (n : Zq)

def toPoly (a : Array Nat) : Poly := Vector.ofFn fun i : Fin 256 => zq a[i.val]!
def ofPoly (p : Poly) : Array Nat := p.toArray.map (·.val)
def ofPolyI (p : Poly) : Array Int := (ofPoly p).map Int.ofNat

def toRPoly (a : Array Int) : RPoly := Vector.ofFn fun i : Fin 256 => a[i.val]!
def ofRPoly (p : RPoly) : Array Int := p.toArray

def toRVec (n : Nat) (a : Array (Array Int)) : Vector RPoly n :=
  Vector.ofFn fun i : Fin n => toRPoly a[i.val]!
def ofRVec {n : Nat} (v : Vector RPoly n) : Array (Array Int) := v.toArray.map ofRPoly

def toHint (k : Nat) (rows : HintRows) : Vector HintPoly k :=
  Vector.ofFn fun i : Fin k => Vector.ofFn fun j : Fin 256 => (rows[i.val]!).contains j.val

def ofHint {k : Nat} (h : Vector HintPoly k) : HintRows :=
  h.toArray.map fun hp => ((List.range 256).filter fun j => hp[j]!).toArray

/-- Fuel large enough that no sampler of the vectors runs out. -/
def bigFuel : Fuel := { rejNTT := 1000, rejBounded := 1000, sampleInBall := 1000 }

def impl : Impl where
  p2r r := Power2Round ML_DSA_44 (zq r)
  dec s r :=
    let p := pOf s
    (Decompose p (zq r), HighBits p (zq r), LowBits p (zq r))
  mh s z r := MakeHint (pOf s) (zq z) (zq r)
  uh s h r := UseHint (pOf s) h (zq r)
  ntt a := ofPoly (NTT (toPoly a))
  intt a := ofPoly (NTTInv (toPoly a))
  mul a b := ofPoly (MultiplyNTT (toPoly a) (toPoly b))
  sbp b w := SimpleBitPack (toRPoly w) b
  sbu b bs := ofRPoly (SimpleBitUnpack bs b) |>.map canon
  bp a b w := BitPack (toRPoly w) a b
  bu a b bs := ofRPoly (BitUnpack bs a b) |>.map canon
  hbp s rows := let p := pOf s; HintBitPack p (toHint p.k rows)
  hbu s y := let p := pOf s; (HintBitUnpack p y).map ofHint
  pke s rho t1 := let p := pOf s; pkEncode p rho (toRVec p.k t1)
  pkd s pk := let p := pOf s; let (rho, t1) := pkDecode p pk; (rho, ofRVec t1)
  ske s rho K tr s1 s2 t0 :=
    let p := pOf s
    skEncode p rho K tr (toRVec p.ℓ s1) (toRVec p.k s2) (toRVec p.k t0)
  skd s sk :=
    let p := pOf s
    let (rho, K, tr, s1, s2, t0) := skDecode p sk
    some (rho, K, tr, ofRVec s1, ofRVec s2, ofRVec t0)
  sge s ct z h := let p := pOf s; sigEncode p ct (toRVec p.ℓ z) (toHint p.k h)
  sgd s σ :=
    let p := pOf s
    (sigDecode p σ).map fun (ct, z, h) => (ct, ofRVec z, ofHint h)
  w1e s w := let p := pOf s; w1Encode p (toRVec p.k w)
  c3b a b c := (CoeffFromThreeBytes a.toUInt8 b.toUInt8 c.toUInt8).map (·.val)
  chb e b := CoeffFromHalfByte e b
  shake w m d := if w == 128 then SHAKE128 m d else SHAKE256 m d
  rntt f rho := (RejNTTPoly f rho).map ofPolyI
  rbnd s f rho := (RejBoundedPoly (pOf s) f rho).map ofRPoly
  sib s f rho := (SampleInBall (pOf s) f rho).map ofRPoly
  expa s f rho :=
    let p := pOf s
    (ExpandA p f rho).map fun A => A.toArray.flatMap fun row => row.toArray.map ofPolyI
  exps s f rho :=
    let p := pOf s
    (ExpandS p f rho).map fun (s1, s2) => ofRVec s1 ++ ofRVec s2
  expm s rho kappa := ofRVec (ExpandMask (pOf s) rho kappa)
  kgi s xi := KeyGen_internal (pOf s) xi bigFuel
  sgi s sk m rnd := Sign_internal (pOf s) sk m rnd bigFuel
  sgn s sk m ctx rnd := Sign (pOf s) sk m ctx rnd bigFuel
  vri s pk m sg := Verify_internal (pOf s) pk m sg bigFuel
  vrf s pk m sg ctx := Verify (pOf s) pk m sg ctx bigFuel

end XSpecDiff.Ours
