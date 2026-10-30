import Spec.Rounding
import Spec.NTTOps
import Spec.Encode

/-!
# Differential check against VCVio: our side

An executable (`lake build spec-diff-vcvio && .lake/build/bin/spec-diff-vcvio <vectors> <output>`) that runs
the FIPS 204 specification in `lean/Spec` (Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint, NTT,
NTTInv, MultiplyNTT, the bit packers, HintBitPack / HintBitUnpack, the pk / sk / signature codecs and
w1Encode) on the vectors written by `scripts/diff-vcvio/gen_vectors.py` and prints one canonical output line
per input line.  `scripts/diff-vcvio/DiffEval.lean` is the same driver for the VCVio side; the shared part
between the `BEGIN COMMON` / `END COMMON` markers is identical in both, and `scripts/diff-vcvio/compare.py`
diffs the two outputs.

Adapters (ours): parameter sets 44 / 65 / 87 select `ML_DSA_44` / `ML_DSA_65` / `ML_DSA_87`; a number
`n` is the `Zq` element `(n : Zq)`; a signed integer polynomial is an `RPoly`; a hint vector is a list of
index lists per row (`Vector (Vector Bool 256) k`).
-/

-- BEGIN COMMON (identical in both evaluators; `scripts/diff-vcvio/check-common.sh` checks this)
/-! ## Shared driver: vector parsing, canonical output, dispatch

Plain-type interface `Impl` that each side adapts its own types to.  Parameter sets are the numbers
44 / 65 / 87.  Polynomials are `Array Int` of length 256; coefficients in outputs are printed as canonical
decimal integers: signed for the rounding functions (their results are integers), in `[0, q)` for
everything that is a ring element. -/

namespace DiffCommon

/-- The modulus `q`. -/
def qNat : Nat := 8380417

/-- A hint vector: for each of the `k` rows, the ascending list of indices `j` with `h[i]_j = 1`. -/
abbrev HintRows := Array (Array Nat)

/-- Plain-typed view of the functions under test. -/
structure Impl where
  p2r : Nat → Int × Int
  /-- `(Decompose r, HighBits r, LowBits r)` -/
  dec : Nat → Nat → (Int × Int) × Int × Int
  mh : Nat → Nat → Nat → Bool
  uh : Nat → Bool → Nat → Int
  ntt : Array Nat → Array Nat
  intt : Array Nat → Array Nat
  mul : Array Nat → Array Nat → Array Nat
  sbp : Nat → Array Int → List UInt8
  sbu : Nat → List UInt8 → Array Int
  bp : Nat → Nat → Array Int → List UInt8
  bu : Nat → Nat → List UInt8 → Array Int
  hbp : Nat → HintRows → List UInt8
  hbu : Nat → List UInt8 → Option HintRows
  pke : Nat → List UInt8 → Array (Array Int) → List UInt8
  pkd : Nat → List UInt8 → List UInt8 × Array (Array Int)
  ske : Nat → List UInt8 → List UInt8 → List UInt8 → Array (Array Int) → Array (Array Int) →
    Array (Array Int) → List UInt8
  skd : Nat → List UInt8 → List UInt8 × List UInt8 × List UInt8 × Array (Array Int) × Array (Array Int) ×
    Array (Array Int)
  sge : Nat → List UInt8 → Array (Array Int) → HintRows → List UInt8
  sgd : Nat → List UInt8 → Option (List UInt8 × Array (Array Int) × HintRows)
  w1e : Nat → Array (Array Int) → List UInt8

/-- `k` of the parameter set (FIPS 204, Table 1). -/
def kOf : Nat → Nat | 44 => 4 | 65 => 6 | _ => 8
/-- `ℓ` of the parameter set. -/
def lOf : Nat → Nat | 44 => 4 | 65 => 5 | _ => 7

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def unhex (s : String) : List UInt8 :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i => (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!).toUInt8

def hexDigit (n : Nat) : Char := Nat.digitChar n

def hexOf (bs : List UInt8) : String :=
  String.ofList (bs.foldr (fun b acc => hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: acc) [])

def hex64 (h : UInt64) : String :=
  let n := h.toNat
  String.ofList ((List.range 16).reverse.map fun i => hexDigit ((n / 16 ^ i) % 16))

/-- FNV-1a style mixing of one integer into a 64-bit digest. -/
def fnv (h : UInt64) (x : Int) : UInt64 :=
  (h ^^^ (x + 4294967296).toNat.toUInt64) * 1099511628211

def pn (s : String) : Nat := s.toNat!
def pz (s : String) : Int := s.toInt!

def showInts (xs : Array Int) : String := " ".intercalate (xs.toList.map toString)
def showNats (xs : Array Nat) : String := " ".intercalate (xs.toList.map toString)

/-- Canonical representative in `[0, q)`. -/
def canon (x : Int) : Int := x % (qNat : Int)

def showRows (rows : HintRows) : String :=
  " ".intercalate (rows.toList.map fun r =>
    if r.isEmpty then "-" else ",".intercalate (r.toList.map toString))

def parseRow (s : String) : Array Nat :=
  if s == "-" then #[] else (s.splitOn ",").toArray.map pn

/-- Split a flat list of integer fields into `n` polynomials of 256 coefficients. -/
def polysOf (n : Nat) (fs : List String) : Array (Array Int) :=
  let a := fs.toArray
  (Array.range n).map fun i => (Array.range 256).map fun j => pz a[i * 256 + j]!

def showPolys (ps : Array (Array Int)) : String :=
  " ".intercalate (ps.toList.map (fun p => showInts (p.map canon)))

def runLine (I : Impl) (line : String) : String :=
  match line.splitOn " " with
  | ["P2R", r] => let (a, b) := I.p2r (pn r); s!"{a} {b}"
  | ["DEC", s, r] =>
    let ((a, b), hb, lb) := I.dec (pn s) (pn r)
    s!"D {a} {b} H {hb} L {lb}"
  | ["MH", s, z, r] => if I.mh (pn s) (pn z) (pn r) then "1" else "0"
  | ["UH", s, h, r] => toString (I.uh (pn s) (pn h == 1) (pn r))
  | ["SWEEP", kind, s, c] =>
    let lo := pn c * 65536
    let hi := min (lo + 65536) qNat
    let sn := if s == "-" then 44 else pn s
    let step : Nat → UInt64 → UInt64 :=
      if kind == "P2R" then fun r h => let (a, b) := I.p2r r; fnv (fnv h a) b
      else if kind == "DEC" then fun r h =>
        let ((a, b), hb, lb) := I.dec sn r
        fnv (fnv (fnv (fnv h a) b) hb) lb
      else if kind == "UH0" then fun r h => fnv h (I.uh sn false r)
      else fun r h => fnv h (I.uh sn true r)
    let d := (List.range (hi - lo)).foldl (fun h i => step (lo + i) h) 14695981039346656037
    hex64 d
  | "NTT" :: cs => showInts ((I.ntt (cs.toArray.map pn)).map (Int.ofNat ·))
  | "INTT" :: cs => showInts ((I.intt (cs.toArray.map pn)).map (Int.ofNat ·))
  | "MUL" :: cs =>
    let a := cs.toArray.map pn
    showInts ((I.mul (a.extract 0 256) (a.extract 256 512)).map (Int.ofNat ·))
  | "SBP" :: b :: cs => hexOf (I.sbp (pn b) (cs.toArray.map pz))
  | ["SBU", b, h] => showInts (I.sbu (pn b) (unhex h))
  | "BP" :: a :: b :: cs => hexOf (I.bp (pn a) (pn b) (cs.toArray.map pz))
  | ["BU", a, b, h] => showInts (I.bu (pn a) (pn b) (unhex h))
  | "HBP" :: s :: rows => hexOf (I.hbp (pn s) (rows.toArray.map parseRow))
  | "HBPX" :: s :: rows => hexOf (I.hbp (pn s) (rows.toArray.map parseRow))
  | ["HBU", s, h] =>
    match I.hbu (pn s) (unhex h) with
    | none => "none"
    | some rows => showRows rows
  | "PKE" :: s :: rho :: cs => hexOf (I.pke (pn s) (unhex rho) (polysOf (kOf (pn s)) cs))
  | ["PKD", s, h] =>
    let (rho, t1) := I.pkd (pn s) (unhex h)
    s!"{hexOf rho} {showPolys t1}"
  | "SKE" :: s :: rho :: key :: tr :: cs =>
    let S := pn s
    let l := lOf S
    let k := kOf S
    let all := polysOf (l + 2 * k) cs
    hexOf (I.ske S (unhex rho) (unhex key) (unhex tr) (all.extract 0 l) (all.extract l (l + k))
      (all.extract (l + k) (l + 2 * k)))
  | ["SKD", s, h] =>
    let (rho, key, tr, s1, s2, t0) := I.skd (pn s) (unhex h)
    s!"{hexOf rho} {hexOf key} {hexOf tr} {showPolys s1} {showPolys s2} {showPolys t0}"
  | "SGE" :: s :: ct :: cs =>
    let S := pn s
    let l := lOf S
    let k := kOf S
    let zs := polysOf l (cs.take (l * 256))
    let rows := ((cs.drop (l * 256)).toArray.map parseRow)
    hexOf (I.sge S (unhex ct) zs (rows.extract 0 k))
  | ["SGD", s, h] =>
    match I.sgd (pn s) (unhex h) with
    | none => "none"
    | some (ct, z, rows) => s!"{hexOf ct} {showPolys z} {showRows rows}"
  | "W1E" :: s :: cs => hexOf (I.w1e (pn s) (polysOf (kOf (pn s)) cs))
  | _ => "ERR unknown-or-malformed-line"

def runFile (I : Impl) (inp outp : String) : IO UInt32 := do
  let lines ← IO.FS.lines inp
  let h ← IO.FS.Handle.mk outp .write
  let mut n := 0
  for line in lines do
    if line.isEmpty then continue
    h.putStrLn (runLine I line)
    n := n + 1
  h.flush
  IO.eprintln s!"{n} lines"
  return 0

end DiffCommon
-- END COMMON

open Spec DiffCommon

def pOf : Nat → Params
  | 44 => ML_DSA_44
  | 65 => ML_DSA_65
  | _ => ML_DSA_87

def zq (n : Nat) : Zq := (n : Zq)

def toPoly (a : Array Nat) : Poly := Vector.ofFn fun i : Fin 256 => zq a[i.val]!
def ofPoly (p : Poly) : Array Nat := p.toArray.map (·.val)

def toRPoly (a : Array Int) : RPoly := Vector.ofFn fun i : Fin 256 => a[i.val]!
def ofRPoly (p : RPoly) : Array Int := p.toArray

def toRVec (n : Nat) (a : Array (Array Int)) : Vector RPoly n :=
  Vector.ofFn fun i : Fin n => toRPoly a[i.val]!
def ofRVec {n : Nat} (v : Vector RPoly n) : Array (Array Int) := v.toArray.map ofRPoly

def toHint (k : Nat) (rows : HintRows) : Vector HintPoly k :=
  Vector.ofFn fun i : Fin k => Vector.ofFn fun j : Fin 256 => (rows[i.val]!).contains j.val

def ofHint {k : Nat} (h : Vector HintPoly k) : HintRows :=
  h.toArray.map fun hp => ((List.range 256).filter fun j => hp[j]!).toArray

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
    (rho, K, tr, ofRVec s1, ofRVec s2, ofRVec t0)
  sge s ct z h := let p := pOf s; sigEncode p ct (toRVec p.ℓ z) (toHint p.k h)
  sgd s σ :=
    let p := pOf s
    (sigDecode p σ).map fun (ct, z, h) => (ct, ofRVec z, ofHint h)
  w1e s w := let p := pOf s; w1Encode p (toRVec p.k w)

def main (args : List String) : IO UInt32 :=
  match args with
  | [inp, outp] => runFile impl inp outp
  | _ => do
    IO.eprintln "usage: spec-diff-vcvio <vectors> <output>"
    return 2
