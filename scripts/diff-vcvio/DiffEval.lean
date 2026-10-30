import LatticeCrypto.MLDSA.Concrete.Rounding
import LatticeCrypto.MLDSA.Concrete.NTT
import LatticeCrypto.MLDSA.Concrete.Encoding

/-!
# Differential check against the FIPS 204 specification in `lean/Spec`: VCVio side

Scratch evaluator, built inside a clone of VCVio (it is not part of VCVio and is never sent upstream):
`lake build vcv-diff && .lake/build/bin/vcv-diff <vectors> <output>`.  `setup-vcvio.sh` copies this file into
the clone and registers the executable.  It runs `MLDSA.Concrete` (Rounding.lean, NTT.lean, Encoding.lean)
on the vectors written by `gen_vectors.py` and prints the same canonical text as
`lean/SpecTests/DiffVCVio.lean`; the part between `BEGIN COMMON` / `END COMMON` is identical in both files.

Adapters (VCVio): parameter sets 44 / 65 / 87 select `mldsa44` / `mldsa65` / `mldsa87`; a number is a
`Coeff = ZMod modulus`; a polynomial is an `Rq` (`Vector Coeff 256`), and a transform-domain one is
`Tq = ⟨Rq⟩`; byte lists are `ByteArray` / `Bytes n = Vector UInt8 n`; a hint is `Vector Bool 256`.
Signed packer inputs are cast into `Coeff` (their packers read `centeredRepr`); their packer interval `[a, b]`
is FIPS 204's `[-a, b]`, so FIPS `(a, b)` is passed as `(-a, b)`.  Note that `ntt`, `invNTT` and `multiplyNTTs`
are `@[implemented_by]` the loop kernels `loopNTT`, `loopInvNTT`, `loopMultiplyNTTs`, so this executable runs
the loop kernels, not the proof-oriented definitions.  Their `sigDecode` rejects a wrong length while ours
leaves that to `Verify_internal`, so only correctly sized signatures are generated.
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

open MLDSA MLDSA.Concrete DiffCommon

def pOf : Nat → MLDSA.Params
  | 44 => mldsa44
  | 65 => mldsa65
  | _ => mldsa87

def cf (n : Nat) : Coeff := (n : Coeff)
def cfi (n : Int) : Coeff := (n : Coeff)

def toRq (a : Array Nat) : Rq := Vector.ofFn fun i : Fin ringDegree => cf a[i.val]!
def toRqI (a : Array Int) : Rq := Vector.ofFn fun i : Fin ringDegree => cfi a[i.val]!
def ofRq (r : Rq) : Array Nat := Array.ofFn fun i : Fin ringDegree => (r.get i).val
def ofRqI (r : Rq) : Array Int := (ofRq r).map (Int.ofNat ·)
def toTq (a : Array Nat) : Tq := ⟨toRq a⟩
def ofTq (t : Tq) : Array Nat := ofRq t.coeffs

def toBA (l : List UInt8) : ByteArray := ByteArray.mk l.toArray
def ofBA (b : ByteArray) : List UInt8 := byteArrayToList b
def toBytes (n : Nat) (l : List UInt8) : Bytes n := Vector.ofFn fun i : Fin n => l.getD i.val 0

def toRqVec (n : Nat) (a : Array (Array Int)) : Vector Rq n :=
  Vector.ofFn fun i : Fin n => toRqI a[i.val]!
def ofRqVec {n : Nat} (v : Vector Rq n) : Array (Array Int) := v.toArray.map ofRqI

def toHint (k : Nat) (rows : HintRows) : Vector Hint k :=
  Vector.ofFn fun i : Fin k => Vector.ofFn fun j : Fin ringDegree => (rows[i.val]!).contains j.val

def ofHint {k : Nat} (h : Vector Hint k) : HintRows :=
  h.toArray.map fun hp => ((List.range ringDegree).filter fun j => hp.toArray.getD j false).toArray

def impl : Impl where
  p2r r := let (a, b) := power2RoundCoeff (cf r); (Int.ofNat a, b)
  dec s r :=
    let g := (pOf s).gamma2
    let (a, b) := decomposeCoeff (cf r) g
    ((Int.ofNat a, b), Int.ofNat (highBitsCoeff (cf r) g), lowBitsCoeff (cf r) g)
  mh s z r := makeHintCoeff (cf z) (cf r) (pOf s).gamma2
  uh s h r := Int.ofNat (useHintCoeff h (cf r) (pOf s).gamma2)
  ntt a := ofTq (MLDSA.Concrete.ntt (toRq a))
  intt a := ofRq (invNTT (toTq a))
  mul a b := ofTq (multiplyNTTs (toTq a) (toTq b))
  sbp b w := ofBA (simpleBitPackPoly (toRqI w) b)
  sbu b bs := ofRqI (simpleBitUnpackPoly (toBA bs) b)
  bp a b w := ofBA (bitPackPoly (toRqI w) (-(a : Int)) b)
  bu a b bs := ofRqI (bitUnpackPoly (toBA bs) (-(a : Int)) b)
  hbp s rows := let p := pOf s; ofBA (hintBitPack p (toHint p.k rows))
  hbu s y := let p := pOf s; (hintBitUnpack p (toBA y)).map ofHint
  pke s rho t1 := let p := pOf s; ofBA (pkEncode p (toBytes 32 rho) (toRqVec p.k t1))
  pkd s pk :=
    let p := pOf s
    let (rho, t1) := pkDecode p (toBA pk)
    (rho.toList, ofRqVec t1)
  ske s rho K tr s1 s2 t0 :=
    let p := pOf s
    ofBA (skEncode p (toBytes 32 rho) (toBytes 32 K) (toBytes 64 tr) (toRqVec p.l s1) (toRqVec p.k s2)
      (toRqVec p.k t0))
  skd s sk :=
    let p := pOf s
    let (rho, K, tr, s1, s2, t0) := skDecode p (toBA sk)
    (rho.toList, K.toList, tr.toList, ofRqVec s1, ofRqVec s2, ofRqVec t0)
  sge s ct z h :=
    let p := pOf s
    ofBA (sigEncode p (toBytes (p.lambda / 4) ct) (toRqVec p.l z) (toHint p.k h))
  sgd s σ :=
    let p := pOf s
    (sigDecode p (toBA σ)).map fun (ct, z, h) => (ct.toList, ofRqVec z, ofHint h)
  w1e s w := let p := pOf s; w1Encode p (toRqVec p.k w)

def main (args : List String) : IO UInt32 :=
  match args with
  | [inp, outp] => runFile impl inp outp
  | _ => do
    IO.eprintln "usage: vcv-diff <vectors> <output>"
    return 2
