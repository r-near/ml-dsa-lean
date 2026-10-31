/-!
# Shared driver for the compiled differential (ours versus ocaml-pq)

The plain-typed interface `Impl` is what each side adapts its own types to; `runLine` parses one vector line
and prints one canonical output line.  The line formats are documented in `scripts/xspec/gen_vectors.py` and
`scripts/diff-vcvio/gen_vectors.py` (the leaf formats are the ones used for the VCVio differential).
Parameter sets are the numbers 44 / 65 / 87.  Polynomials are `Array Int` of length 256; ring elements are
printed as canonical decimal integers in `[0, q)`, results of the rounding functions as signed integers.
-/

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
  skd : Nat → List UInt8 → Option (List UInt8 × List UInt8 × List UInt8 × Array (Array Int) × Array (Array Int) ×
    Array (Array Int))
  sge : Nat → List UInt8 → Array (Array Int) → HintRows → List UInt8
  sgd : Nat → List UInt8 → Option (List UInt8 × Array (Array Int) × HintRows)
  w1e : Nat → Array (Array Int) → List UInt8
  /-- `CoeffFromThreeBytes` -/
  c3b : Nat → Nat → Nat → Option Nat
  /-- `CoeffFromHalfByte η b` -/
  chb : Nat → Nat → Option Int
  /-- `SHAKE128` (128) or `SHAKE256` (256) of a message, `d` bytes of output -/
  shake : Nat → List UInt8 → Nat → List UInt8
  /-- `RejNTTPoly` with `fuel` loop iterations on `ρ` (34 bytes) -/
  rntt : Nat → List UInt8 → Option (Array Int)
  /-- `RejBoundedPoly` for the parameter set, with `fuel` loop iterations -/
  rbnd : Nat → Nat → List UInt8 → Option (Array Int)
  /-- `SampleInBall` for the parameter set, with `fuel` -/
  sib : Nat → Nat → List UInt8 → Option (Array Int)
  /-- `ExpandA`: the `k ⋅ ℓ` polynomials in row-major order -/
  expa : Nat → Nat → List UInt8 → Option (Array (Array Int))
  /-- `ExpandS`: `s₁` then `s₂` -/
  exps : Nat → Nat → List UInt8 → Option (Array (Array Int))
  /-- `ExpandMask ρ κ`: the `ℓ` polynomials -/
  expm : Nat → List UInt8 → Nat → Array (Array Int)
  /-- `KeyGen_internal ξ`: `(pk, sk)` -/
  kgi : Nat → List UInt8 → Option (List UInt8 × List UInt8)
  /-- `Sign_internal sk M' rnd` -/
  sgi : Nat → List UInt8 → List UInt8 → List UInt8 → Option (List UInt8)
  /-- `Sign sk M ctx rnd` -/
  sgn : Nat → List UInt8 → List UInt8 → List UInt8 → List UInt8 → Option (List UInt8)
  /-- `Verify_internal pk M' σ` -/
  vri : Nat → List UInt8 → List UInt8 → List UInt8 → Option Bool
  /-- `Verify pk M σ ctx` -/
  vrf : Nat → List UInt8 → List UInt8 → List UInt8 → List UInt8 → Option Bool

/-- `k` of the parameter set (FIPS 204, Table 1). -/
def kOf : Nat → Nat | 44 => 4 | 65 => 6 | _ => 8
/-- `ℓ` of the parameter set. -/
def lOf : Nat → Nat | 44 => 4 | 65 => 5 | _ => 7

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

def unhex (s : String) : List UInt8 :=
  if s == "-" then [] else
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i => (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!).toUInt8

def hexDigit (n : Nat) : Char := Nat.digitChar n

def hexOf (bs : List UInt8) : String :=
  if bs.isEmpty then "-" else
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

def showOpt {α : Type} (f : α → String) : Option α → String
  | none => "none"
  | some a => f a

def showBool (b : Bool) : String := if b then "1" else "0"

/-- Centered (signed) polynomials print as they are; ring elements through `canon`. -/
def showSigned (ps : Array (Array Int)) : String :=
  " ".intercalate (ps.toList.map (fun p => showInts p))

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
  | ["SWEEPC3B", c] =>
    -- all 2^24 triples (b0, b1, b2) in chunks of 65536: n = b0 + 256 b1 + 65536 b2 (chunk c fixes b2 = c)
    let d := (List.range 65536).foldl (fun h i =>
      match I.c3b (i % 256) (i / 256) (pn c) with
      | none => fnv h (-1)
      | some z => fnv h z) 14695981039346656037
    hex64 d
  | ["SWEEPCHB", eta] =>
    let d := (List.range 256).foldl (fun h b =>
      match I.chb (pn eta) b with
      | none => fnv h (-100)
      | some z => fnv h z) 14695981039346656037
    hex64 d
  | ["C3B", a, b, c] => showOpt toString (I.c3b (pn a) (pn b) (pn c))
  | ["CHB", e, b] => showOpt toString (I.chb (pn e) (pn b))
  | ["SHK", w, m, d] => hexOf (I.shake (pn w) (unhex m) (pn d))
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
  | ["HBU", s, h] => showOpt showRows (I.hbu (pn s) (unhex h))
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
    showOpt (fun (rho, key, tr, s1, s2, t0) =>
      s!"{hexOf rho} {hexOf key} {hexOf tr} {showPolys s1} {showPolys s2} {showPolys t0}")
      (I.skd (pn s) (unhex h))
  | "SGE" :: s :: ct :: cs =>
    let S := pn s
    let l := lOf S
    let k := kOf S
    let zs := polysOf l (cs.take (l * 256))
    let rows := ((cs.drop (l * 256)).toArray.map parseRow)
    hexOf (I.sge S (unhex ct) zs (rows.extract 0 k))
  | ["SGD", s, h] =>
    showOpt (fun (ct, z, rows) => s!"{hexOf ct} {showPolys z} {showRows rows}") (I.sgd (pn s) (unhex h))
  | "W1E" :: s :: cs => hexOf (I.w1e (pn s) (polysOf (kOf (pn s)) cs))
  | ["RNTT", f, rho] => showOpt showInts (I.rntt (pn f) (unhex rho))
  | ["RBND", s, f, rho] => showOpt showInts (I.rbnd (pn s) (pn f) (unhex rho))
  | ["SIB", s, f, rho] => showOpt showInts (I.sib (pn s) (pn f) (unhex rho))
  | ["EXA", s, f, rho] => showOpt showPolys (I.expa (pn s) (pn f) (unhex rho))
  | ["EXS", s, f, rho] => showOpt showSigned (I.exps (pn s) (pn f) (unhex rho))
  | ["EXM", s, rho, kappa] => showSigned (I.expm (pn s) (unhex rho) (pn kappa))
  | ["KGI", s, xi] =>
    showOpt (fun (pk, sk) => s!"{hexOf pk} {hexOf sk}") (I.kgi (pn s) (unhex xi))
  | ["SGI", s, sk, m, rnd] => showOpt hexOf (I.sgi (pn s) (unhex sk) (unhex m) (unhex rnd))
  | ["SGN", s, sk, m, ctx, rnd] =>
    showOpt hexOf (I.sgn (pn s) (unhex sk) (unhex m) (unhex ctx) (unhex rnd))
  | ["VRI", s, pk, m, sg] => showOpt showBool (I.vri (pn s) (unhex pk) (unhex m) (unhex sg))
  | ["VRF", s, pk, m, sg, ctx] =>
    showOpt showBool (I.vrf (pn s) (unhex pk) (unhex m) (unhex sg) (unhex ctx))
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
