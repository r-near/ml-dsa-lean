import Spec

/-!
# Differential check against Galois's Cryptol specification: our side

An executable (`lake build spec-diff-cryptol && .lake/build/bin/spec-diff-cryptol <vectors> <output>`) that
runs the FIPS 204 specification in `lean/Spec` on the vector lines written by `scripts/diff-cryptol/gen_vectors.py`
and prints one canonical output line per input line.  `scripts/diff-cryptol/cryptol_eval.py` evaluates the same
lines with `GaloisInc/cryptol-specs` (`Primitive/Asymmetric/Signature/ML_DSA`) and prints the same canonical
lines; `scripts/diff-cryptol/compare.py` diffs the two.  The line formats are listed in
`scripts/diff-cryptol/README.md` (section "Vector and output formats").

The driver is a sibling of `SpecTests/DiffVCVio.lean` (same structure: plain-typed adapters in front of
`lean/Spec`, a line dispatcher, `runFile`), with more tags: the SHAKE functions, the samplers, key generation,
signing and verification.  Adapters: parameter sets 44 / 65 / 87 select `ML_DSA_44` / `ML_DSA_65` /
`ML_DSA_87`; a number `n` is the `Zq` element `(n : Zq)`; a signed integer polynomial is an `RPoly`; a hint
vector is a list of index lists per row (`Vector (Vector Bool 256) k`); a byte string is lower-case hex, with `-`
for the empty string.
-/

open Spec

namespace DiffCryptol

def qNat : Nat := 8380417

def pOf : Nat → Params
  | 44 => ML_DSA_44
  | 65 => ML_DSA_65
  | _ => ML_DSA_87

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Hex to bytes; `-` is the empty string. -/
def unhex (s : String) : List UInt8 :=
  if s == "-" then [] else
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i => (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!).toUInt8

def hexDigit (n : Nat) : Char := Nat.digitChar n

def hexOf (bs : List UInt8) : String :=
  if bs.isEmpty then "-" else
  String.ofList (bs.foldr (fun b acc => hexDigit (b.toNat / 16) :: hexDigit (b.toNat % 16) :: acc) [])

def pn (s : String) : Nat := s.toNat!
def pz (s : String) : Int := s.toInt!

def showInts (xs : Array Int) : String := " ".intercalate (xs.toList.map toString)

def showNats (xs : Array Nat) : String := " ".intercalate (xs.toList.map toString)

def zq (n : Nat) : Zq := (n : Zq)

def toPoly (a : Array Nat) : Poly := Vector.ofFn fun i : Fin 256 => zq a[i.val]!
def ofPoly (p : Poly) : Array Nat := p.toArray.map (·.val)
def toRPoly (a : Array Int) : RPoly := Vector.ofFn fun i : Fin 256 => a[i.val]!
def ofRPoly (p : RPoly) : Array Int := p.toArray

/-- `n` polynomials from a flat list of `n * 256` fields. -/
def polysOf (n : Nat) (fs : List String) : Array (Array Int) :=
  let a := fs.toArray
  (Array.range n).map fun i => (Array.range 256).map fun j => pz a[i * 256 + j]!

def toRVec (n : Nat) (a : Array (Array Int)) : Vector RPoly n :=
  Vector.ofFn fun i : Fin n => toRPoly a[i.val]!
def ofRVec {n : Nat} (v : Vector RPoly n) : Array Int := v.toArray.foldl (fun acc p => acc ++ p.toArray) #[]

/-- A hint vector: for each of the `k` rows, the ascending list of indices `j` with `h[i]_j = 1`. -/
abbrev HintRows := Array (Array Nat)

def parseRow (s : String) : Array Nat :=
  if s == "-" then #[] else (s.splitOn ",").toArray.map pn

def showRows (rows : HintRows) : String :=
  " ".intercalate (rows.toList.map fun r =>
    if r.isEmpty then "-" else ",".intercalate (r.toList.map toString))

def toHint (k : Nat) (rows : HintRows) : Vector HintPoly k :=
  Vector.ofFn fun i : Fin k => Vector.ofFn fun j : Fin 256 => (rows[i.val]!).contains j.val

def ofHint {k : Nat} (h : Vector HintPoly k) : HintRows :=
  h.toArray.map fun hp => ((List.range 256).filter fun j => hp[j]!).toArray

/-- A hint vector as one `0` / `1` character per coefficient, row after row. -/
def showBits {k : Nat} (h : Vector HintPoly k) : String :=
  String.ofList (h.toList.flatMap fun hp => hp.toList.map fun b => if b then '1' else '0')

/-- Parse `k * 256` characters `0` / `1` as a hint vector. -/
def hintOfBits (k : Nat) (s : String) : Vector HintPoly k :=
  let cs := s.toList.toArray
  Vector.ofFn fun i : Fin k => Vector.ofFn fun j : Fin 256 => cs[i.val * 256 + j.val]! == '1'

def polyVec (n : Nat) (fs : List String) : Vector Poly n :=
  let a := fs.toArray
  Vector.ofFn fun i : Fin n => Vector.ofFn fun j : Fin 256 => zq (pn a[i.val * 256 + j.val]!)

def showPolyVec {n : Nat} (v : Vector Poly n) : String :=
  " ".intercalate (v.toList.map fun p => showNats (ofPoly p))

def showOptBool : Option Bool → String
  | none => "none"
  | some true => "true"
  | some false => "false"

/-- Test-only (not part of the specification): the signing loop of Algorithm 7 (`Spec.Sign_internal_bounded`, same
steps) with a different acceptance test, returning the signature and the number of attempts used.
* `target = none`: the acceptance test of Algorithm 7 (`‖z‖∞ < γ₁ − β` and the checks of steps 23 and 28); the result
  is the signature `Sign_internal` returns, and the attempt count tells how often the loop rejected.
* `target = some t`: accept the first attempt whose `‖z‖∞` is exactly `t` and which passes every other check of steps 23
  and 28.  With `t = γ₁ − β − 1` this is a valid signature whose `z` has the largest norm that Verify accepts; with
  `t = γ₁ − β` a signature that Algorithm 7 rejects and that Verify must reject at step 13 although its commitment
  hash is consistent.  `scripts/diff-cryptol` uses these to test the `‖z‖∞ < γ₁ − β` check of Verify, which no ordinary
  signature reaches. -/
def signLoop (p : Params) (sk M' rnd : List UInt8) (target : Option Nat) : Option (List UInt8 × Nat) := Id.run do
  let (ρ, K, tr, s₁, s₂, t₀) := skDecode p sk
  let ŝ₁ := NTTVec (s₁.map RPoly.toZq)
  let ŝ₂ := NTTVec (s₂.map RPoly.toZq)
  let t₀hat := NTTVec (t₀.map RPoly.toZq)
  let some Â := ExpandA p ({} : Fuel).rejNTT ρ | return none
  let μ := H (tr ++ M') 64
  let ρ'' := H (K ++ rnd ++ μ) 64
  let mut κ := 0
  for a in [0:kappaBudget p] do
    let y := (ExpandMask p ρ'' κ).map RPoly.toZq
    let w := NTTInvVec (MatrixVectorNTT Â (NTTVec y))
    let w₁ := HighBitsVec p w
    let c_tilde := H (μ ++ w1Encode p w₁) (p.lam / 4)
    let some c := SampleInBall p ({} : Fuel).sampleInBall c_tilde | return none
    let ĉ := NTT c.toZq
    let cs₁ := NTTInvVec (ScalarVectorNTT ĉ ŝ₁)
    let cs₂ := NTTInvVec (ScalarVectorNTT ĉ ŝ₂)
    let z := y + cs₁
    let r₀ := LowBitsVec p (w - cs₂)
    let ct₀ := NTTInvVec (ScalarVectorNTT ĉ t₀hat)
    let h := MakeHintVec p (-ct₀) (w - cs₂ + ct₀)
    let zOk := match target with
      | none => ‖z‖∞ < p.γ₁ - p.β
      | some t => ‖z‖∞ = t
    if zOk ∧ ‖r₀‖∞ < p.γ₂ - p.β ∧ ‖ct₀‖∞ < p.γ₂ ∧ HintWeight h ≤ p.ω then
      return some (sigEncode p c_tilde (z.map Poly.modPM) h, a + 1)
    κ := κ + p.ℓ
    if 2 ^ 16 < κ + p.ℓ then return none
  return none

def runLine (line : String) : String :=
  -- KGO and KGT only select other Cryptol entry points; our key generation is the same function
  let line := if line.startsWith "KGO " || line.startsWith "KGT " then "KG " ++ line.drop 4 else line
  match line.splitOn " " with
  -- FIPS 202
  | ["H256", l, m] => hexOf (SHAKE256 (unhex m) (pn l))
  | ["H128", l, m] => hexOf (SHAKE128 (unhex m) (pn l))
  -- Section 7.4, k * 256 scalars per line (`S` selects the parameter set)
  | "P2R" :: s :: rs =>
    let p := pOf (pn s)
    let r := rs.toArray.map pn
    let a := r.map fun x => (Power2Round p (zq x)).1
    let b := r.map fun x => (Power2Round p (zq x)).2
    s!"{showInts a} ; {showInts b}"
  | "DEC" :: s :: rs =>
    let p := pOf (pn s)
    let r := rs.toArray.map pn
    let a := r.map fun x => (Decompose p (zq x)).1
    let b := r.map fun x => (Decompose p (zq x)).2
    let hb := r.map fun x => HighBits p (zq x)
    let lb := r.map fun x => LowBits p (zq x)
    s!"{showInts a} ; {showInts b} ; {showInts hb} ; {showInts lb}"
  | "MH" :: s :: rest =>
    let p := pOf (pn s)
    let n := p.k * 256
    let z := (rest.take n).toArray.map pn
    let r := (rest.drop n).toArray.map pn
    String.ofList ((List.range n).map fun i => if MakeHint p (zq z[i]!) (zq r[i]!) then '1' else '0')
  | "UH" :: s :: hbits :: rs =>
    let p := pOf (pn s)
    let n := p.k * 256
    let hb := hbits.toList.toArray
    let r := rs.toArray.map pn
    showInts ((List.range n).toArray.map fun i => UseHint p (hb[i]! == '1') (zq r[i]!))
  -- NTT
  | "NTT" :: cs => showNats (ofPoly (NTT (toPoly (cs.toArray.map pn))))
  | "INTT" :: cs => showNats (ofPoly (NTTInv (toPoly (cs.toArray.map pn))))
  | "MUL" :: cs =>
    let a := cs.toArray.map pn
    showNats (ofPoly (MultiplyNTT (toPoly (a.extract 0 256)) (toPoly (a.extract 256 512))))
  -- Section 7.1 packers
  | "SBP" :: b :: cs => hexOf (SimpleBitPack (toRPoly (cs.toArray.map pz)) (pn b))
  | ["SBU", b, h] => showInts (ofRPoly (SimpleBitUnpack (unhex h) (pn b)))
  | "BP" :: a :: b :: cs => hexOf (BitPack (toRPoly (cs.toArray.map pz)) (pn a) (pn b))
  | ["BU", a, b, h] => showInts (ofRPoly (BitUnpack (unhex h) (pn a) (pn b)))
  | "HBP" :: s :: rows =>
    let p := pOf (pn s)
    hexOf (HintBitPack p (toHint p.k (rows.toArray.map parseRow)))
  | ["HBU", s, h] =>
    let p := pOf (pn s)
    match HintBitUnpack p (unhex h) with
    | none => "none"
    | some rows => showRows (ofHint rows)
  -- Section 7.2 / 7.3 codecs
  | "PKE" :: s :: rho :: cs =>
    let p := pOf (pn s)
    hexOf (pkEncode p (unhex rho) (toRVec p.k (polysOf p.k cs)))
  | ["PKD", s, h] =>
    let p := pOf (pn s)
    let (rho, t1) := pkDecode p (unhex h)
    s!"{hexOf rho} ; {showInts (ofRVec t1)}"
  | "SKE" :: s :: rho :: key :: tr :: cs =>
    let p := pOf (pn s)
    let all := polysOf (p.ℓ + 2 * p.k) cs
    hexOf (skEncode p (unhex rho) (unhex key) (unhex tr) (toRVec p.ℓ (all.extract 0 p.ℓ))
      (toRVec p.k (all.extract p.ℓ (p.ℓ + p.k))) (toRVec p.k (all.extract (p.ℓ + p.k) (p.ℓ + 2 * p.k))))
  | ["SKD", s, h] =>
    let p := pOf (pn s)
    let (rho, key, tr, s1, s2, t0) := skDecode p (unhex h)
    s!"{hexOf rho} ; {hexOf key} ; {hexOf tr} ; {showInts (ofRVec s1)} ; {showInts (ofRVec s2)} ; {showInts (ofRVec t0)}"
  | "SGE" :: s :: ct :: cs =>
    let p := pOf (pn s)
    let zs := polysOf p.ℓ (cs.take (p.ℓ * 256))
    let rows := (cs.drop (p.ℓ * 256)).toArray.map parseRow
    hexOf (sigEncode p (unhex ct) (toRVec p.ℓ zs) (toHint p.k rows))
  | ["SGD", s, h] =>
    let p := pOf (pn s)
    match sigDecode p (unhex h) with
    | none => "none"
    | some (ct, z, hh) => s!"{hexOf ct} ; {showInts (ofRVec z)} ; {showRows (ofHint hh)}"
  | "W1E" :: s :: cs =>
    let p := pOf (pn s)
    hexOf (w1Encode p (toRVec p.k (polysOf p.k cs)))
  -- Section 7.3 samplers (default fuel)
  | ["SIB", s, h] =>
    match SampleInBall (pOf (pn s)) ({} : Fuel).sampleInBall (unhex h) with
    | none => "none"
    | some c => showInts (ofRPoly c)
  | ["RNTT", h] =>
    match RejNTTPoly ({} : Fuel).rejNTT (unhex h) with
    | none => "none"
    | some a => showNats (ofPoly a)
  | ["RBP", s, h] =>
    match RejBoundedPoly (pOf (pn s)) ({} : Fuel).rejBounded (unhex h) with
    | none => "none"
    | some a => showInts (ofRPoly a)
  | ["EXA", s, h] =>
    match ExpandA (pOf (pn s)) ({} : Fuel).rejNTT (unhex h) with
    | none => "none"
    | some A => " ".intercalate (A.toList.flatMap fun row => row.toList.map fun a => showNats (ofPoly a))
  | ["EXS", s, h] =>
    match ExpandS (pOf (pn s)) ({} : Fuel).rejBounded (unhex h) with
    | none => "none"
    | some (s1, s2) => s!"{showInts (ofRVec s1)} ; {showInts (ofRVec s2)}"
  | ["EXM", s, h, kappa] =>
    showInts (ofRVec (ExpandMask (pOf (pn s)) (unhex h) (pn kappa)))
  -- Algorithms 1, 2, 3 (and 6)
  | ["KG", s, xi] =>
    match KeyGen (pOf (pn s)) (unhex xi) with
    | none => "none"
    | some (pk, sk) => s!"{hexOf pk} ; {hexOf sk}"
  | ["SGN", s, sk, m, ctx, rnd] =>
    match Sign (pOf (pn s)) (unhex sk) (unhex m) (unhex ctx) (unhex rnd) with
    | none => "none"
    | some sg => hexOf sg
  | ["SGI", s, sk, mp, rnd] =>
    match Sign_internal (pOf (pn s)) (unhex sk) (unhex mp) (unhex rnd) with
    | none => "none"
    | some sg => hexOf sg
  | ["VRI", s, pk, mp, sg] =>
    showOptBool (Verify_internal (pOf (pn s)) (unhex pk) (unhex mp) (unhex sg))
  | ["SGF", s, sk, m, ctx, rnd, kind] =>
    let p := pOf (pn s)
    let target := if kind == "eq" then p.γ₁ - p.β else if kind == "lt" then p.γ₁ - p.β - 1 else p.γ₁ - p.β + 1
    let c := unhex ctx
    match signLoop p (unhex sk) (IntegerToBytes 0 1 ++ IntegerToBytes c.length 1 ++ c ++ unhex m) (unhex rnd) (some target) with
    | none => "none"
    | some (sg, _) => hexOf sg
  | ["SGA", s, sk, m, ctx, rnd] =>
    let p := pOf (pn s)
    let c := unhex ctx
    match signLoop p (unhex sk) (IntegerToBytes 0 1 ++ IntegerToBytes c.length 1 ++ c ++ unhex m) (unhex rnd) none with
    | none => "none"
    | some (_, n) => toString n
  | ["VER", s, pk, m, sg, ctx] =>
    showOptBool (Verify (pOf (pn s)) (unhex pk) (unhex m) (unhex sg) (unhex ctx))
  | _ => "ERR unknown-or-malformed-line"

def runFile (inp outp : String) : IO UInt32 := do
  let lines ← IO.FS.lines inp
  let h ← IO.FS.Handle.mk outp .write
  let mut n := 0
  for line in lines do
    if line.isEmpty then continue
    h.putStrLn (runLine line)
    n := n + 1
  h.flush
  IO.eprintln s!"{n} lines"
  return 0

end DiffCryptol

def main (args : List String) : IO UInt32 :=
  match args with
  | [inp, outp] => DiffCryptol.runFile inp outp
  | _ => do
    IO.eprintln "usage: spec-diff-cryptol <vectors> <output>"
    return 2
