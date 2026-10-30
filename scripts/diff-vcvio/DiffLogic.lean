import LatticeCrypto.MLDSA.Concrete.NTT

/-!
# VCVio: the proof-oriented NTT definitions against the executable loop kernels

In `MLDSA/Concrete/NTT.lean`, `ntt`, `invNTT` and `multiplyNTTs` are `@[implemented_by]` the loop kernels
`loopNTT`, `loopInvNTT`, `loopMultiplyNTTs`, so a compiled run of `DiffEval.lean` exercises only the loop kernels, and
the file itself notes that "this module does not yet prove the imperative Array programs extensionally equal"
to the structural definitions.  This scratch executable evaluates the structural definitions (the eight
certified butterfly stages, `nttCoeffs` / `invNTTCoeffs`), whose private pieces are copied here verbatim, on the first
`N` forward and `N` inverse vectors of `ntt.txt` and prints one line per vector, in the same canonical text as
`DiffEval.lean`.  The proof obligations in `nttStage` are `sorry`, which is fine for evaluation (they are erased).

usage: `vcv-logic <ntt.txt> <output> <N>`.
-/

open MLDSA MLDSA.Concrete

private def getZ (a : Array Coeff) (i : Nat) : Coeff := a.getD i 0

private theorem layer_shape :
    ∀ s : Fin 8, 2 ^ s.val * (2 * (128 / 2 ^ s.val)) = polyBackend.degree := by
  decide

private abbrev NTTCoord := Fin polyBackend.degree

private def layerLayout (s : Fin 8) :
    LatticeCrypto.NTTCert.ButterflyLayout
      (Fin (2 ^ s.val) × Fin (128 / 2 ^ s.val)) NTTCoord where
  equiv := (LatticeCrypto.NTTCert.blockLayout (2 ^ s.val) (128 / 2 ^ s.val)).equiv.trans
    (finCongr (layer_shape s))

private def nttStage (s : Fin 8) :
    LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord :=
  LatticeCrypto.NTTCert.butterflyStage (layerLayout s)
    (fun pair => getZ zetaTable (2 ^ s.val + pair.1.val))
    (fun pair => -getZ zetaTable (2 ^ (s.val + 1) - 1 - pair.1.val))
    (by intro pair; sorry)

private def nttStages :
    List (LatticeCrypto.NTTCert.ScaledStage Coeff NTTCoord) :=
  [nttStage 0, nttStage 1, nttStage 2, nttStage 3,
    nttStage 4, nttStage 5, nttStage 6, nttStage 7]

private def nttCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.forwardStages nttStages input

private def invNTTCoeffs (input : NTTCoord → Coeff) : NTTCoord → Coeff :=
  LatticeCrypto.NTTCert.scaleCoeffs nInv
    (LatticeCrypto.NTTCert.inverseStages nttStages input)

def toRq (a : Array Nat) : Rq := Vector.ofFn fun i : Fin ringDegree => (a[i.val]! : Coeff)
def ofRq (r : Rq) : Array Nat := Array.ofFn fun i : Fin ringDegree => (r.get i).val

def logicNtt (a : Array Nat) : Array Nat :=
  ofRq (LatticeCrypto.NTTCert.applyCoeffTransform polyBackend nttCoeffs (toRq a))

def logicInvNtt (a : Array Nat) : Array Nat :=
  ofRq (LatticeCrypto.NTTCert.applyCoeffTransform polyBackend invNTTCoeffs (toRq a))

def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, outp, n] =>
    let n := n.toNat!
    let lines ← IO.FS.lines inp
    let h ← IO.FS.Handle.mk outp .write
    let mut nf := 0
    let mut ni := 0
    for line in lines do
      match line.splitOn " " with
      | "NTT" :: cs =>
        if nf < n then
          nf := nf + 1
          h.putStrLn (" ".intercalate ((logicNtt (cs.toArray.map String.toNat!)).toList.map toString))
      | "INTT" :: cs =>
        if ni < n then
          ni := ni + 1
          h.putStrLn (" ".intercalate ((logicInvNtt (cs.toArray.map String.toNat!)).toList.map toString))
      | _ => pure ()
    h.flush
    return 0
  | _ =>
    IO.eprintln "usage: vcv-logic <ntt.txt> <output> <N>"
    return 2
