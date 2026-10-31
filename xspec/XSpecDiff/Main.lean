import XSpecDiff.Ours
import XSpecDiff.Theirs

/-! `xspec-diff ours|theirs <vectors> <output>`: print one canonical output line per input line. -/

def main (args : List String) : IO UInt32 :=
  match args with
  | ["ours", inp, outp] => DiffCommon.runFile XSpecDiff.Ours.impl inp outp
  | ["theirs", inp, outp] => do
    let r ← DiffCommon.runFile XSpecDiff.Theirs.impl inp outp
    return r
  | _ => do
    IO.eprintln "usage: xspec-diff ours|theirs <vectors> <output>"
    return 2
