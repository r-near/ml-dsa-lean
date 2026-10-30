import Impl

/-!
# Differential evaluation of the extracted code (`lean/Impl`)

A compiled executable that evaluates the Aeneas-extracted Rust (`Impl.*`) on input vectors and prints canonical
outputs, to be compared with the native Rust on the same inputs (`examples/impl_eval.rs`). This is an empirical check
of the Charon/Aeneas translation, which is part of the trusted base.

Usage: `impl-eval INPUTS OUTPUTS`. Each line of INPUTS is `op arg arg ...` (see `scripts/gen-impl-eval-inputs.py` for
the encodings); OUTPUTS gets one line per input line: the canonical result, `N` for `None`, `FAIL` when the extracted
function returns `fail` (the Rust panics), `DIV` for divergence, or `BADIN` for a malformed line.
Run through `scripts/impl-eval.sh`.
-/

open Aeneas Aeneas.Std Impl

namespace ImplEval

abbrev Poly := Aeneas.Std.Array U32 256#usize
abbrev BPoly := Aeneas.Std.Array Bool 256#usize

/-! ## Scalars, arrays and slices from text -/

def mkU {ty : UScalarTy} (n : Nat) : UScalar ty := ⟨BitVec.ofNat _ n⟩

def arrD {α : Type} (n : Usize) (l : List α) (d : α) : Aeneas.Std.Array α n :=
  if h : l.length = n.val then ⟨l, h⟩ else Aeneas.Std.Array.repeat n d

def arrOf? {α : Type} (n : Usize) (l : List α) : Option (Aeneas.Std.Array α n) :=
  if h : l.length = n.val then some ⟨l, h⟩ else none

def sliceOf {α : Type} (l : List α) : Slice α :=
  if h : l.length ≤ Usize.max then ⟨l, h⟩ else ⟨[], Nat.zero_le _⟩

def hexVal (c : UInt8) : Nat :=
  if c ≥ 48 && c ≤ 57 then (c - 48).toNat else if c ≥ 97 && c ≤ 102 then (c - 87).toNat else (c - 55).toNat

def hexNat (b : ByteArray) (off len : Nat) : Nat :=
  (List.range len).foldl (fun acc i => acc * 16 + hexVal (b.get! (off + i))) 0

/-- Bytes (as naturals) of a hex string; `-` is the empty string. -/
def unhex (s : String) : List Nat :=
  if s == "-" then []
  else
    let b := s.toUTF8
    (List.range (b.size / 2)).map fun i => hexNat b (2 * i) 2

def bytesOf (s : String) : List U8 := (unhex s).map fun n => mkU n

def hexChar (n : Nat) : Char := Char.ofNat (if n < 10 then 48 + n else 87 + n)

def hexWord (w n : Nat) : String :=
  String.ofList ((List.range w).reverse.map fun i => hexChar ((n / 16 ^ i) % 16))

def hexNats (l : List Nat) : String :=
  if l.isEmpty then "-" else String.join (l.map fun b => hexWord 2 b)

def hexBytes {n : Usize} (a : Aeneas.Std.Array U8 n) : String := hexNats (a.val.map fun b => b.val)
def hexSlice (a : Slice U8) : String := hexNats (a.val.map fun b => b.val)

def polyAt (b : ByteArray) (i : Nat) : Poly :=
  arrD 256#usize ((List.range 256).map fun j => mkU (hexNat b (2048 * i + 8 * j) 8)) 0#u32

def polyOf (s : String) : Option Poly :=
  let b := s.toUTF8
  if b.size == 2048 then some (polyAt b 0) else none

def polysOf (n : Usize) (s : String) : Option (Aeneas.Std.Array Poly n) :=
  let b := s.toUTF8
  if b.size == 2048 * n.val then
    arrOf? n ((List.range n.val).map fun i => polyAt b i)
  else none

/-- `K` rows of `L` polynomials. -/
def matOf (K L : Usize) (s : String) : Option (Aeneas.Std.Array (Aeneas.Std.Array Poly L) K) :=
  let b := s.toUTF8
  if b.size == 2048 * K.val * L.val then
    arrOf? K ((List.range K.val).map fun i =>
      arrD L ((List.range L.val).map fun j => polyAt b (i * L.val + j)) (polyAt b 0))
  else none

def bpolyAt (b : ByteArray) (i : Nat) : BPoly :=
  arrD 256#usize ((List.range 256).map fun j => b.get! (256 * i + j) == 49) false

def bpolysOf (n : Usize) (s : String) : Option (Aeneas.Std.Array BPoly n) :=
  let b := s.toUTF8
  if b.size == 256 * n.val then arrOf? n ((List.range n.val).map fun i => bpolyAt b i) else none

def hexPoly (a : Poly) : String := String.join (a.val.map fun c => hexWord 8 c.val)
def hexPolys {n : Usize} (v : Aeneas.Std.Array Poly n) : String := String.join (v.val.map hexPoly)
def hexBPoly (a : BPoly) : String := String.ofList (a.val.map fun x => if x then '1' else '0')
def hexBPolys {n : Usize} (v : Aeneas.Std.Array BPoly n) : String := String.join (v.val.map hexBPoly)

def fin {α : Type} (r : RustM α) (f : α → String) : String :=
  match r with
  | .ok a => f a
  | .fail _ => "FAIL"
  | .div => "DIV"

def dec {ty : UScalarTy} (x : UScalar ty) : String := toString x.val
def optDec {ty : UScalarTy} (o : Option (UScalar ty)) : String :=
  match o with
  | none => "N"
  | some x => toString x.val
def bit (b : Bool) : String := if b then "1" else "0"

def paramsOf (sn : String) : RustM params.Params :=
  if sn == "44" then params.ML_DSA_44 else if sn == "65" then params.ML_DSA_65 else params.ML_DSA_87

def klOf (sn : String) : Usize × Usize :=
  if sn == "44" then (4#usize, 4#usize) else if sn == "65" then (6#usize, 5#usize) else (8#usize, 7#usize)

/-! ## Keccak -/

def leNat (l : List Nat) : Nat := l.foldr (fun b acc => acc * 256 + b) 0

def chunks {α : Type} (k : Nat) (l : List α) : List (List α) :=
  go (l.length + 1) l
where
  go : Nat → List α → List (List α)
    | 0, _ => []
    | _ + 1, [] => []
    | f + 1, l => l.take k :: go f (l.drop k)

def absorbAll (sh : keccak.Shake) : List (List U8) → RustM keccak.Shake
  | [] => pure sh
  | c :: cs => do
    let sh' ← keccak.Shake.absorb sh (sliceOf c)
    absorbAll sh' cs

def squeezeAll (chunk : Nat) : Nat → keccak.Shake → Nat → RustM (List U8)
  | 0, _, _ => pure []
  | f + 1, sh, rem =>
    if rem == 0 then pure []
    else do
      let n := min chunk rem
      let (sh', out) ← keccak.Shake.squeeze sh (sliceOf (List.replicate n (0#u8 : U8)))
      let rest ← squeezeAll chunk f sh' (rem - n)
      pure (out.val ++ rest)

def shakeRun (mk : RustM keccak.Shake) (msg : List U8) (outlen chunk : Nat) : RustM (List U8) := do
  let sh ← mk
  let sh ← absorbAll sh (chunks chunk msg)
  let sh ← keccak.Shake.finalize sh
  squeezeAll chunk (outlen + 1) sh outlen

def keccakOp (op : String) (a : Array String) : Option String :=
  match op with
  | "keccak_f1600" =>
    let bs := unhex a[0]!
    if bs.length != 200 then none
    else
      let words : List U64 := (List.range 25).map fun i => mkU (leNat ((bs.drop (8 * i)).take 8))
      (arrOf? 25#usize words).map fun st =>
        fin (keccak.keccak_f1600 st) fun r =>
          hexNats (r.val.flatMap fun (w : U64) => (List.range 8).map fun j => (w.val / 256 ^ j) % 256)
  | "shake128" | "shake256" =>
    match a[1]!.toNat?, a[2]!.toNat? with
    | some ol, some ch =>
      if ch == 0 then none
      else
        let mk := if op == "shake128" then keccak.Shake.shake128 else keccak.Shake.shake256
        some (fin (shakeRun mk (bytesOf a[0]!) ol ch) fun l => hexNats (l.map fun b => b.val))
    | _, _ => none
  | _ => none

/-! ## Operations that do not depend on the parameter set -/

def plainOp (op : String) (a : Array String) : Option String :=
  match op with
  | "f_add" | "f_sub" | "f_mul" =>
    match a[0]!.toNat?, a[1]!.toNat? with
    | some x, some y =>
      let f := if op == "f_add" then field.add else if op == "f_sub" then field.sub else field.mul
      some (fin (f (mkU x) (mkU y)) dec)
    | _, _ => none
  | "f_neg" => a[0]!.toNat?.map fun x => fin (field.neg (mkU x)) dec
  | "f_small_reduce" => a[0]!.toNat?.map fun x => fin (field.small_reduce (mkU x)) dec
  | "f_barrett_reduce" => a[0]!.toNat?.map fun x => fin (field.barrett_reduce (mkU x)) dec
  | "f_ct_lt_mask" =>
    match a[0]!.toNat?, a[1]!.toNat? with
    | some x, some y => some (fin (field.ct_lt_mask (mkU x) (mkU y)) dec)
    | _, _ => none
  | "f_ct_select" =>
    match a[0]!.toNat?, a[1]!.toNat?, a[2]!.toNat? with
    | some x, some y, some m => some (fin (field.ct_select (mkU x) (mkU y) (mkU m)) dec)
    | _, _, _ => none
  | "ntt" => (polyOf a[0]!).map fun p => fin (ntt.ntt p) hexPoly
  | "ntt_inverse" => (polyOf a[0]!).map fun p => fin (ntt.ntt_inverse p) hexPoly
  | "multiply_ntt" | "add_poly" | "sub_poly" =>
    match polyOf a[0]!, polyOf a[1]! with
    | some x, some y =>
      let f := if op == "multiply_ntt" then ntt.multiply_ntt else if op == "add_poly" then ntt.add_poly else ntt.sub_poly
      some (fin (f x y) hexPoly)
    | _, _ => none
  | "power2round" => a[0]!.toNat?.map fun x => fin (rounding.power2round (mkU x)) fun (r1, r0) => s!"{r1.val} {r0.val}"
  | "infinity_norm" => a[0]!.toNat?.map fun x => fin (rounding.infinity_norm (mkU x)) dec
  | "poly_power2round" =>
    (polyOf a[0]!).map fun p => fin (rounding.poly_power2round p) fun (t1, t0) => hexPoly t1 ++ " " ++ hexPoly t0
  | "rej_ntt_poly" =>
    match arrOf? 34#usize (bytesOf a[0]!) with
    | some rho => some (fin (sampling.rej_ntt_poly rho) hexPoly)
    | none => none
  | "coeff_from_three_bytes" =>
    match a[0]!.toNat?, a[1]!.toNat?, a[2]!.toNat? with
    | some x, some y, some z => some (fin (sampling.coeff_from_three_bytes (mkU x) (mkU y) (mkU z)) optDec)
    | _, _, _ => none
  | "bit_pack" =>
    match polyOf a[0]!, a[1]!.toNat? with
    | some w, some c =>
      some (fin (encode.bit_pack w (mkU c) (sliceOf (List.replicate (32 * c) (0#u8 : U8)))) hexSlice)
    | _, _ => none
  | "bit_unpack" =>
    match a[1]!.toNat? with
    | some c =>
      let v := bytesOf a[0]!
      if v.length != 32 * c then none
      else some (fin (encode.bit_unpack (sliceOf v) (mkU c)) hexPoly)
    | none => none
  | _ => keccakOp op a

/-! ## Operations for one parameter set -/

def setOp (sn : String) (K L : Usize) (base : String) (a : Array String) : Option String :=
  let pr := paramsOf sn
  match base with
  | "matrix_vector_ntt" =>
    match matOf K L a[0]!, polysOf L a[1]! with
    | some m, some v => some (fin (ntt.matrix_vector_ntt m v) hexPolys)
    | _, _ => none
  | "vec_infinity_norm" => (polysOf K a[0]!).map fun v => fin (rounding.vec_infinity_norm v) dec
  | "decompose" =>
    a[0]!.toNat?.map fun x => fin (do let p ← pr; rounding.decompose p (mkU x)) fun (r1, r0) => s!"{r1.val} {r0.val}"
  | "high_bits" => a[0]!.toNat?.map fun x => fin (do let p ← pr; rounding.high_bits p (mkU x)) dec
  | "low_bits" => a[0]!.toNat?.map fun x => fin (do let p ← pr; rounding.low_bits p (mkU x)) dec
  | "make_hint" =>
    match a[0]!.toNat?, a[1]!.toNat? with
    | some z, some r => some (fin (do let p ← pr; rounding.make_hint p (mkU z) (mkU r)) bit)
    | _, _ => none
  | "use_hint" =>
    match a[0]!.toNat?, a[1]!.toNat? with
    | some h, some r => some (fin (do let p ← pr; rounding.use_hint p (h != 0) (mkU r)) dec)
    | _, _ => none
  | "poly_high_bits" => (polyOf a[0]!).map fun w => fin (do let p ← pr; rounding.poly_high_bits p w) hexPoly
  | "poly_low_bits" => (polyOf a[0]!).map fun w => fin (do let p ← pr; rounding.poly_low_bits p w) hexPoly
  | "poly_use_hint" =>
    match polyOf a[1]! with
    | some r =>
      if a[0]!.toUTF8.size == 256 then
        some (fin (do let p ← pr; rounding.poly_use_hint p (bpolyAt a[0]!.toUTF8 0) r) hexPoly)
      else none
    | none => none
  | "coeff_from_half_byte" =>
    a[0]!.toNat?.map fun b => fin (do let p ← pr; sampling.coeff_from_half_byte p (mkU b)) optDec
  | "rej_bounded_poly" =>
    match arrOf? 66#usize (bytesOf a[0]!) with
    | some rho => some (fin (do let p ← pr; sampling.rej_bounded_poly p rho) hexPoly)
    | none => none
  | "expand_a" =>
    match arrOf? 32#usize (bytesOf a[0]!) with
    | some rho =>
      some (fin (sampling.expand_a K L rho) fun m => String.join (m.val.map fun row => hexPolys row))
    | none => none
  | "expand_s" =>
    match arrOf? 64#usize (bytesOf a[0]!) with
    | some rho =>
      some (fin (do let p ← pr; sampling.expand_s K L p rho) fun (s1, s2) => hexPolys s1 ++ " " ++ hexPolys s2)
    | none => none
  | "expand_mask" =>
    match arrOf? 64#usize (bytesOf a[0]!), a[1]!.toNat? with
    | some rho, some mu => some (fin (do let p ← pr; sampling.expand_mask L p rho (mkU mu)) hexPolys)
    | _, _ => none
  | "sample_in_ball" =>
    some (fin (do let p ← pr; sampling.sample_in_ball p (sliceOf (bytesOf a[0]!))) hexPoly)
  | "pk_encode" =>
    match arrOf? 32#usize (bytesOf a[0]!), polysOf K a[1]! with
    | some rho, some t1 =>
      some (fin (encode.pk_encode rho t1 (sliceOf (List.replicate (32 + 320 * K.val) (0#u8 : U8)))) hexSlice)
    | _, _ => none
  | "pk_decode" =>
    some (fin (encode.pk_decode K (sliceOf (bytesOf a[0]!))) fun (rho, t1) => hexBytes rho ++ " " ++ hexPolys t1)
  | "sk_encode" =>
    match arrOf? 32#usize (bytesOf a[0]!), arrOf? 32#usize (bytesOf a[1]!), arrOf? 64#usize (bytesOf a[2]!),
        polysOf L a[3]!, polysOf K a[4]!, polysOf K a[5]! with
    | some rho, some key, some tr, some s1, some s2, some t0 =>
      let len := 128 + 32 * ((K.val + L.val) * (if sn == "65" then 4 else 3) + 13 * K.val)
      some (fin (do
          let p ← pr
          encode.sk_encode p rho key tr s1 s2 t0 (sliceOf (List.replicate len (0#u8 : U8)))) hexSlice)
    | _, _, _, _, _, _ => none
  | "sk_decode" =>
    some (fin (do let p ← pr; encode.sk_decode K L p (sliceOf (bytesOf a[0]!))) fun sk =>
      hexBytes sk.rho ++ " " ++ hexBytes sk.key ++ " " ++ hexBytes sk.tr ++ " " ++ hexPolys sk.s1 ++ " " ++
        hexPolys sk.s2 ++ " " ++ hexPolys sk.t0)
  | "sig_encode" =>
    let ct := if sn == "44" then 32 else if sn == "65" then 48 else 64
    let g1 := if sn == "44" then 18 else 20
    let om := if sn == "44" then 80 else if sn == "65" then 55 else 75
    match polysOf L a[1]!, bpolysOf K a[2]! with
    | some z, some h =>
      let len := ct + L.val * 32 * g1 + om + K.val
      some (fin (do
          let p ← pr
          encode.sig_encode p (sliceOf (bytesOf a[0]!)) z h (sliceOf (List.replicate len (0#u8 : U8)))) hexSlice)
    | _, _ => none
  | "sig_decode" =>
    some (fin (do let p ← pr; encode.sig_decode K L p (sliceOf (bytesOf a[0]!))) fun o =>
      match o with
      | none => "N"
      | some (ct, z, h) => hexBytes ct ++ " " ++ hexPolys z ++ " " ++ hexBPolys h)
  | "w1_encode" =>
    match polysOf K a[0]! with
    | some w1 =>
      let n := K.val * 32 * (if sn == "44" then 6 else 4)
      some (fin (do let p ← pr; encode.w1_encode p w1 (sliceOf (List.replicate n (0#u8 : U8)))) hexSlice)
    | none => none
  | "hint_bit_pack" =>
    match bpolysOf K a[0]! with
    | some h =>
      let om := if sn == "44" then 80 else if sn == "65" then 55 else 75
      some (fin (do let p ← pr; encode.hint_bit_pack p h (sliceOf (List.replicate (om + K.val) (0#u8 : U8)))) hexSlice)
    | none => none
  | "hint_bit_unpack" =>
    some (fin (do let p ← pr; encode.hint_bit_unpack K p (sliceOf (bytesOf a[0]!))) fun o =>
      match o with
      | none => "N"
      | some h => hexBPolys h)
  | _ => none

/-! ## The public API -/

def keygenOf {a b : Usize} (f : Aeneas.Std.Array U8 32#usize → RustM (Aeneas.Std.Array U8 a × Aeneas.Std.Array U8 b))
    (args : Array String) : Option String :=
  (arrOf? 32#usize (bytesOf args[0]!)).map fun xi => fin (f xi) fun (pk, sk) => hexBytes pk ++ " " ++ hexBytes sk

def signOf {a b : Usize}
    (f : Aeneas.Std.Array U8 a → Slice U8 → Slice U8 → Aeneas.Std.Array U8 32#usize →
      RustM (Option (Aeneas.Std.Array U8 b)))
    (args : Array String) : Option String :=
  match arrOf? a (bytesOf args[0]!), arrOf? 32#usize (bytesOf args[3]!) with
  | some sk, some rnd =>
    some (fin (f sk (sliceOf (bytesOf args[1]!)) (sliceOf (bytesOf args[2]!)) rnd) fun o =>
      match o with
      | none => "N"
      | some s => hexBytes s)
  | _, _ => none

def signIntOf {a b : Usize}
    (f : Aeneas.Std.Array U8 a → Slice U8 → Aeneas.Std.Array U8 32#usize → RustM (Option (Aeneas.Std.Array U8 b)))
    (args : Array String) : Option String :=
  match arrOf? a (bytesOf args[0]!), arrOf? 32#usize (bytesOf args[2]!) with
  | some sk, some rnd =>
    some (fin (f sk (sliceOf (bytesOf args[1]!)) rnd) fun o =>
      match o with
      | none => "N"
      | some s => hexBytes s)
  | _, _ => none

def verifyOf {a b : Usize}
    (f : Aeneas.Std.Array U8 a → Slice U8 → Slice U8 → Aeneas.Std.Array U8 b → RustM Bool)
    (args : Array String) : Option String :=
  match arrOf? a (bytesOf args[0]!), arrOf? b (bytesOf args[3]!) with
  | some pk, some sg =>
    some (fin (f pk (sliceOf (bytesOf args[1]!)) (sliceOf (bytesOf args[2]!)) sg) bit)
  | _, _ => none

def verifyIntOf {a b : Usize}
    (f : Aeneas.Std.Array U8 a → Slice U8 → Aeneas.Std.Array U8 b → RustM Bool)
    (args : Array String) : Option String :=
  match arrOf? a (bytesOf args[0]!), arrOf? b (bytesOf args[2]!) with
  | some pk, some sg => some (fin (f pk (sliceOf (bytesOf args[1]!)) sg) bit)
  | _, _ => none

def apiOp (sn base : String) (a : Array String) : Option String :=
  match base, sn with
  | "keygen", "44" => keygenOf api.keygen_44 a
  | "keygen", "65" => keygenOf api.keygen_65 a
  | "keygen", "87" => keygenOf api.keygen_87 a
  | "sign", "44" => signOf api.sign_44 a
  | "sign", "65" => signOf api.sign_65 a
  | "sign", "87" => signOf api.sign_87 a
  | "sign_internal", "44" => signIntOf api.sign_internal_44 a
  | "sign_internal", "65" => signIntOf api.sign_internal_65 a
  | "sign_internal", "87" => signIntOf api.sign_internal_87 a
  | "verify", "44" => verifyOf api.verify_44 a
  | "verify", "65" => verifyOf api.verify_65 a
  | "verify", "87" => verifyOf api.verify_87 a
  | "verify_internal", "44" => verifyIntOf api.verify_internal_44 a
  | "verify_internal", "65" => verifyIntOf api.verify_internal_65 a
  | "verify_internal", "87" => verifyIntOf api.verify_internal_87 a
  | _, _ => none

def evalLine (line : String) : String :=
  match line.splitOn " " with
  | [] => "BADIN"
  | op :: rest =>
    let a := rest.toArray
    let sn := (op.takeEnd 2).toString
    let r :=
      if sn == "44" || sn == "65" || sn == "87" then
        let base := (op.dropEnd 2).toString
        match apiOp sn base a with
        | some r => some r
        | none => let (K, L) := klOf sn; setOp sn K L base a
      else plainOp op a
    r.getD "BADIN"

end ImplEval

open ImplEval in
def main (args : List String) : IO UInt32 := do
  match args with
  | [inp, outp] =>
    let hin ← IO.FS.Handle.mk inp .read
    let hout ← IO.FS.Handle.mk outp .write
    let t0 ← IO.monoMsNow
    let mut n := 0
    repeat
      let line ← hin.getLine
      if line.isEmpty then break
      let line := if line.back == '\n' then (line.dropEnd 1).toString else line
      hout.putStrLn (evalLine line)
      n := n + 1
    hout.flush
    let t1 ← IO.monoMsNow
    IO.eprintln s!"impl-eval: {n} cases in {t1 - t0} ms"
    return 0
  | _ =>
    IO.eprintln "usage: impl-eval INPUTS OUTPUTS"
    return 2
