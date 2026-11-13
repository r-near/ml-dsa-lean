#!/usr/bin/env python3
"""Cryptol side of the differential: evaluate vector lines with GaloisInc/cryptol-specs, print canonical lines.

    cryptol_eval.py CHUNK FIRST OUT [ERR]

CHUNK is a vector file (or a slice of one), FIRST the index of its first line in the whole vector file, OUT the
file that receives one canonical output line per input line (the same text `spec-diff-cryptol` prints for that
line), ERR a file that keeps Cryptol's raw stderr/stdout noise (errors) for debugging.  Fails closed: a line
for which Cryptol printed no result (error, timeout, missing tag) is written as `CRYPTOL-ERROR`.

Needs `$CRYPTOL_TOOLS` (default `$HOME/rx/scratch/cryptol-tools`, see setup.sh).  Every expression is wrapped as
`(index : [32]) # <payload>`, an unsigned 32-bit tag followed by the flat payload word, printed by Cryptol as one
hexadecimal token (see `cry/DiffDrv.cry`); the decoders below turn the payload back into the canonical text.
"""
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import PARAMS, Q  # noqa: E402

TOOLS = os.environ.get("CRYPTOL_TOOLS", os.path.expanduser("~/rx/scratch/cryptol-tools"))
HERE = os.path.dirname(os.path.abspath(__file__))
TIMEOUT = int(os.environ.get("CRYPTOL_TIMEOUT", "7200"))


# ----------------------------------------------------------------------------- literals

def blit(h):
    """Cryptol literal for a byte string given as hex (`-` is empty): ([..] : [n][8])."""
    b = b"" if h == "-" else bytes.fromhex(h)
    return "([" + ",".join(str(x) for x in b) + f"] : [{len(b)}][8])"


def ilit(fields):
    return "[" + ",".join(fields) + "]"


def polys(fields, n):
    """n polynomials (lists of 256 integer literals) from a flat field list."""
    return "[" + ",".join(ilit(fields[i * 256:(i + 1) * 256]) for i in range(n)) + "]"


def hword(bits):
    """A row of a hint vector as a 256-bit literal; element j is bit 255 - j (element 0 is the MSB)."""
    v = 0
    for j, c in enumerate(bits):
        if c == "1":
            v |= 1 << (255 - j)
    return f"(0x{v:064x} : [256])"


def hint_rows_word(rows):
    out = []
    for r in rows:
        w = 0
        for j in r:
            w |= 1 << (255 - j)
        out.append(f"(0x{w:064x} : [256])")
    return "[" + ",".join(out) + "]"


def parse_row(s):
    return [] if s == "-" else [int(x) for x in s.split(",")]


# ----------------------------------------------------------------------------- expressions

def module_of(f):
    tag = f[0]
    if tag in ("P2R", "DEC", "MH", "UH", "HBP", "HBU", "PKE", "PKD", "SKE", "SKD", "SGE", "SGD", "W1E", "SIB", "RBP",
               "EXA", "EXS", "EXM", "KG", "KGO", "KGT", "SGN", "SGI", "VER", "VRI"):
        return "Drv" + f[1]
    return "Drv44"


def expr(f):
    """Cryptol payload expression for the vector line with fields f."""
    t = f[0]
    if t == "H256":
        return f"join (S::H`{{{f[1]}}} {blit(f[2])})"
    if t == "H128":
        return f"join (S::G`{{{f[1]}}} {blit(f[2])})"
    if t in ("P2R", "DEC"):
        P = PARAMS[int(f[1])]
        x = polys(f[2:], P["k"])
        if t == "P2R":
            return f"(\\(a, b) -> vI (join a) # vI (join b)) (S::Power2Round {x})"
        return (f"(\\x -> (\\(a, b) -> vI (join a) # vI (join b)) (S::Decompose x) # vI (join (S::HighBits x)) # "
                f"vI (join (S::LowBits x))) {x}")
    if t == "MH":
        P = PARAMS[int(f[1])]
        n = P["k"] * 256
        z = polys(f[2:2 + n], P["k"])
        r = polys(f[2 + n:2 + 2 * n], P["k"])
        return f"join (S::MakeHint {z} {r})"
    if t == "UH":
        P = PARAMS[int(f[1])]
        h = "[" + ",".join(hword(f[2][i * 256:(i + 1) * 256]) for i in range(P["k"])) + "]"
        r = polys(f[3:], P["k"])
        return f"vI (join (S::UseHint {h} {r}))"
    if t == "NTT":
        return f"vZ (S::NTT {ilit(f[1:])})"
    if t == "INTT":
        return f"vZ (S::NTTInv {ilit(f[1:])})"
    if t == "MUL":
        return f"vZ (S::MultiplyNTT {ilit(f[1:257])} {ilit(f[257:513])})"
    if t == "SBP":
        return f"join (S::SimpleBitPack`{{{f[1]}}} {ilit(f[2:])})"
    if t == "SBU":
        return f"vI (S::SimpleBitUnpack`{{{int(f[1])}}} {blit(f[2])})"
    if t == "BP":
        return f"join (S::BitPack`{{{f[1]}, {f[2]}}} {ilit(f[3:])})"
    if t == "BU":
        a, b = int(f[1]), int(f[2])
        return f"vI (S::BitUnpack`{{{a}, {b}}} {blit(f[3])})"
    if t == "HBP":
        return f"join (S::HintBitPack {hint_rows_word([parse_row(r) for r in f[2:]])})"
    if t == "HBU":
        P = PARAMS[int(f[1])]
        return f"optW ((\\o -> case o of Some h -> Some (join h); None -> None) (S::HintBitUnpack {blit(f[2])}))"
    if t == "PKE":
        P = PARAMS[int(f[1])]
        return f"join (S::pkEncode {blit(f[2])} {polys(f[3:], P['k'])})"
    if t == "PKD":
        return f"(\\(rho, t1) -> join rho # vI (join t1)) (S::pkDecode {blit(f[2])})"
    if t == "SKE":
        P = PARAMS[int(f[1])]
        k, l = P["k"], P["l"]
        v = f[5:]
        return (f"join (S::skEncode {blit(f[2])} {blit(f[3])} {blit(f[4])} {polys(v[:l * 256], l)} "
                f"{polys(v[l * 256:(l + k) * 256], k)} {polys(v[(l + k) * 256:], k)})")
    if t == "SKD":
        return (f"(\\(rho, K, tr, s1, s2, t0) -> join rho # join K # join tr # vI (join s1) # vI (join s2) # "
                f"vI (join t0)) (S::skDecode {blit(f[2])})")
    if t == "SGE":
        P = PARAMS[int(f[1])]
        l, k = P["l"], P["k"]
        v = f[3:]
        return (f"join (S::sigEncode {blit(f[2])} {polys(v[:l * 256], l)} "
                f"{hint_rows_word([parse_row(r) for r in v[l * 256:l * 256 + k]])})")
    if t == "SGD":
        return (f"(\\(ct, z, oh) -> join ct # vI (join z) # optW ((\\o -> case o of Some h -> Some (join h); "
                f"None -> None) oh)) (S::sigDecode {blit(f[2])})")
    if t == "W1E":
        P = PARAMS[int(f[1])]
        return f"join (S::w1Encode {polys(f[2:], P['k'])})"
    if t == "SIB":
        return f"vI (S::SampleInBall {blit(f[2])})"
    if t == "RNTT":
        return f"vZ (S::RejNTTPoly {blit(f[1])})"
    if t == "RBP":
        return f"vI (S::RejBoundedPoly {blit(f[2])})"
    if t == "EXA":
        return f"vZ (join (join (S::ExpandA {blit(f[2])})))"
    if t == "EXS":
        return f"(\\(a, b) -> vI (join a) # vI (join b)) (S::ExpandS {blit(f[2])})"
    if t == "EXM":
        return f"vI (join (S::ExpandMask {blit(f[2])} {f[3]}))"
    if t in ("KG", "KGO", "KGT"):
        m = {"KG": "S", "KGO": "O", "KGT": "T"}[t]
        return f"(\\(pk, sk) -> join pk # join sk) ({m}::KeyGen_internal {blit(f[2])})"
    if t == "SGN":
        return (f"optW ((\\o -> case o of Some s -> Some (join s); None -> None) "
                f"(D::Sign {blit(f[2])} (join {blit(f[3])}) {blit(f[4])} (Some {blit(f[5])})))")
    if t == "SGI":
        # Sign_internal(sk, M', rnd): M' given as hex bytes
        return f"join (T::Sign_internal {blit(f[2])} (join {blit(f[3])}) {blit(f[4])})"
    if t == "VER":
        return f"optBool (D::Verify {blit(f[2])} (join {blit(f[3])}) {blit(f[4])} {blit(f[5])})"
    if t == "VRI":
        return f"optBool (Some (T::Verify_internal {blit(f[2])} (join {blit(f[3])}) {blit(f[4])}))"
    raise ValueError("unknown tag " + t)


# ----------------------------------------------------------------------------- decoding of the payload word

def sints(h):
    out = []
    for i in range(0, len(h), 8):
        v = int(h[i:i + 8], 16)
        out.append(v - (1 << 32) if v >= 1 << 31 else v)
    return out


def bhex(h):
    return h if h else "-"


def sj(xs):
    return " ".join(str(x) for x in xs)


def rows_of_bits(bits, k):
    rows = []
    for i in range(k):
        r = [j for j in range(256) if bits[i * 256 + j] == "1"]
        rows.append(",".join(map(str, r)) if r else "-")
    return " ".join(rows)


def hex_bits(h, n):
    return bin(int(h, 16))[2:].zfill(n) if h else ""


def decode(f, h):
    """Canonical output text for line fields f given the payload hex digits h (without the 8-digit tag)."""
    t = f[0]
    if t in ("H256", "H128", "SBP", "BP", "HBP", "PKE", "SKE", "SGE", "W1E", "SGI"):
        return bhex(h)
    if t == "P2R":
        v = sints(h)
        n = len(v) // 2
        return f"{sj(v[:n])} ; {sj(v[n:])}"
    if t == "DEC":
        v = sints(h)
        n = len(v) // 4
        return " ; ".join(sj(v[i * n:(i + 1) * n]) for i in range(4))
    if t == "MH":
        return hex_bits(h, len(h) * 4)
    if t in ("UH", "NTT", "INTT", "MUL", "SBU", "BU", "SIB", "RNTT", "RBP", "EXA", "EXM"):
        return sj(sints(h))
    if t == "HBU":
        k = PARAMS[int(f[1])]["k"]
        if h[:2] == "00":
            return "none"
        return rows_of_bits(hex_bits(h[2:], k * 256), k)
    if t == "PKD":
        return f"{bhex(h[:64])} ; {sj(sints(h[64:]))}"
    if t == "SKD":
        P = PARAMS[int(f[1])]
        k, l = P["k"], P["l"]
        n1, n2 = l * 256 * 8, k * 256 * 8
        rho, key, tr, rest = h[:64], h[64:128], h[128:256], h[256:]
        s1, s2, t0 = rest[:n1], rest[n1:n1 + n2], rest[n1 + n2:]
        return f"{rho} ; {key} ; {tr} ; {sj(sints(s1))} ; {sj(sints(s2))} ; {sj(sints(t0))}"
    if t == "SGD":
        P = PARAMS[int(f[1])]
        k, l, ct = P["k"], P["l"], P["ct_len"]
        ctx = h[:2 * ct]
        zs = h[2 * ct:2 * ct + l * 256 * 8]
        opt = h[2 * ct + l * 256 * 8:]
        if opt[:2] == "00":
            return "none"
        return f"{ctx} ; {sj(sints(zs))} ; {rows_of_bits(hex_bits(opt[2:], k * 256), k)}"
    if t == "EXS":
        v = sints(h)
        P = PARAMS[int(f[1])]
        n1 = P["l"] * 256
        return f"{sj(v[:n1])} ; {sj(v[n1:])}"
    if t in ("KG", "KGO", "KGT"):
        P = PARAMS[int(f[1])]
        return f"{h[:2 * P['pk_len']]} ; {h[2 * P['pk_len']:]}"
    if t == "SGN":
        return "none" if h[:2] == "00" else bhex(h[2:])
    if t in ("VER", "VRI"):
        return {"00": "none", "01": "false", "02": "true"}[h[:2]]
    raise ValueError("unknown tag " + t)


# ----------------------------------------------------------------------------- driver

def main():
    chunk, first, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    err = sys.argv[4] if len(sys.argv) > 4 else None
    lines = [ln.rstrip("\n") for ln in open(chunk) if ln.strip()]
    fields = [ln.split(" ") for ln in lines]
    script = [":set base=16"]
    cur = None
    for i, f in enumerate(fields):
        m = module_of(f)
        if m != cur:
            script.append(f":module {m}")
            cur = m
        script.append(f"({first + i} : [32]) # {expr(f)}")
    with tempfile.TemporaryDirectory() as td:
        sp = os.path.join(td, "run.icry")
        with open(sp, "w") as fh:
            fh.write("\n".join(script) + "\n")
        env = dict(os.environ)
        env["CRYPTOLPATH"] = os.path.join(TOOLS, "src/cryptol-specs") + ":" + os.path.join(HERE, "cry")
        env["PATH"] = os.path.join(TOOLS, "cryptol/bin") + ":" + env.get("PATH", "")
        try:
            r = subprocess.run([os.path.join(TOOLS, "cryptol/bin/cryptol"), "-b", sp], env=env, capture_output=True,
                               text=True, timeout=TIMEOUT)
            text = r.stdout + "\n--- stderr ---\n" + r.stderr
        except subprocess.TimeoutExpired as e:
            text = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
            text += "\nTIMEOUT"
    res = {}
    for ln in text.splitlines():
        m = re.fullmatch(r"0x([0-9a-f]{8})([0-9a-f]*)", ln.strip())
        if m:
            res[int(m.group(1), 16)] = m.group(2)
    with open(out, "w") as fh:
        for i, f in enumerate(fields):
            idx = first + i
            if idx in res:
                try:
                    fh.write(decode(f, res[idx]) + "\n")
                except Exception as e:  # malformed payload
                    fh.write(f"CRYPTOL-ERROR decode {e}\n")
            else:
                fh.write("CRYPTOL-ERROR\n")
    if err:
        keep = [ln for ln in text.splitlines()
                if not ln.startswith("Loading") and not re.fullmatch(r"0x[0-9a-f]+", ln.strip())]
        with open(err, "w") as fh:
            fh.write("\n".join(keep) + "\n")


if __name__ == "__main__":
    main()
