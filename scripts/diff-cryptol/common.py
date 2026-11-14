"""Shared tables for the Cryptol differential: parameter sets, small codecs and output stamps (stdlib only)."""
import hashlib
import json
import os

Q = 8380417

PARAMS = {
    44: dict(k=4, l=4, eta=2, tau=39, lam=128, gamma1=2**17, gamma2=(Q - 1) // 88, omega=80),
    65: dict(k=6, l=5, eta=4, tau=49, lam=192, gamma1=2**19, gamma2=(Q - 1) // 32, omega=55),
    87: dict(k=8, l=7, eta=2, tau=60, lam=256, gamma1=2**19, gamma2=(Q - 1) // 32, omega=75),
}
for _s, _p in PARAMS.items():
    _p["beta"] = _p["tau"] * _p["eta"]
    _p["m"] = (Q - 1) // (2 * _p["gamma2"])
    _p["ct_len"] = _p["lam"] // 4
    _p["pk_len"] = 32 + 32 * _p["k"] * 10
    _p["sk_len"] = 128 + 32 * ((_p["k"] + _p["l"]) * (3 if _p["eta"] == 2 else 4) + 13 * _p["k"])
    _p["sig_len"] = _p["ct_len"] + _p["l"] * 32 * (1 + (_p["gamma1"] - 1).bit_length()) + _p["omega"] + _p["k"]

assert (PARAMS[44]["pk_len"], PARAMS[44]["sk_len"], PARAMS[44]["sig_len"]) == (1312, 2560, 2420)
assert (PARAMS[65]["pk_len"], PARAMS[65]["sk_len"], PARAMS[65]["sig_len"]) == (1952, 4032, 3309)
assert (PARAMS[87]["pk_len"], PARAMS[87]["sk_len"], PARAMS[87]["sig_len"]) == (2592, 4896, 4627)


def hx(b):
    """Bytes to the canonical hex field (`-` for the empty string)."""
    return bytes(b).hex() if len(b) else "-"


def unhx(s):
    return b"" if s == "-" else bytes.fromhex(s)


def ints(xs):
    return " ".join(str(x) for x in xs)


def rows_str(rows):
    return " ".join(",".join(map(str, r)) if r else "-" for r in rows)


def parse_rows(s):
    return [[] if f == "-" else [int(x) for x in f.split(",")] for f in s.split(" ")]


# ----------------------------------------------------------------------------- output stamps
# Every output file `<name>.out` of either side has a `<name>.stamp` next to it: a JSON object with the sha256 of the
# vector file the output was computed from (`vec`) and a digest of the program that computed it (`tool`).  A side
# reuses an output only if its stamp matches the current vector file and program, and `compare.py` refuses an output
# whose stamp does not match its vector file, so an output from an earlier seed or an earlier build is never compared.


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for blk in iter(lambda: fh.read(1 << 20), b""):
            h.update(blk)
    return h.hexdigest()


def digest_parts(parts):
    """sha256 over a list of strings (each length-prefixed, so the split is unambiguous)."""
    h = hashlib.sha256()
    for p in parts:
        b = p.encode()
        h.update(len(b).to_bytes(8, "big") + b)
    return h.hexdigest()


def stamp_path(out):
    return (out[:-4] if out.endswith(".out") else out) + ".stamp"


def write_stamp(out, vec, tool):
    sp = stamp_path(out)
    with open(sp + ".tmp", "w") as fh:
        json.dump({"vec": sha256_file(vec), "tool": tool}, fh)
    os.replace(sp + ".tmp", sp)


def read_stamp(out):
    try:
        with open(stamp_path(out)) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return None


def stamp_ok(out, vec, tool=None):
    """True iff `out` exists and its stamp binds it to the current `vec` (and to `tool`, when given)."""
    if not os.path.isfile(out):
        return False
    st = read_stamp(out)
    if not isinstance(st, dict) or st.get("vec") != sha256_file(vec):
        return False
    return tool is None or st.get("tool") == tool
