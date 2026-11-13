"""Shared tables for the Cryptol differential: parameter sets and small codecs (stdlib only)."""

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
