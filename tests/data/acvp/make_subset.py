#!/usr/bin/env python3
"""Build the vendored ACVP subset from usnistgov/ACVP-Server internalProjection.json files.

Usage: python3 -I make_subset.py <ACVP-Server>/gen-val/json-files <output dir> [cases-per-group]

Every test group is kept (all parameter sets, interfaces, pure/preHash, deterministic/hedged, externalMu).
keyGen is kept whole. sigGen keeps the first N cases per group. sigVer keeps N cases per group, chosen
round-robin over the "reason" values so every failure mode (and the valid case) stays represented; the
unused "sk" field is dropped from sigVer. Output is compact JSON, gzipped with a zeroed mtime.
"""
import gzip, json, os, sys

src, out = sys.argv[1], sys.argv[2]
cap = int(sys.argv[3]) if len(sys.argv) > 3 else 5


def load(mode):
    with open(os.path.join(src, f"ML-DSA-{mode}-FIPS204", "internalProjection.json")) as f:
        return json.load(f)


def pick_sigver(tests):
    by_reason = {}
    for t in tests:
        by_reason.setdefault(t["reason"], []).append(t)
    chosen, i = [], 0
    while len(chosen) < cap and any(by_reason.values()):
        for lst in by_reason.values():
            if lst and len(chosen) < cap:
                chosen.append(lst.pop(0))
        i += 1
    return sorted(chosen, key=lambda t: int(t["tcId"]))


def write(mode, data):
    raw = json.dumps(data, separators=(",", ":")).encode()
    path = os.path.join(out, f"{mode}.json.gz")
    with open(path, "wb") as f:
        with gzip.GzipFile(fileobj=f, mode="wb", mtime=0, compresslevel=9) as z:
            z.write(raw)
    print(mode, len(raw), "->", os.path.getsize(path))


os.makedirs(out, exist_ok=True)
d = load("keyGen")
write("keyGen", d)
d = load("sigGen")
for g in d["testGroups"]:
    g["tests"] = g["tests"][:cap]
write("sigGen", d)
d = load("sigVer")
for g in d["testGroups"]:
    g["tests"] = pick_sigver(g["tests"])
    for t in g["tests"]:
        t.pop("sk", None)
write("sigVer", d)
