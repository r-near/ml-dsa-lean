#!/usr/bin/env python3
"""Third opinion: plain-Python transcription of FIPS 204 Algorithms 35-40, 41, 42, 45 checked against the
outputs of both evaluators on vec/rounding.txt and vec/ntt.txt.

usage: reference.py RUN_DIR
Prints, per operation, the number of cases and how many differ from the Python reference for ours / theirs.
"""
import os
import sys

Q = 8380417
GAMMA2 = {44: (Q - 1) // 88, 65: (Q - 1) // 32, 87: (Q - 1) // 32}


def modpm(m, alpha):
    r = m % alpha
    return r - alpha if r > alpha // 2 else r


def p2r(r):
    rp = r % Q
    r0 = modpm(rp, 1 << 13)
    return (rp - r0) // (1 << 13), r0


def decompose(S, r):
    g2 = GAMMA2[S]
    rp = r % Q
    r0 = modpm(rp, 2 * g2)
    if rp - r0 == Q - 1:
        return 0, r0 - 1
    return (rp - r0) // (2 * g2), r0


def make_hint(S, z, r):
    return int(decompose(S, r)[0] != decompose(S, (r + z) % Q)[0])


def use_hint(S, h, r):
    m = (Q - 1) // (2 * GAMMA2[S])
    r1, r0 = decompose(S, r)
    if h == 1 and r0 > 0:
        return (r1 + 1) % m
    if h == 1:
        return (r1 - 1) % m
    return r1


def bitrev8(m):
    return int(format(m, "08b")[::-1], 2)


ZETA = [pow(1753, bitrev8(k), Q) for k in range(256)]


def ntt(w):
    w = list(w)
    m, ln = 0, 128
    while ln >= 1:
        start = 0
        while start < 256:
            m += 1
            z = ZETA[m]
            for j in range(start, start + ln):
                t = z * w[j + ln] % Q
                w[j + ln] = (w[j] - t) % Q
                w[j] = (w[j] + t) % Q
            start += 2 * ln
        ln //= 2
    return w


def intt(w):
    w = list(w)
    m, ln = 256, 1
    while ln < 256:
        start = 0
        while start < 256:
            m -= 1
            z = -ZETA[m] % Q
            for j in range(start, start + ln):
                t = w[j]
                w[j] = (t + w[j + ln]) % Q
                w[j + ln] = (t - w[j + ln]) % Q
                w[j + ln] = z * w[j + ln] % Q
            start += 2 * ln
        ln *= 2
    f = pow(256, -1, Q)
    return [f * x % Q for x in w]


def ref_line(line):
    f = line.split(" ")
    t = f[0]
    if t == "P2R":
        a, b = p2r(int(f[1]))
        return f"{a} {b}"
    if t == "DEC":
        S, r = int(f[1]), int(f[2])
        a, b = decompose(S, r)
        return f"D {a} {b} H {a} L {b}"
    if t == "MH":
        return str(make_hint(int(f[1]), int(f[2]), int(f[3])))
    if t == "UH":
        return str(use_hint(int(f[1]), int(f[2]), int(f[3])))
    if t == "NTT":
        return " ".join(map(str, ntt(list(map(int, f[1:])))))
    if t == "INTT":
        return " ".join(map(str, intt(list(map(int, f[1:])))))
    if t == "MUL":
        a, b = list(map(int, f[1:257])), list(map(int, f[257:513]))
        return " ".join(str(x * y % Q) for x, y in zip(a, b))
    return None


def main():
    run = sys.argv[1]
    stats = {}
    for name in ("rounding", "ntt"):
        inp = open(os.path.join(run, "vec", name + ".txt")).read().split("\n")[:-1]
        ours = open(os.path.join(run, "ours", name + ".out")).read().split("\n")[:-1]
        theirs = open(os.path.join(run, "theirs", name + ".out")).read().split("\n")[:-1]
        for l, o, t in zip(inp, ours, theirs):
            ref = ref_line(l)
            if ref is None:
                continue
            tag = l.split(" ")[0]
            s = stats.setdefault(tag, [0, 0, 0])
            s[0] += 1
            s[1] += o != ref
            s[2] += t != ref
    print(f"{'operation':<8}{'cases':>10}{'ours!=ref':>12}{'theirs!=ref':>13}")
    for k, (n, a, b) in stats.items():
        print(f"{k:<8}{n:>10}{a:>12}{b:>13}")
    return 1 if any(a or b for _, a, b in stats.values()) else 0


if __name__ == "__main__":
    sys.exit(main())
