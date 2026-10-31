#!/usr/bin/env python3
"""Per-function instruction statistics from a rustc --emit asm file: how much of each function is vector code,
and which multiply instructions it uses. Usage: asm-stats.py FILE.s [substring ...]"""
import re, sys, collections

path, pats = sys.argv[1], sys.argv[2:]
funcs = collections.OrderedDict()
cur = None
for line in open(path):
    m = re.match(r'^(_ZN[^:\s]+|[A-Za-z_][\w$.]*):\s*$', line)
    if m and not m.group(1).startswith(('.L', 'LBB')):
        cur = m.group(1)
        funcs[cur] = []
        continue
    if cur and line.startswith('\t') and not line.startswith('\t.'):
        funcs[cur].append(line.strip())

def demangle(s):
    # crude: _ZN8x4_ntt3fold3ntt17h...E -> x4_ntt::fold::ntt
    parts = re.findall(r'(\d+)([A-Za-z_][A-Za-z_0-9$.]*)', s)
    out, rest = [], s[3:]
    i = 0
    while i < len(rest):
        m = re.match(r'(\d+)', rest[i:])
        if not m:
            break
        n = int(m.group(1)); i += len(m.group(1))
        seg = rest[i:i + n]; i += n
        if re.match(r'h[0-9a-f]{16}$', seg):
            break
        out.append(seg)
    return '::'.join(out)

print(f"{'function':52} {'insns':>6} {'ymm':>5} {'xmm':>5} {'vpmuludq':>8} {'vpmuldq':>7} {'vpmulld':>7} {'mulq/mulx':>9} {'imul':>5} {'shuf/perm':>9}")
for name, ins in funcs.items():
    d = demangle(name) if name.startswith('_ZN') else name
    if pats and not any(p in d for p in pats):
        continue
    if not ins:
        continue
    j = ' '.join(ins)
    def c(rx): return len(re.findall(rx, j))
    ymm = sum(1 for i in ins if '%ymm' in i)
    xmm = sum(1 for i in ins if '%xmm' in i and '%ymm' not in i)
    print(f"{d[:52]:52} {len(ins):6} {ymm:5} {xmm:5} {c(r'vpmuludq'):8} {c(r'vpmuldq'):7} {c(r'vpmulld'):7} "
          f"{c(r'(?<![a-z])(mulq|mulxq|mull)'):9} {c(r'imul[lq]'):5} {c(r'(vpshufd|vpermq|vpermd|vpblendd|vpunpck|vpshufb|vperm2i128)'):9}")
