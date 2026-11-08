#!/usr/bin/env python3
"""Per-function instruction summary of an asm file: total, ymm, xmm, scalar rotates, loads/stores to stack."""
import re, sys
fn = None
stats = {}
for line in open(sys.argv[1]):
    if re.match(r'^[A-Za-z_$][^ :]*:', line) and not line.startswith('.L'):
        fn = line.split(':')[0]
        stats[fn] = dict(ins=0, ymm=0, xmm=0, rol=0, rorx=0, vrot=0, spill=0, vxor=0, vpsll=0, vpsrl=0, vpand=0, gather=0, shuf=0)
        continue
    if fn is None or not line.startswith('\t') or line.startswith('\t.'):
        continue
    m = line.split()
    op = m[0]
    s = stats[fn]
    s['ins'] += 1
    if 'ymm' in line: s['ymm'] += 1
    if 'xmm' in line: s['xmm'] += 1
    if op.rstrip('qlwb') in ('rol', 'ror', 'shld', 'shrd') or op in ('rolq','rorq','shldq','shrdq'): s['rol'] += 1
    if op.startswith('rorx'): s['rorx'] += 1
    if op in ('vprolq', 'vprorq'): s['vrot'] += 1
    if op == 'vpxor': s['vxor'] += 1
    if op in ('vpsllq', 'vpsllvq'): s['vpsll'] += 1
    if op in ('vpsrlq', 'vpsrlvq'): s['vpsrl'] += 1
    if op.startswith('vpand') : s['vpand'] += 1
    if 'gather' in op: s['gather'] += 1
    if op.startswith(('vpshuf', 'vperm', 'vpunpck', 'vpblend', 'vinserti', 'vextracti')): s['shuf'] += 1
want = sys.argv[2:] 
print(f"{'function':<44}{'ins':>6}{'ymm':>6}{'xmm':>5}{'rol':>5}{'rorx':>5}{'vxor':>6}{'vsll':>6}{'vsrl':>6}{'shuf':>6}")
for k, s in stats.items():
    if 'fvlab' in k and ('1v' in k or '1t' in k or '4rows' in k or '1v' in k) or (want and any(w in k for w in want)):
        name = re.sub(r'^_ZN\d+fvlab1v(\d+)', lambda m: '', k)
        short = re.search(r'(?:1[vt]|4rows)\d+(\w+?)17h', k)
        print(f"{(short.group(1) if short else k):<44}{s['ins']:>6}{s['ymm']:>6}{s['xmm']:>5}{s['rol']:>5}{s['rorx']:>5}{s['vxor']:>6}{s['vpsll']:>6}{s['vpsrl']:>6}{s['shuf']:>6}")
