#!/usr/bin/env python3
"""Counts the extracted definitions (lean/Impl/Funs.lean) reachable from the verify entry points of the public API, by name
reference, and names any `ntt.*` function among them. Used for the audit in docs/assurance.md section 3 ("every Rust line
reachable from api::verify_* is in an extracted function"): the roots are api.verify_NN, api.verify_internal_NN,
api.verifying_key_NN, api.verify_prepared_NN and api.verify_internal_prepared_NN for NN in 44, 65, 87 (the plain names, which call
the `_with` twins with the CPU-check stub).

Usage: python3 -I scripts/reachable_defs.py [Funs.lean]
"""
import re
import sys
from pathlib import Path

path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent / 'lean/Impl/Funs.lean'
text = path.read_text(encoding='utf-8')
# A top-level declaration starts at a doc comment `/-- [...]:` or at an attribute/def line at column 0.
blocks, names = {}, []
parts = re.split(r'(?m)^(?=/--|@\[|def |divergent def |structure |inductive |abbrev |instance |theorem )', text)
for b in parts:
    m = re.search(r'(?m)^(?:divergent )?(?:def|abbrev|structure|inductive) +([^\s:({\[]+)', b)
    if m:
        blocks.setdefault(m.group(1), '')
        blocks[m.group(1)] += b
        names.append(m.group(1))
known = set(blocks)
ident = re.compile(r"[A-Za-z_][\w.']*")
def deps(n):
    own = n
    out = set()
    for tok in ident.findall(blocks[n]):
        # longest known prefix split on dots (a projection like `x.field` is not a def)
        t = tok
        while t:
            if t in known and t != own:
                out.add(t)
                break
            t = t.rsplit('.', 1)[0] if '.' in t else ''
    return out
roots = [f'api.{op}_{nn}' for op in ('verify', 'verify_internal', 'verifying_key', 'verify_prepared', 'verify_internal_prepared')
         for nn in (44, 65, 87)]
missing = [r for r in roots if r not in known]
if missing:
    print('missing roots:', missing, file=sys.stderr)
    sys.exit(1)
seen, todo = set(roots), list(roots)
while todo:
    for d in deps(todo.pop()):
        if d not in seen:
            seen.add(d); todo.append(d)
ntt = sorted(n for n in seen if n.startswith('ntt.'))
def kind(n):
    m = re.search(r'(?m)^(?:divergent )?(def|abbrev|structure|inductive) +' + re.escape(n) + r'(?![\w.])', blocks[n])
    return m.group(1) if m else '?'
defs = sum(1 for n in seen if kind(n) in ('def', 'abbrev'))
print(f'{len(seen)} extracted declarations reachable from the {len(roots)} verify entry points of api '
      f'({defs} def/abbrev, {len(seen) - defs} types); ntt.* among them: {ntt}')
