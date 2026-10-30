#!/usr/bin/env python3
"""Extract this crate to Lean with Charon + Aeneas (generic, no --monomorphize).

Usage: scripts/extract.py [--src DIR] [--roots FILE] [--work DIR] [--out DIR]
  --src    crate root to extract (Cargo.toml + src/ are copied; default: repo root)
  --roots  extraction roots file (default: scripts/extract-roots.txt)
  --work   scratch directory (default: <repo>/.extract)
  --out    destination for Types.lean/Funs.lean/FunsExternal*.lean/extract-report.json (default: lean/Impl)

Needs the tools from scripts/setup-tools.sh. Exits non-zero on any gate failure; --out is only touched on success.
"""
import argparse, copy, hashlib, json, os, re, shutil, subprocess, sys
from pathlib import Path

repo = Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('--src', default=str(repo))
ap.add_argument('--roots', default=str(repo / 'scripts/extract-roots.txt'))
ap.add_argument('--work', default=str(repo / '.extract'))
ap.add_argument('--out', default=str(repo / 'lean/Impl'))
a = ap.parse_args()
src, work, out = Path(a.src).resolve(), Path(a.work).resolve(), Path(a.out).resolve()

CRATE = 'ml_dsa_verified'
NS = 'Impl'
AENEAS_PIN, CHARON_PIN = 'build-183e4f0', 'nightly-2026.09.02'
T = Path.home() / 'hax-tools'
AENEAS = T / f'cache/hax/tools/aeneas/{AENEAS_PIN}/aeneas'
for tool in [T / 'bin/cargo-hax', AENEAS]:
    if not tool.exists():
        sys.exit(f'missing tool {tool.name}: run scripts/setup-tools.sh')

roots = [l.strip() for l in Path(a.roots).read_text().splitlines() if l.strip() and not l.lstrip().startswith('#')]
failures = []
def fail(msg):
    failures.append(msg); print('GATE FAIL:', msg, file=sys.stderr)

# Every pub fn in api.rs must be a root.
api = src / 'src/api.rs'
if api.exists():
    for fn in re.findall(r'^\s*pub fn (\w+)', api.read_text(), re.M):
        if f'{CRATE}::api::{fn}' not in roots:
            fail(f'pub fn api::{fn} is not listed in the roots file')

if work.exists():
    shutil.rmtree(work)
crate = work / 'crate'
(crate).mkdir(parents=True)
shutil.copytree(src / 'src', crate / 'src')
cargo = (src / 'Cargo.toml').read_text()
cargo = re.sub(r'(?ms)^\[dev-dependencies\]\n.*?(?=^\[|\Z)', '', cargo)  # test-only oracle
(crate / 'Cargo.toml').write_text(cargo)
include = ', '.join(json.dumps(r) for r in roots)
(crate / 'hax.toml').write_text(f'''[tools]
aeneas = "{AENEAS_PIN}"
charon = "{CHARON_PIN}"
[versions]
lean = "leanprover/lean4:v4.31.0"
hax-lean-lib = "v0.3.30"
[scenario.generic]
backend = "lean"
include = [{include}]
no-default-features = false
charon-args = []
env = {{ RUSTFLAGS = "--cfg miri" }}
''')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
src_sha = hashlib.sha256(b''.join(p.read_bytes() for p in sorted((crate / 'src').rglob('*.rs')))).hexdigest()

env = os.environ.copy()
for k in ['RUSTFLAGS', 'CARGO_ENCODED_RUSTFLAGS', 'CARGO_BUILD_RUSTFLAGS', 'CARGO_TARGET_DIR']:
    env.pop(k, None)
env.update(PATH=str(T / 'bin') + os.pathsep + env['PATH'], XDG_CACHE_HOME=str(T / 'cache'),
           CHARON_MIRI_SYSROOTS=str(T / 'charon-sysroot-nightly-2026-08-18'))
with (work / 'hax.log').open('w') as log:
    r = subprocess.run(['cargo', 'hax', 'extract', 'generic', '-v'], cwd=crate, env=env,
                       stdout=log, stderr=subprocess.STDOUT, timeout=3000)
hlog = (work / 'hax.log').read_text()
if r.returncode != 0:
    fail(f'cargo hax extract exited {r.returncode} (see {work}/hax.log)')
    print('\n'.join(hlog.splitlines()[-30:]), file=sys.stderr)
llbc_cands = list(crate.glob('proofs/**/*.llbc'))
record = {'crate': CRATE, 'namespace': NS, 'variant': 'generic (no --monomorphize, no charon args)',
          'roots': roots, 'src_sha256': src_sha,
          'tools': {'aeneas': AENEAS_PIN, 'charon': CHARON_PIN, 'cargo_hax': '0.4.2',
                    'rust': 'nightly-2026-08-18', 'lean': 'v4.31.0'}}
if not llbc_cands:
    fail('no LLBC produced')
else:
    original = json.loads(llbc_cands[0].read_text())
    shutil.copy2(llbc_cands[0], work / 'actual.llbc')
    # Reversible rename of "Instantiated" type names (Aeneas name-clash workaround).
    renames = []
    for d in original['translated']['type_decls']:
        if d and d['item_meta']['name'] and 'Instantiated' in d['item_meta']['name'][-1]:
            old = d['item_meta']['name']
            renames.append((old, old[:-1] + [{'Ident': ['Concrete' + str(d['def_id']), 0]}]))
    changes = []
    def transform(v, path=()):
        if isinstance(v, list):
            for b, af in renames:
                if v == b:
                    changes.append(list(path)); return copy.deepcopy(af)
            return [transform(x, path + (i,)) for i, x in enumerate(v)]
        if isinstance(v, dict):
            return {k: transform(x, path + (k,)) for k, x in v.items()}
        return v
    renamed = transform(original)
    restored = copy.deepcopy(renamed)
    for p in changes:
        b, c = original, restored
        for k in p[:-1]:
            b, c = b[k], c[k]
        c[p[-1]] = copy.deepcopy(b[p[-1]])
    assert restored == original, 'type-rename is not reversible'
    (work / 'renamed.llbc').write_text(json.dumps(renamed, separators=(',', ':')) + '\n')
    record['rename_changes'] = len(changes)

    cmd = [str(AENEAS), '-backend', 'lean', '-split-files', '-namespace', NS, str(work / 'renamed.llbc'),
           '-dest', str(work / 'lean'), '-subdir', NS]
    with (work / 'aeneas.log').open('w') as log:
        ar = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, timeout=1800)
    # Aeneas colors its log levels ("[\x1b[91mError\x1b[39m ]"); strip ANSI escapes before matching.
    alog = re.sub(r'\x1b\[[0-9;]*m', '', (work / 'aeneas.log').read_text())
    alines = alog.splitlines()
    if ar.returncode != 0:
        fail(f'aeneas exited {ar.returncode}')
    errs = [l for l in alines if re.search(r'\[\s*Error\s*\]', l) or 'Internal error' in l or 'Uncaught exception' in l]
    warns = [l for l in alines if re.search(r'\[\s*Warning\s*\]', l) or 'may be incorrect' in l]
    for i, l in enumerate(alines):
        if l in errs or l in warns:
            print('\n'.join(alines[i:i + 12]))
            break
    clashes = [l for l in alog.splitlines() if 'name clash' in l.lower()]
    for kind, lines in [('[Error]', errs), ('[Warning]/may be incorrect', warns), ('Name clash', clashes)]:
        if lines:
            fail(f'{len(lines)} aeneas {kind} line(s); first: {lines[0]}')

    funs = [d for d in original['translated']['fun_decls'] if d]
    def nm(d):
        parts = []
        for c in d['item_meta']['name']:
            if 'Ident' in c: parts.append(c['Ident'][0])
            elif 'Impl' in c: parts.append('{impl}')
            else: parts.append(list(c)[0])
        return '::'.join(parts)
    opaque = sorted({nm(d) for d in funs if d.get('body') in (None, 'Opaque')
                     or (isinstance(d.get('body'), dict) and 'Opaque' in d['body'])})
    local_opaque = [o for o in opaque if o.split('::')[0] == CRATE]
    if local_opaque:
        fail(f'local opaque function(s): {local_opaque}')
    record.update(llbc_fun_decls=len(funs), llbc_opaque_funs=opaque, local_opaque_funs=local_opaque,
                  aeneas_exit_code=ar.returncode, aeneas_errors=len(errs), aeneas_warnings=len(warns),
                  aeneas_name_clashes=len(clashes))

    lean = work / 'lean' / NS
    if not (lean / 'Funs.lean').exists():
        fail('Funs.lean not generated')
    else:
        ext = lean / 'FunsExternal_Template.lean'
        axioms = re.findall(r'^axiom (\S+)', ext.read_text(), re.M) if ext.exists() else []
        funs_txt = (lean / 'Funs.lean').read_text()
        referenced = [x for x in axioms if re.search(r'(?<![\w.])' + re.escape(x) + r'(?![\w])', funs_txt)]
        if referenced:
            fail(f'external axioms referenced from Funs.lean: {referenced}')
        record.update(external_axioms_declared=len(axioms), external_axioms_referenced=len(referenced),
                      lean_defs=len(re.findall(r'^(?:divergent )?def ', funs_txt, re.M)))

# Never commit box-absolute paths.
def scrub(v):
    return re.sub(r'(/home/[^/\s"]+|/Users/[^/\s"]+)', '$HOME', v) if isinstance(v, str) else v
record = json.loads(scrub(json.dumps(record)))
(work / 'extract-report.json').write_text(json.dumps(record, indent=1) + '\n')
print(json.dumps({k: record.get(k) for k in ['aeneas_exit_code', 'llbc_fun_decls', 'lean_defs', 'aeneas_errors',
      'aeneas_warnings', 'aeneas_name_clashes', 'local_opaque_funs', 'external_axioms_referenced']}))
if failures:
    sys.exit(f'extraction FAILED ({len(failures)} gate failure(s)); {out} untouched')
out.mkdir(parents=True, exist_ok=True)
for f in ['Types.lean', 'Funs.lean', 'FunsExternal_Template.lean']:
    s = work / 'lean' / NS / f
    if s.exists():
        shutil.copy2(s, out / f)
# No external axioms are referenced (gated above), so the template is the module Funs.lean imports.
shutil.copy2(out / 'FunsExternal_Template.lean', out / 'FunsExternal.lean')
shutil.copy2(work / 'extract-report.json', out / 'extract-report.json')
print(f'extraction OK -> {out}')
