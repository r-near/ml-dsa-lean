#!/usr/bin/env python3
"""Extract this crate to Lean with Charon + Aeneas (generic, no --monomorphize).

Usage: scripts/extract.py [--src DIR] [--roots FILE] [--work DIR] [--out DIR]
  --src    crate root to extract (Cargo.toml + src/ are copied; default: repo root)
  --roots  extraction roots file (default: scripts/extract-roots.txt)
  --work   directory for logs and intermediate files (default: <repo>/.extract); the crate itself is staged in a fresh
           temporary directory outside the checkout, so no ancestor .cargo/config.toml applies
  --out    destination for Types.lean/Funs.lean/FunsExternal*.lean/extract-report.json (default: lean/Impl)

Records extract_inputs_sha256 (digest of src/, Cargo.toml without dev-dependencies, the roots and the tool pins) and impl_sha256
(hash of each file written to --out) in extract-report.json; the `extract-hash` step of scripts/ci.sh
(scripts/extract_hash.py) fails if either no longer matches the tree. --out must be absent or hold only files this script writes (no
symlinks, no other files): it is not emptied. To compare with the committed directory, extract into a new empty one.

Needs the tools from scripts/setup-tools.sh (ML_DSA_TOOLS overrides their location, default ~/hax-tools). Exits non-zero on any gate failure; --out is only touched on success.
"""
import argparse, copy, json, os, re, shutil, subprocess, sys, tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import extract_hash  # one definition of the hashes recorded in the report; scripts/ci.sh checks them

repo = Path(__file__).resolve().parent.parent
ap = argparse.ArgumentParser()
ap.add_argument('--src', default=str(repo))
ap.add_argument('--roots', default=str(repo / 'scripts/extract-roots.txt'))
ap.add_argument('--work', default=str(repo / '.extract'))
ap.add_argument('--out', default=str(repo / 'lean/Impl'))
a = ap.parse_args()
src, work = Path(a.src).resolve(), Path(a.work).resolve()
out = Path(os.path.abspath(a.out))  # not resolved: a symlinked --out is refused below
out_problems = extract_hash.output_dir_problems(out)
if out_problems:
    sys.exit(f'refusing to extract into {out}: ' + '; '.join(out_problems) + '. Use a new empty directory.')

CRATE = 'ml_dsa_lean'
NS = 'Impl'
AENEAS_PIN, CHARON_PIN = extract_hash.AENEAS_PIN, extract_hash.CHARON_PIN
T = Path(os.environ.get('ML_DSA_TOOLS', str(Path.home() / 'hax-tools')))
AENEAS = T / f'cache/hax/tools/aeneas/{AENEAS_PIN}/aeneas'
for tool in [T / 'bin/cargo-hax', AENEAS]:
    if not tool.exists():
        sys.exit(f'missing tool {tool.name}: run scripts/setup-tools.sh')

roots = extract_hash.read_roots(a.roots)
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
work.mkdir(parents=True)
# Stage exactly the extraction inputs (src/, Cargo.toml without dev-dependencies, hax.toml) with the code scripts/ci.sh
# uses to check the recorded digest; a symlink under src/ is an error. The crate goes into a fresh temporary directory
# outside the checkout so that Cargo does not read a .cargo/config.toml from an ancestor directory.
crate = Path(tempfile.mkdtemp(prefix='ml-dsa-extract-'))
try:
    inputs_sha = extract_hash.stage_crate(src, roots, crate)
except ValueError as e:
    sys.exit(f'cannot stage the extraction inputs: {e}')

# A controlled environment: only these variables are passed on (no RUSTFLAGS, CARGO_* or anything env!/option_env! could
# read), CARGO_HOME is a fresh directory (no cargo-hax shadowing the verified one, no config.toml or registry), and the
# verified cargo-hax is run by absolute path. Not isolated: PATH (the tools it names are looked up there after the pinned
# tool directory), HOME and RUSTUP_HOME (rustup finds the nightly toolchain through them), and the system's C/Rust installation.
PASS_THROUGH = ['HOME', 'USER', 'LOGNAME', 'LANG', 'LC_ALL', 'LC_CTYPE', 'TERM', 'TMPDIR', 'TZ', 'RUSTUP_HOME',
                'SSL_CERT_FILE', 'SSL_CERT_DIR']
env = {k: os.environ[k] for k in PASS_THROUGH if k in os.environ}
env.update(PATH=str(T / 'bin') + os.pathsep + os.environ.get('PATH', ''), XDG_CACHE_HOME=str(T / 'cache'),
           CHARON_MIRI_SYSROOTS=str(T / 'charon-sysroot-nightly-2026-08-18'), CARGO_HOME=str(work / 'cargo-home'))
with (work / 'hax.log').open('w') as log:
    r = subprocess.run([str(T / 'bin/cargo-hax'), 'hax', 'extract', 'generic', '-v'], cwd=crate, env=env,
                       stdout=log, stderr=subprocess.STDOUT, timeout=3000)
hlog = (work / 'hax.log').read_text()
if r.returncode != 0:
    fail(f'cargo hax extract exited {r.returncode} (see {work}/hax.log)')
    print('\n'.join(hlog.splitlines()[-30:]), file=sys.stderr)
llbc_cands = list(crate.glob('proofs/**/*.llbc'))
record = {'crate': CRATE, 'namespace': NS, 'variant': 'generic (no --monomorphize, no charon args)',
          'roots': roots, 'extract_inputs_sha256': inputs_sha,
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
        record['impl_sha256'] = extract_hash.generated_sha256s(lean)
        record.update(external_axioms_declared=len(axioms), external_axioms_referenced=len(referenced),
                      lean_defs=len(re.findall(r'^(?:divergent )?def ', funs_txt, re.M)))

# Never commit machine-specific absolute paths.
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
shutil.rmtree(crate, ignore_errors=True)
print(f'extraction OK -> {out}')
