#!/usr/bin/env python3
"""Hashes that bind the shipped Rust (src/) to the committed extraction (lean/Impl).

One definition of each hash, shared by scripts/extract.py (which records them in lean/Impl/extract-report.json) and the
`extract-hash` step of scripts/ci.sh (which checks them on every push and pull request), so the two cannot drift.

Usage: python3 -I scripts/extract_hash.py src-sha256 [CRATE_ROOT]   print the source hash of CRATE_ROOT/src (default: repo)
       python3 -I scripts/extract_hash.py check                     compare the repo against lean/Impl/extract-report.json

`check` fails (exit 1) if
  - src_sha256 in the report differs from the hash of src/*.rs now,
  - the report records no impl_sha256, or the .lean files in lean/Impl are not exactly the recorded set or differ in content,
  - the roots in the report differ from scripts/extract-roots.txt.
It needs no Lean, Charon or Aeneas. It is a consistency check of committed files (someone who edits both lean/Impl and
the report passes it); the `lean.yml` workflow re-runs the extraction and diffs the result, which catches that too.
"""
import hashlib
import json
import sys
from pathlib import Path

# Output file name in lean/Impl -> name of the file Aeneas generates (extract.py copies the template to FunsExternal.lean,
# because no external axiom is referenced).
IMPL_FILES = {
    'Types.lean': 'Types.lean',
    'Funs.lean': 'Funs.lean',
    'FunsExternal_Template.lean': 'FunsExternal_Template.lean',
    'FunsExternal.lean': 'FunsExternal_Template.lean',
}


def file_sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def src_sha256(crate_root):
    """sha256 of the concatenated bytes of every *.rs under CRATE_ROOT/src, in sorted path order."""
    files = sorted((Path(crate_root) / 'src').rglob('*.rs'))
    return hashlib.sha256(b''.join(p.read_bytes() for p in files)).hexdigest()


def generated_sha256s(gen_dir):
    """Hashes of the files Aeneas generated in GEN_DIR, keyed by their name in lean/Impl (missing files are left out)."""
    gen_dir = Path(gen_dir)
    return {out: file_sha256(gen_dir / gen) for out, gen in IMPL_FILES.items() if (gen_dir / gen).exists()}


def read_roots(path):
    return [l.strip() for l in Path(path).read_text().splitlines() if l.strip() and not l.lstrip().startswith('#')]


def check(repo):
    repo = Path(repo)
    report_path = repo / 'lean/Impl/extract-report.json'
    if not report_path.is_file():
        return [f'{report_path} not found']
    report = json.loads(report_path.read_text())
    errors = []
    recorded = report.get('src_sha256')
    actual = src_sha256(repo)
    if recorded != actual:
        errors.append('src/ changed since the last extraction: run scripts/extract.py and commit lean/Impl\n'
                      f'  src/*.rs sha256 now:                 {actual}\n'
                      f'  src_sha256 in extract-report.json:   {recorded}')
    impl = report.get('impl_sha256')
    if not isinstance(impl, dict) or not impl:
        errors.append('extract-report.json records no impl_sha256: run scripts/extract.py and commit lean/Impl')
    else:
        present = {p.name for p in (repo / 'lean/Impl').glob('*.lean')}
        for name in sorted(present - set(impl)):
            errors.append(f'lean/Impl/{name} is not in the extraction report (hand-added file?)')
        for name in sorted(set(impl) - present):
            errors.append(f'lean/Impl/{name} is in the extraction report but missing')
        for name in sorted(present & set(impl)):
            if file_sha256(repo / 'lean/Impl' / name) != impl[name]:
                errors.append(f'lean/Impl/{name} differs from the extraction that was recorded (hand edit?): '
                              'run scripts/extract.py and commit lean/Impl')
    roots = read_roots(repo / 'scripts/extract-roots.txt')
    if report.get('roots') != roots:
        errors.append('scripts/extract-roots.txt differs from the roots in extract-report.json: '
                      'run scripts/extract.py and commit lean/Impl')
    return errors


def main(argv):
    repo = Path(__file__).resolve().parent.parent
    if len(argv) >= 2 and argv[1] == 'src-sha256' and len(argv) <= 3:
        print(src_sha256(argv[2] if len(argv) == 3 else repo))
        return 0
    if len(argv) == 2 and argv[1] == 'check':
        errors = check(repo)
        if errors:
            for e in errors:
                print(f'EXTRACT HASH FAIL: {e}', file=sys.stderr)
            return 1
        print(f'extract hash OK: src/ sha256 {src_sha256(repo)}; '
              f'{len(json.loads((repo / "lean/Impl/extract-report.json").read_text())["impl_sha256"])} lean/Impl files match the report')
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
