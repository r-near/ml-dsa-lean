#!/usr/bin/env python3
"""Hashes that bind the shipped Rust (src/) to the committed extraction (lean/Impl).

One definition of each hash, shared by scripts/extract.py (which records them in lean/Impl/extract-report.json) and the
`extract-hash` step of scripts/ci.sh (which checks them on every push and pull request), so the two cannot drift. The
extraction inputs are staged by the same function (stage_crate) in both, so the producer and the consumer hash the same
bytes.

Usage: python3 -I scripts/extract_hash.py check                     compare the repo against lean/Impl/extract-report.json
       python3 -I scripts/extract_hash.py inputs-sha256             print the digest of the extraction inputs of this repo
       python3 -I scripts/extract_hash.py tree-sha256 DIR           print a digest of every file in DIR (paths, contents,
                                                                    execute bits; fails on a symlink); setup-tools.sh uses it

extract_inputs_sha256 is the sha256 of a manifest with one line per file of the staged crate, `sha256  relative/path`,
sorted by path. The staged crate is what Charon sees: every file under src/ (any extension, since include_str! and the
like can read them), Cargo.toml without its [dev-dependencies] section, and the generated hax.toml (which carries the
extraction roots and the Charon and Aeneas pins). A symlink or other special file under src/ is an error.

`check` fails (exit 1) if
  - the digest of the extraction inputs now differs from the one in the report,
  - the report records no impl_sha256, or lean/Impl is not exactly the recorded set of files (recursive; any other file,
    in any subdirectory, is an error) with the recorded contents,
  - there is a symlink or special file anywhere in lean/Impl, or lean, lean/Impl or src is itself a symlink,
  - the roots in the report differ from scripts/extract-roots.txt.
It needs no Lean, Charon or Aeneas. It is a consistency check of committed files (someone who edits both lean/Impl and
the report passes it); the `lean.yml` workflow extracts into an empty directory and compares every file of the result
with lean/Impl, which catches that too.
"""
import hashlib
import json
import os
import re
import shutil
import sys
import tempfile
from pathlib import Path

# Output file name in lean/Impl -> name of the file Aeneas generates (extract.py copies the template to FunsExternal.lean,
# because no external axiom is referenced).
IMPL_FILES = {
    'Types.lean': 'Types.lean',
    'Funs.lean': 'Funs.lean',
    'FunsExternal_Template.lean': 'FunsExternal_Template.lean',
    'FunsExternal.lean': 'FunsExternal_Template.lean',
}
REPORT = 'extract-report.json'

# Pins that go into hax.toml (and so into the digest of the extraction inputs).
AENEAS_PIN, CHARON_PIN = 'build-183e4f0', 'nightly-2026.09.02'
LEAN_PIN, HAX_LEAN_LIB_PIN = 'leanprover/lean4:v4.31.0', 'v0.3.30'


def file_sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def walk_files(root):
    """(files, problems): every regular file under ROOT as {posix relative path: Path}, not following symlinks.
    Symlinks (to files or directories) and other special files are reported in problems, not followed."""
    root = Path(root)
    files, problems = {}, []
    if root.is_symlink():
        return files, [f'{root} is a symlink']
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        for name in list(dirnames):
            p = Path(dirpath) / name
            if p.is_symlink():
                problems.append(f'{p.relative_to(root).as_posix()} is a symlink')
                dirnames.remove(name)
        for name in filenames:
            p = Path(dirpath) / name
            rel = p.relative_to(root).as_posix()
            if p.is_symlink():
                problems.append(f'{rel} is a symlink')
            elif not p.is_file():
                problems.append(f'{rel} is not a regular file')
            else:
                files[rel] = p
    return files, problems


def manifest_sha256(files):
    """sha256 of the manifest of FILES ({relative path: Path}): `sha256  path` lines sorted by path."""
    text = ''.join(f'{file_sha256(files[rel])}  {rel}\n' for rel in sorted(files))
    return hashlib.sha256(text.encode()).hexdigest()


def tree_sha256(root):
    """Digest of every file under ROOT: path, execute bit and content. Raises ValueError on a symlink or special file."""
    files, problems = walk_files(root)
    if problems:
        raise ValueError('; '.join(problems))
    text = ''.join(f"{file_sha256(files[rel])} {'x' if os.access(files[rel], os.X_OK) else '-'} {rel}\n"
                   for rel in sorted(files))
    return hashlib.sha256(text.encode()).hexdigest()


def read_roots(path):
    return [l.strip() for l in Path(path).read_text().splitlines() if l.strip() and not l.lstrip().startswith('#')]


def hax_toml(roots):
    include = ', '.join(json.dumps(r) for r in roots)
    return f'''[tools]
aeneas = "{AENEAS_PIN}"
charon = "{CHARON_PIN}"
[versions]
lean = "{LEAN_PIN}"
hax-lean-lib = "{HAX_LEAN_LIB_PIN}"
[scenario.generic]
backend = "lean"
include = [{include}]
no-default-features = true
charon-args = []
env = {{ RUSTFLAGS = "--cfg miri" }}
'''


def stage_crate(repo, roots, dest):
    """Write the extraction inputs of the crate at REPO into the new directory DEST: src/ (regular files only),
    Cargo.toml without [dev-dependencies] (a test-only oracle), and hax.toml. Returns the digest of what was written.
    Raises ValueError if src/ contains a symlink or special file or is missing."""
    repo, dest = Path(repo), Path(dest)
    src_files, problems = walk_files(repo / 'src')
    if problems:
        raise ValueError('src/: ' + '; '.join(problems))
    if not src_files:
        raise ValueError('src/ has no files')
    for rel, p in src_files.items():
        (dest / 'src' / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, dest / 'src' / rel)
    if (repo / 'Cargo.toml').is_symlink():
        raise ValueError('Cargo.toml is a symlink')
    cargo = (repo / 'Cargo.toml').read_text()
    cargo = re.sub(r'(?ms)^\[dev-dependencies\]\n.*?(?=^\[|\Z)', '', cargo)
    (dest / 'Cargo.toml').write_text(cargo)
    (dest / 'hax.toml').write_text(hax_toml(roots))
    return inputs_sha256(dest)


def inputs_sha256(crate_dir):
    """Digest of the staged crate in CRATE_DIR (src/**, Cargo.toml, hax.toml only)."""
    files, problems = walk_files(crate_dir)
    if problems:
        raise ValueError('; '.join(problems))
    return manifest_sha256({r: p for r, p in files.items() if r.startswith('src/') or r in ('Cargo.toml', 'hax.toml')})


def generated_sha256s(gen_dir):
    """Hashes of the files Aeneas generated in GEN_DIR, keyed by their name in lean/Impl (missing files are left out)."""
    gen_dir = Path(gen_dir)
    return {out: file_sha256(gen_dir / gen) for out, gen in IMPL_FILES.items() if (gen_dir / gen).exists()}


def repo_inputs_sha256(repo):
    repo = Path(repo)
    with tempfile.TemporaryDirectory() as tmp:
        return stage_crate(repo, read_roots(repo / 'scripts/extract-roots.txt'), Path(tmp) / 'crate')


def check(repo):
    repo = Path(repo)
    report_path = repo / 'lean/Impl' / REPORT
    for d in ('lean', 'lean/Impl', 'src'):
        if (repo / d).is_symlink():
            return [f'{d} is a symlink']
    if not report_path.is_file():
        return [f'{report_path} not found']
    report = json.loads(report_path.read_text())
    errors = []
    recorded = report.get('extract_inputs_sha256')
    try:
        actual = repo_inputs_sha256(repo)
    except ValueError as e:
        actual = None
        errors.append(f'extraction inputs: {e}')
    if actual is not None and recorded != actual:
        errors.append('the extraction inputs (src/, Cargo.toml, roots, tool pins) changed since the last extraction: '
                      'run scripts/extract.py and commit lean/Impl\n'
                      f'  digest now:                                 {actual}\n'
                      f'  extract_inputs_sha256 in extract-report.json: {recorded}')
    impl = report.get('impl_sha256')
    present, problems = walk_files(repo / 'lean/Impl')
    present.pop(REPORT, None)
    errors += [f'lean/Impl/{p}' for p in problems]
    if not isinstance(impl, dict) or not impl:
        errors.append('extract-report.json records no impl_sha256: run scripts/extract.py and commit lean/Impl')
    else:
        for name in sorted(set(present) - set(impl)):
            errors.append(f'lean/Impl/{name} is not in the extraction report (hand-added file?)')
        for name in sorted(set(impl) - set(present)):
            errors.append(f'lean/Impl/{name} is in the extraction report but missing')
        for name in sorted(set(present) & set(impl)):
            if file_sha256(present[name]) != impl[name]:
                errors.append(f'lean/Impl/{name} differs from the extraction that was recorded (hand edit?): '
                              'run scripts/extract.py and commit lean/Impl')
    if report.get('roots') != read_roots(repo / 'scripts/extract-roots.txt'):
        errors.append('scripts/extract-roots.txt differs from the roots in extract-report.json: '
                      'run scripts/extract.py and commit lean/Impl')
    return errors


def main(argv):
    repo = Path(__file__).resolve().parent.parent
    if len(argv) == 2 and argv[1] == 'inputs-sha256':
        try:
            print(repo_inputs_sha256(repo))
        except ValueError as e:
            print(f'EXTRACT HASH FAIL: extraction inputs: {e}', file=sys.stderr)
            return 1
        return 0
    if len(argv) == 3 and argv[1] == 'tree-sha256':
        try:
            print(tree_sha256(argv[2]))
        except (ValueError, OSError) as e:
            print(f'tree-sha256: {e}', file=sys.stderr)
            return 1
        return 0
    if len(argv) == 2 and argv[1] == 'check':
        errors = check(repo)
        if errors:
            for e in errors:
                print(f'EXTRACT HASH FAIL: {e}', file=sys.stderr)
            return 1
        report = json.loads((repo / 'lean/Impl' / REPORT).read_text())
        print(f'extract hash OK: extraction inputs sha256 {report["extract_inputs_sha256"]}; '
              f'{len(report["impl_sha256"])} lean/Impl files match the report')
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
