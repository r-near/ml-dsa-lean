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
like can read them), Cargo.toml without its [dev-dependencies] section and with the `[package]` version replaced by the
placeholder `0.0.0`, and the generated hax.toml (which carries the extraction roots and the Charon and Aeneas pins). A
symlink or other special file under src/ is an error.

The version is normalized so that a release (release-plz bumps `version` in Cargo.toml) does not move the digest or
force a re-extraction: the version string cannot change the extracted code (src/ cannot read it, since env! is refused
below), and the staged crate Charon sees carries the same placeholder. Only the single `version = "..."` key of the
`[package]` table is replaced; `rust-version`, dependency versions and every other line are digested as they are. A
Cargo.toml without exactly one such line is an error.

`check` fails (exit 1) if
  - the digest of the extraction inputs now differs from the one in the report,
  - the report records no impl_sha256, or lean/Impl is not exactly the recorded set of files (recursive; any other file,
    in any subdirectory, is an error) with the recorded contents,
  - there is a symlink or special file anywhere in lean/Impl, or lean, lean/Impl or src is itself a symlink,
  - the roots in the report differ from scripts/extract-roots.txt.
It needs no Lean, Charon or Aeneas. It is a consistency check of committed files (someone who edits both lean/Impl and
the report passes it); the `lean.yml` workflow extracts into an empty directory and compares every file of the result
with lean/Impl, which catches that too.

Unsupported inputs. The verified subset is a plain library crate, so extraction refuses (and `check` fails on) anything
that would change the shipped build without changing the staged crate: a build script (build.rs, or `build =` or
`links =` in Cargo.toml), env!/option_env!/include!/include_str!/include_bytes! in src/, a `.cargo` directory or a
rust-toolchain file at the repository root, and file names with control characters or invalid UTF-8 (they would make
the manifests ambiguous). If the crate ever needs one of these, add the files it reads to the manifest instead.

Threat model. These checks are meant to catch accidental drift between src/ and lean/Impl, and tampering that is hidden
inside generated or cached files (a hand-edited lean/Impl file, a symlinked or extra file, a modified tool directory).
They cannot stop anyone who can change the workflows or scripts in a commit from disabling them: that is what code review
of .github/ and scripts/ is for, not CI.
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

# Macros that read inputs from outside the staged crate (the environment or other files).
MACROS = re.compile(r'\b(?:env|option_env|include|include_str|include_bytes)\s*!')

# Pins that go into hax.toml (and so into the digest of the extraction inputs).
AENEAS_PIN, CHARON_PIN = 'build-183e4f0', 'nightly-2026.09.02'
LEAN_PIN, HAX_LEAN_LIB_PIN = 'leanprover/lean4:v4.31.0', 'v0.3.30'


def file_sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def bad_name(name):
    """True if NAME has a control character or is not valid UTF-8 (the manifests are line based)."""
    try:
        name.encode('utf-8')
    except UnicodeEncodeError:
        return True
    return any(ord(c) < 32 or ord(c) == 127 for c in name)


def walk_files(root):
    """(files, problems): every regular file under ROOT as {posix relative path: Path}, not following symlinks.
    Symlinks (to files or directories), special files and names with control characters or invalid UTF-8 are reported in
    problems, not followed."""
    root = Path(root)
    files, problems = {}, []
    if root.is_symlink():
        return files, [f'{root} is a symlink']
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        for name in list(dirnames):
            p = Path(dirpath) / name
            if bad_name(name):
                problems.append(f'{p.relative_to(root).as_posix()!a} has a control character or invalid UTF-8 in its name')
                dirnames.remove(name)
            elif p.is_symlink():
                problems.append(f'{p.relative_to(root).as_posix()} is a symlink')
                dirnames.remove(name)
        for name in filenames:
            p = Path(dirpath) / name
            rel = p.relative_to(root).as_posix()
            if bad_name(name):
                problems.append(f'{rel!a} has a control character or invalid UTF-8 in its name')
            elif p.is_symlink():
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


PACKAGE_TABLE = re.compile(r'(?ms)^\[package\]\n.*?(?=^\[|\Z)')
PACKAGE_VERSION = re.compile(r'(?m)^version[ \t]*=[ \t]*"[^"\n]*"[ \t]*$')
VERSION_PLACEHOLDER = '0.0.0'


def normalize_version(cargo_text):
    """CARGO_TEXT with the `version = "..."` line of the `[package]` table replaced by `version = "0.0.0"`, so a release
    bump does not change the staged Cargo.toml. Only that one key is touched (`rust-version`, dependency versions and
    everything else stay). Raises ValueError unless the file has exactly one [package] table with exactly one such line."""
    tables = PACKAGE_TABLE.findall(cargo_text)
    if len(tables) != 1:
        raise ValueError(f'Cargo.toml has {len(tables)} [package] tables, expected 1')
    table = tables[0]
    if len(PACKAGE_VERSION.findall(table)) != 1:
        raise ValueError('the [package] table of Cargo.toml needs exactly one `version = "..."` line')
    return cargo_text.replace(table, PACKAGE_VERSION.sub(f'version = "{VERSION_PLACEHOLDER}"', table), 1)


def stage_crate(repo, roots, dest):
    """Write the extraction inputs of the crate at REPO into the new directory DEST: src/ (regular files only),
    Cargo.toml without [dev-dependencies] (a test-only oracle) and with the package version normalized to 0.0.0, and
    hax.toml. Returns the digest of what was written.
    Raises ValueError if src/ contains a symlink or special file or is missing."""
    repo, dest = Path(repo), Path(dest)
    src_files, problems = walk_files(repo / 'src')
    if problems:
        raise ValueError('src/: ' + '; '.join(problems))
    if not src_files:
        raise ValueError('src/ has no files')
    cargo_text = (repo / 'Cargo.toml').read_text()
    if (repo / 'build.rs').exists() or re.search(r'(?m)^\s*(build|links)\s*=', cargo_text):
        raise ValueError('a build script (build.rs, `build =` or `links =` in Cargo.toml) is not supported: '
                         'it changes the shipped build but is not extracted')
    for rel, p in src_files.items():
        m = MACROS.search(p.read_bytes().decode('utf-8', 'replace')) if rel.endswith('.rs') else None
        if m:
            raise ValueError(f'src/{rel} uses {m.group(0)}, which reads inputs from outside the staged crate')
    for rel, p in src_files.items():
        (dest / 'src' / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(p, dest / 'src' / rel)
    if (repo / 'Cargo.toml').is_symlink():
        raise ValueError('Cargo.toml is a symlink')
    cargo = cargo_text
    cargo = re.sub(r'(?ms)^\[dev-dependencies\]\n.*?(?=^\[|\Z)', '', cargo)
    cargo = normalize_version(cargo)
    (dest / 'Cargo.toml').write_text(cargo)
    (dest / 'hax.toml').write_text(hax_toml(roots))
    return inputs_sha256(dest)


def inputs_sha256(crate_dir):
    """Digest of the staged crate in CRATE_DIR (src/**, Cargo.toml, hax.toml only)."""
    files, problems = walk_files(crate_dir)
    if problems:
        raise ValueError('; '.join(problems))
    return manifest_sha256({r: p for r, p in files.items() if r.startswith('src/') or r in ('Cargo.toml', 'hax.toml')})


def output_dir_problems(out):
    """Reasons not to extract into OUT: it is a symlink, or it holds a symlink, a special file or any file that is not
    one of the files extraction writes (a stale file would survive and the result would not be the extraction)."""
    out = Path(out)
    if out.is_symlink():
        return [f'{out} is a symlink']
    if not out.exists():
        return []
    files, problems = walk_files(out)
    return problems + [f'{rel} is not a file extraction writes' for rel in sorted(set(files) - set(IMPL_FILES) - {REPORT})]


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
    errors = []
    # Cargo builds the crate from the repository root, so only a root-level config or toolchain file applies (the
    # subprojects checkct/, tools/ and fuzz/ have their own).
    for name, why in (('.cargo', 'a .cargo directory'), ('rust-toolchain', 'a toolchain override'),
                      ('rust-toolchain.toml', 'a toolchain override')):
        if (repo / name).exists() or (repo / name).is_symlink():
            errors.append(f'{name}: {why} changes the shipped build but is not part of the extraction inputs')
    report = json.loads(report_path.read_text())
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
