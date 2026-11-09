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
Cargo.toml without exactly one such line is an error, and so is one where, parsed as TOML, the normalized file differs
from the original in anything but package.version (the same parse check guards the [dev-dependencies] removal). `check`
first runs a self-test of both against manifests they must reject.

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
import tomllib
from pathlib import Path

# Output file name in lean/Impl -> name of the file Aeneas generates (extract.py copies the cleaned template to
# FunsExternal.lean, because no external axiom is referenced). The two FunsExternal files are not byte copies of what Aeneas
# wrote: clean_external removes the unreferenced `axiom` declarations first (see there), so their recorded hashes are those of
# the cleaned text.
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


# One `axiom` declaration of Aeneas's external-functions template: an optional doc comment, an optional attribute line,
# and the `axiom` line with its continuation lines, up to the next blank line.
_AXIOM_BLOCK = re.compile(r'(?:/--(?:(?!-/).)*?-/\n)?(?:@\[[^\n]*\]\n)?axiom [^\n]*\n(?:[ \t][^\n]*\n)*', re.S)


# An axiom or opaque declaration at the start of a line, with any modifiers.
_DECL = re.compile(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*(?:axiom|opaque)\b')


def clean_external(text, referenced=()):
    """TEXT, the external-functions template Aeneas generated, without its `axiom` declarations. Aeneas declares one axiom per
    external function it knows a name pattern for, whether or not the extracted code uses it; the policy is that lean/Impl
    declares no axiom, so extraction removes them (and fails first if Funs.lean refers to one: REFERENCED names those).
    Deterministic: the header and `open` lines are untouched, and each axiom block (its doc comment and attribute line
    included) is dropped. Raises ValueError if REFERENCED is non-empty, or if an `axiom` is left over because it does not have
    the shape the pattern expects (never silently keep or half-remove one)."""
    if referenced:
        raise ValueError(f'external axioms referenced from Funs.lean: {sorted(referenced)}')
    out = []
    for chunk in text.split('\n\n'):
        body = chunk if chunk.endswith('\n') else chunk + '\n'
        if _DECL.search(body):
            if not _AXIOM_BLOCK.fullmatch(body):
                raise ValueError(f'an external axiom block has an unexpected shape: {chunk[:200]!r}')
            continue
        out.append(chunk)
    result = '\n\n'.join(out)
    result = result.rstrip('\n') + '\n'
    if _DECL.search(result):
        raise ValueError('an axiom or opaque declaration is left in the external-functions file after cleaning')
    return result


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


def hax_toml(roots, features=('avx2',)):
    """The hax.toml of the extraction. FEATURES is the cargo feature list the crate is extracted with: `('avx2',)` for the
    extraction that lean/Impl and the proofs are built from, `()` for the second, feature-independence extraction
    (scripts/check-feature-independence.sh), which scripts/extract.py runs with --features ''. Only the first is digested
    into extract_inputs_sha256 of the report."""
    include = ', '.join(json.dumps(r) for r in roots)
    feats = ', '.join(json.dumps(f) for f in features)
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
features = [{feats}]
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
    result = cargo_text.replace(table, PACKAGE_VERSION.sub(f'version = "{VERSION_PLACEHOLDER}"', table), 1)
    # The regexes above are line-based; TOML is not (indented headers, single-quoted or multiline strings, ...). Parse
    # both sides and require that the only change is package.version becoming the placeholder, so a layout the regexes
    # misread can never hide another value (say, a dependency requirement) from the digest.
    before, after = parse_toml(cargo_text), parse_toml(result)
    package = before.get('package')
    if not isinstance(package, dict) or not isinstance(package.get('version'), str):
        raise ValueError('Cargo.toml has no string package.version')
    expected = {**before, 'package': {**package, 'version': VERSION_PLACEHOLDER}}
    if after != expected:
        raise ValueError('normalizing the package version of Cargo.toml changed something else; '
                         'use one plain `version = "..."` line in [package]')
    return result


def parse_toml(text):
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as e:
        raise ValueError(f'Cargo.toml is not valid TOML: {e}') from None


def strip_dev_dependencies(cargo_text):
    """CARGO_TEXT without its [dev-dependencies] table. Raises ValueError unless, parsed, that is the only change."""
    result = re.sub(r'(?ms)^\[dev-dependencies\]\n.*?(?=^\[|\Z)', '', cargo_text)
    expected = {k: v for k, v in parse_toml(cargo_text).items() if k != 'dev-dependencies'}
    if parse_toml(result) != expected:
        raise ValueError('removing [dev-dependencies] from Cargo.toml changed something else; '
                         'keep it one plain [dev-dependencies] table')
    return result


# Manifests the Cargo.toml normalization must reject (each would let it hide or rewrite a value other than the package
# version) and one it must accept unchanged except for the version. `check` runs these first, so a regression in
# normalize_version or strip_dev_dependencies fails CI.
_REJECT = {
    'indented dependency header after a single-quoted package version':
        "[package]\nname = \"s\"\nversion = '0.1.0'\n [dependencies.z]\nversion = \"1\"\n",
    'version under an indented [package.metadata] table':
        '[package]\nname = "s"\nversion = "0.1.0"\n  [package.metadata.x]\nversion = "9"\n',
    'version = line inside a multiline string':
        '[package]\nname = "s"\ndescription = """\nversion = "1"\n"""\nversion = "0.1.0"\n',
    'indented dependency header inside [dev-dependencies]':
        '[package]\nname = "s"\nversion = "0.1.0"\n[dev-dependencies]\na = "1"\n [dependencies.z]\nversion = "1"\n',
}
_ACCEPT = ('[package]\nname = "s"\nversion = "0.1.0"\nrust-version = "1.86"\n\n[dependencies]\nz = { version = "1" }\n'
           '\n[dev-dependencies]\na = "1"\n',
           '[package]\nname = "s"\nversion = "0.0.0"\nrust-version = "1.86"\n\n[dependencies]\nz = { version = "1" }\n\n')


_EXT_HEADER = '-- header\nimport Aeneas\nopen Impl\n\n'
_EXT_AXIOM = ('/-- [core::iter::range::Step::forward]:\n    Source: \'x.rs\'\n    Visibility: public -/\n'
              '@[trait_default, rust_fun "core::iter::range::Step::forward"]\naxiom core.iter.range.Step.forward.default\n'
              '  {Self : Type} (StepInst : core.iter.range.Step Self) :\n  Self → Std.Usize → RustM Self\n')


def clean_external_selftest():
    """Errors if clean_external keeps an axiom, keeps anything else out, accepts a referenced axiom or an axiom of an
    unexpected shape, or if the production path (impl_texts, which runs discovery and cleaning together) does not fail on a
    reference spelled plainly, `_root_.`-qualified, `Impl.`-qualified or with «»-escaped components, in Funs.lean or in
    Types.lean, and does not pass when nothing references the axioms."""
    import tempfile
    errors = []
    want = _EXT_HEADER.rstrip('\n') + '\n'
    for text in (_EXT_HEADER + _EXT_AXIOM, _EXT_HEADER + _EXT_AXIOM + '\n' + _EXT_AXIOM.replace('forward', 'backward'), _EXT_HEADER):
        try:
            if clean_external(text) != want:
                errors.append('clean_external self-test: wrong output')
        except ValueError as e:
            errors.append(f'clean_external self-test: rejected a template: {e}')
    try:
        clean_external(_EXT_HEADER + _EXT_AXIOM, ['core.iter.range.Step.forward.default'])
        errors.append('clean_external self-test: accepted a referenced axiom')
    except ValueError:
        pass
    for odd in (_EXT_HEADER + 'axiom a : Type\n  -- trailing\nstuff\n', _EXT_HEADER + 'private axiom a : Type\n'):
        try:
            clean_external(odd)
            errors.append(f'clean_external self-test: accepted an unexpected axiom shape {odd!r}')
        except ValueError:
            pass
    name = 'core.iter.range.Step.forward.default'
    uses = {
        'plain': name,
        '_root_-qualified': '_root_.' + name,
        'Impl-qualified': 'Impl.' + name,
        'escaped': 'core.iter.\u00abrange\u00bb.Step.forward.default',
        'escaped and _root_-qualified': '_root_.core.\u00abiter\u00bb.range.\u00abStep\u00bb.forward.default',
        'used after an open (suffix)': 'Step.forward.default',
    }
    def tree(tmp, funs_use=None, types_use=None):
        (tmp / 'Types.lean').write_text('import Aeneas\nnamespace Impl\n' + (f'def T := {types_use}\n' if types_use else '') + 'end Impl\n')
        (tmp / 'Funs.lean').write_text('import Aeneas\nnamespace Impl\n' + (f'def f := {funs_use} x\n' if funs_use else 'def f := 1\n') + 'end Impl\n')
        (tmp / 'FunsExternal_Template.lean').write_text(_EXT_HEADER + _EXT_AXIOM)
    with tempfile.TemporaryDirectory() as d:
        tmp = Path(d)
        tree(tmp)
        try:
            if impl_texts(tmp)['FunsExternal.lean'] != want:
                errors.append('impl_texts self-test: wrong cleaned output for an unreferenced axiom')
        except ValueError as e:
            errors.append(f'impl_texts self-test: rejected an unreferenced axiom: {e}')
        # A comment or a string that mentions the name is not a use.
        tree(tmp, funs_use=None)
        (tmp / 'Funs.lean').write_text('namespace Impl\n/-- ' + name + ' -/\n-- ' + name + '\ndef f := "' + name + '"\nend Impl\n')
        try:
            impl_texts(tmp)
        except ValueError as e:
            errors.append(f'impl_texts self-test: a comment or string was taken for a reference: {e}')
        for label, spelling in uses.items():
            for where in ('funs', 'types'):
                tree(tmp, funs_use=spelling if where == 'funs' else None, types_use=spelling if where == 'types' else None)
                try:
                    impl_texts(tmp)
                    errors.append(f'impl_texts self-test: a {label} reference in {where} was not detected')
                except ValueError as e:
                    if name not in str(e):
                        errors.append(f'impl_texts self-test: wrong error for a {label} reference in {where}: {e}')
    return errors


def normalizer_selftest():
    """Errors (a list of strings) if the Cargo.toml normalization accepts a manifest it must reject or mangles one, or if
    clean_external misbehaves."""
    errors = clean_external_selftest()
    for name, text in _REJECT.items():
        try:
            normalize_version(strip_dev_dependencies(text))
            errors.append(f'Cargo.toml normalization self-test: accepted {name}')
        except ValueError:
            pass
    try:
        if normalize_version(strip_dev_dependencies(_ACCEPT[0])) != _ACCEPT[1]:
            errors.append('Cargo.toml normalization self-test: wrong output for a plain manifest')
    except ValueError as e:
        errors.append(f'Cargo.toml normalization self-test: rejected a plain manifest: {e}')
    return errors


def stage_crate(repo, roots, dest, features=('avx2',)):
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
    cargo = strip_dev_dependencies(cargo)
    cargo = normalize_version(cargo)
    (dest / 'Cargo.toml').write_text(cargo)
    (dest / 'hax.toml').write_text(hax_toml(roots, features))
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


_AXIOM_NAME = re.compile(r'(?m)^[ \t]*(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*axiom[ \t]+(\S+)')
_IDENT = re.compile(r"[A-Za-z_\u00C0-\uFFFF][\w.'\u00C0-\uFFFF]*")


def axiom_names(template_text):
    """The names of the `axiom` declarations in the external-functions template text."""
    return [m.group(1).replace('\u00ab', '').replace('\u00bb', '') for m in _AXIOM_NAME.finditer(template_text)]


def _reference_tokens(text):
    """The identifier tokens of Lean TEXT as a set, comment-free and with the escaping removed: «x» becomes x, and the
    `_root_.` and `Impl.` prefixes are dropped, so `_root_.core.iter.range.Step.forward.default`, `Impl.core.iter.«range».Step`
    and the plain name are the same token. (referenced_axioms also matches a dotted token that is a proper suffix of an
    axiom name, a use after an `open`; a single component never matches.)"""
    # Comments cannot reference anything (they are removed by the Lean parser); strings are not names.
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    text = re.sub(r'(?m)--.*$', ' ', text)
    text = re.sub(r'"(?:\\.|[^"\\])*"', ' ', text)
    text = text.replace('\u00ab', '').replace('\u00bb', '')
    toks = set()
    for m in _IDENT.finditer(text):
        tok = m.group(0).rstrip('.')
        for prefix in ('_root_.', 'Impl.'):
            while tok.startswith(prefix):
                tok = tok[len(prefix):]
        toks.add(tok)
    return toks


def referenced_axioms(gen_dir):
    """The axioms declared in the external-functions template of GEN_DIR that any generated file refers to, sorted. Scans
    every file Aeneas generated (Types.lean, Funs.lean, and the template with the axiom declarations themselves removed), by
    identifier token after normalizing the qualified (`_root_.`, `Impl.`) and escaped (`«x»`) spellings, so a use that is
    qualified differently from the declaration is still found. It reports a name that merely shares its last components with a
    used one; that is a reason to look, not a silent pass.

    This detector is a safeguard, not the safety argument. An axiom that is referenced but removed makes Funs.lean fail to
    elaborate (unknown identifier), so the Lean build catches a miss here; the point of failing early is a precise message
    and a policy that lean/Impl never carries an axiom a function depends on."""
    gen_dir = Path(gen_dir)
    template = gen_dir / 'FunsExternal_Template.lean'
    if not template.exists():
        return []
    ttext = template.read_text(encoding='utf-8')
    names = axiom_names(ttext)
    rest = _AXIOM_BLOCK.sub('', ttext)
    corpus = [rest]
    for name in ('Types.lean', 'Funs.lean'):
        if (gen_dir / name).exists():
            corpus.append((gen_dir / name).read_text(encoding='utf-8'))
    toks = set()
    for c in corpus:
        toks |= _reference_tokens(c)
    dotted = [x for x in toks if '.' in x]
    return sorted(n for n in names if n in toks or any(n.endswith('.' + x) for x in dotted))


def impl_texts(gen_dir):
    """What extraction writes to lean/Impl, keyed by the name in lean/Impl: the files Aeneas generated in GEN_DIR, with the
    external-functions template cleaned by clean_external (missing files are left out). Discovers the referenced axioms
    itself (referenced_axioms) and passes them to clean_external, so cleaning cannot be asked to ignore a reference.
    Raises ValueError as clean_external."""
    gen_dir = Path(gen_dir)
    referenced = referenced_axioms(gen_dir)
    texts = {}
    for out, gen in IMPL_FILES.items():
        if (gen_dir / gen).exists():
            text = (gen_dir / gen).read_text(encoding='utf-8')
            texts[out] = clean_external(text, referenced) if gen == 'FunsExternal_Template.lean' else text
    return texts


def generated_sha256s(gen_dir):
    """Hashes of the files extraction writes (impl_texts), keyed by their name in lean/Impl."""
    return {out: hashlib.sha256(text.encode('utf-8')).hexdigest() for out, text in impl_texts(gen_dir).items()}


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
    selftest = normalizer_selftest()
    if selftest:
        return selftest
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
    for name in ('FunsExternal.lean', 'FunsExternal_Template.lean'):
        if name in present:
            text = present[name].read_text(encoding='utf-8')
            try:
                if clean_external(text) != text:
                    errors.append(f'lean/Impl/{name} still declares axioms: run scripts/extract.py and commit lean/Impl')
            except ValueError as e:
                errors.append(f'lean/Impl/{name}: {e}')
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
