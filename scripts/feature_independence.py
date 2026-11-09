#!/usr/bin/env python3
"""The Lean half of the target-feature-independence gate (scripts/check-feature-independence.sh).

Since round 12 the crate has no run-time choice between code paths: `api::verify_*`, `verifying_key_*` and the prepared verify
call the 4-way functions, and a build that wants AVX2 code says so at compile time (`-C target-feature=+avx2`). The Lean proofs
are about one extraction of the crate. This gate checks that the extraction does not depend on the target features, by
extracting the crate twice from the same src/, both times with `--cfg miri` (which scripts/extract.py always sets):

  main   rustflags `--cfg miri`                                   -> lean/Impl            the extraction every proof is built from
  alt    rustflags `--cfg miri -C target-feature=+avx,+avx2`      -> a scratch directory  the extraction of an AVX2 build

and requires the two generated Lean trees to be the same, declaration by declaration. The whitelist of differences is EMPTY: the
crate has no `cfg` that reads `target_feature` (scripts/cfg_inventory.py fails on one), so any difference would be a new,
unreviewed dependence of the proved code on the build's target features.

An empty comparison could pass without the second extraction having seen the flags (a typo in a flag, a stripped environment, the
same flags twice). Three checks stop that:
  * `compare` reads the `rustflags` that each extraction recorded in its extract-report.json, and fails unless they are exactly the
    two strings above (so the two runs were configured differently, and as intended), and unless their input digests differ;
  * `probe-check` compares two extractions of scripts/fi-probe, a one-function crate whose body is `cfg!(target_feature = "avx2")`:
    it must come out as `false` in main and `true` in alt. That is a positive control: if the flags did not reach the compiler
    the probe would be identical in both and the gate fails;
  * `compare` also requires that the verify-path declarations (MUST_BE_PRESENT) exist in both extractions, so the comparison
    covered the code the gate is about.

Usage: python3 -I scripts/feature_independence.py compare MAIN_DIR ALT_DIR
       python3 -I scripts/feature_independence.py probe-check PROBE_MAIN_DIR PROBE_ALT_DIR
       python3 -I scripts/feature_independence.py --self-test

`compare` and `probe-check` run the self-test first.
"""
import json
import re
import sys
from pathlib import Path

FILES = ['Types.lean', 'Funs.lean', 'FunsExternal.lean', 'FunsExternal_Template.lean']
REPORT = 'extract-report.json'

# The rustflags of the two extractions, as scripts/extract_hash.py (RUSTFLAGS_BASE, RUSTFLAGS_AVX2) writes them into hax.toml and
# scripts/extract.py records them in the report.
FLAGS_MAIN = '--cfg miri'
FLAGS_ALT = '--cfg miri -C target-feature=+avx,+avx2'

# Expected differences, keyed (file, declaration key) -> (kind, why). `differs`: present in both, different text. `main-only` /
# `alt-only`: the declaration exists in one extraction only. EMPTY: nothing may differ. An entry would have to say why the proved
# code may depend on the target features, and the gate fails if an entry matches nothing.
WHITELIST = {}

# Declarations that must exist in both extractions (and, since the whitelist is empty, be byte-identical): the verify path that the
# AVX2 build changes the code generation of. A rename or removal makes the gate fail rather than silently narrow its scope.
MUST_BE_PRESENT = [
    '[ml_dsa_lean::api::verify_44]:',
    '[ml_dsa_lean::api::verify_65]:',
    '[ml_dsa_lean::api::verify_87]:',
    '[ml_dsa_lean::api::verify_internal_65]:',
    '[ml_dsa_lean::api::verifying_key_65]:',
    '[ml_dsa_lean::api::verify_prepared_65]:',
    '[ml_dsa_lean::api::verify_internal_prepared_65]:',
    '[ml_dsa_lean::verify::verify_internal_x4]:',
    '[ml_dsa_lean::verify::prepare_vk_into_x4]:',
    '[ml_dsa_lean::verify::verify_prepared_internal]:',
    '[ml_dsa_lean::verify::verify_internal]:',
    '[ml_dsa_lean::verify::prepare_vk]:',
    '[ml_dsa_lean::sampling::expand_a_tr_into_x4]:',
]

PROBE_KEY = '[ml_dsa_lean::probe::avx2_enabled]:'

KEY = re.compile(r'^/-- (\[[^\]\n]+\])([^\n]*)')


def parse(text):
    """(prefix, blocks, suffix): TEXT split at its top-level doc comments `/-- [rust path]...`. `blocks` is a list of
    (key, text); a key is the bracketed Rust path plus the rest of the doc comment's first line (`: loop body 0:`), so the
    pieces of one function are distinct. The prefix is everything before the first block; the suffix is the closing
    `end Impl` (and anything after it)."""
    lines = text.split('\n')
    starts = [i for i, l in enumerate(lines) if KEY.match(l)]
    if not starts:
        return text, [], ''
    prefix = '\n'.join(lines[:starts[0]])
    blocks = []
    for n, s in enumerate(starts):
        e = starts[n + 1] if n + 1 < len(starts) else len(lines)
        body = '\n'.join(lines[s:e])
        m = KEY.match(lines[s])
        blocks.append((m.group(1) + m.group(2).strip(), body))
    # The suffix: the last block ends at `end Impl`.
    last_key, last = blocks[-1]
    m = re.search(r'\n(end Impl[^\n]*\n*)\Z', last + '\n')
    suffix = ''
    if m:
        suffix = m.group(1)
        blocks[-1] = (last_key, last[:last.rindex('end Impl')])
    return prefix, blocks, suffix


def norm(block):
    return block.rstrip('\n') + '\n'


def read_report(d):
    p = Path(d) / REPORT
    if not p.is_file():
        return None
    return json.loads(p.read_text(encoding='utf-8'))


def check_reports(main_dir, alt_dir):
    """Errors if the two extractions were not run with the intended, different rustflags."""
    errors = []
    rm, ra = read_report(main_dir), read_report(alt_dir)
    if rm is None or ra is None:
        return [f'{REPORT} is missing from the {"main" if rm is None else "alt"} extraction: cannot tell how it was run']
    if rm.get('rustflags') != FLAGS_MAIN:
        errors.append(f'the main extraction ran with rustflags {rm.get("rustflags")!r}, expected {FLAGS_MAIN!r}')
    if ra.get('rustflags') != FLAGS_ALT:
        errors.append(f'the alt extraction ran with rustflags {ra.get("rustflags")!r}, expected {FLAGS_ALT!r}')
    if rm.get('rustflags') == ra.get('rustflags'):
        errors.append('both extractions ran with the same rustflags: the comparison would be vacuous')
    if rm.get('extract_inputs_sha256') == ra.get('extract_inputs_sha256'):
        errors.append('both extractions have the same input digest (src/, Cargo.toml, hax.toml): the flags did not enter the inputs')
    if rm.get('roots') != ra.get('roots'):
        errors.append('the two extractions have different roots')
    if rm.get('tools') != ra.get('tools'):
        errors.append('the two extractions used different tools')
    return errors


def compare(main_dir, alt_dir):
    """List of error strings; empty if the two extractions were run as intended and differ only as the whitelist says."""
    errors, seen = check_reports(main_dir, alt_dir), set()
    for f in FILES:
        pm, pa = Path(main_dir) / f, Path(alt_dir) / f
        if not pm.is_file() or not pa.is_file():
            if pm.is_file() != pa.is_file():
                errors.append(f'{f}: present in only one extraction')
            continue
        hm, bm, sm = parse(pm.read_text(encoding='utf-8'))
        ha, ba, sa = parse(pa.read_text(encoding='utf-8'))
        if hm != ha:
            errors.append(f'{f}: the header (imports, options, namespace) differs')
        if sm != sa:
            errors.append(f'{f}: the footer differs')
        dm, da = {}, {}
        for k, b in bm:
            if k in dm:
                errors.append(f'{f}: duplicate declaration key {k} in the main extraction')
            dm[k] = norm(b)
        for k, b in ba:
            if k in da:
                errors.append(f'{f}: duplicate declaration key {k} in the alt extraction')
            da[k] = norm(b)
        for k in sorted(set(dm) | set(da)):
            if k in dm and k in da:
                kind = None if dm[k] == da[k] else 'differs'
            else:
                kind = 'main-only' if k in dm else 'alt-only'
            w = WHITELIST.get((f, k))
            if w:
                seen.add((f, k))
            if kind is None:
                if w:
                    errors.append(f'{f}: {k} is whitelisted as {w[0]} but the two extractions agree on it: remove the entry')
            elif w is None:
                errors.append(f'{f}: {k} {kind.replace("-", " ")}: not in the whitelist of scripts/feature_independence.py')
            elif w[0] != kind:
                errors.append(f'{f}: {k} is {kind}, whitelisted as {w[0]}')
    for key in WHITELIST:
        if key not in seen:
            errors.append(f'{key[0]}: whitelist entry {key[1]} matches no declaration in either extraction')
    # The comparison must have covered the verify path.
    try:
        by_key = [{k: norm(b) for k, b in parse((Path(d) / 'Funs.lean').read_text(encoding='utf-8'))[1]}
                  for d in (main_dir, alt_dir)]
    except OSError as e:
        return errors + [f'Funs.lean: {e}']
    for k in MUST_BE_PRESENT:
        if k not in by_key[0] or k not in by_key[1]:
            errors.append(f'Funs.lean: {k} missing from an extraction (the gate must cover it)')
        elif by_key[0][k] != by_key[1][k]:
            errors.append(f'Funs.lean: {k} differs between the extractions (it must be the same text in every build)')
    return errors


def probe_check(main_dir, alt_dir):
    """Errors unless the probe crate (one function, `cfg!(target_feature = "avx2")`) extracted differently under the two flag
    sets: false without the target features, true with them. This is the positive control of the gate."""
    errors = check_reports(main_dir, alt_dir)
    texts = []
    for d in (main_dir, alt_dir):
        try:
            blocks = {k: norm(b) for k, b in parse((Path(d) / 'Funs.lean').read_text(encoding='utf-8'))[1]}
        except OSError as e:
            return errors + [f'probe Funs.lean: {e}']
        if PROBE_KEY not in blocks:
            return errors + [f'probe: {PROBE_KEY} is missing from an extraction of scripts/fi-probe']
        texts.append(blocks[PROBE_KEY])
    if texts[0] == texts[1]:
        errors.append('the probe extracted identically with and without the AVX2 target features: the flags do not reach the '
                      'compiler, so the main comparison proves nothing')
    else:
        if not re.search(r'\bok false\b', texts[0]) or not re.search(r'\bok true\b', texts[1]):
            errors.append('the probe differs between the extractions but not as `false` without and `true` with the target '
                          f'features:\n--- main\n{texts[0]}\n--- alt\n{texts[1]}')
    return errors


# ----------------------------------------------------------------------------------------------------------------------------
# Self-test: synthetic extraction trees, to show that `compare` and `probe-check` reject what they must reject.
# ----------------------------------------------------------------------------------------------------------------------------

def _fun(name, body):
    return (f"/-- [ml_dsa_lean::{name}]:\n    Source: 'x.rs', lines 1:0-1:1 -/\ndef {name.replace('::', '.')}\n"
            f"  := do\n  {body}\n\n")


def _write_tree(d, funs, flags, digest, roots=('r',)):
    d.mkdir()
    (d / 'Types.lean').write_text('-- header\nnamespace Impl\n\nend Impl\n')
    (d / 'Funs.lean').write_text('-- header\nnamespace Impl\n\n' + funs + 'end Impl\n')
    (d / 'FunsExternal.lean').write_text('-- ext\nnamespace Impl\n\nend Impl\n')
    (d / REPORT).write_text(json.dumps({'rustflags': flags, 'extract_inputs_sha256': digest, 'roots': list(roots),
                                        'tools': {'aeneas': 'a'}}))


def _must_funs(body='ok 1'):
    return ''.join(_fun(k[len('[ml_dsa_lean::'):-len(']:')], body) for k in MUST_BE_PRESENT)


def self_test():
    """Errors if `compare` or `probe_check` accept a tree pair they must reject, or reject the expected one."""
    import tempfile
    errs = []

    def run_compare(label, expect_ok, needle=None, main_funs=None, alt_funs=None, main_flags=FLAGS_MAIN, alt_flags=FLAGS_ALT,
                    main_digest='d1', alt_digest='d2'):
        with tempfile.TemporaryDirectory() as t:
            t = Path(t)
            _write_tree(t / 'main', main_funs if main_funs is not None else _must_funs(), main_flags, main_digest)
            _write_tree(t / 'alt', alt_funs if alt_funs is not None else _must_funs(), alt_flags, alt_digest)
            e = compare(t / 'main', t / 'alt')
        if expect_ok and e:
            errs.append(f'self-test {label}: unexpected errors {e}')
        if not expect_ok:
            if not e:
                errs.append(f'self-test {label}: the problem was not reported')
            elif needle and not any(needle in x for x in e):
                errs.append(f'self-test {label}: no error mentions {needle!r}: {e}')

    run_compare('identical trees from the intended flags', True)
    # Vacuity: the same flags twice, even though the trees are identical.
    run_compare('the same flags twice', False, 'same rustflags', alt_flags=FLAGS_MAIN)
    run_compare('the same input digest twice', False, 'same input digest', alt_digest='d1')
    run_compare('a typo in the alt flags', False, 'expected', alt_flags='--cfg miri -C target-feature=+avx2')
    run_compare('flags missing from the report', False, 'expected', alt_flags=None)
    extra = _fun('verify::new_helper', 'ok 4')
    run_compare('a declaration only in main', False, 'main only', main_funs=_must_funs() + extra)
    run_compare('a declaration only in alt', False, 'alt only', alt_funs=_must_funs() + extra)
    run_compare('a target-feature-split function', False, 'differs',
                main_funs=_must_funs() + _fun('verify::split', 'ok 1'), alt_funs=_must_funs() + _fun('verify::split', 'ok 2'))
    run_compare('a verify-path function that differs', False, 'differs', alt_funs=_must_funs().replace('ok 1', 'ok 9', 1))
    run_compare('a verify-path function missing from both', False, 'missing',
                main_funs=_must_funs().replace('verify::verify_internal_x4', 'verify::other', 1),
                alt_funs=_must_funs().replace('verify::verify_internal_x4', 'verify::other', 1))
    if WHITELIST:
        errs.append('self-test: the whitelist must be empty')

    def run_probe(label, expect_ok, main_body, alt_body, needle=None):
        with tempfile.TemporaryDirectory() as t:
            t = Path(t)
            _write_tree(t / 'main', _fun('probe::avx2_enabled', main_body), FLAGS_MAIN, 'd1')
            _write_tree(t / 'alt', _fun('probe::avx2_enabled', alt_body), FLAGS_ALT, 'd2')
            e = probe_check(t / 'main', t / 'alt')
        if expect_ok and e:
            errs.append(f'self-test probe {label}: unexpected errors {e}')
        if not expect_ok:
            if not e:
                errs.append(f'self-test probe {label}: the problem was not reported')
            elif needle and not any(needle in x for x in e):
                errs.append(f'self-test probe {label}: no error mentions {needle!r}: {e}')

    run_probe('false then true', True, 'ok false', 'ok true')
    run_probe('identical (the flags did not reach the compiler)', False, 'ok false', 'ok false', 'do not reach')
    run_probe('reversed', False, 'ok true', 'ok false', 'not as `false`')
    return errs


def main(argv):
    args = argv[1:]
    if args and args[0] == '--self-test':
        errs = self_test()
        for e in errs:
            print(e, file=sys.stderr)
        if not errs:
            print('feature_independence self-test OK')
        return 1 if errs else 0
    if len(args) == 3 and args[0] in ('compare', 'probe-check'):
        errs = self_test()
        if errs:
            for e in errs:
                print(f'FEATURE-INDEPENDENCE FAIL (self-test): {e}', file=sys.stderr)
            return 1
        if args[0] == 'compare':
            errs = compare(args[1], args[2])
        else:
            errs = probe_check(args[1], args[2])
        for e in errs:
            print(f'FEATURE-INDEPENDENCE FAIL: {e}', file=sys.stderr)
        if errs:
            return 1
        if args[0] == 'compare':
            print(f'feature independence: the extractions with rustflags {FLAGS_MAIN!r} and {FLAGS_ALT!r} are the same Lean; '
                  f'whitelist: {len(WHITELIST)} entries (empty); {len(MUST_BE_PRESENT)} verify-path declarations present and identical')
        else:
            print('probe: `cfg!(target_feature = "avx2")` extracted as false without and true with the target features '
                  '(the flags reach the compiler)')
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
