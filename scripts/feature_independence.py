#!/usr/bin/env python3
"""The Lean half of the feature-independence gate (scripts/check-feature-independence.sh).

The crate is extracted twice, both times with `--cfg miri` and both from the same src/:

  main   feature `avx2`   -> lean/Impl            the extraction every proof is built from
  alt    no features      -> a scratch directory  the extraction of a build WITHOUT the verify dispatch

(A default build, and any build that is not x86_64, compiles the alt configuration of every `cfg` that mentions `avx2`
and `target_arch = "x86_64"`; the only `cfg` the extraction itself decides is `miri`, set in both.) This script compares the
two generated Lean trees declaration by declaration and fails on any difference that is not in the whitelist below. The
whitelist is exact in both directions: a listed difference that disappears is also an error, so the list cannot go stale.

Usage: python3 -I scripts/feature_independence.py compare MAIN_DIR ALT_DIR
       python3 -I scripts/feature_independence.py gen-lean ALT_DIR            print lean/Proofs/NoDispatch.lean
       python3 -I scripts/feature_independence.py check-lean ALT_DIR FILE     fail unless FILE is what gen-lean prints
       python3 -I scripts/feature_independence.py --self-test

`compare` also runs the self-test first.

`gen-lean` copies the alt declarations that differ (the `cpu.Avx2` type and the three `dispatch::*_on` functions) and the
three `fast_verify::*_with` functions (text-identical to main, but elaborated against the alt `Avx2`) into a Lean file in the
namespace `Impl.NoDispatch`, and appends the theorems that the alt `_with` functions equal the scalar functions for every
token value. The names it does not copy resolve to `Impl.*`, where the same declarations exist (the diff proves that they have
the same text). The file is part of the default build (`Proofs.NoDispatch`), so the alt declarations are elaborated and the
theorems checked by the same Lean run as every other proof.
"""
import re
import sys
from pathlib import Path

FILES = ['Types.lean', 'Funs.lean', 'FunsExternal.lean', 'FunsExternal_Template.lean']

# Expected differences, keyed (file, declaration key). `differs`: present in both, different text. `main-only` /
# `alt-only`: the declaration exists in one extraction only. Nothing else may differ. Each entry says why it is allowed.
WHITELIST = {
    ('Types.lean', '[ml_dsa_lean::cpu::Avx2]'): (
        'differs', 'the token: an inhabited struct where the dispatch exists, an uninhabited enum elsewhere (src/cpu.rs)'),
    ('Funs.lean', '[ml_dsa_lean::fast_verify::dispatch::verify_internal_on]:'): (
        'differs', 'dispatch entry point: one call of the AVX2 function, or `match t {}` (extracted as unreachable)'),
    ('Funs.lean', '[ml_dsa_lean::fast_verify::dispatch::verify_prepared_on]:'): (
        'differs', 'dispatch entry point: one call of the AVX2 function, or `match t {}` (extracted as unreachable)'),
    ('Funs.lean', '[ml_dsa_lean::fast_verify::dispatch::prepare_vk_on]:'): (
        'differs', 'dispatch entry point: one call of the AVX2 function, or `match t {}` (extracted as unreachable)'),
    ('Funs.lean', '[ml_dsa_lean::fast_verify::dispatch::verify_internal_avx2]:'): (
        'main-only', 'the #[target_feature(enable = "avx2")] function; it exists only where the dispatch does'),
    ('Funs.lean', '[ml_dsa_lean::fast_verify::dispatch::verify_prepared_avx2]:'): (
        'main-only', 'the #[target_feature(enable = "avx2")] function; it exists only where the dispatch does'),
    ('Funs.lean', '[ml_dsa_lean::fast_verify::dispatch::prepare_vk_avx2]:'): (
        'main-only', 'the #[target_feature(enable = "avx2")] function; it exists only where the dispatch does'),
}

# Declarations that must be byte-identical in both extractions (they are the point of the gate), checked on their own so a
# future whitelist edit cannot silently cover them.
MUST_MATCH = [
    '[ml_dsa_lean::fast_verify::verify_internal_with]:',
    '[ml_dsa_lean::fast_verify::verify_prepared_internal_with]:',
    '[ml_dsa_lean::fast_verify::prepare_vk_with]:',
    '[ml_dsa_lean::verify::verify_internal]:',
    '[ml_dsa_lean::verify::prepare_vk]:',
    '[ml_dsa_lean::verify::verify_prepared_internal]:',
    '[ml_dsa_lean::cpu::avx2]:',
]

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


def compare(main_dir, alt_dir):
    """List of error strings; empty if the two extractions differ only as the whitelist says."""
    errors, seen = [], set()
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
    # The point of the gate.
    by_key = [{k: norm(b) for k, b in parse((Path(d) / 'Funs.lean').read_text(encoding='utf-8'))[1]}
              for d in (main_dir, alt_dir)]
    for k in MUST_MATCH:
        if k not in by_key[0] or k not in by_key[1]:
            errors.append(f'Funs.lean: {k} missing from an extraction')
        elif by_key[0][k] != by_key[1][k]:
            errors.append(f'Funs.lean: {k} differs between the extractions (it must be the same text in every build)')
    return errors


def alt_block(alt_dir, fname, key_prefix):
    blocks = parse((Path(alt_dir) / fname).read_text(encoding='utf-8'))[1]
    hits = [norm(b) for k, b in blocks if k == key_prefix]
    if len(hits) != 1:
        raise ValueError(f'{fname}: expected one declaration {key_prefix}, found {len(hits)}')
    return hits[0]


NAMES_TYPES = ['[ml_dsa_lean::cpu::Avx2]']
NAMES_FUNS = ['[ml_dsa_lean::fast_verify::dispatch::verify_internal_on]:',
              '[ml_dsa_lean::fast_verify::verify_internal_with]:',
              '[ml_dsa_lean::fast_verify::dispatch::prepare_vk_on]:',
              '[ml_dsa_lean::fast_verify::prepare_vk_with]:',
              '[ml_dsa_lean::fast_verify::dispatch::verify_prepared_on]:',
              '[ml_dsa_lean::fast_verify::verify_prepared_internal_with]:']

LEAN_HEAD = '''import Impl.Funs

/-!
# The build without the verify dispatch is the scalar verify (generated; do not edit)

Generated by `scripts/feature_independence.py gen-lean` from the second extraction of `scripts/check-feature-independence.sh`
(`--features ''`: no `avx2`, still `--cfg miri`), which is what a default build, and any build that is not x86_64, compiles in
place of the dispatch. In that build the CPU-check token `cpu::Avx2` is an uninhabited enum, and the dispatch entry points
are `match t {{}}`. The gate proves that everything else in the two extractions is the same text (the declarations below are
the whole difference, plus the three AVX2 functions that exist only with the dispatch); this file elaborates the declarations
that differ, with the three `fast_verify::*_with` functions (which are text-identical to the ones `Proofs/Dispatch.lean` proves
about), and proves them equal to the scalar functions for every `Option cpu.Avx2`: `none` is the scalar call, and `some` is
impossible because `cpu.Avx2` has no value. The declarations live in `Impl.NoDispatch`; every other name they use is the
`Impl` declaration, which the gate proved to be the same in the second extraction.
-/

open Aeneas Aeneas.Std RustM ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace Impl.NoDispatch

'''

LEAN_FOOT = '''end Impl.NoDispatch

namespace Proofs.NoDispatch
open Aeneas Aeneas.Std RustM

theorem verify_internal_with_eq (K L : Std.Usize) (t : Option Impl.NoDispatch.cpu.Avx2) (p : Impl.params.Params)
    (pk m_prefix m sig : Slice Std.U8) :
    Impl.NoDispatch.fast_verify.verify_internal_with K L t p pk m_prefix m sig =
      Impl.verify.verify_internal K L p pk m_prefix m sig := by
  cases t with
  | none => rfl
  | some a => cases a

theorem prepare_vk_with_eq (K L : Std.Usize) (t : Option Impl.NoDispatch.cpu.Avx2) (pk : Slice Std.U8) :
    Impl.NoDispatch.fast_verify.prepare_vk_with K L t pk = Impl.verify.prepare_vk K L pk := by
  cases t with
  | none => rfl
  | some a => cases a

theorem verify_prepared_internal_with_eq {K L : Std.Usize} (t : Option Impl.NoDispatch.cpu.Avx2)
    (p : Impl.params.Params) (vk : Impl.verify.PreparedVk K L) (m_prefix m sig : Slice Std.U8) :
    Impl.NoDispatch.fast_verify.verify_prepared_internal_with t p vk m_prefix m sig =
      Impl.verify.verify_prepared_internal p vk m_prefix m sig := by
  cases t with
  | none => rfl
  | some a => cases a

end Proofs.NoDispatch
'''


def gen_lean(alt_dir):
    out = [LEAN_HEAD.replace('{{}}', '{}')]
    for k in NAMES_TYPES:
        out.append(alt_block(alt_dir, 'Types.lean', k))
    for k in NAMES_FUNS:
        out.append(alt_block(alt_dir, 'Funs.lean', k))
    return '\n'.join(out) + '\n' + LEAN_FOOT


_SELF_MAIN_T = '''-- header
namespace Impl

/-- [ml_dsa_lean::cpu::Avx2]
    Source: 'x.rs', lines 1:0-1:1 -/
def cpu.Avx2 := Unit

end Impl
'''
_SELF_ALT_T = _SELF_MAIN_T.replace('def cpu.Avx2 := Unit', 'inductive cpu.Avx2 where')


def _fun(name, body):
    return (f"/-- [ml_dsa_lean::{name}]:\n    Source: 'x.rs', lines 1:0-1:1 -/\ndef {name.replace('::', '.')}\n"
            f"  := do\n  {body}\n\n")


def _selftest_trees(tmp, extra_main='', extra_alt='', with_main='ok 1', with_alt='ok 1', on_main='ok 2', on_alt='fail panic'):
    names_with = ['fast_verify::verify_internal_with', 'fast_verify::verify_prepared_internal_with',
                  'fast_verify::prepare_vk_with', 'verify::verify_internal', 'verify::prepare_vk',
                  'verify::verify_prepared_internal', 'cpu::avx2']
    ons = ['fast_verify::dispatch::verify_internal_on', 'fast_verify::dispatch::verify_prepared_on',
           'fast_verify::dispatch::prepare_vk_on']
    avx = ['fast_verify::dispatch::verify_internal_avx2', 'fast_verify::dispatch::verify_prepared_avx2',
           'fast_verify::dispatch::prepare_vk_avx2']
    def funs(main):
        s = '-- header\nnamespace Impl\n\n'
        s += ''.join(_fun(n, with_main if main else with_alt) for n in names_with)
        s += ''.join(_fun(n, on_main if main else on_alt) for n in ons)
        if main:
            s += ''.join(_fun(n, 'ok 3') for n in avx)
        s += extra_main if main else extra_alt
        return s + 'end Impl\n'
    for d, main in (('main', True), ('alt', False)):
        (tmp / d).mkdir()
        (tmp / d / 'Types.lean').write_text(_SELF_MAIN_T if main else _SELF_ALT_T)
        (tmp / d / 'Funs.lean').write_text(funs(main))
        (tmp / d / 'FunsExternal.lean').write_text('-- ext\nnamespace Impl\n\nend Impl\n')


def self_test():
    """Errors if `compare` accepts a tree pair it must reject, or rejects the expected one."""
    import tempfile
    errs = []
    def run(label, expect_ok, needle=None, **kw):
        with tempfile.TemporaryDirectory() as t:
            t = Path(t)
            _selftest_trees(t, **kw)
            e = compare(t / 'main', t / 'alt')
            if expect_ok and e:
                errs.append(f'self-test {label}: unexpected errors {e}')
            if not expect_ok:
                if not e:
                    errs.append(f'self-test {label}: the difference was not reported')
                elif needle and not any(needle in x for x in e):
                    errs.append(f'self-test {label}: no error mentions {needle!r}: {e}')
    run('the expected differences only', True)
    run('a declaration only in main', False, 'main only', extra_main=_fun('verify::new_helper', 'ok 4'))
    run('a declaration only in alt', False, 'alt only', extra_alt=_fun('verify::new_helper', 'ok 4'))
    run('a cfg-split ordinary function', False, 'differs',
        extra_main=_fun('verify::cfg_split', 'ok 1'), extra_alt=_fun('verify::cfg_split', 'ok 2'))
    run('a cfg-split _with body', False, 'differs', with_main='ok 1', with_alt='ok 9')
    run('a whitelisted difference that vanished', False, 'agree', on_alt='ok 2')
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
    if len(args) == 3 and args[0] == 'compare':
        errs = self_test()
        if errs:
            for e in errs:
                print(f'FEATURE-INDEPENDENCE FAIL (self-test): {e}', file=sys.stderr)
            return 1
        errs = compare(args[1], args[2])
        for e in errs:
            print(f'FEATURE-INDEPENDENCE FAIL: {e}', file=sys.stderr)
        if errs:
            return 1
        print(f'feature independence: the two extractions agree except for {len(WHITELIST)} whitelisted declarations:')
        for (f, k), (kind, why) in sorted(WHITELIST.items()):
            print(f'  {f} {k} ({kind}): {why}')
        print(f'  byte-identical, checked separately: {len(MUST_MATCH)} declarations ({MUST_MATCH[0]}, ...)')
        return 0
    if len(args) == 2 and args[0] == 'gen-lean':
        sys.stdout.write(gen_lean(args[1]))
        return 0
    if len(args) == 3 and args[0] == 'check-lean':
        want = gen_lean(args[1])
        have = Path(args[2]).read_text(encoding='utf-8') if Path(args[2]).is_file() else None
        if have != want:
            print(f'FEATURE-INDEPENDENCE FAIL: {args[2]} is not what `gen-lean` prints from the second extraction '
                  f'(regenerate it with scripts/check-feature-independence.sh --update)', file=sys.stderr)
            return 1
        print(f'{args[2]} matches the second extraction')
        return 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
