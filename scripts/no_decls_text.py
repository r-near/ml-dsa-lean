#!/usr/bin/env python3
"""Text half of scripts/check-no-decls.sh: scan the Lean sources under lean/Impl, lean/Spec and lean/Proofs for the
constructs the project's axiom policy forbids, ignoring comments and string literals (a doc comment may say "no sorry").

Forbidden: a declaration `axiom` or `opaque` (with modifiers), the terms/tactics `sorry`, `admit` and `native_decide`
(also `decide +native`, `Lean.ofReduceBool`), and the attributes `implemented_by`, `extern` and `export`.

Usage: python3 -I scripts/no_decls_text.py [--self-test] DIR...      exit 0 if clean, 1 on a finding, 2 on usage error
"""
import re
import sys
from pathlib import Path

KEYWORD_DECL = re.compile(r'(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*(axiom|opaque)\b')
TOKENS = re.compile(r'(?<![\w.\'!?])(sorry|admit|native_decide|ofReduceBool)(?![\w\'!?])')
DECIDE_NATIVE = re.compile(r'\bdecide\s*\+\s*native\b')
ATTR = re.compile(r'@\[([^\]]*)\]')
ATTR_BAD = re.compile(r'(?<![\w.])(implemented_by|extern|export)(?![\w])')


def strip_lean(text):
    """TEXT with line comments, (nested) block comments and string/char literal contents replaced by spaces (newlines kept)."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j
        elif text.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/-', j): depth += 1; j += 2
                elif text.startswith('-/', j): depth -= 1; j += 2
                else: j += 1
            out.append(re.sub(r'[^\n]', ' ', text[i:j])); i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append('"' + re.sub(r'[^\n]', ' ', text[i + 1:j - 1]) + '"'); i = j
        else:
            out.append(c); i += 1
    return ''.join(out)


def findings(text):
    """List of (line number, what) for the forbidden constructs in the Lean source TEXT."""
    s = strip_lean(text)
    res = []
    def add(m, what):
        res.append((s.count('\n', 0, m.start()) + 1, what))
    for m in KEYWORD_DECL.finditer(s):
        add(m, f'{m.group(1)} declaration')
    for m in TOKENS.finditer(s):
        add(m, m.group(1))
    for m in DECIDE_NATIVE.finditer(s):
        add(m, 'decide +native')
    for m in ATTR.finditer(s):
        for a in ATTR_BAD.finditer(m.group(1)):
            add(m, f'attribute {a.group(1)}')
    return sorted(set(res))


SELF_CASES = {
    'axiom': 'axiom foo : False\n', 'private axiom': 'private axiom foo : False\n',
    'attributed axiom': '@[trait_default] axiom foo : False\n', 'opaque': 'opaque foo : Nat\n',
    'sorry': 'theorem t : 1 = 2 := by\n  sorry\n', 'admit': 'theorem t : 1 = 2 := by admit\n',
    'native_decide': 'example : 1 + 1 = 2 := by native_decide\n', 'decide +native': 'example : 1 + 1 = 2 := by decide +native\n',
    'implemented_by': '@[implemented_by g] def f := 1\n', 'extern': '@[extern "c"] opaque f : Nat\n',
}
SELF_CLEAN = [
    '/-- No sorry, no axiom, no native_decide here. -/\ntheorem t : True := trivial\n',
    '-- axiom opaque sorry\ndef opaque_u32 := 1\ndef x := "an axiom and a sorry"\n',
    '/- nested /- sorry -/ axiom -/\ndef f := core.extern.go\n',
]


def self_test():
    errs = []
    for name, src in SELF_CASES.items():
        if not findings(src):
            errs.append(f'self-test: missed {name}')
    for src in SELF_CLEAN:
        if findings(src):
            errs.append(f'self-test: false positive on {src!r}: {findings(src)}')
    return errs


def main(argv):
    args = argv[1:]
    errs = []
    if args and args[0] == '--self-test':
        args = args[1:]
        errs = self_test()
        if errs:
            print('\n'.join(errs), file=sys.stderr)
            return 1
        if not args:
            print('no_decls_text self-test OK')
            return 0
    if not args:
        print(__doc__, file=sys.stderr)
        return 2
    bad, nfiles = [], 0
    for d in args:
        root = Path(d)
        if not root.is_dir():
            print(f'NODECLS FAIL: {d} is not a directory', file=sys.stderr)
            return 1
        for p in sorted(root.rglob('*.lean')):
            nfiles += 1
            for line, what in findings(p.read_text(encoding='utf-8')):
                bad.append(f'{p}:{line}: {what}')
    if nfiles == 0:
        print('NODECLS FAIL: no .lean files found', file=sys.stderr)
        return 1
    if bad:
        for b in bad[:50]:
            print(f'NODECLS FAIL (text): {b}')
        return 1
    print(f'no-decls text scan: {nfiles} files, 0 forbidden constructs')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
