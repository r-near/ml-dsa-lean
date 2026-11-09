#!/usr/bin/env python3
"""Text half of scripts/check-no-decls.sh: scan the Lean sources under lean/Impl, lean/Spec and lean/Proofs for the
constructs the project's axiom policy forbids, ignoring comments and string literals (a doc comment may say "no sorry").

Forbidden: a declaration `axiom` or `opaque` (with modifiers), the terms/tactics `sorry`, `admit` and `native_decide`
(also `decide +native`, `Lean.ofReduceBool`), the attributes `implemented_by`, `extern` and `export`, and the syntax that
makes an opaque or unsafe declaration or adds one while elaborating: `partial` (a `partial def` becomes an `opaque`
constant, which the environment scan also finds, but only in a module that was built), `unsafe`, `initialize`,
`builtin_initialize`, `run_cmd`, `run_elab`, `run_meta`, `addDecl`, `addAndCompile`. The existing sources use none of them
outside comments; a proof that needs one is a conversation, not a gate exception.

Each argument is a directory (every .lean file under it, recursively) or a single .lean file; the gate passes the three
directories and their root modules (Impl.lean, Spec.lean, Proofs.lean), which no directory scan sees.

Usage: python3 -I scripts/no_decls_text.py [--self-test] PATH...      exit 0 if clean, 1 on a finding, 2 on usage error
"""
import re
import sys
from pathlib import Path

KEYWORD_DECL = re.compile(r'(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:private|protected|noncomputable|unsafe|partial)[ \t]+)*(axiom|opaque)\b')
TOKENS = re.compile(r'(?<![\w.\'!?])(sorry|admit|native_decide|ofReduceBool)(?![\w\'!?])')
DECIDE_NATIVE = re.compile(r'\bdecide\s*\+\s*native\b')
ATTR = re.compile(r'@\[([^\]]*)\]')
ATTR_BAD = re.compile(r'(?<![\w.])(implemented_by|extern|export)(?![\w])')
# Syntax that produces an opaque or unsafe constant, or declares one while elaborating.
OPAQUE_SYNTAX = re.compile(r"(?<![\w.'!?])(partial|unsafe|initialize|builtin_initialize|run_cmd|run_elab|run_meta)(?![\w'!?])|"
                           r"(?<![\w'!?])(?:[\w]+\.)*(addDecl|addAndCompile)(?![\w'!?])")


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
    for m in OPAQUE_SYNTAX.finditer(s):
        add(m, f'{m.group(1) or m.group(2)} (makes or adds an opaque/unsafe declaration)')
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
    'partial def': 'partial def f (n : Nat) : Nat := f n\n', 'private partial def': 'private partial def f (n : Nat) : Nat := f n\n',
    'attributed partial def': '@[inline] partial def f (n : Nat) : Nat := f n\n', 'unsafe def': 'unsafe def f : Nat := 1\n',
    'initialize': 'initialize r : IO.Ref Nat <- IO.mkRef 0\n', 'run_cmd': 'run_cmd Lean.logInfo "x"\n',
    'addDecl': 'def f : Lean.CoreM Unit := Lean.addDecl d\n',
}
SELF_CLEAN = [
    '/-- No sorry, no axiom, no native_decide here. -/\ntheorem t : True := trivial\n',
    '-- axiom opaque sorry\ndef opaque_u32 := 1\ndef x := "an axiom and a sorry"\n',
    '/- nested /- sorry -/ axiom -/\ndef f := core.extern.go\n',
    '/-- A partial proof, partial correctness; an unsafe-looking `unsafeCast` is not used. -/\ntheorem partial_correct : True := trivial\n',
    'def isPartial := 1\ndef partial_sum := 2\n',
]


def self_test():
    import tempfile
    errs = []
    for name, src in SELF_CASES.items():
        if not findings(src):
            errs.append(f'self-test: missed {name}')
    for src in SELF_CLEAN:
        if findings(src):
            errs.append(f'self-test: false positive on {src!r}: {findings(src)}')
    # Scan paths: a root module given as a file is scanned, and so is a module nobody imports (the scan is textual).
    with tempfile.TemporaryDirectory() as d:
        root = Path(d)
        (root / 'Proofs').mkdir()
        (root / 'Proofs.lean').write_text('axiom zzRootAxiom : False\n')
        (root / 'Proofs' / 'Unbuilt.lean').write_text('partial def zzUnbuilt (n : Nat) : Nat := zzUnbuilt n\n')
        (root / 'Ok.lean').write_text('theorem t : True := trivial\n')
        for name, args, want in (('a root module given as a file', [str(root / 'Proofs.lean')], 1),
                                 ('an unbuilt module with a partial def, found by directory', [str(root / 'Proofs')], 1),
                                 ('a clean file', [str(root / 'Ok.lean')], 0)):
            if scan_paths(args)[0] != want:
                errs.append(f'self-test: {name}: wrong verdict')
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
    rc, lines, nfiles = scan_paths(args)
    for l in lines:
        print(l)
    if rc == 0:
        print(f'no-decls text scan: {nfiles} files, 0 forbidden constructs')
    return rc


def scan_paths(paths):
    """(exit code, output lines, files scanned) for the files and directories PATHS."""
    bad, nfiles = [], 0
    for d in paths:
        root = Path(d)
        if root.is_file():
            files = [root]
        elif root.is_dir():
            files = sorted(root.rglob('*.lean'))
        else:
            return 1, [f'NODECLS FAIL: {d} is not a directory or a file'], 0
        for p in files:
            nfiles += 1
            for line, what in findings(p.read_text(encoding='utf-8')):
                bad.append(f'{p}:{line}: {what}')
    if nfiles == 0:
        return 1, ['NODECLS FAIL: no .lean files found'], 0
    if bad:
        return 1, [f'NODECLS FAIL (text): {b}' for b in bad[:50]], nfiles
    return 0, [], nfiles


if __name__ == '__main__':
    sys.exit(main(sys.argv))
