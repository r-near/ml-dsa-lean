#!/usr/bin/env python3
"""Function-by-function comparison of two sets of checkct driver binaries (checkct/compare-code.sh).

Usage: compare_code.py DIR_A DIR_B     (each holds none/driver-TARGET and avx2/driver-TARGET)
       compare_code.py --self-test

For every binary the text is disassembled with `llvm-objdump -d`. A function is the block under a `ADDR <name>:` label. Masked
before comparing: the leading address of each line (and the raw bytes), hexadecimal immediates and branch targets that
look like addresses (`0x` followed by at least 5 hex digits), the `<symbol+off>` operand annotations, and the 16-hex-digit
hash of a Rust legacy symbol (`17h...E`). Function names are compared with the hash removed. Reported per binary: the number
of functions in each, those only in one side, and those whose masked text differs. Exit 1 when anything differs.

Scope: the masked instruction stream. It is not a proof that two binaries behave alike (a masked immediate could differ in a
way that matters) and not a constant-time result; it is a quick reason to expect that BINSEC would see the same code.

A comparison only counts if both sides are real disassemblies. A missing binary, text that is not an objdump listing (a header
only), a listing with fewer than MIN_FUNCTIONS functions or MIN_INSTRUCTIONS instructions, or one without the driver's entry
points and probes (REQUIRED_SYMBOLS) is an error (exit 2, "COMPARE ERROR"), never "COMPARE OK": two empty maps used to compare
equal. The self-test (run before every comparison, and by `--self-test`, which the `ci-selftest` step of scripts/ci.sh runs in CI) holds the
negative fixtures, among them the header-only listing.
"""
import os
import re
import subprocess
import sys

OBJDUMP = os.environ.get('LLVM_OBJDUMP') or next(
    (str(p) for p in __import__('pathlib').Path.home().glob('.rustup/toolchains/nightly-2026-10-23*/lib/rustlib/*/bin/llvm-objdump')), 'llvm-objdump')
TARGETS = ['riscv32imac-unknown-none-elf', 'thumbv7em-none-eabihf', 'x86_64-unknown-linux-gnu']
HASH = re.compile(r'17h[0-9a-f]{16}E|\.llvm\.\d+|(?<=[NC])s[0-9A-Za-z]{8,12}_(?=\d)')
LABEL = re.compile(r'^([0-9a-f]+) <(.+)>:$')
ADDR_LINE = re.compile(r'^\s*[0-9a-f]+:\s+(?:[0-9a-f]{2}\s+)+(.*)$|^\s*[0-9a-f]+:\s+[0-9a-f]{4,8}\s+(.*)$')
HEXIMM = re.compile(r'0x[0-9a-fA-F]{5,}')
SYMREF = re.compile(r'<[^>]*>')
FORMAT_LINE = re.compile(r'^\S.*:\s+file format \S+', re.M)
SECTION_LINE = re.compile(r'^Disassembly of section \S+:', re.M)

# What a disassembly of the checkct driver must contain, on each side, before any comparison means anything. Symbol names are
# matched after the hash is removed (a legacy `_ZN..E` name and a v0 `_R..` name both end in `<len><name>`); a probe that is
# renamed in checkct/driver fails here instead of being compared as "absent on both sides". The driver's own entry points are
# `_start` and `__checkct_panic` (checkct/driver/src/main.rs); the probes are non-generic `#[checkct]` functions from three of
# its modules (extra.rs, prepared.rs and a second function of extra.rs). The sizes are far below a real driver's (about 235
# functions and 64000 or more instructions per binary) and far above a header: they only reject a truncated or wrong file.
REQUIRED_SYMBOLS = [
    ('_start', re.compile(r'^_start$')),
    ('__checkct_panic', re.compile(r'^__checkct_panic$')),
    ('probe extra::sk_is_well_formed_44', re.compile(r'6driver5extra20sk_is_well_formed_44$')),
    ('probe extra::ntt_vec_44', re.compile(r'6driver5extra10ntt_vec_44$')),
    ('probe prepared::census_sign_prepared_44', re.compile(r'6driver8prepared23census_sign_prepared_44$')),
]
MIN_FUNCTIONS = 100
MIN_INSTRUCTIONS = 10000


class BadDisassembly(Exception):
    """The input is not a usable disassembly of a driver binary. Never turned into a pass."""


def parse_disassembly(out, what='disassembly'):
    """Function map (hash-free name -> masked instruction list) of the llvm-objdump -d text OUT. Raises BadDisassembly if OUT
    is not an objdump listing (no `file format` line and no `Disassembly of section`), has no function, or has a function
    without instructions as its only content."""
    if not FORMAT_LINE.search(out) or not SECTION_LINE.search(out):
        raise BadDisassembly(f'{what}: not an llvm-objdump -d listing (no "file format" line or no "Disassembly of section")')
    fns, cur = {}, None
    for line in out.split('\n'):
        m = LABEL.match(line)
        if m:
            cur = HASH.sub('', m.group(2))
            fns.setdefault(cur, [])
            continue
        if cur is None:
            continue
        m = re.match(r'^\s*[0-9a-f]+:\s*(.*)$', line)
        if m and m.group(1).strip():
            t = SYMREF.sub('<>', m.group(1))
            t = HEXIMM.sub('0xADDR', t)
            fns[cur].append(re.sub(r'\s+', ' ', t).strip())
    if not fns:
        raise BadDisassembly(f'{what}: no function label found (header only?)')
    return fns


def validate(fns, what='disassembly'):
    """Raises BadDisassembly unless FNS looks like the driver: enough functions and instructions, and every REQUIRED_SYMBOLS
    entry present with a nonempty body."""
    n_insn = sum(len(v) for v in fns.values())
    if len(fns) < MIN_FUNCTIONS or n_insn < MIN_INSTRUCTIONS:
        raise BadDisassembly(f'{what}: {len(fns)} functions and {n_insn} instructions; a driver has at least {MIN_FUNCTIONS} '
                             f'functions and {MIN_INSTRUCTIONS} instructions')
    for label, rx in REQUIRED_SYMBOLS:
        hits = [n for n in fns if rx.search(n)]
        if not hits:
            raise BadDisassembly(f'{what}: the expected symbol {label} is missing')
        if not any(fns[n] for n in hits):
            raise BadDisassembly(f'{what}: the expected symbol {label} has no instructions')


def functions(path):
    if not os.path.isfile(path):
        raise BadDisassembly(f'{path}: not a file (missing binary)')
    try:
        out = subprocess.run([OBJDUMP, '-d', '--no-show-raw-insn', path], capture_output=True, text=True, check=True).stdout
    except FileNotFoundError:
        raise BadDisassembly(f'{OBJDUMP}: disassembler not found (set LLVM_OBJDUMP)')
    except subprocess.CalledProcessError as e:
        raise BadDisassembly(f'{path}: llvm-objdump failed: {e.stderr.strip()[:200]}')
    fns = parse_disassembly(out, path)
    validate(fns, path)
    return fns


def compare_maps(fa, fb):
    """(bad, only_a, only_b, diff) for two validated function maps."""
    only_a, only_b = sorted(set(fa) - set(fb)), sorted(set(fb) - set(fa))
    diff = sorted(n for n in set(fa) & set(fb) if fa[n] != fb[n])
    return len(diff) + len(only_a) + len(only_b), only_a, only_b, diff


def self_test():
    """Errors (a list of strings) if a bad disassembly is accepted or a good one rejected."""
    errs = []
    header = '\n/path/driver-x:\tfile format elf64-x86-64\n\nDisassembly of section .text:\n\n'
    def listing(fns, extra=''):
        out = header
        addr = 0x1000
        for name, body in fns.items():
            out += f'{addr:016x} <{name}>:\n'
            for i in body:
                out += f'    {addr:x}:\t{i}\n'
                addr += 4
            out += '\n'
        return out + extra
    good = {'_start': ['jmp 0x401000'], '__checkct_panic': ['jmp 0x401000'],
            '_RNvNtCsAAAAAAAAAAAA_6driver5extra20sk_is_well_formed_44': ['xor eax, eax', 'ret'],
            '_RNvNtCsAAAAAAAAAAAA_6driver5extra10ntt_vec_44': ['xor eax, eax', 'ret'],
            '_RNvNtCsAAAAAAAAAAAA_6driver8prepared23census_sign_prepared_44': ['xor eax, eax', 'ret']}
    for i in range(MIN_FUNCTIONS):
        good[f'_ZN6driver4fill{i}17h0123456789abcdefE'] = ['mov eax, ecx'] * (MIN_INSTRUCTIONS // MIN_FUNCTIONS + 1)
    def expect_bad(label, text):
        try:
            validate(parse_disassembly(text, label), label)
            errs.append(f'compare_code self-test: accepted {label}')
        except BadDisassembly:
            pass
    expect_bad('a header-only disassembly', header)
    expect_bad('an empty string', '')
    expect_bad('text that is not a disassembly', 'ELF: no such section\n')
    expect_bad('a listing with a header and no label', header + '    1000:\tnop\n')
    expect_bad('labels without instructions', listing({n: [] for n in good}))
    expect_bad('a listing of a few functions', listing({'_start': ['nop'], '__checkct_panic': ['nop']}))
    for sym in ('_start', '__checkct_panic', '_RNvNtCsAAAAAAAAAAAA_6driver5extra10ntt_vec_44'):
        expect_bad(f'a driver without {sym}', listing({k: v for k, v in good.items() if k != sym}))
    empty_probe = dict(good)
    empty_probe['_RNvNtCsAAAAAAAAAAAA_6driver5extra10ntt_vec_44'] = []
    expect_bad('a driver whose probe has no instructions', listing(empty_probe))
    # Good input is accepted, and two identical or differing maps compare as they should.
    try:
        fa = parse_disassembly(listing(good), 'good')
        validate(fa, 'good')
        if compare_maps(fa, parse_disassembly(listing(good), 'good'))[0] != 0:
            errs.append('compare_code self-test: identical listings differ')
        other = dict(good)
        other['_RNvNtCsAAAAAAAAAAAA_6driver5extra10ntt_vec_44'] = ['xor eax, eax', 'nop', 'ret']
        if compare_maps(fa, parse_disassembly(listing(other), 'other'))[0] != 1:
            errs.append('compare_code self-test: a changed function was not reported')
        renamed = {k.replace('AAAAAAAAAAAA', 'BBBBBBBBBBBB'): v for k, v in good.items()}
        if compare_maps(fa, parse_disassembly(listing(renamed), 'renamed'))[0] != 0:
            errs.append('compare_code self-test: a changed symbol hash was reported as a difference')
    except BadDisassembly as e:
        errs.append(f'compare_code self-test: rejected a good listing: {e}')
    return errs


def main():
    if sys.argv[1:2] == ['--self-test']:
        errs = self_test()
        for e in errs:
            print(e, file=sys.stderr)
        print('compare_code self-test OK' if not errs else f'compare_code self-test FAILED ({len(errs)})')
        sys.exit(1 if errs else 0)
    errs = self_test()
    if errs:
        for e in errs:
            print(f'COMPARE ERROR (self-test): {e}', file=sys.stderr)
        sys.exit(2)
    if len(sys.argv) != 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    a, b = sys.argv[1:3]
    bad, cells = 0, 0
    for feat in ('none', 'avx2'):
        for t in TARGETS:
            try:
                fa, fb = functions(f'{a}/{feat}/driver-{t}'), functions(f'{b}/{feat}/driver-{t}')
            except BadDisassembly as e:
                print(f'COMPARE ERROR: {e}')
                sys.exit(2)
            cells += 1
            nbad, only_a, only_b, diff = compare_maps(fa, fb)
            print(f'{feat:5} {t:30} functions {len(fa)} / {len(fb)}: identical {len(set(fa) & set(fb)) - len(diff)}, '
                  f'differ {len(diff)}, only in A {len(only_a)}, only in B {len(only_b)}')
            for n in diff[:20]:
                print(f'    differs: {n}')
            for n in only_a[:20]:
                print(f'    only in A: {n}')
            for n in only_b[:20]:
                print(f'    only in B: {n}')
            bad += nbad
    if cells != 2 * len(TARGETS):
        print(f'COMPARE ERROR: compared {cells} binaries, expected {2 * len(TARGETS)}')
        sys.exit(2)
    print(f'COMPARE OK: every function of all {cells} binaries is identical after masking' if not bad
          else f'COMPARE DIFFERENCES: {bad}')
    sys.exit(1 if bad else 0)


main()
