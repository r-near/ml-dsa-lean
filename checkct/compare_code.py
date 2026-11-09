#!/usr/bin/env python3
"""Function-by-function comparison of two sets of checkct driver binaries (checkct/compare-code.sh).

Usage: compare_code.py DIR_A DIR_B     (each holds none/driver-TARGET and avx2/driver-TARGET)

For every binary the text is disassembled with `llvm-objdump -d`. A function is the block under a `ADDR <name>:` label. Masked
before comparing: the leading address of each line (and the raw bytes), hexadecimal immediates and branch targets that
look like addresses (`0x` followed by at least 5 hex digits), the `<symbol+off>` operand annotations, and the 16-hex-digit
hash of a Rust legacy symbol (`17h...E`). Function names are compared with the hash removed. Reported per binary: the number
of functions in each, those only in one side, and those whose masked text differs. Exit 1 when anything differs.

Scope: the masked instruction stream. It is not a proof that two binaries behave alike (a masked immediate could differ in a
way that matters) and not a constant-time result; it is a quick reason to expect that BINSEC would see the same code.
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


def functions(path):
    out = subprocess.run([OBJDUMP, '-d', '--no-show-raw-insn', path], capture_output=True, text=True, check=True).stdout
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
    return fns


def main():
    a, b = sys.argv[1:3]
    bad = 0
    for feat in ('none', 'avx2'):
        for t in TARGETS:
            fa, fb = functions(f'{a}/{feat}/driver-{t}'), functions(f'{b}/{feat}/driver-{t}')
            only_a, only_b = sorted(set(fa) - set(fb)), sorted(set(fb) - set(fa))
            diff = sorted(n for n in set(fa) & set(fb) if fa[n] != fb[n])
            print(f'{feat:5} {t:30} functions {len(fa)} / {len(fb)}: identical {len(set(fa) & set(fb)) - len(diff)}, '
                  f'differ {len(diff)}, only in A {len(only_a)}, only in B {len(only_b)}')
            for n in diff[:20]:
                print(f'    differs: {n}')
            for n in only_a[:20]:
                print(f'    only in A: {n}')
            for n in only_b[:20]:
                print(f'    only in B: {n}')
            bad += len(diff) + len(only_a) + len(only_b)
    print('COMPARE OK: every function is identical after masking' if not bad else f'COMPARE DIFFERENCES: {bad}')
    sys.exit(1 if bad else 0)


main()
