#!/usr/bin/env python3
"""Fails if the theorem counts that README.md states differ from the theorem lists they describe.

The README says "N Lean theorems ... (listed in `lean/headline-theorems.txt`), and M more for the 4-way verify
(`lean/fast-verify-theorems.txt`, `lean/keccak4-theorems.txt`)". N is the number of names in headline-theorems.txt and M the
number in the other two lists together. A name is a line that is not blank, not a comment (`#`) and not an `import`.
The lists may grow; the README must follow them in the same commit.

Usage: python3 -I scripts/check-readme-counts.py [--self-test]
"""
import re
import sys
from pathlib import Path


def names(path):
    return [l.strip() for l in Path(path).read_text(encoding='utf-8').splitlines()
            if l.strip() and not l.lstrip().startswith(('#', 'import '))]


PATTERN = re.compile(r'(\d+) Lean theorems,[^()]*\(listed in `lean/headline-theorems\.txt`\),\s+and\s+(\d+) more for the 4-way verify\s+'
                     r'\(`lean/fast-verify-theorems\.txt`,\s*`lean/keccak4-theorems\.txt`\)')


def check(readme_text, n_headline, n_more):
    m = PATTERN.search(readme_text)
    if not m:
        return ['README.md no longer has the sentence this gate reads ("N Lean theorems ... and M more for the 4-way verify"): '
                'update scripts/check-readme-counts.py with it']
    errs = []
    if int(m.group(1)) != n_headline:
        errs.append(f'README.md says {m.group(1)} headline theorems; lean/headline-theorems.txt has {n_headline}')
    if int(m.group(2)) != n_more:
        errs.append(f'README.md says {m.group(2)} more for the 4-way verify; fast-verify-theorems.txt + keccak4-theorems.txt have {n_more}')
    return errs


def self_test():
    text = ('- **Proof.** 412 Lean theorems, from the top-level API down to the arithmetic (listed in `lean/headline-theorems.txt`), and\n'
            '  88 more for the 4-way verify (`lean/fast-verify-theorems.txt`, `lean/keccak4-theorems.txt`).\n')
    errs = []
    if check(text, 412, 88):
        errs.append('self-test: a matching README was rejected')
    if not check(text, 412, 108):
        errs.append('self-test: a stale "88 more" was accepted')
    if not check(text, 413, 88):
        errs.append('self-test: a stale headline count was accepted')
    if not check('nothing', 1, 1):
        errs.append('self-test: a README without the sentence was accepted')
    return errs


def main(argv):
    errs = self_test()
    if '--self-test' in argv:
        print('\n'.join(errs) or 'check-readme-counts self-test OK')
        return 1 if errs else 0
    if errs:
        print('\n'.join(errs), file=sys.stderr)
        return 1
    repo = Path(__file__).resolve().parent.parent
    nh = len(names(repo / 'lean/headline-theorems.txt'))
    nm = len(names(repo / 'lean/fast-verify-theorems.txt')) + len(names(repo / 'lean/keccak4-theorems.txt'))
    errs = check((repo / 'README.md').read_text(encoding='utf-8'), nh, nm)
    for e in errs:
        print(f'README COUNTS FAIL: {e}', file=sys.stderr)
    if errs:
        return 1
    print(f'README counts OK: {nh} headline theorems, {nm} more (fast-verify + keccak4)')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
