#!/usr/bin/env python3
"""The cfg inventory gate: every `#[cfg(..)]`, `#[cfg_attr(..)]`, `#![cfg..]` and `cfg!(..)` site in src/ against a checked-in,
justified whitelist (scripts/cfg-inventory.txt).

Why. The Lean proofs are about the code the extraction sees: feature `avx2` on and `--cfg miri` (scripts/extract.py). A
`cfg` that selects between two computations makes some build run a body that the extraction did not see, unless the other
body is the one extracted. The feature-independence gate (scripts/check-feature-independence.sh) compares the extractions
of the two configurations that matter for the dispatch; this gate is the Rust-side census that makes sure nobody adds
another `cfg` that selects a computation, on the verify path or anywhere else, without a reviewer seeing it: the build fails
until the new site is written into the whitelist with a justification.

What a site is. The scan strips comments and string literals, then finds each attribute `#[cfg(P)]`, `#![cfg(P)]`,
`#[cfg_attr(P, A..)]`, `#![cfg_attr(..)]` and each `cfg!(P)`. A site is identified by

  file | form | item | predicate | attributes

where `item` is what the attribute is on (`fn name`, `mod name`, `use path`, `struct name`, `impl ..`, ..., or `stmt in fn
name` for a statement or expression inside a function body; for a block or expression inside a function it is the enclosing
function), the predicate is the cfg predicate with whitespace removed, and `attributes` is the attribute list of a
`cfg_attr`. Line numbers are not part of a site, so editing a file does not invalidate the whitelist, but adding, removing
or changing the gating of any site does.

Two kinds of site:
  * `attribute-only`: a `cfg_attr` whose attributes are all in ATTR_ONLY (`inline`, `allow`, `target_feature`, ...). It
    changes code generation or lints, not the computation, and is listed by class: one entry per (file, predicate,
    attributes) with a count. Any other attribute (`path`, `cfg`, `derive`, ...) makes the site `gating`.
  * `gating`: everything else (`#[cfg(..)]` on an item, statement or block, `cfg!(..)`, a gating `cfg_attr`). One entry per
    (file, form, item, predicate) with a count and a justification. This is the list of places where the source text
    that is compiled depends on the configuration; a new or changed entry is a review item.

The whitelist is exact: a site that is not listed, a count that differs, and a listed entry that matches no site are all
errors, and so is an entry without a justification.

Usage: python3 -I scripts/cfg_inventory.py [--root DIR] [--whitelist FILE]        check (exit 1 on any difference)
       python3 -I scripts/cfg_inventory.py --init                                 print a skeleton whitelist for the current src/
       python3 -I scripts/cfg_inventory.py --self-test
"""
import re
import sys
from collections import Counter
from pathlib import Path

ATTR_ONLY = {'inline', 'allow', 'warn', 'deny', 'forbid', 'expect', 'target_feature', 'must_use', 'cold', 'track_caller',
             'doc', 'deprecated'}


def strip_rust(text):
    """TEXT with comments, string literals and char literals replaced by spaces (newlines kept), so that cfg-looking text
    inside them is not scanned. Handles nested block comments and raw strings."""
    out, i, n = [], 0, len(text)
    def blank(s):
        return re.sub(r'[^\n]', ' ', s)
    while i < n:
        c = text[i]
        if text.startswith('//', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(blank(text[i:j])); i = j
        elif text.startswith('/*', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/*', j): depth += 1; j += 2
                elif text.startswith('*/', j): depth -= 1; j += 2
                else: j += 1
            out.append(blank(text[i:j])); i = j
        elif c == 'r' and re.match(r'r#*"', text[i:i + 4]) and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')):
            m = re.match(r'r(#*)"', text[i:])
            end = '"' + m.group(1)
            j = text.find(end, i + len(m.group(0)))
            j = n if j < 0 else j + len(end)
            out.append(blank(text[i:j])); i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append(blank(text[i:j])); i = j
        elif c == "'":
            m = re.match(r"'(?:\\.[^']*|[^\\'])'", text[i:])
            if m:  # a char literal; otherwise a lifetime
                out.append(blank(m.group(0))); i += len(m.group(0))
            else:
                out.append(c); i += 1
        else:
            out.append(c); i += 1
    return ''.join(out)


def match_close(s, i):
    """Index just past the bracket that closes the opening bracket at S[i]."""
    pairs = {'(': ')', '[': ']', '{': '}'}
    stack = [pairs[s[i]]]
    j = i + 1
    while j < len(s) and stack:
        if s[j] in pairs:
            stack.append(pairs[s[j]])
        elif s[j] == stack[-1]:
            stack.pop()
        j += 1
    if stack:
        raise ValueError('unbalanced brackets')
    return j


def split_top(s):
    """S split at top-level commas."""
    parts, depth, cur = [], 0, ''
    for ch in s:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur); cur = ''
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return parts


def squash(s):
    return re.sub(r'\s+', '', s)


FN_SPANS = re.compile(r'\bfn\s+(\w+)')
ITEM = re.compile(r'(?:pub(?:\([^)]*\))?\s+)?(?:(?:const|unsafe|async|extern\s*"[^"]*"|extern)\s+)*'
                  r'(fn|mod|struct|enum|union|static|const|use|impl|trait|type|macro_rules!|let)\b\s*([^\n{;=(<]*)')


def fn_spans(s):
    spans = []
    for m in FN_SPANS.finditer(s):
        j = m.end()
        # the body starts at the first `{` after the signature (a `;` first means a declaration without a body)
        depth = 0
        while j < len(s):
            ch = s[j]
            if ch in '([<' and ch != '<':
                depth += 1
            elif ch in ')]':
                depth -= 1
            elif depth == 0 and ch == ';':
                j = None
                break
            elif depth == 0 and ch == '{':
                break
            j += 1
        if j is None or j >= len(s):
            continue
        try:
            end = match_close(s, j)
        except ValueError:
            continue
        spans.append((j, end, m.group(1)))
    return spans


def describe_item(s, pos, spans, attr_start):
    """What the attribute that ends at S[pos] is on."""
    j = pos
    while True:  # skip whitespace and further attributes
        while j < len(s) and s[j].isspace():
            j += 1
        if s.startswith('#', j) and j + 1 < len(s) and s[j + 1] in '[!':
            k = s.index('[', j)
            j = match_close(s, k)
            continue
        break
    m = ITEM.match(s, j)
    enclosing = [name for (a, b, name) in spans if a < attr_start < b]
    if m:
        kind, rest = m.group(1), ' '.join(m.group(2).split())
        if kind == 'let':
            return f'stmt in fn {enclosing[-1]}' if enclosing else 'let'
        if kind == 'impl' or kind == 'use':
            return f'{kind} {rest[:60]}'.strip()
        return f'{kind} {rest.split()[0] if rest else ""}'.strip()
    return f'stmt in fn {enclosing[-1]}' if enclosing else 'expression'


ATTR = re.compile(r'#\s*(!?)\s*\[\s*(cfg_attr|cfg)\s*\(')
MACRO = re.compile(r'\bcfg!\s*\(')


def sites(text, rel):
    """List of site dicts for the Rust source TEXT of file REL."""
    s = strip_rust(text)
    spans = fn_spans(s)
    out = []
    for m in ATTR.finditer(s):
        open_paren = m.end() - 1
        close = match_close(s, open_paren)
        inner = text[open_paren + 1:close - 1]  # from the original: the stripped text has no string contents
        close_bracket = s.index(']', close)
        form = m.group(2)
        if form == 'cfg':
            site = dict(file=rel, form='cfg', item=describe_item(s, close_bracket + 1, spans, m.start()),
                        pred=squash(inner), attrs='')
            if m.group(1) == '!':
                site['item'] = 'crate'
        else:
            parts = split_top(inner)
            pred = squash(parts[0])
            attrs = [squash(p) for p in parts[1:]]
            names = {re.match(r'[A-Za-z_][\w:]*', a).group(0) if re.match(r'[A-Za-z_]', a) else '' for a in attrs}
            only = bool(attrs) and names <= ATTR_ONLY
            site = dict(file=rel, form='cfg_attr' if only else 'cfg_attr(gating)',
                        item='' if only else describe_item(s, close_bracket + 1, spans, m.start()),
                        pred=pred, attrs=','.join(attrs))
            if m.group(1) == '!' and not only:
                site['item'] = 'crate'
        out.append(site)
    for m in MACRO.finditer(s):
        open_paren = m.end() - 1
        close = match_close(s, open_paren)
        enclosing = [name for (a, b, name) in spans if a < m.start() < b]
        out.append(dict(file=rel, form='cfg!', item=f'expr in fn {enclosing[-1]}' if enclosing else 'expression',
                        pred=squash(text[open_paren + 1:close - 1]), attrs=''))
    return out


def scan(root):
    root = Path(root)
    found = []
    for p in sorted(root.rglob('*.rs')):
        found += sites(p.read_text(encoding='utf-8'), p.relative_to(root.parent).as_posix())
    return found


def key(site):
    return (site['file'], site['form'], site['item'], site['pred'], site['attrs'])


def fmt_entry(k, count, why='TODO'):
    f, form, item, pred, attrs = k
    lines = [f'file: {f}', f'form: {form}']
    if item:
        lines.append(f'item: {item}')
    lines.append(f'cfg: {pred}')
    if attrs:
        lines.append(f'attrs: {attrs}')
    lines += [f'count: {count}', f'why: {why}']
    return '\n'.join(lines)


def parse_whitelist(text):
    entries = {}
    for rec in re.split(r'\n\s*\n', text.strip()):
        lines = [l for l in rec.split('\n') if l.strip() and not l.lstrip().startswith('#')]
        if not lines:
            continue
        d = {}
        last = None
        for l in lines:
            m = re.match(r'(file|form|item|cfg|attrs|count|why):\s?(.*)$', l)
            if m:
                last = m.group(1)
                d[last] = m.group(2)
            elif last == 'why':
                d['why'] += ' ' + l.strip()
            else:
                raise ValueError(f'cannot parse whitelist line {l!r}')
        for need in ('file', 'form', 'cfg', 'count', 'why'):
            if need not in d:
                raise ValueError(f'whitelist entry without {need}: {rec[:120]!r}')
        k = (d['file'], d['form'], d.get('item', ''), d['cfg'], d.get('attrs', ''))
        if k in entries:
            raise ValueError(f'duplicate whitelist entry {k}')
        entries[k] = (int(d['count']), d['why'].strip())
    return entries


def check(root, whitelist_text):
    """List of error strings."""
    errors = []
    try:
        wl = parse_whitelist(whitelist_text)
    except ValueError as e:
        return [str(e)]
    have = Counter(key(s) for s in scan(root))
    for k, n in sorted(have.items()):
        if k not in wl:
            errors.append(f'new cfg site not in the whitelist ({n}x): {" | ".join(x for x in k if x)}')
        elif wl[k][0] != n:
            errors.append(f'cfg site count changed (whitelist {wl[k][0]}, now {n}): {" | ".join(x for x in k if x)}')
    for k, (n, why) in sorted(wl.items()):
        if k not in have:
            errors.append(f'whitelisted cfg site no longer exists: {" | ".join(x for x in k if x)}')
        if not why or why.upper().startswith('TODO'):
            errors.append(f'whitelist entry without a justification: {" | ".join(x for x in k if x)}')
    return errors


def self_test():
    import tempfile
    errs = []
    base = '''
#[cfg(feature = "zeroize")]
use zeroize::Zeroize;
// #[cfg(feature = "fake")] in a comment, and "#[cfg(feature = \\"fake\\")]" in a string are not sites
#[cfg_attr(all(feature = "avx2", not(miri)), inline(always))]
pub fn f(x: u32) -> u32 {
    #[cfg(feature = "zeroize")]
    x.zeroize();
    if cfg!(target_feature = "avx2") { 1 } else { 2 }
}
'''
    def run(label, src, want_ok, needle=None, wl_from=base):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t) / 'src'
            root.mkdir()
            (root / 'a.rs').write_text(wl_from)
            inv = Counter(key(s) for s in scan(root))
            wl = '\n\n'.join(fmt_entry(k, n, 'because') for k, n in sorted(inv.items()))
            (root / 'a.rs').write_text(src)
            e = check(root, wl)
            if want_ok and e:
                errs.append(f'self-test {label}: unexpected {e}')
            if not want_ok and not (e and (needle is None or any(needle in x for x in e))):
                errs.append(f'self-test {label}: not caught ({e})')
    run('unchanged', base, True)
    s0 = sites(base, 'src/a.rs')
    if len(s0) != 4:
        errs.append(f'self-test: base has {len(s0)} sites, expected 4: {s0}')
    run('a new cfg-split body', base + '\n#[cfg(feature = "avx2")]\nfn g() -> u32 { 1 }\n#[cfg(not(feature = "avx2"))]\nfn g() -> u32 { 2 }\n',
        False, 'new cfg site')
    run('a changed predicate', base.replace('target_feature = "avx2"', 'target_feature = "sse2"'), False, 'new cfg site')
    run('a removed site', base.replace('#[cfg(feature = "zeroize")]\n    x.zeroize();', 'x.zeroize();'), False, 'no longer exists')
    run('one more copy of an existing site', base.replace('    x.zeroize();', '    x.zeroize();\n    #[cfg(feature = "zeroize")]\n    x.zeroize();'),
        False, 'count changed')
    run('a cfg_attr that is not attribute-only', base + '\n#[cfg_attr(feature = "avx2", path = "x.rs")]\nmod m;\n', False, 'new cfg site')
    with tempfile.TemporaryDirectory() as t:
        root = Path(t) / 'src'
        root.mkdir()
        (root / 'a.rs').write_text(base)
        inv = Counter(key(s) for s in scan(root))
        wl = '\n\n'.join(fmt_entry(k, n) for k, n in sorted(inv.items()))
        if not any('justification' in x for x in check(root, wl)):
            errs.append('self-test: a TODO justification was accepted')
    return errs


def main(argv):
    args = argv[1:]
    repo = Path(__file__).resolve().parent.parent
    root, wl_path = repo / 'src', repo / 'scripts/cfg-inventory.txt'
    init = False
    while args:
        a = args.pop(0)
        if a == '--self-test':
            errs = self_test()
            for e in errs:
                print(e, file=sys.stderr)
            if not errs:
                print('cfg_inventory self-test OK')
            return 1 if errs else 0
        elif a == '--init':
            init = True
        elif a == '--root':
            root = Path(args.pop(0))
        elif a == '--whitelist':
            wl_path = Path(args.pop(0))
        else:
            print(__doc__, file=sys.stderr)
            return 2
    if init:
        inv = Counter(key(s) for s in scan(root))
        print('\n\n'.join(fmt_entry(k, n) for k, n in sorted(inv.items())))
        return 0
    errs = self_test()
    if errs:
        for e in errs:
            print(f'CFG INVENTORY FAIL (self-test): {e}', file=sys.stderr)
        return 1
    errs = check(root, wl_path.read_text(encoding='utf-8'))
    if errs:
        for e in errs:
            print(f'CFG INVENTORY FAIL: {e}', file=sys.stderr)
        print('CFG INVENTORY FAIL: review the change, then edit scripts/cfg-inventory.txt (see the header of '
              'scripts/cfg_inventory.py)', file=sys.stderr)
        return 1
    inv = scan(root)
    print(f'cfg inventory OK: {len(inv)} sites in {len({s["file"] for s in inv})} files, '
          f'{sum(1 for s in inv if s["form"] == "cfg_attr")} attribute-only, all in the whitelist')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
