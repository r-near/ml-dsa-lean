#!/usr/bin/env python3
"""The cfg inventory gate: every construct in src/ that can select what gets compiled or read at compile time, against a
checked-in, justified whitelist (scripts/cfg-inventory.txt).

Why. The Lean proofs are about the code the extraction sees: feature `avx2` on and `--cfg miri` (scripts/extract.py). A
`cfg` that selects between two computations makes some build run a body that the extraction did not see, unless the other
body is the one extracted. The feature-independence gate (scripts/check-feature-independence.sh) compares the extractions
of the two configurations that matter for the dispatch; this gate is the Rust-side census that makes sure nobody adds
another construct that selects a computation, on the verify path or anywhere else, without a reviewer seeing it: the build
fails until the new site is written into the whitelist with a justification.

How it reads the source. The scan blanks comments and string, byte-string, C-string and character literals (nested block
comments, raw strings with any number of `#`, `br"` and `cr"` prefixes, lifetimes versus character literals), keeping every
offset. In the blanked text it finds, whatever whitespace or comments sit between the tokens:
  * attributes `#[cfg(P)]`, `#![cfg(P)]`, `#[cfg_attr(P, A..)]`, `#![cfg_attr(..)]` (any of `(`, `[`, `{` as the delimiter);
  * macros `cfg!`, `cfg_if!`, `cfg_match!`, `cfg_select!`, `env!`, `option_env!`, `include!`, `include_bytes!`, `include_str!`
    and `is_*_feature_detected!` (the name, optionally behind a path such as `core::` or `$crate::`, then `!`, then any of
    `(`, `[`, `{`);
  * a plain `#[path = ".."]` attribute (the module file is chosen by the attribute, not by `mod`);
  * a `macro_rules!` definition whose body mentions `cfg`, `cfg_attr`, `cfg_if`, `cfg_match` or `cfg_select` (the cfg inside is
    text that the call sites feed; its sites are reported as `in macro_rules NAME`);
  * every other `cfg` or `cfg_attr` identifier in code (a bare `cfg(..)` argument of a macro, a raw identifier `r#cfg`, anything
    the patterns above do not recognize), form `cfg-token`, so a spelling the patterns miss still shows up;
  * a build script: `build.rs` next to Cargo.toml, or a `build = ".."` key in it (a build script can emit `cargo:rustc-cfg`).
A scan that finds no Rust file, or no site at all, fails: a gate that parses zero sites passes vacuously.

What a site is. A site is identified by

  file | form | item | predicate | attributes

where `item` is what the attribute is on (`fn name`, `mod name`, `use path`, `struct name`, `impl ..`, ..., or `stmt in fn
name` for a statement or expression inside a function body; for a block or expression inside a function it is the enclosing
function), the predicate is the cfg predicate (or the macro arguments) with whitespace removed, and `attributes` is the
attribute list of a `cfg_attr`. Line numbers are not part of a site, so editing a file does not invalidate the whitelist, but
adding, removing or changing the gating of any site does.

Two kinds of site:
  * `attribute-only`: a `cfg_attr` whose attributes are all in ATTR_ONLY (`inline`, `allow`, `target_feature`, ...). It
    changes code generation or lints, not the computation, and is listed by class: one entry per (file, predicate,
    attributes) with a count. Any other attribute (`path`, `cfg`, `derive`, ...) makes the site `gating`.
  * `gating`: everything else (`#[cfg(..)]` on an item, statement or block, `cfg!(..)`, a gating `cfg_attr`, a `#[path]`, an
    `env!`, ...). One entry per (file, form, item, predicate) with a count and a justification. This is the list of places
    where the source text that is compiled depends on the configuration; a new or changed entry is a review item.

The whitelist is exact: a site that is not listed, a count that differs, and a listed entry that matches no site are all
errors, and so is an entry without a justification.

The self-test (run first by every invocation, and by `--self-test`) holds the negative fixtures: the audited counterexample
`if cfg! { not(miri) } { return false; }` with the variants `cfg ! [..]`, a comment between the tokens, the attribute forms
with whitespace, `cfg_if!`, `env!`, `include!`, `is_*_feature_detected!`, `#[path]`, `macro_rules!` with cfg, a build script,
lexer traps (raw strings that would hide a site from a naive scanner), and an empty scan. Each must be reported; text that only
looks like a site (a raw string, a doc comment, a longer identifier) must not.

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


CHAR_LIT = re.compile(r"'(?:\\\\.[^']*|[^\\\\'])'")
RAW_OPEN = re.compile(r'(?:br|cr|r)(#*)"')


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
        elif c in 'rbc' and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == '_')) and RAW_OPEN.match(text, i):
            m = RAW_OPEN.match(text, i)
            end = '"' + m.group(1)
            j = text.find(end, m.end())
            j = n if j < 0 else j + len(end)
            out.append(blank(text[i:j])); i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            j = min(j + 1, n)
            out.append(blank(text[i:j])); i = j
        elif c == "'":
            m = CHAR_LIT.match(text, i)
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


ATTR = re.compile(r'#\s*(!?)\s*\[\s*(cfg_attr|cfg)\s*[(\[{]')
PATH_ATTR = re.compile(r'#\s*(!?)\s*\[\s*path\s*=')
# Macros that select or read something at compile time. A path prefix (`core::cfg!`, `$crate::env!`) is allowed.
MACRO_NAMES = (r'cfg|cfg_if|cfg_match|cfg_select|env|option_env|include|include_bytes|include_str'
               r'|is_[A-Za-z0-9_]+_feature_detected|[A-Za-z0-9_]*feature_detected')
MACRO = re.compile(r'(?<![\w$])(?:[A-Za-z_$][\w$]*\s*::\s*)*(' + MACRO_NAMES + r')\s*!\s*[(\[{]')
MACRO_RULES = re.compile(r'(?<![\w$])macro_rules\s*!\s*(\w+)\s*[(\[{]')
CFG_IDENT = re.compile(r'(?<![\w$])(?:cfg_attr|cfg)(?!\w)')
CFG_WORD = re.compile(r'(?<![\w$])(?:cfg|cfg_attr|cfg_if|cfg_match|cfg_select)(?!\w)')


def sites(text, rel):
    """List of site dicts for the Rust source TEXT of file REL."""
    s = strip_rust(text)
    spans = fn_spans(s)
    macro_spans = []
    for m in MACRO_RULES.finditer(s):
        try:
            macro_spans.append((m.end() - 1, match_close(s, m.end() - 1), m.group(1)))
        except ValueError:
            pass
    def where(pos):
        """The enclosing macro_rules definition, if any (its body is text, not code of a function)."""
        inside = [name for (a, b, name) in macro_spans if a < pos < b]
        return inside[-1] if inside else None
    def enclosing_item(pos):
        mac = where(pos)
        if mac:
            return f'in macro_rules {mac}'
        enclosing = [name for (a, b, name) in spans if a < pos < b]
        return enclosing[-1] if enclosing else None
    def item_of(pos_after, attr_start):
        mac = where(attr_start)
        if mac:
            return f'in macro_rules {mac}'
        return describe_item(s, pos_after, spans, attr_start)
    out, covered = [], []
    for m in ATTR.finditer(s):
        open_paren = m.end() - 1
        close = match_close(s, open_paren)
        inner = text[open_paren + 1:close - 1]  # from the original: the stripped text has no string contents
        close_bracket = s.index(']', close)
        covered.append((m.start(), close_bracket + 1))
        form = m.group(2)
        if form == 'cfg':
            site = dict(file=rel, form='cfg', item=item_of(close_bracket + 1, m.start()), pred=squash(inner), attrs='')
            if m.group(1) == '!':
                site['item'] = 'crate'
        else:
            parts = split_top(inner)
            pred = squash(parts[0])
            attrs = [squash(p) for p in parts[1:]]
            names = {re.match(r'[A-Za-z_][\w:]*', a).group(0) if re.match(r'[A-Za-z_]', a) else '' for a in attrs}
            only = bool(attrs) and names <= ATTR_ONLY
            site = dict(file=rel, form='cfg_attr' if only else 'cfg_attr(gating)',
                        item='' if only else item_of(close_bracket + 1, m.start()),
                        pred=pred, attrs=','.join(attrs))
            if m.group(1) == '!' and not only:
                site['item'] = 'crate'
        out.append(site)
    for m in PATH_ATTR.finditer(s):
        open_bracket = s.index('[', m.start())
        close = match_close(s, open_bracket)
        covered.append((m.start(), close))
        out.append(dict(file=rel, form='path', item=item_of(close, m.start()),
                        pred=squash(text[m.end():close - 1]), attrs=''))
    for m in MACRO.finditer(s):
        name = m.group(1)
        open_paren = m.end() - 1
        close = match_close(s, open_paren)
        if name == 'cfg':
            covered.append((m.start(), close))
        encl = enclosing_item(m.start())
        if encl is None:
            item = 'expression'
        elif encl.startswith('in macro_rules'):
            item = encl
        else:
            item = f'expr in fn {encl}'
        out.append(dict(file=rel, form=f'{name}!', item=item, pred=squash(text[open_paren + 1:close - 1]), attrs=''))
    for m in MACRO_RULES.finditer(s):
        try:
            close = match_close(s, m.end() - 1)
        except ValueError:
            continue
        if CFG_WORD.search(s[m.end():close]):
            out.append(dict(file=rel, form='macro_rules(cfg)', item=f'macro_rules {m.group(1)}', pred='body contains cfg', attrs=''))
    # Every other `cfg` or `cfg_attr` identifier in code (a bare `cfg(..)` argument of a macro, a raw identifier, anything the
    # forms above did not recognize) is a site too, so a spelling the patterns miss still shows up here.
    for m in CFG_IDENT.finditer(s):
        if any(a <= m.start() < b for (a, b) in covered):
            continue
        encl = enclosing_item(m.start())
        item = 'expression' if encl is None else (encl if encl.startswith('in macro_rules') else f'expr in fn {encl}')
        out.append(dict(file=rel, form='cfg-token', item=item, pred=squash(text[m.start():m.start() + 48]), attrs=''))
    return out


def build_sites(repo):
    """Sites for a build script: `build.rs` at the crate root, or a `build =` key in Cargo.toml. A build script can emit
    `cargo:rustc-cfg`, so it selects code the extraction does not see."""
    import tomllib
    repo = Path(repo)
    out = []
    if (repo / 'build.rs').exists():
        out.append(dict(file='build.rs', form='build-script', item='build.rs', pred='exists', attrs=''))
    manifest = repo / 'Cargo.toml'
    if manifest.exists():
        pkg = tomllib.loads(manifest.read_text(encoding='utf-8')).get('package', {})
        b = pkg.get('build')
        if b not in (None, False):
            out.append(dict(file='Cargo.toml', form='build-script', item='package.build', pred=squash(str(b)), attrs=''))
    return out


def scan(root):
    root = Path(root)
    found = []
    for p in sorted(root.rglob('*.rs')):
        found += sites(p.read_text(encoding='utf-8'), p.relative_to(root.parent).as_posix())
    return found + build_sites(root.parent)


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
    root = Path(root)
    if not root.is_dir() or not any(root.rglob('*.rs')):
        return [f'no Rust source under {root.name}/ to scan: a gate that scans nothing passes vacuously']
    have = Counter(key(s) for s in scan(root))
    if not have:
        errors.append(f'the scan found no cfg site at all in {root.name}/: the scanner is broken or the path is wrong '
                      f'(a gate that parses zero sites passes vacuously)')
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
    def run(label, src, want_ok, needle=None, extra=None):
        """Whitelist = the sites of BASE; then SRC (and the EXTRA files, name -> text, next to src/) is checked against it."""
        with tempfile.TemporaryDirectory() as t:
            root = Path(t) / 'src'
            root.mkdir()
            (root / 'a.rs').write_text(base)
            inv = Counter(key(s) for s in scan(root))
            wl = '\n\n'.join(fmt_entry(k, n, 'because') for k, n in sorted(inv.items()))
            (root / 'a.rs').write_text(src)
            for name, text in (extra or {}).items():
                (Path(t) / name).write_text(text)
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
    # The audited counterexample (a verify function with a body that only some builds run) and the spellings around it. Each is
    # appended to BASE, so each must be reported as a site that is not in the whitelist.
    counter = 'pub fn verify_internal_with(x: u32) -> bool {\n    if cfg! { not(miri) } { return false; }\n    x > 0\n}\n'
    spellings = {
        'the audited counterexample: cfg! with braces': counter,
        'cfg! with brackets': counter.replace('cfg! { not(miri) }', 'cfg![not(miri)]'),
        'cfg ! [..] with spaces': counter.replace('cfg! { not(miri) }', 'cfg ! [ not(miri) ]'),
        'a block comment between the tokens': counter.replace('cfg! { not(miri) }', 'cfg /* c */ ! /* d */ { not(miri) }'),
        'a line comment between the tokens': counter.replace('cfg! { not(miri) }', 'cfg // c\n    ! { not(miri) }'),
        'a path prefix': counter.replace('cfg! { not(miri) }', 'core::cfg!(not(miri))'),
        'a $crate path prefix': counter.replace('cfg! { not(miri) }', '$crate :: cfg ! (not(miri))'),
        'an attribute with spaces': '# [ cfg ( not ( miri ) ) ]\nfn h() {}\n',
        'an attribute with a comment inside': '#[/* c */ cfg(not(miri))]\nfn h() {}\n',
        'an inner attribute': '#![cfg(not(miri))]\n',
        'an inner attribute with spaces': '# ! [ cfg ( not(miri) ) ]\n',
        'cfg_attr with spaces': '# [ cfg_attr ( not(miri) , path = "y.rs" ) ]\nmod y;\n',
        'cfg_attr with attributes only': '# [ cfg_attr ( not(miri) , inline(never) ) ]\nfn h() {}\n',
        'a cfg attribute with brackets': '#[cfg[not(miri)]]\nfn h() {}\n',
        'a cfg attribute with braces': '#[cfg{not(miri)}]\nfn h() {}\n',
        'a cfg_attr that gates a cfg': '#[cfg_attr(miri, cfg(any()))]\nfn h() {}\n',
        'a raw identifier': 'fn h() -> bool { let r#cfg = true; r#cfg }\n',
        'cfg_if!': 'cfg_if::cfg_if! { if #[cfg(miri)] { fn h() {} } else { fn h() -> u8 { 1 } } }\n',
        'cfg_if! alone': 'cfg_if! { if miri { fn h() {} } }\n',
        'cfg_match!': 'cfg_match! { cfg(miri) => { fn h() {} } _ => { fn h() -> u8 { 1 } } }\n',
        'cfg_select!': 'cfg_select! { miri => { fn h() {} } _ => { fn h() -> u8 { 1 } } }\n',
        'a bare cfg argument of another macro': 'macro_rules! m { ($c:meta) => { #[$c] fn h() {} } }\nm!(cfg(miri));\n',
        'env!': 'const E: &str = env!("PROFILE");\n',
        'option_env!': 'const E: Option<&str> = option_env!("PROFILE");\n',
        'std::env!': 'const E: &str = std::env!("PROFILE");\n',
        'include!': 'include!("other.rs");\n',
        'include_str!': 'const E: &str = include_str!("x.txt");\n',
        'include_bytes!': 'const E: &[u8] = include_bytes!("x.bin");\n',
        'is_x86_feature_detected!': 'fn h() -> bool { is_x86_feature_detected!("avx2") }\n',
        'std::arch::is_x86_feature_detected!': 'fn h() -> bool { std::arch::is_x86_feature_detected!("avx2") }\n',
        'is_aarch64_feature_detected!': 'fn h() -> bool { is_aarch64_feature_detected!("neon") }\n',
        'a plain #[path]': '#[path = "x.rs"]\nmod x;\n',
        'a macro_rules! with cfg in its body': 'macro_rules! m { () => { #[cfg(miri)] fn h() {} } }\n',
        'a macro_rules! that builds a cfg_attr': 'macro_rules! m { () => { #[cfg_attr(miri, inline)] fn h() {} } }\n',
        # The lexer: a raw string with a trailing backslash (a normal string would take `\"` as an escape and swallow the next
        # `cfg!`), more hashes than four characters of lookahead, a byte raw string, a c raw string, a raw string holding quotes.
        'after a raw byte string ending in a backslash': 'fn h() -> bool { let _s = br#"\\"#; if cfg!(not(miri)) { return false; } true }\n',
        'after a raw string with three hashes': 'fn h() -> bool { let _s = r###"a"##b"###; if cfg!(not(miri)) { return false; } true }\n',
        'after a raw C string': 'fn h() -> bool { let _s = cr#"\\"#; if cfg!(not(miri)) { return false; } true }\n',
        'after a char literal quote': "fn h() -> bool { let _q = '\"'; if cfg!(not(miri)) { return false; } true }\n",
        'after a lifetime': "fn h<'a>(x: &'a u8) -> bool { if cfg!(not(miri)) { return false; } *x > 0 }\n",
        'after a nested block comment': 'fn h() -> bool { /* a /* b */ c */ if cfg!(not(miri)) { return false; } true }\n',
    }
    for label, extra in spellings.items():
        run(label, base + '\n' + extra, False, 'new cfg site')
    # Text that only looks like a site must not be one.
    inert = {
        'cfg! in a raw string': 'const S: &str = r##"cfg!(x) "# #[cfg(y)]"##;\n',
        'cfg! in a raw byte string': 'const S: &[u8] = br#"cfg!(x)"#;\n',
        'cfg! in a nested block comment': '/* a /* cfg!(x) */ cfg!(y) */\nfn h() {}\n',
        'cfg in a doc comment': '/// `#[cfg(x)]` and cfg!(y)\nfn h() {}\n',
        'cfg in a string with an escaped quote': 'const S: &str = "a\\" cfg!(x)";\n',
        'a longer identifier': 'fn h(cfg_len: u8, my_cfg: u8, cfgx: u8) -> u8 { cfg_len + my_cfg + cfgx }\n',
        'a character literal': "fn h() -> char { '\"' }\n",
    }
    for label, extra in inert.items():
        run(label, base + '\n' + extra, True)
    # A build script, by file and by Cargo.toml key.
    run('a build.rs', base, False, 'new cfg site', extra={'build.rs': 'fn main() { println!("cargo:rustc-cfg=foo"); }\n'})
    run('a build key in Cargo.toml', base, False, 'new cfg site',
        extra={'Cargo.toml': '[package]\nname = "x"\nversion = "0.0.0"\nbuild = "gen.rs"\n'})
    run('Cargo.toml without a build script', base, True, extra={'Cargo.toml': '[package]\nname = "x"\nversion = "0.0.0"\nbuild = false\n'})
    with tempfile.TemporaryDirectory() as t:
        root = Path(t) / 'src'
        root.mkdir()
        (root / 'a.rs').write_text(base)
        inv = Counter(key(s) for s in scan(root))
        wl = '\n\n'.join(fmt_entry(k, n) for k, n in sorted(inv.items()))
        if not any('justification' in x for x in check(root, wl)):
            errs.append('self-test: a TODO justification was accepted')
    # A scan that parses zero sites must fail, not pass: a source tree without any cfg site, one without any Rust file, a
    # missing directory, and a whitelist that is empty or lists sites that do not exist.
    with tempfile.TemporaryDirectory() as t:
        root = Path(t) / 'src'
        root.mkdir()
        e = check(root, '')
        if not any('no Rust source' in x for x in e):
            errs.append(f'self-test: an empty src/ with an empty whitelist passed ({e})')
        (root / 'a.rs').write_text('pub fn f() -> u8 { 1 }\n')
        e = check(root, '')
        if not any('no cfg site at all' in x for x in e):
            errs.append(f'self-test: a source tree without any cfg site and an empty whitelist passed ({e})')
        e = check(Path(t) / 'missing', '')
        if not any('no Rust source' in x for x in e):
            errs.append(f'self-test: a missing src/ passed ({e})')
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
