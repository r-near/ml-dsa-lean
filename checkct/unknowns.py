#!/usr/bin/env python3
"""For every probe of a run-select.sh "Summary:" block (or /tmp/sel.*.out files), print its status and, for every
instruction BINSEC named, the address, function, source line and instruction: leak lines ("0x... has ... leak") and cut
paths ('[sse:error] Cut path N (uninterpreted "KO") @ 0x...'). x86_64 only; needs GNU objdump (the box host has it).

    python3 -I checkct/unknowns.py BIN LOG_OR_SEL_FILE...      BIN: the <target>.driver copied by OUT=
"""
import re, subprocess, sys

binary, logs = sys.argv[1], sys.argv[2:]
dis = subprocess.run(["objdump", "-d", "-l", "-C", "--no-show-raw-insn", "-M", "att", binary],
                     capture_output=True, text=True, check=True).stdout.splitlines()
# address -> (function, source, instruction)
table, fn, src = {}, "", ""
for line in dis:
    m = re.match(r"^[0-9a-f]+ <(.*)>:$", line)
    if m:
        fn = m.group(1); continue
    m = re.match(r"^(\S.*\.rs):(\d+)", line)
    if m:
        s = m.group(1)
        s = re.sub(r"^.*?/(src/(?:ml-dsa|.*))$", r"\1", s) if False else s
        s = re.sub(r"^/home/opam/\.rustup/toolchains/[^/]*/lib/rustlib/src/rust/", "", s)
        s = s.replace("/home/opam/w/", "").replace("checkct/driver/src/../../../", "")
        src = f"{s}:{m.group(2)}"; continue
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", line)
    if m:
        table[int(m.group(1), 16)] = (fn, src, m.group(2).strip())
    elif re.match(r"^\S.*:$", line):
        fn = line.rstrip(":")          # inlined-function marker lines of objdump -l

def show(addr):
    fn, src, ins = table.get(addr, ("?", "?", "?"))
    return f"{addr:#x}  {ins}   [{src}]   in {fn}"

emit = False
for path in logs:
    for line in open(path, errors="replace"):
        line = line.rstrip("\n")
        if line.startswith("Summary:"):
            emit = True; continue
        if not (emit or line.startswith("  driver ")):
            continue
        m = re.match(r"^  driver\s+(\S+)\s+(\S+)\s+(\S+)", line)
        if m:
            print(f"\n{m.group(2)}  {m.group(3)}"); continue
        m = re.match(r"^\s+(0x[0-9a-f]+) has (.*) leak", line)
        if m:
            print("   leak  " + show(int(m.group(1), 16))); continue
        m = re.search(r"Cut path.*@ (0x[0-9a-f]+)", line)
        if m:
            print("   cut   " + show(int(m.group(1), 16))); continue
        if re.search(r"stat: (pending paths|\[checkct:info\] \d+ / \d+ control|visited instructions \(unrolled\))", line):
            print("   " + line.strip())
