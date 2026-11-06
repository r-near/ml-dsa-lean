#!/usr/bin/env python3
"""One tab-separated row per probe from the "Summary:" block of a run-select.sh / aarch64.sh log, sorted by module, then probe name (driver::extra, ::prepared, ::probes, ::signing, ::split):

    probe  verdict  pending paths  visited instructions  control-flow checks passed/total  <memory-access checks | details>

The last column is the memory-access check count when no UNKNOWNS file is given (thumbv7em, riscv32imac, AArch64), and
otherwise the leaks and cut paths of the probe, "leak|cut <mnemonic> <address> <source line> <function>" joined by "; "
(x86_64: the file is the output of unknowns.py on the same log, which names each address; empty for a probe with
neither). These are the `*.verdicts.tsv` files of checkct/results/sweep-*/. The generator of sweep-15b4ce2's files
was not kept; this script reproduces their format (checked: it regenerates the thumbv7em, riscv32imac and AArch64 files
of that sweep byte for byte from their summary logs). The x86_64 details column lists at most three leaks per probe, which is
how the 15b4ce2 files read (inferred from them); the `.unknowns.txt` files are the full record.

    python3 -I checkct/verdicts-tsv.py LOG [UNKNOWNS_TXT] > TARGET.verdicts.tsv
"""
import re
import sys

log = sys.argv[1]
unk = sys.argv[2] if len(sys.argv) > 2 else None

probes = {}
cur = None
emit = False
for line in open(log, errors="replace"):
    line = line.rstrip("\n")
    if line.startswith("Summary:"):
        emit, cur = True, None  # a later block of the same log replaces the rows of the probes it repeats
        continue
    if not emit:
        continue
    m = re.match(r"^  driver\s+(\S+)\s+(\S+)\s+(\S+)", line)
    if m:
        name = m.group(2).split("::")[-1]
        cur = probes.setdefault(name, {"full": m.group(2), "verdict": m.group(3), "pending": "", "instr": "", "cf": "", "mem": ""})
        continue
    if cur is None:
        continue
    m = re.search(r"pending paths\s+(\d+)", line)
    if m:
        cur["pending"] = m.group(1)
    m = re.search(r"visited instructions \(unrolled\)\s+(\d+)", line)
    if m:
        cur["instr"] = m.group(1)
    m = re.search(r"(\d+ / \d+) control flow checks pass", line)
    if m:
        cur["cf"] = m.group(1).replace(" ", "")
    m = re.search(r"(\d+ / \d+) memory access checks pass", line)
    if m:
        cur["mem"] = m.group(1).replace(" ", "")

details = {}
if unk:
    cur = None
    for line in open(unk, errors="replace"):
        line = line.rstrip("\n")
        m = re.match(r"^(driver::\S+)\s+\S+$", line)
        if m:
            cur = m.group(1).split("::")[-1]
            details[cur] = []
            continue
        m = re.match(r"^   (leak|cut)\s+(0x[0-9a-f]+)\s+(\S+)\s.*?\[([^\]]*)\]\s+in (.*)$", line)
        if m and cur:
            details[cur].append(f"{m.group(1)} {m.group(3)} {m.group(2)} {m.group(4)} {m.group(5)}")

for name in sorted(probes, key=lambda n: probes[n]["full"]):
    p = probes[name]
    last = "; ".join(details.get(name, [])[:3]) if unk else p["mem"]  # at most the first three leaks, as in sweep-15b4ce2
    print("\t".join([name, p["verdict"], p["pending"], p["instr"], p["cf"], last]))
