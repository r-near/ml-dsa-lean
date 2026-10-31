#!/usr/bin/env python3
"""Copy raw job logs into experiments/simd/evidence/ with machine-specific paths scrubbed.
Usage: collect-evidence.py   (run from the worktree root; reads /tmp/simd-*.log written by the rx runs)."""
import os, re, sys

pairs = {
    "/tmp/simd-x1.log": "x1-extraction.txt",
    "/tmp/simd-x1c.log": "x1-rustc-rules.txt",
    "/tmp/simd-x2.log": "x2-extraction.txt",
    "/tmp/simd-x3.log": "x3-extraction.txt",
    "/tmp/simd-x4.log": "x4-extraction.txt",
    "/tmp/simd-x5.log": "x5-extraction.txt",
    "/tmp/simd-bench5.log": "x5-bench.txt",
    "/tmp/simd-asm-report.log": "x4-asm-report.txt",
}
out = "experiments/simd/evidence"
os.makedirs(out, exist_ok=True)

def scrub(s):
    s = re.sub(r"/Users/[^\s)\"']*?/experiments/simd", "experiments/simd", s)
    s = re.sub(r"/Users/[^\s)\"']*", "<path>", s)
    s = re.sub(r"/home/[A-Za-z0-9_.-]+", "<home>", s)
    s = re.sub(r"/data/rx/[^\s)\"']*", "<scratch>", s)
    return s

for src, dst in pairs.items():
    with open(src, errors="replace") as f:
        text = scrub(f.read())
    with open(os.path.join(out, dst), "w") as f:
        f.write(text)
for dst in ("x4-bench.txt", "x2-cfg-avx2-branch.txt"):
    p = os.path.join(out, dst)
    with open(p, errors="replace") as f:
        text = scrub(f.read())
    with open(p, "w") as f:
        f.write(text)
print("ok")
