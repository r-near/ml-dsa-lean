#!/usr/bin/env python3
"""Run the Cryptol side over every vector file of a run directory, in parallel.

    run_theirs.py RUN [--jobs N] [--only REGEX]

For each `name chunk` of RUN/vec/manifest.txt whose RUN/theirs/<name>.out does not exist yet, the lines of
RUN/vec/<name>.txt are cut into chunks of `chunk` lines, each chunk is evaluated by one `cryptol_eval.py`
process (one Cryptol start-up per chunk), and the outputs are merged in order.  The slowest chunks are
started first.  Timing per chunk goes to RUN/theirs/timing.log.
"""
import argparse
import concurrent.futures as cf
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def cost(name):
    s = int(re.search(r"(44|65|87)", name).group(1)) if re.search(r"(44|65|87)", name) else 44
    w = {"ver": 6, "verx": 6, "sgn": 12, "sgi": 12, "kg": 3, "kgo": 3, "kgt": 3, "exa": 2}.get(name.split("_")[0], 1)
    return w * (s / 44.0)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("DIFF_JOBS", "40")))
    ap.add_argument("--only", default="")
    a = ap.parse_args()
    run = a.run
    os.makedirs(os.path.join(run, "theirs"), exist_ok=True)
    jobs = []
    names = []
    for ln in open(os.path.join(run, "vec", "manifest.txt")):
        f = ln.split()
        if not f:
            continue
        name, chunk = f[0], int(f[1])
        if len(f) > 2 and f[2] == "oursonly":
            continue
        if a.only and not re.search(a.only, name):
            continue
        if os.path.exists(os.path.join(run, "theirs", name + ".out")):
            continue
        lines = [x for x in open(os.path.join(run, "vec", name + ".txt")).read().split("\n") if x.strip()]
        cd = os.path.join(run, "theirs", "chunks", name)
        os.makedirs(cd, exist_ok=True)
        for ci, first in enumerate(range(0, len(lines), chunk)):
            cp = os.path.join(cd, f"{ci:06d}.txt")
            with open(cp, "w") as fh:
                fh.write("\n".join(lines[first:first + chunk]) + "\n")
            jobs.append((cost(name) * (1 + 0.01 * len(lines[first:first + chunk])), name, ci, first, cp))
        names.append((name, (len(lines) + chunk - 1) // chunk))
    jobs.sort(key=lambda j: -j[0])
    print(f"{len(jobs)} chunks in {len(names)} files, {a.jobs} jobs", file=sys.stderr)
    tlog = open(os.path.join(run, "theirs", "timing.log"), "a")
    t0 = time.time()

    def work(j):
        _, name, ci, first, cp = j
        t = time.time()
        subprocess.run([sys.executable, "-I", os.path.join(HERE, "cryptol_eval.py"), cp, str(first), cp + ".out", cp + ".err"],
                       check=False)
        tlog.write(f"{name} {ci} {time.time() - t:.1f}\n")
        tlog.flush()
        return name

    done = 0
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for _ in ex.map(work, jobs):
            done += 1
            if done % 50 == 0:
                print(f"  {done}/{len(jobs)} chunks, {time.time() - t0:.0f} s", file=sys.stderr)
    for name, nch in names:
        cd = os.path.join(run, "theirs", "chunks", name)
        with open(os.path.join(run, "theirs", name + ".out"), "w") as fh:
            for ci in range(nch):
                p = os.path.join(cd, f"{ci:06d}.txt.out")
                fh.write(open(p).read() if os.path.exists(p) else "CRYPTOL-ERROR\n")
    print(f"theirs done in {time.time() - t0:.0f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
