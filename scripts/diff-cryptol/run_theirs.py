#!/usr/bin/env python3
"""Run the Cryptol side over every vector file of a run directory, in parallel.

    run_theirs.py RUN [--jobs N] [--only REGEX] [--digests FILE]

For each `name chunk` of RUN/vec/manifest.txt whose output RUN/theirs/<name>.out is missing or not bound (see
common.py: `<name>.stamp`) to the current vector file and to the current evaluator, the lines of RUN/vec/<name>.txt are
cut into chunks of `chunk` lines, each chunk is evaluated by one `cryptol_eval.py` process (one Cryptol start-up per
chunk), and the outputs are merged in order.  The slowest chunks are started first.  Timing per chunk goes to
RUN/theirs/timing.log.

The evaluator identity bound into each stamp is the digest of `cryptol_eval.py`, `common.py`, `cry/*.cry`, the digests
of the Cryptol binaries (see below), the commit of the cryptol-specs clone and the chunk size.  A worker that exits
nonzero or times out fails the file it belongs to: no merged output and no stamp are written for that file, the failure
is reported and the exit status is 1.  Merged outputs are renamed into place only when complete.

Before anything runs, every file of `$CRYPTOL_TOOLS/cryptol/bin` listed in FILE (default `cryptol-3.6.0.bin.sha256`
next to this script, written from the verified release archive) is checked against its digest.
"""
import argparse
import concurrent.futures as cf
import glob
import os
import re
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from common import digest_parts, sha256_file, stamp_ok, write_stamp  # noqa: E402

TOOLS = os.environ.get("CRYPTOL_TOOLS", os.path.expanduser("~/rx/scratch/cryptol-tools"))


def cost(name):
    s = int(re.search(r"(44|65|87)", name).group(1)) if re.search(r"(44|65|87)", name) else 44
    w = {"ver": 6, "verx": 6, "sgn": 12, "sgi": 12, "kg": 3, "kgo": 3, "kgt": 3, "exa": 2}.get(name.split("_")[0], 1)
    return w * (s / 44.0)


def verify_binaries(digests):
    """Check the installed Cryptol binaries against the digests recorded from the verified archive."""
    bad = []
    n = 0
    with open(digests) as fh:
        for ln in fh:
            if not ln.strip():
                continue
            want, rel = ln.split(None, 1)
            rel = rel.strip().lstrip("*")
            p = os.path.join(TOOLS, "cryptol", rel)
            n += 1
            if not os.path.isfile(p) or sha256_file(p) != want:
                bad.append(rel)
    if n == 0 or bad:
        sys.exit(f"run_theirs: the installed Cryptol does not match {digests} ({'empty digest file' if n == 0 else ', '.join(bad)}); "
                 "re-run setup.sh")


def evaluator_identity(digests):
    parts = [sha256_file(os.path.join(HERE, f)) for f in ("cryptol_eval.py", "common.py")]
    parts += [sha256_file(p) for p in sorted(glob.glob(os.path.join(HERE, "cry", "*.cry")))]
    parts.append(sha256_file(digests))
    specs = os.path.join(TOOLS, "src", "cryptol-specs")
    r = subprocess.run(["git", "-C", specs, "rev-parse", "HEAD"], capture_output=True, text=True)
    parts.append(r.stdout.strip() if r.returncode == 0 else "no-git")
    return digest_parts(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("run")
    ap.add_argument("--jobs", type=int, default=int(os.environ.get("DIFF_JOBS", "40")))
    ap.add_argument("--only", default="")
    ap.add_argument("--digests", default=os.path.join(HERE, "cryptol-3.6.0.bin.sha256"))
    a = ap.parse_args()
    run = a.run
    verify_binaries(a.digests)
    ident = evaluator_identity(a.digests)
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
        vp = os.path.join(run, "vec", name + ".txt")
        out = os.path.join(run, "theirs", name + ".out")
        tool = f"{ident}:{chunk}"
        if stamp_ok(out, vp, tool):
            continue
        for p in (out, out[:-4] + ".stamp"):   # whatever is there is not bound to these inputs
            if os.path.exists(p):
                os.remove(p)
        lines = [x for x in open(vp).read().split("\n") if x.strip()]
        cd = os.path.join(run, "theirs", "chunks", name)
        shutil.rmtree(cd, ignore_errors=True)
        os.makedirs(cd)
        for ci, first in enumerate(range(0, len(lines), chunk)):
            cp = os.path.join(cd, f"{ci:06d}.txt")
            with open(cp, "w") as fh:
                fh.write("\n".join(lines[first:first + chunk]) + "\n")
            jobs.append((cost(name) * (1 + 0.01 * len(lines[first:first + chunk])), name, ci, first, cp))
        names.append((name, (len(lines) + chunk - 1) // chunk, vp, out, tool))
    jobs.sort(key=lambda j: -j[0])
    print(f"{len(jobs)} chunks in {len(names)} files, {a.jobs} jobs", file=sys.stderr)
    tlog = open(os.path.join(run, "theirs", "timing.log"), "a")
    t0 = time.time()

    def work(j):
        _, name, ci, first, cp = j
        t = time.time()
        rc = subprocess.run([sys.executable, "-I", os.path.join(HERE, "cryptol_eval.py"), cp, str(first), cp + ".out", cp + ".err"],
                            check=False).returncode
        tlog.write(f"{name} {ci} {time.time() - t:.1f} rc={rc}\n")
        tlog.flush()
        return name, ci, rc

    done = 0
    failed = {}
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for name, ci, rc in ex.map(work, jobs):
            if rc != 0:
                failed.setdefault(name, []).append((ci, rc))
            done += 1
            if done % 50 == 0:
                print(f"  {done}/{len(jobs)} chunks, {time.time() - t0:.0f} s", file=sys.stderr)
    for name, nch, vp, out, tool in names:
        cd = os.path.join(run, "theirs", "chunks", name)
        missing = [ci for ci in range(nch) if not os.path.exists(os.path.join(cd, f"{ci:06d}.txt.out"))]
        if name in failed or missing:
            if name not in failed:
                failed[name] = [(ci, "no output") for ci in missing]
            continue
        with open(out + ".tmp", "w") as fh:
            for ci in range(nch):
                fh.write(open(os.path.join(cd, f"{ci:06d}.txt.out")).read())
        os.replace(out + ".tmp", out)
        write_stamp(out, vp, tool)
    if failed:
        print(f"CRYPTOL WORKER FAILURES in {len(failed)} files, no output written for them (exit 2: Cryptol exited nonzero, "
              "3: timeout; the .err next to the chunk has Cryptol's text):", file=sys.stderr)
        for name in sorted(failed):
            cd = os.path.join(run, "theirs", "chunks", name)
            for ci, rc in failed[name][:5]:
                print(f"  {name} chunk {ci}: {rc}  ({os.path.join(cd, f'{ci:06d}.txt.err')})", file=sys.stderr)
        sys.exit(1)
    print(f"theirs done in {time.time() - t0:.0f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
