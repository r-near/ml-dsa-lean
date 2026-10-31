#!/usr/bin/env bash
# Build the nearcore-profile `bench` at the default target, with the crate's `avx2` feature (runtime dispatch), and at
# x86-64-v3 from the current tree, pick the idlest
# physical core (cpu i and its hyper-thread sibling i+30 both idle), and run both pinned. Run on the build box from
# the repository root:
#   rx submit ntt-bench -- 'set -o pipefail; bash bench/compare.sh LABEL [CPU] 2>&1 | tee bench-LABEL.log'
# CPU (default: the idlest core, chosen at run time) pins both runs; pass the same CPU to compare two trees.
# Output: $HOME/rx/scratch/ntt-bench-LABEL/{default,avx2,v3}.cpuN.tsv (same TSV as bench/run.sh).
# Check `uptime` and `rx ps` first: the numbers are only comparable when the box is otherwise quiet.
set -o pipefail
L=${1:?usage: compare.sh LABEL}
OUT=$HOME/rx/scratch/ntt-bench-$L
mkdir -p "$OUT"
root=$PWD
cd bench || exit 1
for v in default avx2 v3; do
  RF=""; FEAT=""
  [ "$v" = v3 ] && RF="-C target-cpu=x86-64-v3"
  [ "$v" = avx2 ] && FEAT="--features avx2"
  RUSTFLAGS="$RF" cargo build --profile nearcore --bin bench $FEAT --message-format=json-render-diagnostics >"$OUT/$v.json" || exit 1
  python3 - "$OUT/$v.json" "$OUT/bench-$v" <<'PY'
import json, shutil, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "bench":
        exe = m["executable"]
shutil.copy(exe, sys.argv[2])
PY
done
cd "$root" || exit 1
uptime
ps -eo pcpu,psr,comm --sort=-pcpu | head -6
CPU=${2:-$(python3 - <<'PY'
import time
def snap():
    d = {}
    for l in open("/proc/stat"):
        if l.startswith("cpu") and l[3].isdigit():
            f = l.split(); n = int(f[0][3:]); v = list(map(int, f[1:])); d[n] = (sum(v), v[3] + v[4])
    return d
a = snap(); time.sleep(2); b = snap()
busy = {n: 1 - (b[n][1] - a[n][1]) / max(1, (b[n][0] - a[n][0])) for n in a}
print(min(range(1, 30), key=lambda i: busy[i] + busy[i + 30]))
PY
)}
echo "pinned cpu $CPU (sibling $((CPU + 30)))"
for v in default avx2 v3; do
  echo "== $v $(date -u +%H:%M:%S) load $(cut -d' ' -f1-3 /proc/loadavg)"
  taskset -c "$CPU" "$OUT/bench-$v" --label "$L-$v-cpu$CPU" | tee "$OUT/$v.cpu$CPU.tsv"
done
echo "== done; load $(cut -d' ' -f1-3 /proc/loadavg)"
