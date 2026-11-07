#!/usr/bin/env bash
# Verify timings under nearcore's build settings: scalar verify, the dispatched (4-way AVX2) verify, and an x86-64-v3 build,
# next to aws-lc-rs and mldsa-native AVX2 as references. Run from the repository root on an otherwise idle x86_64 Linux machine:
#   bash bench/fast-verify.sh LABEL [CPU] 2>&1 | tee fast-verify-LABEL.log
# Environment: SETS (default 65; e.g. 44,65,87), ROUNDS (default 15), ML_DSA_SCRATCH (output root, as in compare.sh),
#              HT_OFFSET (distance to the hyper-thread sibling, default half the logical CPUs),
#              TOOLCHAIN (a rustup toolchain such as 1.95.0, nearcore's; default: the toolchain in effect). The numbers in
#              bench/results say which one they used.
#
# Variants (all in the `nearcore` profile of bench/Cargo.toml: opt-level 3, fat LTO, one codegen unit, abort on panic, plus
# overflow-checks, exactly as nearcore's [profile.release]; and nearcore's x86_64 target features, which do not include AVX2):
#   scalar  no `avx2` feature: the proved scalar verify.                                   RUSTFLAGS = nearcore's
#   avx2    `--features avx2`: runtime dispatch; on AVX2 hardware verify is the 4-way body. RUSTFLAGS = nearcore's
#   v3      `--features avx2` and -C target-cpu=x86-64-v3: AVX2 is static, no detection.   RUSTFLAGS = target-cpu=x86-64-v3
# The `avx2` rows are the shipping configuration: the proved 4-way body (verify::verify_internal_x4) with the AVX2 lane ops.
#
# `ours+prepared-vk verify` is the prepared-key verify: not dispatched (it runs no ExpandA), so it is the same code in all
# three variants up to the NTT dispatch. `ours verify` includes building the key's matrix every call.
set -o pipefail
L=${1:?usage: fast-verify.sh LABEL [CPU]}
SETS=${SETS:-65}
ROUNDS=${ROUNDS:-15}
OUT=${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}/fast-verify-$L
mkdir -p "$OUT"
root=$PWD
# nearcore's .cargo/config.toml, section [target.'cfg(target_arch = "x86_64")'] (same string as scripts/ci.sh).
NC_RUSTFLAGS="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
cd bench || exit 1
for v in scalar avx2 v3; do
  RF="$NC_RUSTFLAGS"; FEAT=""
  [ "$v" = avx2 ] && FEAT="--features avx2"
  [ "$v" = v3 ] && { RF="-C target-cpu=x86-64-v3"; FEAT="--features avx2"; }
  CARGO_PROFILE_NEARCORE_OVERFLOW_CHECKS=true RUSTFLAGS="$RF" cargo ${TOOLCHAIN:+"+$TOOLCHAIN"} build --profile nearcore --bin bench $FEAT \
    --message-format=json-render-diagnostics >"$OUT/$v.json" || exit 1
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
# Idleness check: only a count, no process names (they identify the machine).
ps -eo pcpu --no-headers | awk '$1 > 5 { n++ } END { print "processes above 5% CPU:", n + 0 }'
HT=${HT_OFFSET:-$(( $(nproc) / 2 ))}
CPU=${2:-$(python3 - "$HT" <<'PY'
import sys, time
HT = int(sys.argv[1])
def snap():
    d = {}
    for l in open("/proc/stat"):
        if l.startswith("cpu") and l[3].isdigit():
            f = l.split(); n = int(f[0][3:]); v = list(map(int, f[1:])); d[n] = (sum(v), v[3] + v[4])
    return d
a = snap(); time.sleep(2); b = snap()
busy = {n: 1 - (b[n][1] - a[n][1]) / max(1, (b[n][0] - a[n][0])) for n in a}
print(min(range(1, HT), key=lambda i: busy[i] + busy[i + HT]))
PY
)}
echo "pinned cpu $CPU (sibling $((CPU + HT)))"
for v in scalar avx2 v3; do
  echo "== $v $(date -u +%H:%M:%S) load $(cut -d' ' -f1-3 /proc/loadavg)"
  taskset -c "$CPU" "$OUT/bench-$v" --label "$L-$v-cpu$CPU" --sets "$SETS" --rounds "$ROUNDS" --only verify,verifying-key | tee "$OUT/$v.cpu$CPU.tsv"
done
echo "== done; load $(cut -d' ' -f1-3 /proc/loadavg)"
python3 - "$OUT" "$CPU" "$SETS" <<'PY'
import sys
out, cpu, sets = sys.argv[1], sys.argv[2], [int(x) for x in sys.argv[3].split(",")]
def load(v):
    rows = {}
    for line in open(f"{out}/{v}.cpu{cpu}.tsv"):
        f = line.rstrip("\n").split("\t")
        if f[0] == "ROW" and f[1] != "label" and f[3] in ("verify", "verifying-key"):
            rows[(int(f[2]), f[4])] = float(f[5]) / 1000
    return rows
data = {v: load(v) for v in ("scalar", "avx2", "v3")}
for st in sets:
    print(f"\nML-DSA-{st} verify, microseconds (median of rounds), nearcore profile")
    print(f"{'implementation':<28}{'scalar':>9}{'avx2':>9}{'v3':>9}")
    for imp in ("ours", "ours+verifying-key", "ours+prepared-vk", "aws-lc-rs", "mldsa-native-avx2", "libcrux-avx2", "rustcrypto"):
        if (st, imp) in data["scalar"]:
            print(f"{imp:<28}" + "".join(f"{data[v].get((st, imp), float('nan')):>9.1f}" for v in ("scalar", "avx2", "v3")))
    s, a = data["scalar"].get((st, "ours")), data["avx2"].get((st, "ours"))
    if s and a:
        print(f"ours: dispatched / scalar = {a / s:.2f}")
PY
