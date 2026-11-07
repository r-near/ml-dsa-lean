#!/usr/bin/env bash
# ns per 4-way Keccak-f[1600] permutation (AVX2 lane operations) and ExpandA-65 time, under nearcore's profile and target
# features. Run from the repository root on an idle x86_64 Linux machine: bash bench/keccak4.sh [CPU] [TOOLCHAIN]
set -o pipefail
CPU=${1:-3}
cd bench || exit 1
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
RUSTFLAGS="$NC" cargo ${2:+"+$2"} build --profile nearcore --bin keccak4 --bin expanda --features internals,avx2 \
  --message-format=json-render-diagnostics >"${TMPDIR:-/tmp}/k4.json" || exit 1
exe() {
  python3 - "${TMPDIR:-/tmp}/k4.json" "$1" <<'PY'
import json, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == sys.argv[2]:
        exe = m["executable"]
print(exe)
PY
}
uptime
for i in 1 2 3; do taskset -c "$CPU" "$(exe keccak4)"; done
taskset -c "$CPU" "$(exe expanda)"
