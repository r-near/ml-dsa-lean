#!/usr/bin/env bash
# Run the step-level micro benchmark (bench/src/bin/micro.rs) pinned, with nearcore's profile and target features and the
# `avx2` dispatch. Run from the repository root on an idle x86_64 Linux machine: bash bench/micro.sh [CPU] [TOOLCHAIN]
set -o pipefail
CPU=${1:-3}
cd bench || exit 1
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
CARGO_PROFILE_NEARCORE_OVERFLOW_CHECKS=true RUSTFLAGS="$NC" cargo ${2:+"+$2"} build --profile nearcore --bin micro --features internals,avx2 \
  --message-format=json-render-diagnostics >"${TMPDIR:-/tmp}/micro.json" || exit 1
EXE=$(python3 - "${TMPDIR:-/tmp}/micro.json" <<'PY'
import json, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "micro":
        exe = m["executable"]
print(exe)
PY
)
uptime
taskset -c "$CPU" "$EXE"
