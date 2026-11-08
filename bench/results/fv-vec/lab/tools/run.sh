#!/usr/bin/env bash
# usage: run.sh TOOLCHAIN [variant...]   -- asm summary + timing of the lab variants under nearcore flags
set -o pipefail
TC=$1; shift
cd "$(dirname "$0")/.." || exit 1
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq ${RUSTFLAGS_EXTRA:-}"
echo "== toolchain $TC: $(rustc +$TC -V)"
bash tools/asm.sh "$TC" "${TMPDIR:-/tmp}/fvlab-asm-$TC" || exit 1
RUSTFLAGS="$NC" cargo +"$TC" build --release --features avx2 --bin bench --message-format=json-render-diagnostics >"${TMPDIR:-/tmp}/fvlab-$TC.json" || exit 1
EXE=$(python3 -c "
import json,sys
e=None
for l in open('${TMPDIR:-/tmp}/fvlab-$TC.json'):
    try: m=json.loads(l)
    except ValueError: continue
    if m.get('reason')=='compiler-artifact' and m.get('executable') and m['target']['name']=='bench': e=m['executable']
print(e)")
taskset -c "${CPU:-20}" "$EXE" "$@"
