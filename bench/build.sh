#!/usr/bin/env bash
# Builds the `bench` binary in four variants and copies them to $1 (as bench-VARIANT; micro and prof are built
# after them as micro-release-default and prof-profiling):
#   release-default    cargo's release profile, default target-cpu
#   nearcore-default   opt-level 3, fat LTO, 1 codegen unit, panic = abort; default target-cpu
#   release-native     release with RUSTFLAGS=-C target-cpu=native
#   nearcore-native    nearcore profile with RUSTFLAGS=-C target-cpu=native
#   nearcore-v3        nearcore profile with RUSTFLAGS=-C target-cpu=x86-64-v3 (AVX2, BMI2, FMA; no AVX-512)
# mldsa-native's C and assembly are built by crosscheck's build.rs (gcc -O3, default architecture, no LTO) and
# are the same in all four variants; RUSTFLAGS does not reach them. Usage: bench/build.sh OUTDIR [extra]
# (`extra` builds only micro, prof and nearcore-v3).
set -euo pipefail
out=${1:?usage: build.sh OUTDIR}
mkdir -p "$out"
cd "$(dirname "$0")"

build() { # name profile rustflags [bin [cargo args...]]
  local name=$1 profile=$2 rf=$3 bin=${4:-bench}
  shift $(( $# < 4 ? $# : 4 ))
  echo "== build $bin $name (profile=$profile RUSTFLAGS='$rf' $*)"
  RUSTFLAGS="$rf" cargo build --profile "$profile" --bin "$bin" "$@" --message-format=json-render-diagnostics >"$out/$name.$bin.json"
  python3 - "$out/$name.$bin.json" "$out/$bin-$name" "$bin" <<'PY'
import json, shutil, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == sys.argv[3]:
        exe = m["executable"]
shutil.copy(exe, sys.argv[2])
print("->", sys.argv[2])
PY
}

if [ "${2:-all}" != "extra" ]; then
  build release-default release ""
  build nearcore-default nearcore ""
  build release-native release "-C target-cpu=native"
  build nearcore-native nearcore "-C target-cpu=native"
fi
build nearcore-v3 nearcore "-C target-cpu=x86-64-v3"

# Step microbenchmarks and the sampling profiler (not part of the headline numbers). The profiler needs symbols
# and frame pointers.
build release-default release "" micro --features internals
build native release "-C target-cpu=native" micro --features internals
build v3 release "-C target-cpu=x86-64-v3" micro --features internals
build profiling profiling "-C force-frame-pointers=yes" prof --features prof
