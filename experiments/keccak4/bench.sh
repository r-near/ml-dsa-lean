#!/usr/bin/env bash
# Phase 0: build keccak4 at the default target and at x86-64-v3, run pinned to one quiet core, count vector asm.
# Usage: bash experiments/keccak4/bench.sh
set -o pipefail
cd experiments/keccak4 || exit 1
out="$HOME/rx/scratch/keccak4-out"; rm -rf "$out"; mkdir -p "$out"
cpu=$(python3 ../simd/jobs/pick-cpu.py)
unset RUSTFLAGS
cargo build --release 2>&1 | tail -2; [ "${PIPESTATUS[0]}" -eq 0 ] || exit 1
cp target/release/keccak4 "$out/bench-default"
RUSTFLAGS="-C target-cpu=x86-64-v3" cargo build --release 2>&1 | tail -2; [ "${PIPESTATUS[0]}" -eq 0 ] || exit 1
cp target/release/keccak4 "$out/bench-v3"
echo "load: $(cut -d' ' -f1-3 /proc/loadavg); cpu $cpu: $(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2)"
for rep in 1 2; do
  for v in default v3; do
    taskset -c "$cpu" "$out/bench-$v" "$v-r$rep" 2>&1 | grep -v '^$'
  done
done
count() { # file
  echo "lines $(wc -l < "$1") | ymm: vpxor $(grep -c 'vpxor.*ymm' "$1") vpsllq $(grep -c 'vpsllq.*ymm' "$1") vpsrlq $(grep -c 'vpsrlq.*ymm' "$1") vpandn $(grep -c 'vpandn.*ymm' "$1") vpor $(grep -c 'vpor.*ymm' "$1") | xmm: pxor $(grep -cE '\bp?xor.*xmm' "$1") psllq $(grep -cE 'psllq.*xmm' "$1") | scalar: rol/ror $(grep -cE '\b(rol|ror)x?q' "$1") xorq $(grep -c 'xorq' "$1") | extract/insert: $(grep -cE 'vpextrq|vpinsrq|vextracti128|vinserti128' "$1")"
}
extract() { # asmfile fn out
  awk -v f="$2" '$0 ~ ("^_RNv.*7keccak4[0-9]+" f ":$") {p=1} p {print} p && /^\.Lfunc_end/ {exit}' "$1" > "$3"
}
for tag in v3 default; do
  if [ $tag = v3 ]; then RUSTFLAGS="-C target-cpu=x86-64-v3" cargo rustc --release --lib -- --emit asm="$out/$tag.s" 2>&1 | tail -1
  else RUSTFLAGS="" cargo rustc --release --lib -- --emit asm="$out/$tag.s" 2>&1 | tail -1; fi
  for f in x4_v2_default x4_v2_avx2 x4_v4_default x4_v4_avx2 x4_v5_default x4_v5_avx2 x4_v6_default x4_v7_default x4_v7_avx2 x4_v2a_default x4_v2a_avx2 x4_v2c_default x4_v2c_avx2 scalar4; do
    extract "$out/$tag.s" "$f" "$out/$f.$tag.s"
    echo "== $f ($tag build): $(count "$out/$f.$tag.s")"
  done
done
