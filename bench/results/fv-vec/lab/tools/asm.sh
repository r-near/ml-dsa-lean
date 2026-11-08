#!/usr/bin/env bash
# usage: asm.sh TOOLCHAIN OUTDIR   -- emits asm for the lab lib (nearcore feature flags) and summarizes per-variant functions
set -o pipefail
TC=$1; OUT=$2; mkdir -p "$OUT"
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq"
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "$HERE/.." || exit 1
RUSTFLAGS="$NC" cargo +"$TC" rustc --release --lib --features avx2 -- --emit=asm -Cdebuginfo=0 ${EXTRA:+$EXTRA} 2>&1 | grep -E '^error' | head
rm -f target/release/deps/fvlab-*.s; touch src/lib.rs
RUSTFLAGS="$NC" cargo +"$TC" rustc --release --lib --features avx2 -- --emit=asm -Cdebuginfo=0 ${EXTRA:+$EXTRA} 2>&1 | grep -E '^error' | head
cp "$(ls -t target/release/deps/fvlab-*.s | head -1)" "$OUT/lab.s"
python3 "$HERE/summ.py" "$OUT/lab.s"
