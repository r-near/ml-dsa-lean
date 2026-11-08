#!/usr/bin/env bash
# usage: remarks.sh TOOLCHAIN  -- SLP/loop-vectorize remarks for the lab lib (nearcore flags)
TC=$1
cd "$(dirname "$0")/.." || exit 1
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq"
touch src/lib.rs
RUSTFLAGS="$NC" cargo +"$TC" rustc --release --lib --features avx2 -- --emit=asm -Cdebuginfo=1 -Cremark=slp-vectorizer,loop-vectorize,loop-unroll -Cllvm-args=-pass-remarks-missed=slp-vectorizer 2>&1 | grep -E 'remark|note: ' | sed -e 's#^.*/src/#src/#' | sort | uniq -c | sort -rn | head -${2:-40}
