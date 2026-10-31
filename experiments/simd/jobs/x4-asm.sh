#!/usr/bin/env bash
# Why does the crate's NTT not vectorize at x86-64-v3? Emit LLVM loop-vectorizer remarks and asm for
# (1) the x4_ntt crate (verbatim copies of src/field.rs and src/ntt.rs plus the rewrites) and
# (2) the real crate (src/ only; the check below confirms the copies are identical).
set -o pipefail
out="$HOME/rx/scratch/simd-asm"; rm -rf "$out"; mkdir -p "$out"
for f in field ntt; do cmp src/$f.rs experiments/simd/x4_ntt/src/$f.rs && echo "copy of src/$f.rs is identical"; done
export RUSTFLAGS="-C target-cpu=x86-64-v3 -C debuginfo=1 -C remark=loop-vectorize -C remark=slp-vectorizer -C llvm-args=-pass-remarks-missed=loop-vectorize -C llvm-args=-pass-remarks-analysis=loop-vectorize"
echo "RUSTFLAGS=$RUSTFLAGS"
( cd experiments/simd/x4_ntt && cargo rustc --release --lib -- --emit asm ) > "$out/x4.build.txt" 2>&1
echo "x4 build rc=$?"
cp experiments/simd/x4_ntt/target/release/deps/x4_ntt-*.s "$out/x4_v3.s"
( cargo rustc --release --lib --features internals -- --emit asm ) > "$out/real.build.txt" 2>&1
echo "real build rc=$?"
cp target/release/deps/ml_dsa_verified-*.s "$out/real_v3.s"
wc -l "$out"/*
