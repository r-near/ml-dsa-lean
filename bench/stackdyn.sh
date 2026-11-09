#!/usr/bin/env bash
# usage: dyn.sh VARIANT(default|lto) ; builds dynamic harness with stack sizes, runs it
set -o pipefail
cd "$(dirname "$0")/../tools/stack"
TC=nightly-2026-10-06
SYSROOT=$(rustc +nightly --print sysroot)
BIN=$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/bin
V=$1
if [ "$V" = lto ]; then export CARGO_PROFILE_RELEASE_LTO=fat CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1; fi
RUSTFLAGS="${DYN_RUSTFLAGS--Zemit-stack-sizes}" cargo +$TC build --release -p dynamic 2>&1 | grep -E "^error|Finished" 
mkdir -p out/$V
"$BIN/llvm-readobj" --stack-sizes target/release/dynamic > out/$V/dynamic.sizes.txt
target/release/dynamic | tee out/$V/dynamic.txt | grep -E "dyn (verify_(44|65|87)|verifying_key_[0-9]+|verify_prepared_[0-9]+|verify_internal_[0-9]+) |baseline"
echo "--- biggest frames"
python3 - out/$V/dynamic.sizes.txt <<'PY'
import re,sys
rows=[];n=None
for l in open(sys.argv[1]):
    m=re.match(r'\s*Functions: \[(.*)\]',l)
    m=re.match(r'\s*Name: (.*)',l)
    if m: n=m.group(1).strip()
    m=re.match(r'\s*Size: (0x[0-9A-Fa-f]+)',l)
    if m and n: rows.append((int(m.group(1),16),n)); n=None
rows.sort(reverse=True)
for s,n in rows[:25]: print(s,n)
PY
