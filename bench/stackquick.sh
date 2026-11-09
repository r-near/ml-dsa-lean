#!/usr/bin/env bash
# Quick stack table for the verify functions: painted (x86_64, default and fat-LTO release builds, tools/stack/dynamic) and the
# static walk of thumbv7em (default and fat LTO, tools/stack/stackbin). KB per row; roots: verify_NN, verifying_key_NN, verify_prepared_NN.
#   bash bench/stackquick.sh [TARGETS]     TARGETS: space list of "x86 thumb" (default both)
set -o pipefail
cd "$(dirname "$0")/../tools/stack"
TC=nightly-2026-10-06
SYSROOT=$(rustc +nightly --print sysroot)
BIN=$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/bin
EXCL="core::panicking,core::slice::index,core::option::,core::result::,core::fmt::,rust_begin_unwind,panic_bounds,core::panic::"
cargo +$TC build --release -p walker 2>&1 | tail -1
mkdir -p out; cp target/release/walker out/walker-quick; WALKER=$PWD/out/walker-quick
ROWS='^\| (wrapper:)?(stk_)?(verify_(44|65|87)|verifying_key_(44|65|87)|verify_prepared_(44|65|87)) '
for V in default lto; do
  if [ "$V" = lto ]; then export CARGO_PROFILE_RELEASE_LTO=fat CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1; else unset CARGO_PROFILE_RELEASE_LTO CARGO_PROFILE_RELEASE_CODEGEN_UNITS; fi
  mkdir -p out/$V
  RUSTFLAGS="-Zemit-stack-sizes" cargo +$TC build --release -p dynamic 2>&1 | grep -E "^error|Finished" >&2
  echo "== painted x86_64 $V"; target/release/dynamic | grep -E "^dyn (verify_(44|65|87)|verifying_key_(44|65|87)|verify_prepared_(44|65|87)) " | tr '\n' ';'; echo
  for T in x86_64-unknown-linux-gnu thumbv7em-none-eabi; do
    case $T in x86*) ARCH=x86; XF="-Clinker=rust-lld -Clinker-flavor=ld.lld -Crelocation-model=static -Zplt=yes" ;; *) ARCH=thumb; XF="" ;; esac
    RUSTFLAGS="-Zemit-stack-sizes -Cdebuginfo=1 $XF" cargo +$TC build --release -p stackbin --bin stackbin --target $T \
      -Zbuild-std=core,compiler_builtins -Zbuild-std-features=compiler-builtins-mem 2>&1 | grep -E "^error|Finished" >&2
    exe=target/$T/release/stackbin
    "$BIN/llvm-readobj" --stack-sizes $exe > out/$V/$T.sizes.txt
    "$BIN/llvm-objdump" -d --no-show-raw-insn $exe > out/$V/$T.dis.txt
    echo "== static $T $V"; $WALKER elf --arch $ARCH --sizes out/$V/$T.sizes.txt --dis out/$V/$T.dis.txt --exclude "$EXCL" > out/$V/$T.report.md; grep -E "$ROWS" out/$V/$T.report.md | cut -d'|' -f2,3 | tr -d ' ' | tr '\n' ';'; echo
  done
done
