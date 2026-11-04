#!/usr/bin/env bash
# Stack measurement for the public api functions. From the repository root:
#   rx submit stack -- 'set -o pipefail; bash tools/stack/run.sh 2>&1 | tee stack.log'
# Output goes to tools/stack/out/<variant>/ (ignored by git) and to stdout.
#
# Two build variants, because inlining decides the frame sizes:
#   default  the release profile of this workspace: codegen-units = 16, no LTO
#   lto      codegen-units = 1 and fat LTO (what a size/speed-tuned downstream binary tends to use)
set -o pipefail
cd "$(dirname "$0")"
TC=nightly-2026-10-06
# LLVM tools come from the floating nightly (the pinned toolchain does not ship llvm-tools).
SYSROOT=$(rustc +nightly --print sysroot)
BIN=$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/bin
test -x "$BIN/llvm-objdump" || { echo "llvm-objdump not found in $BIN"; exit 1; }

COMMON="-Zemit-stack-sizes -Cdebuginfo=1"
EXCL="core::panicking,core::slice::index,core::option::,core::result::,core::fmt::,rust_begin_unwind,panic_bounds,core::panic::"
cargo +$TC build --release -p walker 2>&1 | tail -1
WALKER=$PWD/target/release/walker

elf_target() { # name triple extra-rustflags
  local name=$1 triple=$2 extra=$3
  echo "=== building $triple ($VARIANT)"
  RUSTFLAGS="$COMMON $extra" cargo +$TC build --release -p stackbin --bin stackbin --target "$triple" \
    -Zbuild-std=core,compiler_builtins -Zbuild-std-features=compiler-builtins-mem 2>&1 | grep -E "^error|warning: unused|Finished" || return 1
  local exe=target/$triple/release/stackbin
  "$BIN/llvm-readobj" --stack-sizes "$exe" > $OUT/$name.sizes.txt
  "$BIN/llvm-objdump" -d --no-show-raw-insn "$exe" > $OUT/$name.dis.txt
}

run_variant() {
  VARIANT=$1
  OUT=out/$VARIANT
  mkdir -p $OUT
  elf_target x86_64 x86_64-unknown-linux-gnu "-Clinker=rust-lld -Clinker-flavor=ld.lld -Crelocation-model=static -Zplt=yes"
  elf_target thumbv7em thumbv7em-none-eabi ""
  elf_target riscv32 riscv32imac-unknown-none-elf ""

  echo "=== building wasm32-unknown-unknown ($VARIANT)"
  RUSTFLAGS="$COMMON" cargo +$TC rustc --release -p stackbin --lib --crate-type cdylib --target wasm32-unknown-unknown \
    -Zbuild-std=core,compiler_builtins 2>&1 | grep -E "^error|Finished"
  "$BIN/llvm-objdump" -d --no-show-raw-insn target/wasm32-unknown-unknown/release/stackbin.wasm > $OUT/wasm32.dis.txt

  echo "=== building the dynamic harness with stack sizes ($VARIANT)"
  RUSTFLAGS="-Zemit-stack-sizes" cargo +$TC build --release -p dynamic 2>&1 | grep -E "^error|Finished"
  "$BIN/llvm-readobj" --stack-sizes target/release/dynamic > $OUT/dynamic.sizes.txt
  "$BIN/llvm-objdump" -d --no-show-raw-insn target/release/dynamic > $OUT/dynamic.dis.txt

  echo "--- dynamic symbols bound by the std harness (GOT calls in its disassembly go to these)"
  "$BIN/llvm-readobj" --dyn-relocations target/release/dynamic | grep -E "GLOB_DAT|JUMP_SLOT" | awk '{print $3}' | sort | uniq -c | tr '\n' ' '; echo
  echo; echo "################ [$VARIANT] x86_64-unknown-linux-gnu"
  $WALKER elf --arch x86 --sizes $OUT/x86_64.sizes.txt --dis $OUT/x86_64.dis.txt --exclude "$EXCL" | tee $OUT/x86_64.report.md
  echo "################ [$VARIANT] thumbv7em-none-eabi"
  $WALKER elf --arch thumb --sizes $OUT/thumbv7em.sizes.txt --dis $OUT/thumbv7em.dis.txt --exclude "$EXCL" | tee $OUT/thumbv7em.report.md
  echo "################ [$VARIANT] riscv32imac-unknown-none-elf"
  $WALKER elf --arch riscv --sizes $OUT/riscv32.sizes.txt --dis $OUT/riscv32.dis.txt --exclude "$EXCL" | tee $OUT/riscv32.report.md
  echo "################ [$VARIANT] wasm32-unknown-unknown"
  $WALKER wasm --dis $OUT/wasm32.dis.txt --exclude "$EXCL" | tee $OUT/wasm32.report.md
  echo "################ [$VARIANT] static walk of the dynamic harness binary (x86_64, std)"
  $WALKER elf --arch x86 --sizes $OUT/dynamic.sizes.txt --dis $OUT/dynamic.dis.txt --exclude "$EXCL" | tee $OUT/dynamic-static.report.md

  echo "################ [$VARIANT] dynamic (x86_64 stack painting, only -Zemit-stack-sizes, so the same code as the static walk above)"
  target/release/dynamic | tee $OUT/dynamic.txt

  echo "=== building the dynamic harness with no extra compiler flags ($VARIANT)"
  RUSTFLAGS="" cargo +$TC build --release -p dynamic 2>&1 | grep -E "^error|Finished"
  echo "################ [$VARIANT] dynamic (x86_64 stack painting, plain release build)"
  target/release/dynamic | tee $OUT/dynamic-plain.txt
}

run_variant default
(
  export CARGO_PROFILE_RELEASE_LTO=fat CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1
  run_variant lto
)

echo "################ dynamic (x86_64 stack painting), dev profile (opt-level 0, debug assertions): cargo test and debug builds"
mkdir -p out
RUSTFLAGS="" cargo +$TC build -p dynamic 2>&1 | grep -E "^error|Finished"
target/debug/dynamic | tee out/dynamic-debug.txt

echo "################ allocas (x86_64 optimized IR of the library, codegen-units = 1)"
mkdir -p out
cargo +$TC rustc --release -p ml-dsa-lean --lib --target x86_64-unknown-linux-gnu -- \
  --emit=llvm-ir=$PWD/out/lib.ll -Zfewer-names=no 2>&1 | tail -1
$WALKER allocas --ll out/lib.ll --min 1024 | tee out/allocas.md
