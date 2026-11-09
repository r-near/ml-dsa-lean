#!/usr/bin/env bash
# Compares the machine code of the checkct driver of two checkouts, function by function.
#   bash checkct/compare-code.sh build NAME      build this checkout's driver (release, as `cargo build --release -p driver`, in
#                                                the nightly the harness pins) for riscv32imac, thumbv7em and x86_64, without and with
#                                                the `avx2` feature, and keep the six binaries under $CMP_DIR/NAME
#   bash checkct/compare-code.sh compare A B     disassemble the binaries of A and B and compare every function
# CMP_DIR defaults to ~/rx/scratch/cmp. LLVM_OBJDUMP names the disassembler (default: llvm-objdump of the pinned nightly).
#
# What this is. A comparison of instruction streams with addresses masked (see checkct/compare_code.py), to show that a change of
# `src/` did not change the code of the functions BINSEC analyzes. It is NOT a constant-time verdict and it does not replace the
# BINSEC runs: the lifter, the solver and the machine model are not involved. Only the default release profile is compared, not
# the profiles with nearcore's flags.
set -euo pipefail
CMP_DIR=${CMP_DIR:-$HOME/rx/scratch/cmp}
case "${1:-}" in
build)
  name=$2
  root=$(cd "$(dirname "$0")/.." && pwd)
  cd "$root/checkct"
  for feat in none avx2; do
    if [ "$feat" = none ]; then cargo build --release -p driver; else cargo build --release -p driver --features avx2; fi
    for t in riscv32imac-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-linux-gnu; do
      mkdir -p "$CMP_DIR/$name/$feat"
      cp "target/$t/release/driver" "$CMP_DIR/$name/$feat/driver-$t"
    done
  done
  ls -l "$CMP_DIR/$name"/*/
  ;;
compare)
  exec python3 -I "$(dirname "$0")/compare_code.py" "$CMP_DIR/$2" "$CMP_DIR/$3"
  ;;
*)
  echo "usage: $0 build NAME | compare A B" >&2
  exit 2
  ;;
esac
