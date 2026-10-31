#!/usr/bin/env bash
# Run run-prepared.sh with the same arguments, keep its log, and map every leak address of its Summary to file:line with
# leaks.sh (the driver binaries are copied to OUT by run-select.sh). From the repository root:
#   rx submit pk-ct -- bash checkct/prepared-leaks.sh 'prepared__census' 'x86_64-unknown-linux-gnu thumbv7em-none-eabihf' 600
set -o pipefail
OUT="${OUT:-$HOME/rx/scratch/pk-ct/bin}"
export OUT
LOG="${LOG:-$HOME/rx/scratch/pk-ct/prepared.log}"
mkdir -p "$(dirname "$LOG")"
bash checkct/run-prepared.sh "$@" 2>&1 | tee "$LOG"
echo "=== leak sites"
OBJDUMP="$(ls "$HOME"/.rustup/toolchains/nightly-2026-10-06-*/lib/rustlib/*/bin/llvm-objdump 2>/dev/null | head -1)"
bash checkct/leaks.sh "$LOG" "$OUT" ${OBJDUMP:+"$OBJDUMP"}
