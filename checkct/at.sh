#!/usr/bin/env bash
# Disassemble around an address of a driver built by checkct/select-ntt.sh:
#   bash checkct/at.sh MODE ADDR [CONTEXT_BYTES]     MODE = default | dispatch | avx2 | navx2
set -o pipefail
case "$1" in
  default) D=ntt-ct-out ;; dispatch) D=ntt-ct-out-dispatch ;; avx2) D=ntt-ct-out-avx2 ;; navx2) D=ntt-ct-out-navx2 ;;
  *) D=$1 ;;
esac
BIN="$HOME/rx/scratch/$D/x86_64-unknown-linux-gnu.driver"
ADDR=$2; N=${3:-24}
OBJDUMP=$(ls "$HOME"/.rustup/toolchains/*/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump 2>/dev/null | head -1)
[ -z "$OBJDUMP" ] && OBJDUMP=$(command -v llvm-objdump objdump | head -1)
a=$((ADDR))
"$OBJDUMP" -d -l --start-address=$((a - N)) --stop-address=$((a + N)) "$BIN" 2>&1 | tail -30
