#!/usr/bin/env bash
# bash checkct/scan-avx2.sh DRIVER_DIR   (a directory printed as "drivers copied to ..." by checkct/select-ntt.sh)
set -o pipefail
D="$HOME/rx/scratch/${1:?driver dir name under ~/rx/scratch}"
OBJDUMP=$(ls "$HOME"/.rustup/toolchains/*/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump 2>/dev/null | head -1)
"$OBJDUMP" -d --no-show-raw-insn "$D/x86_64-unknown-linux-gnu.driver" > "$D/disasm.txt"
python3 -I "$(dirname "$0")/scan-avx2.py" "$D/disasm.txt"
