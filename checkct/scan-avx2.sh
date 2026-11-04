#!/usr/bin/env bash
# bash checkct/scan-avx2.sh DRIVER_DIR   (a directory printed as "drivers copied to ..." by checkct/select-ntt.sh dispatch,
# given as a name under $ML_DSA_SCRATCH, default ${XDG_CACHE_HOME:-~/.cache}/ml-dsa-lean/scratch). Needs a driver built with the dispatch (PROFILE=dispatch or nearcore-dispatch);
# fails if the disassembly has no `*_avx2` function, which is what the default build and the static-AVX2 profiles give.
set -o pipefail
SCRATCH="${ML_DSA_SCRATCH:-${XDG_CACHE_HOME:-$HOME/.cache}/ml-dsa-lean/scratch}"
D="$SCRATCH/${1:?driver dir name under $SCRATCH}"
OBJDUMP=$(ls "$HOME"/.rustup/toolchains/*/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump 2>/dev/null | head -1)
[ -n "$OBJDUMP" ] || { echo "scan-avx2: no llvm-objdump under ~/.rustup/toolchains" >&2; exit 1; }
"$OBJDUMP" -d --no-show-raw-insn "$D/x86_64-unknown-linux-gnu.driver" > "$D/disasm.txt" || exit 1
n=$(grep -Ec '^[0-9a-f]+ <[^>]*_avx2[^>]*>:$' "$D/disasm.txt")
if [ "$n" -eq 0 ]; then
  echo "scan-avx2: FAILED: no *_avx2 function in $D/x86_64-unknown-linux-gnu.driver (built without the dispatch? use PROFILE=dispatch)" >&2
  exit 1
fi
echo "scan-avx2: $n *_avx2 functions found"
python3 -I "$(dirname "$0")/scan-avx2.py" "$D/disasm.txt"
