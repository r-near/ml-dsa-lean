#!/usr/bin/env bash
# Map the leak addresses in a cargo-checkct log to source lines.
#   bash checkct/leaks.sh LOG BINDIR [OBJDUMP]
# LOG    output of checkct/run.sh (needs its "Summary:" section)
# BINDIR the OUT directory of run.sh (<target>.driver binaries built with debug info)
# OBJDUMP llvm-objdump (default: the one from the floating nightly's llvm-tools component)
set -o pipefail
LOG=$1; BINDIR=$2
OBJDUMP=${3:-$(rustc +nightly --print sysroot)/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objdump}
awk '/^Summary:/{s=1} s' "$LOG" | while read -r a b c d rest; do
  case "$a" in
    driver) tgt=$b; ep=$c; stat=$d ;;
    0x*) # "0x02cef2 has control flow leak (37.347s)"
      addr=$a
      case "$tgt" in
        riscv32imac*) bin=$BINDIR/riscv32imac-unknown-none-elf.driver ;;
        thumbv7em*) bin=$BINDIR/thumbv7em-none-eabihf.driver ;;
        x86_64*) bin=$BINDIR/x86_64-unknown-linux-gnu.driver ;;
      esac
      a_dec=$((addr))
      # "; file:line" comment lines precede the instruction they annotate; print the last one and the instruction.
      "$OBJDUMP" -d -l --no-show-raw-insn --start-address=$a_dec --stop-address=$((a_dec + 4)) "$bin" 2>/dev/null |
        awk -v ep="$ep" -v tgt="$tgt" -v addr="$addr" '
          /^; .*\.rs:[0-9]+/ { src=$0 }
          /^ +[0-9a-f]+:/ && !done { sub(/^; /,"",src); gsub(/^.*\/src\//,"src/",src); printf "%s %s %s  %s  |%s\n", ep, tgt, addr, src, $0; done=1 }'
      ;;
  esac
done
