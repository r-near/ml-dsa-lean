#!/usr/bin/env bash
# Disassemble around BINSEC addresses with source lines (GNU objdump, so it runs on the box host, where llvm-objdump
# is not installed). For the "which instruction did BINSEC stop at / leak at" questions of a Summary: block.
#   bash checkct/leak-context.sh BIN ADDR [ADDR...]       BEFORE and AFTER bytes: env, default 48 and 24
# BIN is a <target>.driver copied by run-select.sh with OUT=. ADDR is the hex address BINSEC printed (0x...).
set -o pipefail
BIN=$1; shift
for a in "$@"; do
  A=$((a))
  echo "=== $a"
  objdump -d -l -C --no-show-raw-insn -M att --start-address=$((A - ${BEFORE:-48})) --stop-address=$((A + ${AFTER:-24})) "$BIN" |
    grep -v '^$' | sed -e 's|/home/opam/w/||' -e 's|/rustc/[0-9a-f]*/||' |
    awk -v a="$(printf '%x' "$A")" '{ if ($0 ~ "^ +" a ":") print "-->" $0; else print "   " $0 }'
done
