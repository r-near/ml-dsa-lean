#!/usr/bin/env bash
# Runs inside the ct-binsec container (started by aarch64.sh). Env: ONLY, TIMEOUT, JOBS.
set -o pipefail
mkdir /home/opam/w && cp -r /src/src /src/checkct /src/Cargo.toml /home/opam/w/ || exit 1
rm -rf /home/opam/w/checkct/target
cd /home/opam/w/checkct && eval "$(opam env)"
T=aarch64-unknown-linux-gnu
export CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static${NONEON:+ -C target-feature=-neon,-fp-armv8}"
cargo build --release -p driver --target $T 2>&1 | tail -3
B=/home/opam/w/checkct/target/$T/release/driver
export B
test -f "$B" || { echo "build failed"; exit 1; }
SECS=$(readelf -SW "$B" | sed 's/^ *\[ *[0-9]*\] *//' |
  awk '$2!="NOBITS" && $2!="NULL" && $2!="NOTE" && $0 ~ / [A-Z]*A[A-Z]* +[0-9]+ +[0-9]+ +[0-9]+$/ {print $1}' |
  grep -v '^\.note' | paste -sd, | sed 's/,/, /g')
echo "sections: $SECS"
readelf -sW "$B" > /tmp/syms.txt
grep -o '__checkct_entrypoint_descriptor__[A-Za-z0-9_]*' /tmp/syms.txt | sed 's/.*__//' | sort -u > /tmp/names.txt
mkdir -p /tmp/a64
: > /tmp/todo.txt
while read -r n; do
  echo "$n" | grep -Eq "$ONLY" || continue
  sym=$(awk '$4=="FUNC"{print $8}' /tmp/syms.txt | grep -E "^_RNvNtC[A-Za-z0-9]+_6driver[0-9]+(probes|extra|signing|prepared|split)[0-9]+${n}\$" | head -1)
  [ -z "$sym" ] && { echo "no symbol for $n"; continue; }
  cat > /tmp/a64/$n.binsec <<S
load sections $SECS from file
starting from <$sym>
with concrete stack pointer
x30 := 0x8badf00d
replace <__checkct_private_rand> () by
    res<64> := secret
    return res
end
replace <__checkct_public_rand> () by
    res<64> := nondet
    return res
end
halt at <__checkct_panic>
halt at 0x8badf00d
explore all
S
  echo "$n" >> /tmp/todo.txt
done < /tmp/names.txt
echo "selected $(wc -l < /tmp/todo.txt) probes"
run_one() {
  n=$1
  out=$(binsec -sse -checkct -sse-depth 1000000000 -sse-jump-enum 64 -sse-script /tmp/a64/$n.binsec -sse-timeout "$TIMEOUT" \
    -checkct-leak-info instr -isa aarch64 -checkct-features control-flow,memory-access,dividend,divisor "$B" 2>&1)
  st=$(echo "$out" | sed -n 's/.*Program status is : \([a-z]*\).*/\1/p' | head -1)
  {
    echo "  driver  aarch64-unknown-linux-gnu  driver::$n  ${st:-error}"
    echo "$out" | sed -n 's/.*\[checkct:result\] Instruction \(.*\)/      \1/p'
    [ -z "$st" ] && echo "$out" | grep -v '^ *$' | tail -6 | sed 's/^/      err: /'
    echo "$out" | grep -E 'checks pass|visited instructions \(unrolled\)|pending paths|branching points' | sed 's/^ */      stat: /'
    # Why a probe is not secure (as run-select.sh): the timeout line, or the lifter's "uninterpreted"/"unknown" cut.
    [ "$st" = secure ] || echo "$out" | grep -iE 'timeout has left|uninterpreted|cut path|unsupported|undefined|not executable|cannot' | sort | uniq -c | sort -rn | head -6 | sed 's/^ */      note: /'
  }> /tmp/a64/$n.out
  echo "done $n ${st:-error}"
}
export -f run_one
xargs -r -P "$JOBS" -L1 bash -c 'run_one $0' < /tmp/todo.txt
echo "Summary:"
cat /tmp/a64/*.out
if [ -d /out ]; then cp "$B" /out/aarch64-unknown-linux-gnu.driver; fi
