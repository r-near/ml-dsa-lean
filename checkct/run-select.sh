#!/usr/bin/env bash
# Re-run selected probes with a long timeout (cargo-checkct has no entrypoint filter). From the repository root:
#   rx submit ct4 -- 'set -o pipefail; ONLY="hint_step|vec_power2round" TIMEOUT=7200 bash checkct/run-select.sh 2>&1 | tee sel.log'
# Environment:
#   ONLY     extended regex over the entrypoint names (driver__module__probe); required
#   TIMEOUT  seconds per probe (default 7200)
#   TARGETS  space separated target list (default: all three)
#   JOBS     parallel BINSEC instances (default 16; a probe killed at the memory cap reports "error", never "secure")
#   OUT      as in run.sh (copies the compiled drivers)
#   PROFILE  as in run.sh (nearcore = opt-level 3, fat LTO, one codegen unit)
#   NAME     container name (default ct-select)
#   CT_MEMORY / CT_CPUS  docker --memory / --cpus caps for the container (default 64g / 24). BINSEC runs can grow to
#            tens of GB each; without a cap they have pushed the box out of memory and killed unrelated Lean builds.
# Builds the drivers and generates the BINSEC scripts through `cargo-checkct run --timeout 1`, then runs BINSEC
# on the matching scripts with the same command line cargo-checkct uses. Prints a "Summary:" block in the same
# shape as run.sh, so checkct/leaks.sh can map the leak addresses to source lines.
set -o pipefail
: "${ONLY:?set ONLY to a regex over the probe names}"
TIMEOUT="${TIMEOUT:-7200}"
NAME="${NAME:-ct-select}"
TARGETS="${TARGETS:-riscv32imac-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-linux-gnu}"
JOBS="${JOBS:-16}"
MOUNT=""
if [ -n "$OUT" ]; then
  mkdir -p "$OUT" && chmod 777 "$OUT" && MOUNT="-v $OUT:/out"
fi
PENV=""
case "$PROFILE" in nearcore|nearcore-novec)
  PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort" ;; esac
# BINSEC cannot lift some SSE2 instructions (movmskpd) that LLVM emits when it vectorizes the loops at opt-level 3.
# cargo-checkct drops RUSTFLAGS, so use the per-target variable, which replaces the x86_64 rustflags of checkct/.cargo/config.toml, so repeat them.
if [ "$PROFILE" = nearcore-novec ]; then
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false"
  PENV="$PENV -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
fi
docker run --rm --memory "${CT_MEMORY:-64g}" --memory-swap "${CT_MEMORY:-64g}" --cpus "${CT_CPUS:-24}" --name "$NAME" $MOUNT $PENV -e ONLY="$ONLY" -e TIMEOUT="$TIMEOUT" -e TARGETS="$TARGETS" -e JOBS="$JOBS" \
  -v "$PWD":/src:ro ct-binsec bash -c '
  mkdir /home/opam/w && cp -r /src/src /src/checkct /src/Cargo.toml /home/opam/w/ &&
  rm -rf /home/opam/w/checkct/target && cd /home/opam/w && eval $(opam env) &&
  cargo-checkct run --dir /home/opam/w --timeout 1 --jobs 60 --skip-unknown >/dev/null 2>&1
  cd /home/opam/w/checkct/target || exit 1
  run_one() {
    t=$1; s=$2; isa=""
    case "$t" in thumb*) isa="-isa armv7:thumb" ;; esac
    ep=$(basename "$s" .binsec); ep=${ep#driver.}; ep=$(echo "$ep" | sed "s/__/::/g")
    out=$(binsec -sse -checkct -sse-depth 1000000000 -sse-jump-enum 64 -sse-script "$s" -sse-timeout "$TIMEOUT" \
      -checkct-leak-info instr $isa -checkct-features control-flow,memory-access,dividend,divisor "$t/release/driver" 2>&1)
    st=$(echo "$out" | sed -n "s/.*Program status is : \([a-z]*\).*/\1/p" | head -1)
    {
      echo "  driver  $t  $ep  ${st:-error}"
      echo "$out" | sed -n "s/.*\[checkct:result\] Instruction \(.*\)/      \1/p"
      echo "$out" | grep -E "visited instructions \(unrolled\)|branching points|checks pass|pending paths" | sed "s/^ */      stat: /"
    } > "/tmp/sel.$t.$ep.out"
    echo "done $t $ep ${st:-error}"   # streamed as each probe finishes
  }
  export -f run_one
  for t in $TARGETS; do for s in $t/release/driver.*.binsec; do
    n=$(basename "$s" .binsec); n=${n#driver.}
    echo "$n" | grep -Eq "$ONLY" && echo "$t $s"
  done; done > /tmp/jobs.txt
  echo "selected $(wc -l < /tmp/jobs.txt) probes"
  xargs -P "$JOBS" -L1 bash -c "run_one \$0 \$1" < /tmp/jobs.txt
  echo "Summary:"
  cat /tmp/sel.*.out
  if [ -d /out ]; then
    for t in $TARGETS; do cp /home/opam/w/checkct/target/$t/release/driver /out/$t.driver; done
  fi'
