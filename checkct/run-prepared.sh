#!/usr/bin/env bash
# Run the prepared-signing-key probes (checkct/driver/src/prepared.rs) one target at a time, one probe at a time,
# through run-select.sh. From the repository root:
#   rx submit pk-ct -- bash checkct/run-prepared.sh 'prepared__(prepare_sk|signing_key)' 'x86_64-unknown-linux-gnu' 3000
# Arguments (rx does not forward environment variables, so they are positional; each also has an environment variable):
#   $1  ONLY     regex over the probe names (default: every probe of prepared.rs)
#   $2  TARGETS  space separated target list, run one after the other (default: all three)
#   $3  TIMEOUT  seconds per probe (default 3000)
#   $4  CT_MEMORY docker memory cap (default 64g; raise it to rerun a probe that ended in "error")
#   JOBS         parallel probes within one target (default 6; the targets still run one after the other)
#   OUT          directory for the compiled driver binaries, for checkct/leaks.sh (default: ~/rx/scratch/pk-ct/bin)
set -o pipefail
ONLY="${1:-${ONLY:-prepared__}}"
TARGETS="${2:-${TARGETS:-x86_64-unknown-linux-gnu thumbv7em-none-eabihf riscv32imac-unknown-none-elf}}"
TIMEOUT="${3:-${TIMEOUT:-3000}}"
CT_MEMORY="${4:-${CT_MEMORY:-64g}}"
OUT="${OUT:-$HOME/rx/scratch/pk-ct/bin}"
rc=0
for t in $TARGETS; do
  echo "=== target $t"
  CT_MEMORY="$CT_MEMORY" NAME=pk-ct JOBS="${JOBS:-6}" TARGETS="$t" ONLY="$ONLY" TIMEOUT="$TIMEOUT" OUT="$OUT" bash checkct/run-select.sh 2>&1 || rc=1
done
exit $rc
