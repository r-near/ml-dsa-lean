#!/usr/bin/env bash
# Run one probe again inside a RUNNING run-select.sh container (docker exec), on the scripts and driver it built, with a
# short timeout and the full BINSEC log. For diagnosis of a probe of a sweep in flight; not for verdicts.
#   bash checkct/probe-now.sh CONTAINER PROBE [TIMEOUT] [extra binsec args]     PROBE e.g. extra__sk_is_well_formed_44
# A dispatch container needs the cache pre-set: use the /tmp/mod.* script run-select.sh wrote (this script prefers it).
set -o pipefail
C=$1; P=$2; T=${3:-120}; shift 3 2>/dev/null
docker exec -w /home/opam/w/checkct/target "$C" bash -c '
  eval $(opam env); t=x86_64-unknown-linux-gnu; s=$t/release/driver.driver__'"$P"'.binsec
  m=$(ls /tmp/mod.*."driver::'"${P/__/::}"'".binsec 2>/dev/null | head -1); [ -n "$m" ] && s=$m
  echo "script: $s"
  timeout '"$((T + 120))"' binsec -sse -checkct -sse-depth 1000000000 -sse-jump-enum 64 -sse-script $s -sse-timeout '"$T"' \
    -checkct-leak-info instr -checkct-features control-flow,memory-access,dividend,divisor '"$*"' $t/release/driver 2>&1'
