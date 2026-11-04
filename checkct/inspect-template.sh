#!/usr/bin/env bash
# List ct-ntt* containers; with an argument "kill", stop the ones whose run was killed (killing a run does not stop its container).
docker ps --format '{{.Names}} {{.Status}}' | grep '^ct-ntt' || true
if [ "$1" = kill ]; then
  for n in $(docker ps --format '{{.Names}}' | grep '^ct-ntt' | grep -v "^$2$"); do docker kill "$n"; done
fi
