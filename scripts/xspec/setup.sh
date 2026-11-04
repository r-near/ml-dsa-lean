#!/usr/bin/env bash
# Prepare the xspec lake project on Linux:
#   bash scripts/xspec/setup.sh [all|update|cache|spec|theirs]
# Network use: GitHub (lake dependencies: Mathlib, ocaml-pq) and the Mathlib cache.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
step="${1:-all}"
df -h "$XS_WORK" | tail -1
update() { [ -f lake-manifest.json ] || lake update 2>&1 | tail -20; }
cache() { lake exe cache get 2>&1 | tail -5; }
spec() { lake build Spec 2>&1 | tail -60; }
theirs() { lake build OcamlPq 2>&1 | tail -30; }
case "$step" in
  update) update ;;
  cache) update; cache ;;
  spec) update; cache; spec ;;
  theirs) update; cache; theirs ;;
  all) update; cache; spec; theirs ;;
  *) echo "usage: setup.sh [all|update|cache|spec|theirs]"; exit 2 ;;
esac
echo SETUP-DONE
