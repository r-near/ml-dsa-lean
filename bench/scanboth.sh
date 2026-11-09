#!/usr/bin/env bash
# Builds the stack-offset scanner twice (nearcore's flags; nearcore's flags + AVX2) and runs the scan on both. Usage: scanboth.sh CPU NAME
# Every set (44, 65, 87) and operation (verify, vk, prepared). Exits 1 if either scan fails.
set -o pipefail
CPU=${1:?cpu}; NAME=${2:?name}
cd "$(dirname "$0")/.."
export SETS=${SETS:-44,65,87} OPS=${OPS:-verify,vk,prepared}
rc=0
bash bench/stackscan.sh build "$NAME-nc" || exit 1
EXTRA_RF="-Ctarget-feature=+avx,+avx2" bash bench/stackscan.sh build "$NAME-nca" || exit 1
echo "##### nearcore flags"; bash bench/stackscan.sh check "$CPU" "$NAME-nc" || rc=1
echo "##### nearcore flags + avx2"; bash bench/stackscan.sh check "$CPU" "$NAME-nca" || rc=1
exit $rc
