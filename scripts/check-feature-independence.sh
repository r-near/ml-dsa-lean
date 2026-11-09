#!/usr/bin/env bash
# Feature-independence gate (run on Linux with the extraction tools of scripts/setup-tools.sh; no Lean needed except for the
# generated file's own build, which scripts/lean-check.sh does).
#
# Why. The Lean proofs are about one extraction of the crate: feature `avx2` on, `--cfg miri` (scripts/extract.py). A default
# build, a build with the feature off, and any build that is not x86_64 compile a different `cfg` configuration of the same
# source: the dispatch is not there. If a function had a different body in the two configurations (a `cfg`-split body), the
# proofs would say nothing about the default build's version. This gate extracts the crate a second time, in the
# configuration without the dispatch (`--features ''`, still `--cfg miri`, from the same src/), and compares the two
# generated Lean trees declaration by declaration (scripts/feature_independence.py):
#   * every declaration is byte-identical except an explicit, commented whitelist (the `cpu::Avx2` type, the three
#     `fast_verify::dispatch::*_on` entry points, and the three `*_avx2` functions that exist only with the dispatch);
#   * the three `fast_verify::*_with` functions, the scalar verify functions they call, and the stub `cpu::avx2` are
#     additionally required to be identical on their own;
#   * lean/Proofs/NoDispatch.lean (committed, generated from the second extraction) elaborates the declarations that differ
#     and proves the default-configuration `_with` functions equal the scalar functions for every token value. It is part of
#     the default build, so scripts/lean-check.sh checks it; this script checks that it is what the second extraction
#     generates.
# The second extraction is the Lean model of the default build for these functions; what it does not cover is the same as
# for the main extraction (the compiler; the `cfg` conditions that are not `miri`/`avx2`/`x86_64`, which scripts/cfg-inventory.py
# lists and justifies one by one).
#
# Usage: scripts/check-feature-independence.sh            compare, and check lean/Proofs/NoDispatch.lean
#        scripts/check-feature-independence.sh --update   also rewrite lean/Proofs/NoDispatch.lean from the second extraction
set -euo pipefail
cd "$(dirname "$0")/.."
UPDATE=0
for a in "$@"; do
  case "$a" in
    --update) UPDATE=1 ;;
    *) echo "usage: $0 [--update]" >&2; exit 2 ;;
  esac
done
python3 -I scripts/extract_hash.py check
python3 -I scripts/feature_independence.py --self-test
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
python3 scripts/extract.py --features '' --out "$WORK/Impl" --work "$WORK/work" > "$WORK/extract.log" 2>&1 \
  || { tail -30 "$WORK/extract.log"; echo "FEATURE-INDEPENDENCE FAIL: the second extraction failed"; exit 1; }
tail -2 "$WORK/extract.log"
python3 -I scripts/feature_independence.py compare lean/Impl "$WORK/Impl"
if [ "$UPDATE" -eq 1 ]; then
  python3 -I scripts/feature_independence.py gen-lean "$WORK/Impl" > lean/Proofs/NoDispatch.lean
  echo "wrote lean/Proofs/NoDispatch.lean"
fi
python3 -I scripts/feature_independence.py check-lean "$WORK/Impl" lean/Proofs/NoDispatch.lean
echo "FEATURE-INDEPENDENCE OK"
