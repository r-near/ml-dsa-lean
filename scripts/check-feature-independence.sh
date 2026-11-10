#!/usr/bin/env bash
# Target-feature-independence gate (run on Linux with the extraction tools of scripts/setup-tools.sh; no Lean needed).
#
# Why. The Lean proofs are about one extraction of the crate (scripts/extract.py: `--cfg miri`, no extra flags). Since round 12 the
# crate has no run-time choice between code paths and no `cfg` that reads a target feature: `api::verify_*`, `verifying_key_*` and
# the prepared verify call the 4-way functions directly, and a build that wants AVX2 code compiles with
# `-C target-feature=+avx2`, which changes what LLVM emits for the same Rust source and nothing else. This gate checks the "nothing
# else": it extracts the crate a second time from the same src/ with `-C target-feature=+avx,+avx2` added to the rustc flags (through
# the `env` RUSTFLAGS of hax.toml, which is how the extraction passes flags), and requires the two generated Lean trees to be
# the same, declaration by declaration (scripts/feature_independence.py). The whitelist of differences is empty.
#
# It cannot pass vacuously:
#   * each extraction records its rustflags in extract-report.json, and `compare` fails unless they are exactly `--cfg miri` and
#     `--cfg miri -C target-feature=+avx,+avx2` (so identical flags, a typo or a stripped flag fail);
#   * a positive control: scripts/fi-probe, a one-function crate whose body is `cfg!(target_feature = "avx2")`, is extracted under both
#     flag sets, and the gate fails unless it comes out as `false` and `true` (so the flags demonstrably reach the compiler);
#   * the comparison must have covered the verify path (declarations listed in scripts/feature_independence.py, present and identical);
#   * the script's self-test feeds synthetic tree pairs (same flags, split function, missing declaration, ...) to `compare` and
#     `probe-check` and requires them to be rejected.
# What it does not cover is the same as for the main extraction: the compiler's translation of the Rust, and the `cfg` conditions
# that are not `miri`, which scripts/cfg-inventory.py lists and justifies one by one.
#
# Usage: scripts/check-feature-independence.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ "$#" -eq 0 ] || { echo "usage: $0" >&2; exit 2; }
ALT_FLAGS='-C target-feature=+avx,+avx2'
python3 -I scripts/extract_hash.py check
python3 -I scripts/feature_independence.py --self-test
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT
extract() { # NAME SRC ROOTS RUSTFLAGS
  python3 scripts/extract.py --src "$2" --roots "$3" --rustflags "$4" --out "$WORK/$1/Impl" --work "$WORK/$1/work" > "$WORK/$1.log" 2>&1 \
    || { tail -30 "$WORK/$1.log"; echo "FEATURE-INDEPENDENCE FAIL: the extraction '$1' failed"; exit 1; }
  tail -1 "$WORK/$1.log"
}
# The crate with the AVX2 target features; the main extraction is the committed lean/Impl (extract_hash.py check ties it to src/).
extract alt . scripts/extract-roots.txt "$ALT_FLAGS"
python3 -I scripts/feature_independence.py compare lean/Impl "$WORK/alt/Impl"
# The positive control. Its manifest is kept as Cargo.toml.in (see that file), so stage the crate with it as Cargo.toml.
PROBE="$WORK/fi-probe"
mkdir -p "$PROBE"
cp -R scripts/fi-probe/src "$PROBE/src"
cp scripts/fi-probe/Cargo.toml.in "$PROBE/Cargo.toml"
extract probe-main "$PROBE" scripts/fi-probe/roots.txt ''
extract probe-alt "$PROBE" scripts/fi-probe/roots.txt "$ALT_FLAGS"
python3 -I scripts/feature_independence.py probe-check "$WORK/probe-main/Impl" "$WORK/probe-alt/Impl"
echo "FEATURE-INDEPENDENCE OK"
