#!/usr/bin/env bash
# Run one minimal crate through the pinned Charon + Aeneas (same invocation as scripts/extract.py, generic variant).
# Usage (on the build box): extract-mini.sh CRATE_DIR WORK_DIR ROOT_PATH...
#   ROOT_PATH is a fully qualified Rust path, e.g. x1_target_feature::caller
# Env: SIMD_RUSTFLAGS (default "--cfg miri", as the main crate), SIMD_CHARON_ARGS (default "", a TOML array body).
# Writes WORK_DIR/{hax.log,aeneas.log,lean/Impl/*.lean}; exits 0 only if Charon and Aeneas both exit 0.
set -uo pipefail
src=$(realpath "$1"); work=$2; shift 2
T="$HOME/hax-tools"
AENEAS_PIN=build-183e4f0; CHARON_PIN=nightly-2026.09.02
rm -rf "$work"; mkdir -p "$work/crate"
cp -r "$src/src" "$src/Cargo.toml" "$work/crate/"
include=""; for r in "$@"; do include+="\"$r\", "; done
cat > "$work/crate/hax.toml" <<TOML
[tools]
aeneas = "$AENEAS_PIN"
charon = "$CHARON_PIN"
[versions]
lean = "leanprover/lean4:v4.31.0"
hax-lean-lib = "v0.3.30"
[scenario.generic]
backend = "lean"
include = [${include%, }]
no-default-features = true
charon-args = [${SIMD_CHARON_ARGS:-}]
env = { RUSTFLAGS = "${SIMD_RUSTFLAGS---cfg miri}" }
TOML
unset RUSTFLAGS CARGO_ENCODED_RUSTFLAGS CARGO_BUILD_RUSTFLAGS CARGO_TARGET_DIR
export PATH="$T/bin:$PATH" XDG_CACHE_HOME="$T/cache" CHARON_MIRI_SYSROOTS="$T/charon-sysroot-nightly-2026-08-18"
(cd "$work/crate" && cargo hax extract generic -v) > "$work/hax.log" 2>&1
hrc=$?
echo "charon exit: $hrc"
llbc=$(find "$work/crate" -name '*.llbc' | head -1)
if [ -z "$llbc" ]; then echo "no llbc"; tail -40 "$work/hax.log"; exit 1; fi
cp "$llbc" "$work/actual.llbc"
"$T/cache/hax/tools/aeneas/$AENEAS_PIN/aeneas" -backend lean -split-files -namespace Impl "$work/actual.llbc" \
  -dest "$work/lean" -subdir Impl > "$work/aeneas.log" 2>&1
arc=$?
echo "aeneas exit: $arc"
sed -i 's/\x1b\[[0-9;]*m//g' "$work/aeneas.log"
# Scrub home paths from anything that may be copied into the repo.
sed -i -E 's#(/home/[^/ "]+|/Users/[^/ "]+)#$HOME#g' "$work/hax.log" "$work/aeneas.log"
exit $(( hrc != 0 || arc != 0 ))
