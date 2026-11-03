#!/usr/bin/env bash
# Box-runnable check script for the Rust crate (no GitHub Actions). Run it on the build box:
#
#   rx submit ci-nc -- 'set -o pipefail; scripts/ci.sh 2>&1 | tee ci.log'      # whole run takes tens of minutes
#   rx wait ci-nc
#
# Usage: scripts/ci.sh [--lean] [--fuzz-secs N] [--only step[,step...]] [--strict]
#   --lean         also run scripts/lean-check.sh (the Lean done-gate; slow, heavy, off by default)
#   --fuzz-secs N  seconds per fuzz target for the smoke runs (default 60)
#   --only a,b     run only the named steps
#   --strict       a SKIP (missing tool or toolchain that cannot be installed) counts as a failure
#
# Steps run one after another and never stop at the first failure; every step prints a STEP-RESULT line and the
# last lines are a summary table plus "CI SUMMARY: ...". Exit status is 0 only if no step failed (and, with
# --strict, none was skipped).
#
# Steps: test-default, test-zeroize, test-zeroize-release, test-avx2, thumbv7em, msrv-1.86, nearcore-build,
# nearcore-test, nearcore-test-avx2, wasm32, wasm32-zeroize, fuzz-<target> (one per target in fuzz/fuzz_targets), deny, lean.
#
# test-zeroize runs the zeroize feature's tests in the dev profile WITHOUT the `stack_residue_*` scans, and
# test-zeroize-release runs the full suite (including the scans) in release. Reason, found by this script: the stack
# scans pass in release but fail at opt-level 0 (8 of 19 tests in tests/zeroize.rs find s1, s2, s1_hat or K copies in
# dead frames after keygen, pk_from_sk and signing_key; sign and sign_prepared pass). The wipe claims in src/api.rs
# are therefore about optimized builds. Reproducer: cargo test --features zeroize --test zeroize stack_residue
#
# "nearcore-*" steps reproduce nearcore's release build as read at nearcore cd5a94457: toolchain 1.95.0
# (rust-toolchain.toml), [profile.release] overflow-checks = true, panic = "abort", lto = "fat", codegen-units = 1
# (Cargo.toml), and the x86_64 rustflags of .cargo/config.toml (below). The build runs with panic = abort. The test
# harness needs unwinding, so cargo ignores `panic` for test targets (Cargo book, profile `panic` setting: tests,
# benches, build scripts and proc macros always unwind); the step output shows what happened.
set -uo pipefail
cd "$(dirname "$0")/.."

FUZZ_SECS=60
LEAN=0
STRICT=0
ONLY=""
while [ $# -gt 0 ]; do
  case "$1" in
    --lean) LEAN=1 ;;
    --strict) STRICT=1 ;;
    --fuzz-secs) shift; FUZZ_SECS="${1:?--fuzz-secs needs a number}" ;;
    --only) shift; ONLY=",${1:?--only needs a list},"  ;;
    -h|--help) sed -n 2,26p "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

NEARCORE_TC="${NEARCORE_TC:-1.95.0}"
MSRV_TC="${MSRV_TC:-1.86.0}"
# From nearcore's .cargo/config.toml, section [target.'cfg(target_arch = "x86_64")'] at nearcore cd5a94457.
NEARCORE_RUSTFLAGS="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
CI_TOOLS="${CI_TOOLS:-$HOME/.cache/ml-dsa-verified-ci/tools}"

NAMES=(); RESULTS=(); TIMES=()
want() { [ -z "$ONLY" ] || [[ "$ONLY" == *",$1,"* ]]; }
record() { NAMES+=("$1"); RESULTS+=("$2"); TIMES+=("$3"); echo "STEP-RESULT $1 $2 (${3}s)"; }

# run_step NAME CMD...  : runs CMD (a function or command), PASS iff it exits 0.
run_step() {
  local name="$1"; shift
  want "$name" || return 0
  echo; echo "=== STEP $name: $* ==="
  local t0=$SECONDS rc=0
  "$@" || rc=$?
  local dt=$((SECONDS - t0))
  case "$rc" in
    0) record "$name" PASS "$dt" ;;
    77) record "$name" SKIP "$dt" ;;
    *) echo "STEP $name FAILED with exit code $rc"; record "$name" FAIL "$dt" ;;
  esac
}

# cargo_retry_target TOOLCHAIN TARGET CMD...: runs CMD; if rustc reports E0463 (target not installed), installs the
# target once with rustup and retries.
cargo_retry_target() {
  local tc="$1" target="$2"; shift 2
  local log; log="$(mktemp)"
  "$@" 2>&1 | tee "$log"
  local rc=${PIPESTATUS[0]}
  if [ "$rc" -ne 0 ] && grep -q "E0463" "$log"; then
    echo "E0463: target $target is missing for toolchain $tc; installing it with rustup and retrying once"
    rustup target add --toolchain "$tc" "$target" || { rm -f "$log"; return 1; }
    "$@"; rc=$?
  fi
  rm -f "$log"
  return "$rc"
}

# need_toolchain TC: 0 if installed (or installed now), 77 (SKIP) otherwise.
need_toolchain() {
  rustup toolchain list | grep -q "^$1" && return 0
  echo "toolchain $1 not installed; trying rustup toolchain install $1 --profile minimal"
  rustup toolchain install "$1" --profile minimal && return 0
  echo "SKIP: toolchain $1 unavailable"; return 77
}

step_test_default() { cargo test; }
step_test_zeroize() { cargo test --features zeroize -- --skip stack_residue; }
step_test_zeroize_release() { cargo test --release --features zeroize; }
step_test_avx2() { cargo test --features avx2; }
step_thumbv7em() {
  cargo_retry_target "$(rustup show active-toolchain | awk '{print $1}')" thumbv7em-none-eabihf \
    cargo build --release --target thumbv7em-none-eabihf
}
step_msrv() {
  need_toolchain "$MSRV_TC" || return $?
  # The library only: the dev-dependencies (git oracle, serde_json, ...) have their own, higher MSRV. The `avx2`
  # feature is why rust-version is 1.86 (safe #[target_feature] functions), so build with it on and off.
  cargo "+$MSRV_TC" --version && \
  cargo "+$MSRV_TC" build --release && \
  cargo "+$MSRV_TC" build --release --features zeroize,avx2
}

nearcore_env() {
  # Runs "$@" with nearcore's release profile (as read at cd5a94457) and target features.
  env CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true CARGO_PROFILE_RELEASE_LTO=fat \
      CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 CARGO_PROFILE_RELEASE_PANIC=abort \
      RUSTFLAGS="$NEARCORE_RUSTFLAGS" "$@"
}
step_nearcore_build() {
  need_toolchain "$NEARCORE_TC" || return $?
  local log; log="$(mktemp)"
  nearcore_env cargo "+$NEARCORE_TC" --version || return 1
  nearcore_env cargo "+$NEARCORE_TC" build --release -v 2>&1 | tee "$log"
  local rc=${PIPESTATUS[0]}
  if [ "$rc" -eq 0 ]; then
    # Confirm the profile took effect: cargo prints the rustc command line with -v.
    if ! grep -E "Running .*--crate-name ml_dsa_verified" "$log" | grep -q "overflow-checks=on"; then
      echo "could not find overflow-checks=on in the rustc command line"; rc=1
    fi
    if ! grep -E "Running .*--crate-name ml_dsa_verified" "$log" | grep -q "panic=abort"; then
      echo "could not find panic=abort in the rustc command line"; rc=1
    fi
  fi
  rm -f "$log"
  return "$rc"
}
# nearcore_profile_check test|build [cargo args]: prints the profile cargo really uses for this crate's units under
# the nearcore settings (from cargo's unit graph, which also works when the build is already fresh; needs
# RUSTC_BOOTSTRAP for the unstable flag, only to read the plan) and fails unless overflow-checks is on and LTO is fat for
# every unit, and, for `build`, panic is abort. For `test` the units show panic=unwind: cargo ignores
# `panic = "abort"` for test targets.
nearcore_profile_check() {
  local sub="$1"; shift
  local noexec=""; [ "$sub" = test ] && noexec="--no-run"
  RUSTC_BOOTSTRAP=1 nearcore_env cargo "+$NEARCORE_TC" "$sub" --release "$@" $noexec --unit-graph -Zunstable-options \
    2>/dev/null | python3 -I -c '
import json, sys
sub = sys.argv[1]
g = json.load(sys.stdin)
seen, bad = set(), 0
for u in g["units"]:
    if "ml-dsa-verified" not in u["pkg_id"] or "-fuzz" in u["pkg_id"]:
        continue
    p, t = u["profile"], u["target"]
    k = (t["name"], u["mode"], p["name"], "opt=" + str(p["opt_level"]), "lto=" + str(p["lto"]),
         "cgu=" + str(p.get("codegen_units")), "overflow_checks=" + str(p["overflow_checks"]), "panic=" + p["panic"])
    if k in seen:
        continue
    seen.add(k)
    print("profile", *k)
    bad += (not p["overflow_checks"]) or p["lto"] != "fat" or (sub == "build" and p["panic"] != "abort")
print("profile units:", len(seen), "violations:", bad)
sys.exit(1 if bad or not seen else 0)
' "$sub"
}
step_nearcore_build() {
  need_toolchain "$NEARCORE_TC" || return $?
  nearcore_env cargo "+$NEARCORE_TC" --version || return 1
  nearcore_profile_check build || { echo "profile check failed"; return 1; }
  nearcore_env cargo "+$NEARCORE_TC" build --release
}
step_nearcore_test() {
  need_toolchain "$NEARCORE_TC" || return $?
  nearcore_profile_check test || { echo "profile check failed"; return 1; }
  nearcore_env cargo "+$NEARCORE_TC" test --release
}
step_nearcore_test_avx2() {
  need_toolchain "$NEARCORE_TC" || return $?
  nearcore_profile_check test --features avx2 || { echo "profile check failed"; return 1; }
  nearcore_env cargo "+$NEARCORE_TC" test --release --features avx2
}
step_wasm32() {
  need_toolchain "$NEARCORE_TC" || return $?
  cargo_retry_target "$NEARCORE_TC" wasm32-unknown-unknown cargo "+$NEARCORE_TC" build --release --target wasm32-unknown-unknown
}
step_wasm32_zeroize() {
  need_toolchain "$NEARCORE_TC" || return $?
  cargo_retry_target "$NEARCORE_TC" wasm32-unknown-unknown cargo "+$NEARCORE_TC" build --release --target wasm32-unknown-unknown --features zeroize
}

fuzz_toolchain() {
  if [ -n "${FUZZ_TOOLCHAIN:-}" ]; then echo "$FUZZ_TOOLCHAIN"; return; fi
  rustup toolchain list | grep -o '^nightly[^ ]*' | sort | tail -1
}
step_fuzz() {
  local target="$1" tc; tc="$(fuzz_toolchain)"
  if ! cargo fuzz --version >/dev/null 2>&1; then echo "SKIP: cargo-fuzz is not installed"; return 77; fi
  if [ -z "$tc" ]; then echo "SKIP: no nightly toolchain installed"; return 77; fi
  # cargo-fuzz picks the wrong default target on the box (it stops with "sanitizer is incompatible with statically
  # linked libc" and E0463 for musl), so pass the host triple explicitly.
  local host; host="$(rustc "+$tc" -vV | sed -n 's/^host: //p')"
  echo "cargo-fuzz: $(cargo fuzz --version); toolchain $tc; host $host; ${FUZZ_SECS}s on $target"
  # Seed corpus from the vendored ACVP vectors (fuzz/src/bin/gen_seeds.rs); corpus/ is git-ignored.
  if [ ! -d fuzz/corpus/"$target" ]; then
    (cd fuzz && cargo "+$tc" run --release --bin gen_seeds -- ../tests/data/acvp corpus) || return 1
  fi
  (cd fuzz && cargo "+$tc" fuzz run --target "$host" "$target" -- -max_total_time="$FUZZ_SECS" -rss_limit_mb=4096)
}
step_deny() {
  local denycmd=""
  if cargo deny --version >/dev/null 2>&1; then denycmd="cargo deny"
  elif [ -x "$CI_TOOLS/bin/cargo-deny" ]; then denycmd="$CI_TOOLS/bin/cargo-deny deny"
  else
    echo "cargo-deny not found; installing it from crates.io into $CI_TOOLS (nothing is published)"
    cargo install --locked cargo-deny --root "$CI_TOOLS" || { echo "SKIP: cargo-deny could not be installed"; return 77; }
    denycmd="$CI_TOOLS/bin/cargo-deny deny"
  fi
  # Fetches the RustSec advisory database (a public git repository); sends nothing about this project.
  $denycmd --version && $denycmd check
}
step_lean() { scripts/lean-check.sh; }

run_step test-default step_test_default
run_step test-zeroize step_test_zeroize
run_step test-zeroize-release step_test_zeroize_release
run_step test-avx2 step_test_avx2
run_step thumbv7em step_thumbv7em
run_step msrv-1.86 step_msrv
run_step nearcore-build step_nearcore_build
run_step nearcore-test step_nearcore_test
run_step nearcore-test-avx2 step_nearcore_test_avx2
run_step wasm32 step_wasm32
run_step wasm32-zeroize step_wasm32_zeroize
for f in fuzz/fuzz_targets/*.rs; do
  t="$(basename "$f" .rs)"
  run_step "fuzz-$t" step_fuzz "$t"
done
run_step deny step_deny
if [ "$LEAN" -eq 1 ]; then run_step lean step_lean; fi

echo; echo "=== SUMMARY ==="
fail=0; skip=0; pass=0
for i in "${!NAMES[@]}"; do
  printf '%-22s %-5s %6ss\n' "${NAMES[$i]}" "${RESULTS[$i]}" "${TIMES[$i]}"
  case "${RESULTS[$i]}" in PASS) pass=$((pass+1)) ;; SKIP) skip=$((skip+1)) ;; *) fail=$((fail+1)) ;; esac
done
if [ "$STRICT" -eq 1 ] && [ "$skip" -gt 0 ]; then fail=$((fail+skip)); fi
echo "CI SUMMARY: $pass passed, $fail failed, $skip skipped$( [ "$LEAN" -eq 0 ] && echo ' (Lean gate not run; pass --lean)')"
[ "$fail" -eq 0 ]
