#!/usr/bin/env bash
# Check script for the Rust crate (no GitHub Actions). Run it on a Linux x86_64 machine with rustup:
#
#   bash scripts/ci.sh
#
# (the whole run takes tens of minutes on a cold build cache. A warm cache, for example from a compiler wrapper that
# shares compiled crates, makes the build steps finish in seconds, so a short step time is not evidence that a step did
# nothing.)
#
# Usage: scripts/ci.sh [--lean] [--fuzz-secs N] [--only step[,step...]] [--strict]
#   --lean         also run scripts/lean-check.sh (the Lean done-gate; slow, heavy, off by default)
#   --fuzz-secs N  seconds per fuzz target for the smoke runs (default 60)
#   --only a,b     run only the named steps; an unknown step name is an error (exit 2), and a run in which no step ran
#                  fails
#   --strict       a SKIP (missing tool or toolchain that cannot be installed) counts as a failure
#
# Steps run one after another and never stop at the first failure; every step prints a STEP-RESULT line and the
# last lines are a summary table plus "CI SUMMARY: ...". Exit status is 0 only if no step failed (and, with
# --strict, none was skipped).
#
# Steps: test-default, test-zeroize, test-zeroize-release, test-avx2, avx2-inlining, thumbv7em, msrv-1.86, nearcore-build,
# nearcore-test, nearcore-test-avx2, nearcore-test-zeroize, wasm32, wasm32-zeroize, diff-awslc,
# fuzz-<target> (one per target in fuzz/fuzz_targets), deny, extract-hash, axiom-gate-selftest, no-decls-text, cfg-inventory,
# readme-counts, feature-independence (with --lean), lean.
#
# extract-hash, axiom-gate-selftest, no-decls-text, cfg-inventory and readme-counts need no Rust and no Lean:
#   extract-hash          fails if the extraction inputs (every file under src/, Cargo.toml with its package version normalized
#                         to 0.0.0 so a release bump does not count, the roots, the tool pins), any file
#                         under lean/Impl (recursively) or scripts/extract-roots.txt no longer match what
#                         lean/Impl/extract-report.json recorded at the last extraction, or if there is a symlink in them
#                         (scripts/extract_hash.py; the thorough check, re-running the extraction into an empty directory
#                         and comparing every file, is in .github/workflows/lean.yml).
#   axiom-gate-selftest   runs scripts/check-axioms.sh on a missing, an empty and a comment-only list and fails unless it
#                         exits 1 with "AXIOM GATE FAIL", so the gate cannot silently pass on no declarations.
#   no-decls-text         the text half of scripts/check-no-decls.sh: its self-test (each forbidden construct is found, comments
#                         and strings are not), then a scan of every .lean file under lean/Impl, lean/Spec and lean/Proofs for
#                         axiom, opaque, sorry, admit, native_decide, implemented_by and extern. The Lean half (the whole
#                         environment, with an injected-declaration self-test) runs in the `lean` step via scripts/lean-check.sh.
#   cfg-inventory         every #[cfg(..)], #[cfg_attr(..)] and cfg!(..) site in src/ against the justified whitelist
#                         scripts/cfg-inventory.txt (scripts/cfg_inventory.py): a new or changed cfg-split body fails until a
#                         reviewer writes it into the whitelist.
#   readme-counts         the theorem counts in README.md against the theorem lists (scripts/check-readme-counts.py).
# feature-independence (--lean only; needs the extraction tools of scripts/setup-tools.sh, no Lean) extracts the crate a second
# time without the verify dispatch and diffs the generated Lean against lean/Impl, failing on any difference outside a
# whitelist (scripts/check-feature-independence.sh). SKIP when the tools are missing.
#
# NOTE: test-zeroize skips stack_residue_* where they fail at opt-level 0. test-zeroize runs the zeroize feature's tests in
# the dev profile (opt-level 0) without the 21 failing stack-residue scans (keygen, pk_from_sk, sign, sign_prepared and the
# three attempt scans, for 44/65/87) and with the 3 that pass (signing_key for 44/65/87); the drop and SHAKE wipe tests run
# too. test-zeroize-release and nearcore-test-zeroize run the full suite, all 24 scans, in release. Counts reproduced on
# a Linux x86_64 machine and an aarch64 macOS machine: of the 24 stack-residue scan tests in tests/zeroize.rs, 21 find copies
# of secrets in dead stack frames at opt-level 0; all 24 pass in release; at dev opt-level 1 macOS passes all 28 tests and Linux 26
# (keygen 44/65 fail). The wipe claims in src/api.rs are therefore about optimized builds. Reproducer:
# cargo test --features zeroize --test zeroize stack_residue
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
    -h|--help) awk '/^set -u/ {exit} NR > 1 {print}' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
  shift
done

# Known step names; --only must name only these (a typo must not turn the run into a silent no-op).
KNOWN_STEPS=(test-default test-zeroize test-zeroize-release test-avx2 avx2-inlining thumbv7em msrv-1.86 nearcore-build nearcore-test
             nearcore-test-avx2 nearcore-test-zeroize wasm32 wasm32-zeroize diff-awslc deny extract-hash axiom-gate-selftest no-decls-text
             cfg-inventory readme-counts feature-independence lean)
for f in fuzz/fuzz_targets/*.rs; do KNOWN_STEPS+=("fuzz-$(basename "$f" .rs)"); done
if [ -n "$ONLY" ]; then
  IFS=',' read -r -a _only <<< "${ONLY#,}"
  for n in "${_only[@]}"; do
    [ -z "$n" ] && continue
    ok=0; for k in "${KNOWN_STEPS[@]}"; do [ "$k" = "$n" ] && ok=1; done
    if [ "$ok" -eq 0 ]; then
      echo "unknown step in --only: $n" >&2; echo "known steps: ${KNOWN_STEPS[*]}" >&2; exit 2
    fi
  done
fi

NEARCORE_TC="${NEARCORE_TC:-1.95.0}"
MSRV_TC="${MSRV_TC:-1.86.0}"
# From nearcore's .cargo/config.toml, section [target.'cfg(target_arch = "x86_64")'] at nearcore cd5a94457.
NEARCORE_RUSTFLAGS="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
CI_TOOLS="${CI_TOOLS:-$HOME/.cache/ml-dsa-lean-ci/tools}"

NAMES=(); RESULTS=(); TIMES=(); ZEROIZE_SKIPPED=0
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
step_test_zeroize() {
  echo "NOTE: skipping 21 of the 24 stack_residue_* scans (they fail at opt-level 0, see the header of this script and Z-1 in docs/assurance.md); running the 3 signing_key scans and the other tests"
  ZEROIZE_SKIPPED=1
  # `--skip` matches substrings of the full test path (ml_dsa_44::stack_residue_keygen, ...), and `stack_residue_` is a
  # substring of every scan, so the first run skips all of them and the second runs the three that pass.
  cargo test --features zeroize -- --skip stack_residue_ && \
    cargo test --features zeroize --test zeroize -- stack_residue_signing_key
}
step_test_zeroize_release() { cargo test --release --features zeroize; }
# The avx2 steps run the AVX2 tests (tests/keccak4_avx2.rs, tests/fast_verify.rs, tests/fast_verify_x4.rs, tests/fast_verify_tr.rs, and the
# ACVP, Wycheproof and KAT suites through the dispatched API). ML_DSA_REQUIRE_AVX2=1 turns "this machine has no AVX2, so
# the AVX2 path was not compared" from a printed note into a failure; GitHub-hosted x86_64 runners have AVX2.
step_test_avx2() { ML_DSA_REQUIRE_AVX2=1 cargo test --features avx2; }
# The generated part of src/keccak4.rs is current; the AVX2 4-way verify body is compiled with AVX2 and LLVM vectorized the
# 4-way permutation in it (a scalar permutation is correct but 3x slower); see the script header.
step_avx2_inlining() { python3 scripts/gen_keccak4_round.py --check && bash scripts/check-avx2-inlining.sh; }
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
# nearcore_profile_check test|build [cargo args]: prints the profile cargo really uses for this crate's units under
# the nearcore settings (from cargo's unit graph, which also works when the build is already fresh; needs
# RUSTC_BOOTSTRAP for the unstable flag, only to read the plan) and fails unless overflow-checks is on and LTO is fat for
# every unit, and, for `build`, panic is abort. For `test` the units show panic=unwind: cargo ignores
# `panic = "abort"` for test targets.
nearcore_profile_check() {
  local sub="$1"; shift
  local noexec=""; [ "$sub" = test ] && noexec="--no-run"
  RUSTC_BOOTSTRAP=1 nearcore_env cargo "+$NEARCORE_TC" "$sub" --release "$@" $noexec --unit-graph -Zunstable-options \
    | python3 -I -c '
import json, sys
sub = sys.argv[1]
g = json.load(sys.stdin)
seen, bad = set(), 0
for u in g["units"]:
    if "ml-dsa-lean" not in u["pkg_id"] or "-fuzz" in u["pkg_id"]:
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
# nearcore_target_features_check: nearcore's x86_64 target features must reach rustc. `--print cfg` through `cargo rustc`
# shows the cfg of the crate build, with RUSTFLAGS applied.
nearcore_target_features_check() {
  local cfg rc=0 f
  cfg="$(nearcore_env cargo "+$NEARCORE_TC" rustc --release --lib -- --print cfg)" || { echo "cargo rustc --print cfg failed"; return 1; }
  for f in sse4.2 bmi2 lzcnt movbe; do
    if grep -qx "target_feature=\"$f\"" <<<"$cfg"; then echo "target_feature=\"$f\" present"
    else echo "MISSING: target_feature=\"$f\" is not in rustc's cfg under the nearcore RUSTFLAGS"; rc=1; fi
  done
  return "$rc"
}
# nearcore_overflow_flag_check: after touching src/lib.rs (a fresh build prints no rustc line), the verbose build must
# show the crate's rustc invocation with `-C overflow-checks=on` and `-C panic=abort`.
nearcore_overflow_flag_check() {
  local log rc=0 line; log="$(mktemp)"
  touch src/lib.rs
  # --color never: with CARGO_TERM_COLOR=always (as in GitHub Actions) the "Running" line carries escape codes.
  nearcore_env cargo "+$NEARCORE_TC" build --release -v --color never 2>&1 | tee "$log"
  if [ "${PIPESTATUS[0]}" -ne 0 ]; then rm -f "$log"; return 1; fi
  line="$(grep -E "Running .*--crate-name ml_dsa_lean" "$log" | head -n 1)"
  rm -f "$log"
  if [ -z "$line" ]; then echo "no rustc line for ml_dsa_lean in the verbose build output"; return 1; fi
  case "$line" in *"-C overflow-checks=on"*) echo "rustc line has -C overflow-checks=on" ;; *) echo "MISSING: -C overflow-checks=on in the rustc line"; rc=1 ;; esac
  case "$line" in *"-C panic=abort"*) echo "rustc line has -C panic=abort" ;; *) echo "MISSING: -C panic=abort in the rustc line"; rc=1 ;; esac
  return "$rc"
}
step_nearcore_build() {
  need_toolchain "$NEARCORE_TC" || return $?
  nearcore_env cargo "+$NEARCORE_TC" --version || return 1
  nearcore_profile_check build || { echo "profile check failed"; return 1; }
  nearcore_target_features_check || return 1
  nearcore_overflow_flag_check || return 1
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
  ML_DSA_REQUIRE_AVX2=1 nearcore_env cargo "+$NEARCORE_TC" test --release --features avx2
}
step_nearcore_test_zeroize() {
  # The zeroize feature (tests/zeroize.rs, including all 24 stack-residue scans) under nearcore's release profile.
  need_toolchain "$NEARCORE_TC" || return $?
  nearcore_profile_check test --features zeroize --test zeroize || { echo "profile check failed"; return 1; }
  nearcore_env cargo "+$NEARCORE_TC" test --release --features zeroize --test zeroize
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
  # cargo-fuzz picks the wrong default target on some machines (it stops with "sanitizer is incompatible with statically
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
step_diff_awslc() {
  # Differential test against aws-lc-rs (tests/awslc_diff.rs; see its header). Release counts: the dev profile runs only
  # a smoke subset. On a disagreement the test fails and writes the failing inputs to target/awslc-diff-dump/.
  cargo test --release --test awslc_diff -- --nocapture || {
    echo "diff-awslc FAILED: ours and aws-lc-rs disagree, or the public API disagrees with the slice verdict; failing inputs are in target/awslc-diff-dump/"
    return 1
  }
}
step_extract_hash() { python3 -I scripts/extract_hash.py check; }
step_axiom_gate_selftest() {
  # The "no list / no declarations" cases exit before check-axioms.sh runs Lean, so this needs no Lean. The real list
  # is never touched; the temp lists live in a scratch directory.
  local tmp rc=0; tmp="$(mktemp -d)"
  printf '' > "$tmp/empty.txt"
  printf '# only comments, imports and blank lines\nimport Proofs.PartialAPI\n\n   \n' > "$tmp/no-decls.txt"
  expect_gate_fail "$tmp/missing.txt" "list file $tmp/missing.txt not found" || rc=1
  expect_gate_fail "$tmp/empty.txt" "list file $tmp/empty.txt names no declarations" || rc=1
  expect_gate_fail "$tmp/no-decls.txt" "list file $tmp/no-decls.txt names no declarations" || rc=1
  rm -rf "$tmp"
  [ "$rc" -eq 0 ] && echo "axiom gate self-test OK: a missing, an empty and a declaration-free list all fail the gate"
  return "$rc"
}
# expect_gate_fail LISTFILE MESSAGE: scripts/check-axioms.sh --list LISTFILE must exit 1 and print "AXIOM GATE FAIL: MESSAGE".
expect_gate_fail() {
  local out rc=0
  out="$(scripts/check-axioms.sh --list "$1" 2>&1)" || rc=$?
  if [ "$rc" -eq 1 ] && grep -qxF "AXIOM GATE FAIL: $2" <<<"$out"; then echo "ok: exit 1, \"AXIOM GATE FAIL: $2\""; return 0; fi
  echo "SELF-TEST FAIL: scripts/check-axioms.sh --list $1 exited $rc; wanted exit 1 with \"AXIOM GATE FAIL: $2\"; output:"
  printf '%s\n' "$out"
  return 1
}
step_no_decls_text() { scripts/check-no-decls.sh --text-only && python3 -I scripts/no_decls_text.py --self-test; }
step_cfg_inventory() { python3 -I scripts/cfg_inventory.py; }
step_readme_counts() { python3 -I scripts/check-readme-counts.py; }
step_feature_independence() {
  if [ ! -x "${ML_DSA_TOOLS:-$HOME/hax-tools}/bin/cargo-hax" ]; then echo "SKIP: the extraction tools are not installed (scripts/setup-tools.sh)"; return 77; fi
  scripts/check-feature-independence.sh
}
# lean-check.sh runs the feature-independence gate itself unless told not to; this script has already run it as its own step.
step_lean() { ML_DSA_FEATURE_INDEPENDENCE_DONE=1 scripts/lean-check.sh; }

run_step test-default step_test_default
run_step test-zeroize step_test_zeroize
run_step test-zeroize-release step_test_zeroize_release
run_step test-avx2 step_test_avx2
run_step avx2-inlining step_avx2_inlining
run_step thumbv7em step_thumbv7em
run_step msrv-1.86 step_msrv
run_step nearcore-build step_nearcore_build
run_step nearcore-test step_nearcore_test
run_step nearcore-test-avx2 step_nearcore_test_avx2
run_step nearcore-test-zeroize step_nearcore_test_zeroize
run_step wasm32 step_wasm32
run_step wasm32-zeroize step_wasm32_zeroize
for f in fuzz/fuzz_targets/*.rs; do
  t="$(basename "$f" .rs)"
  run_step "fuzz-$t" step_fuzz "$t"
done
run_step diff-awslc step_diff_awslc
run_step deny step_deny
run_step extract-hash step_extract_hash
run_step axiom-gate-selftest step_axiom_gate_selftest
run_step no-decls-text step_no_decls_text
run_step cfg-inventory step_cfg_inventory
run_step readme-counts step_readme_counts
if [ "$LEAN" -eq 1 ] || [[ "$ONLY" == *",feature-independence,"* ]]; then run_step feature-independence step_feature_independence; fi
if [ "$LEAN" -eq 1 ] || [[ "$ONLY" == *",lean,"* ]]; then run_step lean step_lean; fi

echo; echo "=== SUMMARY ==="
fail=0; skip=0; pass=0
for i in "${!NAMES[@]}"; do
  printf '%-22s %-5s %6ss\n' "${NAMES[$i]}" "${RESULTS[$i]}" "${TIMES[$i]}"
  case "${RESULTS[$i]}" in PASS) pass=$((pass+1)) ;; SKIP) skip=$((skip+1)) ;; *) fail=$((fail+1)) ;; esac
done
if [ "$STRICT" -eq 1 ] && [ "$skip" -gt 0 ]; then fail=$((fail+skip)); fi
if [ "$ZEROIZE_SKIPPED" -eq 1 ]; then
  echo "NOTE: skipping 21 of 24 stack_residue_* scans in test-zeroize (fail at opt-level 0, see the header of this script and Z-1 in docs/assurance.md); test-zeroize-release and nearcore-test-zeroize cover them in release"
fi
if [ "${#NAMES[@]}" -eq 0 ]; then
  echo "no step ran (--only matched nothing that was enabled)"; fail=$((fail+1))
fi
echo "CI SUMMARY: $pass passed, $fail failed, $skip skipped$( [ "$LEAN" -eq 0 ] && echo ' (Lean gate not run; pass --lean)')"
[ "$fail" -eq 0 ]
