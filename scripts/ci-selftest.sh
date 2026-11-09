#!/usr/bin/env bash
# Self-test of the Lean path of scripts/ci.sh and scripts/lean-check.sh: did the feature-independence check run when it had to?
#
# Why. ci.sh used to pass ML_DSA_FEATURE_INDEPENDENCE_DONE=1 to lean-check.sh unconditionally, so `--lean --only lean` (which
# filters the feature-independence step out) skipped the check in both places and still reported all steps passed. The flag is now
# set only after the step passed in the same invocation. This script proves it, with the real ci.sh and the real lean-check.sh
# copied into a scratch tree whose other scripts are stubs that record when they run (no Lean, no Rust and no extraction tools
# are needed):
#   A  --strict --lean --only lean                          the check runs once, inside lean-check.sh
#   B  --strict --only feature-independence,lean            the check runs once, as its own step; lean-check.sh does not repeat it
#   C  the same, with the check failing                     the step fails, lean-check.sh runs the check again, the exit status is nonzero
#   D  the tools missing (the step SKIPs)                   lean-check.sh runs the check; with --strict the skip fails the run
#   E  a flag inherited from the caller's environment       is ignored: the check runs
#   F  lean-check.sh with a module argument                 says PARTIAL; without a flag a full run runs the check
#   G  a copy of ci.sh with the old unconditional flag      case A must fail on it (the self-test catches the bug it is about)
# Usage: bash scripts/ci-selftest.sh   (exit 0 and a final "ci-selftest OK" line only if every case behaves)
set -uo pipefail
cd "$(dirname "$0")/.."
REPO="$PWD"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
fails=0
note() { echo "ci-selftest: $*"; }
bad() { echo "ci-selftest FAIL: $*"; fails=$((fails + 1)); }

# mktree DIR CI_SH: a scratch tree with the real lean-check.sh, CI_SH as scripts/ci.sh and recording stubs for the rest.
mktree() {
  local d="$1" ci="$2" n
  mkdir -p "$d/scripts" "$d/lean" "$d/fuzz/fuzz_targets" "$d/home/.elan/bin" "$d/bin" "$d/tools/bin" "$d/notools"
  cp "$ci" "$d/scripts/ci.sh"
  cp "$REPO/scripts/lean-check.sh" "$d/scripts/lean-check.sh"
  for n in check-axioms.sh check-no-decls.sh reachable-defs.sh; do
    printf '#!/usr/bin/env bash\necho "%s $*" >> "$CI_SELFTEST_REC"\nexit 0\n' "$n" > "$d/scripts/$n"
  done
  for n in cfg_inventory.py check-readme-counts.py; do
    printf 'import os\nopen(os.environ["CI_SELFTEST_REC"], "a").write("%s\\n")\n' "$n" > "$d/scripts/$n"
  done
  # The check under test: records each run, and fails when FI_RC says so.
  printf '#!/usr/bin/env bash\necho "FI-RAN" >> "$CI_SELFTEST_REC"\nexit "${FI_RC:-0}"\n' > "$d/scripts/check-feature-independence.sh"
  # lake and timeout stubs (lean-check.sh puts $HOME/.elan/bin first on its PATH; macOS has no timeout).
  printf '#!/usr/bin/env bash\ncase "$1" in exe) exit 0 ;; build) echo "Build completed successfully (stub)"; exit 0 ;; esac\nexit 0\n' > "$d/home/.elan/bin/lake"
  printf '#!/usr/bin/env bash\nshift\nexec "$@"\n' > "$d/bin/timeout"
  printf '#!/usr/bin/env bash\nexit 0\n' > "$d/tools/bin/cargo-hax"
  chmod +x "$d"/scripts/*.sh "$d"/scripts/*.py "$d/home/.elan/bin/lake" "$d/bin/timeout" "$d/tools/bin/cargo-hax"
}

# run_in DIR ENV... -- CMD...: runs CMD in DIR with the recording file fresh; prints nothing, leaves DIR/out and DIR/rec.
run_in() {
  local d="$1"; shift
  local envs=()
  while [ "$1" != "--" ]; do envs+=("$1"); shift; done
  shift
  : > "$d/rec"
  (cd "$d" && env "CI_SELFTEST_REC=$d/rec" "HOME=$d/home" "PATH=$d/bin:$PATH" "ML_DSA_TOOLS=$d/tools" ${envs[@]+"${envs[@]}"} "$@") > "$d/out" 2>&1
  return $?
}
fi_runs() { grep -c '^FI-RAN$' "$1/rec" || true; }

# case_a TREE: the lean step alone must run the check exactly once.
case_a() {
  local d="$1" rc=0 n
  run_in "$d" -- bash scripts/ci.sh --strict --lean --only lean || rc=$?
  n="$(fi_runs "$d")"
  [ "$rc" -eq 0 ] && [ "$n" -eq 1 ] && ! grep -q 'already checked' "$d/out" && grep -q 'CI SUMMARY: 1 passed, 0 failed, 0 skipped' "$d/out"
}

mktree "$T/real" "$REPO/scripts/ci.sh"

# A
if case_a "$T/real"; then note "A ok: --lean --only lean runs the feature-independence check (once, inside lean-check.sh)"
else bad "A: --lean --only lean did not run the feature-independence check exactly once (see below)"; cat "$T/real/out" | tail -8; fi

# B
rc=0; run_in "$T/real" -- bash scripts/ci.sh --strict --only feature-independence,lean || rc=$?
if [ "$rc" -eq 0 ] && [ "$(fi_runs "$T/real")" -eq 1 ] && grep -q 'already checked' "$T/real/out" \
   && grep -q 'CI SUMMARY: 2 passed, 0 failed, 0 skipped' "$T/real/out"; then
  note "B ok: with its own step the check runs once and lean-check.sh does not repeat it"
else bad "B: rc=$rc, check runs=$(fi_runs "$T/real")"; tail -8 "$T/real/out"; fi

# C
rc=0; run_in "$T/real" FI_RC=1 -- bash scripts/ci.sh --strict --only feature-independence,lean || rc=$?
if [ "$rc" -ne 0 ] && [ "$(fi_runs "$T/real")" -eq 2 ] && ! grep -q 'already checked' "$T/real/out"; then
  note "C ok: a failing step does not set the flag; lean-check.sh runs the check again; the run fails"
else bad "C: rc=$rc, check runs=$(fi_runs "$T/real") (want nonzero and 2)"; tail -8 "$T/real/out"; fi

# D
rc=0; run_in "$T/real" "ML_DSA_TOOLS=$T/real/notools" -- bash scripts/ci.sh --lean --only feature-independence,lean || rc=$?
if [ "$rc" -eq 0 ] && [ "$(fi_runs "$T/real")" -eq 1 ] && grep -q 'STEP-RESULT feature-independence SKIP' "$T/real/out" \
   && ! grep -q 'already checked' "$T/real/out"; then
  note "D ok: a skipped step does not set the flag; lean-check.sh runs the check"
else bad "D: rc=$rc, check runs=$(fi_runs "$T/real")"; tail -8 "$T/real/out"; fi
rc=0; run_in "$T/real" "ML_DSA_TOOLS=$T/real/notools" -- bash scripts/ci.sh --strict --lean --only feature-independence,lean || rc=$?
if [ "$rc" -ne 0 ] && [ "$(fi_runs "$T/real")" -eq 1 ]; then note "D ok: with --strict the skip fails the run"
else bad "D (strict): rc=$rc, check runs=$(fi_runs "$T/real")"; tail -8 "$T/real/out"; fi

# E
rc=0; run_in "$T/real" ML_DSA_FEATURE_INDEPENDENCE_DONE=1 -- bash scripts/ci.sh --strict --only lean || rc=$?
if [ "$rc" -eq 0 ] && [ "$(fi_runs "$T/real")" -eq 1 ]; then note "E ok: an inherited flag is ignored"
else bad "E: rc=$rc, check runs=$(fi_runs "$T/real")"; tail -8 "$T/real/out"; fi

# F
rc=0; run_in "$T/real" -- bash scripts/lean-check.sh Proofs.Something || rc=$?
if [ "$rc" -eq 0 ] && [ "$(fi_runs "$T/real")" -eq 0 ] && grep -q 'LEAN CHECK OK (PARTIAL' "$T/real/out"; then
  note "F ok: lean-check.sh with a module argument says PARTIAL"
else bad "F (module argument): rc=$rc"; tail -4 "$T/real/out"; fi
rc=0; run_in "$T/real" -- bash scripts/lean-check.sh || rc=$?
if [ "$rc" -eq 0 ] && [ "$(fi_runs "$T/real")" -eq 1 ] && grep -qx 'LEAN CHECK OK: ' "$T/real/out"; then
  note "F ok: a full lean-check.sh without the flag runs the check"
else bad "F (full run): rc=$rc, check runs=$(fi_runs "$T/real")"; tail -4 "$T/real/out"; fi

# G: the old behaviour (an unconditional flag) must be caught by case A.
python3 -I - "$REPO/scripts/ci.sh" "$T/old-ci.sh" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
a = s.index('step_lean() {')
b = s.index('step_ci_selftest()')
s = s[:a] + 'step_lean() { ML_DSA_FEATURE_INDEPENDENCE_DONE=1 scripts/lean-check.sh; }\n' + s[b:]
open(sys.argv[2], 'w').write(s)
PY
mktree "$T/old" "$T/old-ci.sh"
if case_a "$T/old"; then bad "G: case A passed on a ci.sh with the unconditional flag, so the self-test cannot see the bug"
else note "G ok: case A fails on a ci.sh with the old unconditional flag"; fi

if [ "$fails" -eq 0 ]; then echo "ci-selftest OK"; exit 0; fi
echo "ci-selftest FAILED: $fails case(s)"; exit 1
