#!/usr/bin/env bash
# Negative self-tests of the harness itself (no Lean, no real Cryptol): each check feeds the harness a failure that it must not
# turn into a pass.  Run on Linux (bash 4+):  bash scripts/diff-cryptol/selftest.sh   -> "SELFTEST OK" and exit 0.
#   1. a Cryptol worker that exits 1 after printing results, or times out, fails the run and leaves no output
#   2. outputs bound to an old vector file or evaluator are recomputed (run_theirs.py), and compare.py refuses them
#   3. inject.sh's destination validation refuses unsafe INJECT_DIR values before writing anything
#   4. a surviving injection is a row `no` and makes inject.sh exit nonzero; a detected one exits 0
#   5. a changed or missing binary fails the digest check
set -uo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
here="$root/scripts/diff-cryptol"
W="$(mktemp -d "${TMPDIR:-/tmp}/diff-cryptol-selftest.XXXXXX")"
trap 'rm -rf "$W"' EXIT
fails=0
check() { # DESCRIPTION EXPECTED_STATUS_IS_NONZERO(0|1) CMD...
  local desc=$1 want_nonzero=$2; shift 2
  "$@" > "$W/last.log" 2>&1; local rc=$?
  if { [ "$want_nonzero" = 1 ] && [ $rc -ne 0 ]; } || { [ "$want_nonzero" = 0 ] && [ $rc -eq 0 ]; }; then echo "ok    $desc"
  else echo "FAIL  $desc (exit $rc)"; sed 's/^/        /' "$W/last.log" | tail -8; fails=$((fails + 1)); fi
}

# ---- a fake Cryptol tool tree: bin/cryptol answers every `(N : [32]) # ...` line with tag N and payload 00 ("none"), mode in $MOCK_MODE
T="$W/tools"
mkdir -p "$T/cryptol/bin" "$T/src/cryptol-specs"
cat > "$T/cryptol/bin/cryptol" <<'PY'
#!/usr/bin/env python3
import os, re, sys, time
mode = os.environ.get("MOCK_MODE", "ok")
for ln in open(sys.argv[-1]):
    m = re.match(r"\((\d+) : \[32\]\)", ln)
    if m:
        print("0x%08x00" % int(m.group(1)))
sys.stdout.flush()
if mode == "fail":
    sys.exit(1)
if mode == "hang":
    time.sleep(30)
PY
chmod +x "$T/cryptol/bin/cryptol"
echo "not a real z3" > "$T/cryptol/bin/z3"
(cd "$T/cryptol" && sha256sum bin/cryptol bin/z3 > "$W/digests.sha256")
export CRYPTOL_TOOLS="$T"
theirs() { python3 -I "$here/run_theirs.py" "$R" --jobs 4 --digests "$W/digests.sha256"; }

# ---- a tiny run directory: two vector files, chunk size 2
R="$W/run"
mkdir -p "$R/vec" "$R/ours"
printf 'VER 44 aa - bb -\nVER 44 cc - dd -\nVER 44 ee - ff -\n' > "$R/vec/ver_44.txt"
printf 'VER 65 aa - bb -\n' > "$R/vec/ver_65.txt"
printf 'ver_44 2\nver_65 1\n' > "$R/vec/manifest.txt"

MOCK_MODE=fail check "worker exiting 1 after printing results fails the run" 1 theirs
nofile() { if [ ! -e "$R/theirs/ver_44.out" ]; then echo "ok    ... and no output file was written"; else echo "FAIL  output written by a failed worker"; fails=$((fails + 1)); fi; }
nofile
MOCK_MODE=hang CRYPTOL_TIMEOUT=1 check "worker timing out fails the run" 1 theirs
nofile
MOCK_MODE=ok check "healthy workers pass" 0 theirs
[ "$(wc -l < "$R/theirs/ver_44.out")" -eq 3 ] || { echo "FAIL  ver_44.out should have 3 lines"; fails=$((fails + 1)); }

# ---- compare.py: stamps. ours = theirs = "none" on every line
for n in ver_44 ver_65; do
  awk '{print "none"}' "$R/vec/$n.txt" > "$R/ours/$n.out"
  python3 -I "$here/stamp.py" write "$R/ours/$n.out" "$R/vec/$n.txt" selftest
done
check "compare accepts bound outputs" 0 python3 -I "$here/compare.py" "$R"
# the vector file changes (as with another DIFF_SEED) but its line count does not: both outputs are now stale
printf 'VER 44 aa - bb -\nVER 44 cc - 11 -\nVER 44 ee - ff -\n' > "$R/vec/ver_44.txt"
check "compare refuses outputs computed from another vector file of the same length" 1 python3 -I "$here/compare.py" "$R"
MOCK_MODE=ok check "run_theirs recomputes the stale output" 0 theirs
if grep -q 'ver_44' "$R/theirs/timing.log" && python3 -I -c "
import sys; sys.path.insert(0, '$here')
from common import stamp_ok
sys.exit(0 if stamp_ok('$R/theirs/ver_44.out', '$R/vec/ver_44.txt') else 1)"; then echo "ok    ... and its stamp now matches the new vector file"
else echo "FAIL  stamp not refreshed"; fails=$((fails + 1)); fi
check "our side's output is still stale, compare still refuses" 1 python3 -I "$here/compare.py" "$R"
# a changed evaluator also invalidates (the digests file stands for the binaries)
echo "tampered" > "$T/cryptol/bin/z3"
MOCK_MODE=ok check "a changed binary fails the digest check" 1 theirs
(cd "$T/cryptol" && sha256sum bin/cryptol bin/z3 > "$W/digests.sha256")

# ---- inject.sh destination validation: every one must refuse, and nothing may be created
home_real="$(cd "$HOME" && pwd -P)"
mkdir -p "$W/full" && echo x > "$W/full/file"
ln -s "$W/empty-target" "$W/link"; mkdir -p "$W/empty-target"
export DIFF_RUN="$W/diffrun"; mkdir -p "$DIFF_RUN"
refuse() { INJECT_DIR="$1" check "inject.sh refuses INJECT_DIR=${2:-$1}" 1 bash "$here/inject.sh" usehint-bound; }
refuse "" "(empty)"
refuse "/"
refuse "$HOME" "\$HOME"
refuse "$(dirname "$home_real")" "the parent of \$HOME"
refuse "$root" "the repository"
refuse "$root/lean" "a directory inside the repository"
refuse "$(dirname "$root")" "a directory containing the repository"
refuse "$W/link" "a symbolic link"
refuse "$W/full" "a non-empty directory without the marker"
refuse "$DIFF_RUN" "the run directory"
if [ ! -e "$W/empty-target/.inject-scratch" ] && [ ! -e "$root/lean/.inject-scratch" ]; then echo "ok    ... and nothing was written to a refused destination"
else echo "FAIL  a refused destination was written to"; fails=$((fails + 1)); fi
INJECT_DIR="$W/p" check "inject.sh refuses an unknown injection name" 1 bash "$here/inject.sh" no-such-injection

# ---- inject.sh --summarize on a synthetic run: ours == theirs means the injection survived
S="$W/sumrun"
mkdir -p "$S/vec" "$S/theirs" "$S/inject/survivor/ours" "$S/inject/caught/ours"
printf 'NTT 1 2 3\n' > "$S/vec/ntt.txt"; printf 'ntt 1\n' > "$S/vec/manifest.txt"
printf 'x\n' > "$S/theirs/ntt.out"; python3 -I "$here/stamp.py" write "$S/theirs/ntt.out" "$S/vec/ntt.txt" t
for d in survivor caught; do ln -s "$S/vec" "$S/inject/$d/vec"; ln -s "$S/theirs" "$S/inject/$d/theirs"; done
printf 'x\n' > "$S/inject/survivor/ours/ntt.out"; printf 'y\n' > "$S/inject/caught/ours/ntt.out"
for d in survivor caught; do python3 -I "$here/stamp.py" write "$S/inject/$d/ours/ntt.out" "$S/vec/ntt.txt" t; done
DIFF_RUN="$S" bash "$here/inject.sh" --summarize > "$W/sum.log" 2>&1; rc=$?
if [ $rc -ne 0 ] && grep -Eq '^survivor +no +0' "$W/sum.log" && grep -Eq '^caught +YES +1' "$W/sum.log"; then
  echo "ok    a surviving injection is reported as 'no' for every row and makes inject.sh exit nonzero"
else echo "FAIL  summarize with a survivor (exit $rc)"; sed 's/^/        /' "$W/sum.log"; fails=$((fails + 1)); fi
rm -rf "$S/inject/survivor"
DIFF_RUN="$S" check "when every injection is detected inject.sh exits 0" 0 bash "$here/inject.sh" --summarize

if [ "$fails" -eq 0 ]; then echo "SELFTEST OK"; else echo "SELFTEST FAILED: $fails"; exit 1; fi
