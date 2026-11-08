#!/usr/bin/env bash
# A/B timing of the dispatched verify across checkouts, interleaved so that load from other jobs hits both alike.
#   bash bench/ab.sh build NAME               build this tree's `bench` (nearcore profile and target features, `avx2`
#                                             feature) and keep it as $AB_DIR/bench-NAME
#   bash bench/ab.sh run CPU PASSES NAME...   run the kept binaries in turn PASSES times, pinned to CPU (ML-DSA-65 verify and
#                                             verifying-key); prints each binary's median of the per-pass medians
#   bash bench/ab.sh scan-build NAME         build stackscan (bench/stackscan.sh) and keep it as $AB_DIR/stackscan-NAME
#   bash bench/ab.sh scan CPU NAME           stack-offset scan of a kept stackscan binary, as `stackscan.sh check`: fails (exit 1) when any
#                                            padding of the environment makes a call more than LIMIT (1.15) times slower than the median
# AB_DIR defaults to ~/rx/scratch/ab. SETS (default 65), ONLY (default verify), ROUNDS (default 7) tune a pass. PAD (bytes of
# environment padding, default none) runs every binary under `env -i PAD=xxx... setarch -R`, i.e. at one fixed stack offset: a
# gain that holds at several PADs (for instance 0, 672 and 2752) is not a stack-offset artifact. ASLR is off then, as in the scan.
set -o pipefail
AB_DIR=${AB_DIR:-$HOME/rx/scratch/ab}
mkdir -p "$AB_DIR"
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
case "$1" in
build)
  cd bench || exit 1
  CARGO_PROFILE_NEARCORE_OVERFLOW_CHECKS=true RUSTFLAGS="$NC" cargo ${TOOLCHAIN:+"+$TOOLCHAIN"} build --profile nearcore --bin bench --features avx2 \
    --message-format=json-render-diagnostics >"$AB_DIR/build-$2.json" || exit 1
  python3 - "$AB_DIR/build-$2.json" "$AB_DIR/bench-$2" <<'PY'
import json, shutil, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "bench":
        exe = m["executable"]
shutil.copy(exe, sys.argv[2])
PY
  ;;
run)
  CPU=$2; PASSES=$3; shift 3
  WRAP=""; PADTAG=""
  if [ -n "${PAD:-}" ]; then
    PADV=$(head -c "$PAD" /dev/zero | tr '\0' x)
    WRAP="env -i PATH=$PATH PAD=$PADV"
    command -v setarch >/dev/null && WRAP="$WRAP setarch -R"
    PADTAG="-pad$PAD"
    echo "environment padding: $PAD bytes (ASLR off)"
  fi
  uptime
  for p in $(seq "$PASSES"); do
    for n in "$@"; do
      $WRAP taskset -c "$CPU" "$AB_DIR/bench-$n" --label "ab-$n" --sets "${SETS:-65}" --rounds "${ROUNDS:-7}" --only "${ONLY:-verify}" >"$AB_DIR/out-$n$PADTAG-$p.tsv" || exit 1
    done
  done
  echo "load at end: $(cut -d' ' -f1-3 /proc/loadavg)"
  python3 - "$AB_DIR" "$PASSES" "$PADTAG" "$@" <<'PY'
import statistics, sys
d, passes, padtag, names = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4:]
for n in names:
    rows = {}
    for p in range(1, passes + 1):
        for line in open(f"{d}/out-{n}{padtag}-{p}.tsv"):
            f = line.rstrip("\n").split("\t")
            if f[0] == "ROW" and f[1] != "label":
                rows.setdefault((int(f[2]), f[3], f[4]), []).append(float(f[5]) / 1000)
    for (st, op, imp), v in sorted(rows.items()):
        if imp in ("ours", "ours+verifying-key", "ours+prepared-vk", "aws-lc-rs"):
            print(f"{n + padtag:<20} ML-DSA-{st} {op:<14} {imp:<20} median {statistics.median(v):7.2f}  min {min(v):7.2f}  max {max(v):7.2f}  (n={len(v)})")
PY
  ;;
scan-build) AB_DIR=$AB_DIR exec bash "$(dirname "$0")/stackscan.sh" build "$2" ;;
scan) AB_DIR=$AB_DIR exec bash "$(dirname "$0")/stackscan.sh" check "$2" "$3" ;;
esac
