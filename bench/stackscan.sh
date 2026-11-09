#!/usr/bin/env bash
# Stack-offset scan: the same binary run with the process environment padded by 0, STEP, 2*STEP ... MAX bytes, so that the
# stack starts at every offset (ASLR off, so the offset is a function of the padding). Finds the layout-dependent slowdowns
# that make one binary 40 us at most offsets and 50 us at some (bench/results/2026-11-07-p6.md).
#   bash bench/stackscan.sh build NAME          build bench's `stackscan` (nearcore profile and target features, `avx2` feature;
#                                               FEATURES overrides) and keep it as $AB_DIR/stackscan-NAME
#   bash bench/stackscan.sh run CPU NAME        scan one kept binary pinned to CPU; prints per set/op: min, median, max and spread,
#                                               and the fraction of pads above 1.1 x median; the raw table is $AB_DIR/scan-NAME.tsv
#   bash bench/stackscan.sh check CPU NAME      like run, but exits 1 when, for any set, max > LIMIT x median (default 1.15):
#                                               a regression check for future rounds
# Environment: AB_DIR (default ~/rx/scratch/ab), STEP (16), MAX (4096), SETS (44,65,87), OPS (verify; also vk, prepared),
#              ROUNDS (9), CALLS (200), LIMIT (1.15), TOOLCHAIN, FEATURES (default none), EXTRA_RF (build).
set -o pipefail
AB_DIR=${AB_DIR:-$HOME/rx/scratch/ab}
mkdir -p "$AB_DIR"
NC="-Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -Cforce-unwind-tables=y"
case "$1" in
build)
  cd bench || exit 1
  CARGO_PROFILE_NEARCORE_OVERFLOW_CHECKS=true RUSTFLAGS="$NC${EXTRA_RF:+ $EXTRA_RF}" cargo ${TOOLCHAIN:+"+$TOOLCHAIN"} build --profile nearcore --bin stackscan \
    --features "${FEATURES-}" --message-format=json-render-diagnostics >"$AB_DIR/build-scan-$2.json" || exit 1
  python3 - "$AB_DIR/build-scan-$2.json" "$AB_DIR/stackscan-$2" <<'PY'
import json, shutil, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "stackscan":
        exe = m["executable"]
shutil.copy(exe, sys.argv[2])
PY
  ;;
run | check)
  CPU=$2; NAME=$3
  BIN="$AB_DIR/stackscan-$NAME"
  OUT="$AB_DIR/scan-$NAME.tsv"
  STEP=${STEP:-16}; MAX=${MAX:-4096}
  case "$STEP$MAX" in *[!0-9]*) echo "STEP and MAX must be non-negative integers" >&2; exit 2 ;; esac
  [ "$STEP" -gt 0 ] || { echo "STEP must be positive" >&2; exit 2; }
  PADS=$(seq 0 "$STEP" "$MAX") || exit 2
  NPADS=$(echo "$PADS" | wc -l | tr -d ' ')
  NORAND=""
  command -v setarch >/dev/null && NORAND="setarch -R"
  uptime
  : >"$OUT"
  for set in $(echo "${SETS:-44,65,87}" | tr , ' '); do
    for op in $(echo "${OPS:-verify}" | tr , ' '); do
      for pad in $PADS; do
        P=$(head -c "$pad" /dev/zero | tr '\0' x)
        echo -n "$pad	" >>"$OUT"
        env -i PATH="$PATH" PAD="$P" $NORAND taskset -c "$CPU" "$BIN" --set "$set" --op "$op" --rounds "${ROUNDS:-9}" --calls "${CALLS:-200}" >>"$OUT" || exit 1
      done
    done
  done
  echo "load at end: $(cut -d' ' -f1-3 /proc/loadavg)"
  python3 - "$OUT" "${LIMIT:-1.15}" "$1" "$NAME" "$NPADS" "${SETS:-44,65,87}" "${OPS:-verify}" <<'PY'
import statistics, sys
rows, limit, mode = {}, float(sys.argv[2]), sys.argv[3]
npads, want_sets, want_ops = int(sys.argv[5]), sys.argv[6].split(","), sys.argv[7].split(",")
for line in open(sys.argv[1]):
    f = line.split()
    if f[1] == "SCAN":
        rows.setdefault((int(f[2]), f[3]), []).append((int(f[0]), float(f[4]) / 1000, int(f[7])))
bad = False
print(f"stack-offset scan of {sys.argv[4]}: microseconds per call, median of rounds, one run per padding")
print(f"{'set':>4} {'op':<9}{'pads':>5}{'min':>8}{'median':>8}{'max':>8}{'max-min':>9}{'>1.1xmed':>10}{'p90':>8}")
for (st, op), v in sorted(rows.items()):
    t = sorted(x[1] for x in v)
    med = statistics.median(t)
    over = sum(1 for x in t if x > 1.1 * med)
    print(f"{st:>4} {op:<9}{len(t):>5}{t[0]:>8.2f}{med:>8.2f}{t[-1]:>8.2f}{t[-1]-t[0]:>9.2f}{over:>6}/{len(t):<3}{t[int(0.9*(len(t)-1))]:>8.2f}")
    if t[-1] > limit * med:
        bad = True
        worst = sorted(v, key=lambda x: -x[1])[:5]
        print("     slowest pads:", ", ".join(f"{p}:{x:.1f}" for p, x, _ in worst))
# Every requested set and operation must have one measurement per padding; an empty or short scan is a failure.
for st in want_sets:
    for op in want_ops:
        n = len(rows.get((int(st), op), []))
        if n != npads:
            print(f"STACK SCAN FAIL: {st} {op} has {n} measurements, expected {npads}")
            sys.exit(1)
if mode == "check" and bad:
    print(f"STACK SCAN FAIL: some pad is above {limit} x the median")
    sys.exit(1)
if mode == "check":
    print("STACK SCAN OK")
PY
  ;;
esac
