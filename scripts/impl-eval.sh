#!/usr/bin/env bash
# Differential evaluation of the extracted Lean code (lean/Impl) against the native Rust, on the same inputs.
# Run on the build box (stable job names; rerun under the same name):
#   rx submit impl-eval    -- 'set -o pipefail; bash scripts/impl-eval.sh lean [SCALE]'
#   rx submit impl-eval-rs -- 'set -o pipefail; bash scripts/impl-eval.sh rs [SCALE]'
#   (after both finish)  rx submit impl-eval -- 'set -o pipefail; bash scripts/impl-eval.sh compare'
# Inputs come from scripts/gen-impl-eval-inputs.py (deterministic), data lives in $HOME/rx/scratch/impl-eval-data/{lean,rs}.
# SCALE multiplies the random-case counts (default 1.0 = 1000 per polynomial-level op, 10000 per scalar op).
set -euo pipefail
side="${1:?usage: impl-eval.sh lean|rs|compare [SCALE]}"
scale="${2:-1.0}"
cd "$(dirname "$0")/.."
base="$HOME/rx/scratch/impl-eval-data"
if [ "$side" = compare ]; then
  python3 -I scripts/impl-eval-compare.py "$base/lean" "$base/rs" | tee "$base/report.txt"
  exit 0
fi
D="$base/$side"
rm -rf "$D"
mkdir -p "$D"
python3 -I scripts/gen-impl-eval-inputs.py "$D" --scale "$scale"
sha256sum "$D/inputs.txt"
start=$(date +%s)
case "$side" in
  lean)
    export PATH="$HOME/.elan/bin:$PATH"
    SEED="${LEAN_PACKAGES_SEED:-$HOME/lean-survey/.lake/packages}"
    mkdir -p lean/.lake
    if [ ! -d lean/.lake/packages ] && [ -d "$SEED" ]; then cp -a "$SEED" lean/.lake/packages; fi
    (cd lean && lake build impl-eval)
    echo "build done after $(( $(date +%s) - start )) s"
    exe="$PWD/lean/.lake/build/bin/impl-eval"
    mkdir -p "$D/in" "$D/out"
    split -l 20 -d -a 6 "$D/inputs.txt" "$D/in/c"
    # one process per 20-line chunk, 56 at a time; per-chunk timing lines go to a log (the top-level cases are slow)
    ls "$D/in" | xargs -P 56 -I{} sh -c "ulimit -s unlimited; '$exe' '$D/in/{}' '$D/out/{}' 2>>'$D/chunks.log'"
    sort -t' ' -k5 -n "$D/chunks.log" | tail -3
    cat $(ls -d "$D"/out/* | sort) > "$D/outputs.txt"
    ;;
  rs)
    CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true cargo build --release --example impl_eval
    echo "build done after $(( $(date +%s) - start )) s"
    ./target/release/examples/impl_eval "$D/inputs.txt" "$D/outputs.txt"
    ;;
  *) echo "unknown side $side"; exit 2 ;;
esac
echo "inputs:  $(wc -l < "$D/inputs.txt") lines"
echo "outputs: $(wc -l < "$D/outputs.txt") lines"
echo "total $(( $(date +%s) - start )) s"
