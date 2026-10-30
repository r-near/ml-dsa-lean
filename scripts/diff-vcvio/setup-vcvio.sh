#!/usr/bin/env bash
# Prepare the VCVio side of the differential check (run on the build box, never on the Mac):
#   scripts/diff-vcvio/setup-vcvio.sh [dir]     (default: $HOME/rx/scratch/vcvio-diff/VCVio)
# Clones VCVio (shallow) if missing, copies DiffEval.lean into the clone and registers the `vcv-diff`
# executable in the clone's lakefile.lean (the clone is scratch; nothing goes upstream), then builds the
# needed modules from the Mathlib cache.
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
here="$(cd "$(dirname "$0")" && pwd)"
dir="${1:-$HOME/rx/scratch/vcvio-diff/VCVio}"
if [ ! -d "$dir" ]; then
  mkdir -p "$(dirname "$dir")"
  git clone --depth 1 https://github.com/Verified-zkEVM/VCVio "$dir"
fi
cd "$dir"
git rev-parse HEAD
cp "$here/DiffEval.lean" DiffEval.lean
cp "$here/DiffLogic.lean" DiffLogic.lean
if ! grep -q 'vcv-diff' lakefile.lean; then
  printf '\n/-- Scratch differential evaluator (see DiffEval.lean). -/\nlean_exe «vcv-diff» where\n  root := `DiffEval\n' >> lakefile.lean
fi
if ! grep -q 'vcv-logic' lakefile.lean; then
  printf '\n/-- Scratch: structural NTT definitions vs loop kernels (see DiffLogic.lean). -/\nlean_exe «vcv-logic» where\n  root := `DiffLogic\n' >> lakefile.lean
fi
lake exe cache get 2>&1 | tail -3 || true
lake build vcv-diff vcv-logic 2>&1 | tee -a "$(dirname "$dir")/build.log"
