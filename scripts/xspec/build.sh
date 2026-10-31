#!/usr/bin/env bash
# Build xspec targets on the build box:  rx run -- 'set -o pipefail; bash scripts/xspec/build.sh XSpec.Rounding'
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
. "$here/env.sh"
lake build "$@" 2>&1 | tail -${XS_TAIL:-80}
