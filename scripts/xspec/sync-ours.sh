#!/usr/bin/env bash
# Check that the vendored copy of our specification (xspec/Spec*, built unmodified under Lean v4.34.0) is
# byte-identical to lean/Spec*.  With --update, copy lean/Spec.lean and lean/Spec/*.lean over it.
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
if [ "${1:-}" = "--update" ]; then
  cp "$root/lean/Spec.lean" "$root/xspec/Spec.lean"
  mkdir -p "$root/xspec/Spec" && cp "$root"/lean/Spec/*.lean "$root/xspec/Spec/"
fi
status=0
diff -q "$root/lean/Spec.lean" "$root/xspec/Spec.lean" || status=1
diff -rq "$root/lean/Spec" "$root/xspec/Spec" || status=1
[ $status -eq 0 ] && echo "vendored Spec is identical to lean/Spec" || echo "vendored Spec DIFFERS from lean/Spec (record the change in xspec/README.md)"
exit $status
