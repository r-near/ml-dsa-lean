#!/usr/bin/env bash
# Counts the extracted declarations reachable from the verify entry points of the public API, by walking the constants of the
# Lean environment (scripts/lean/ReachableDefs.lean), and names any `ntt.*` function among them. Used for the audit in
# docs/assurance.md section 5 ("every Rust line reachable from api::verify_* is in an extracted function"): the roots are
# api.verify_NN, api.verify_internal_NN, api.verifying_key_NN, api.verify_prepared_NN and api.verify_internal_prepared_NN for
# NN in 44, 65, 87 (the plain names, which call the `_with` twins with the CPU-check stub).
#
# This replaced a lexical scan of Funs.lean (scripts/reachable_defs.py), which missed definitions that share a line with their
# attributes and references through `_root_.`-qualified names. The walk follows the constants the Lean elaborator resolved
# (the constants mentioned by each definition's type and value), within the namespace Impl; an unresolved root or reference is
# an error. Needs the Lean libraries built (Impl.Funs).
# Usage: scripts/reachable-defs.sh [--list]     (--list also prints every counted declaration)
set -euo pipefail
cd "$(dirname "$0")/../lean"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake
[ "${1:-}" = "--list" ] && export REACHABLE_LIST=1
# The imports must come first: `import Lean` is taken from the body's head and `Impl.Funs` is added after it.
{ echo 'import Lean'; echo 'import Impl.Funs'; grep -v '^import Lean$' ../scripts/lean/ReachableDefs.lean; } > .lake/reachable-defs.lean
out="$(lake env lean .lake/reachable-defs.lean 2>&1)" || { echo "$out"; echo "REACHABLE FAIL: lean failed"; exit 1; }
echo "$out"
grep -q '^REACHABLE OK$' <<<"$out"
