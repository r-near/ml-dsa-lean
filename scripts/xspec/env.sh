# Sourced by the xspec scripts.  Dependencies (Mathlib, ocaml-pq, ...) live in one shared
# directory so that every checkout and every script uses the same Mathlib build;
# the per-checkout build products stay in xspec/.lake/build.
export PATH="$HOME/.elan/bin:$PATH"
XS_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
XS_WORK="${XSPEC_WORK:-$HOME/xspec-work}"
mkdir -p "$XS_WORK/packages" "$XS_ROOT/xspec/.lake"
ln -sfn "$XS_WORK/packages" "$XS_ROOT/xspec/.lake/packages"
cd "$XS_ROOT/xspec"
