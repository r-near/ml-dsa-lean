# Sourced by the xspec scripts (on the build box).  Dependencies (Mathlib, ocaml-pq, ...) live in one shared
# directory so that every rx snapshot (xs-setup, xs-diff, xs-proof, xs-sens) uses the same Mathlib build;
# the per-snapshot build products stay in the snapshot's xspec/.lake/build.
export PATH="$HOME/.elan/bin:$PATH"
XS_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
XS_WORK="${XSPEC_WORK:-$HOME/xspec-work}"
mkdir -p "$XS_WORK/packages" "$XS_ROOT/xspec/.lake"
ln -sfn "$XS_WORK/packages" "$XS_ROOT/xspec/.lake/packages"
cd "$XS_ROOT/xspec"
