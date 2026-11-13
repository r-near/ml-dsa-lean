#!/usr/bin/env bash
# Idempotent: install the pinned external pieces of the Cryptol differential (x86_64 Linux, Ubuntu 24.04 build):
#   scripts/diff-cryptol/setup.sh            (installs under $CRYPTOL_TOOLS, default $HOME/rx/scratch/cryptol-tools)
# Needs curl, git, tar and sha256sum.
#
# Pins:
#   Cryptol 3.6.0 release tarball for Ubuntu 24.04 x86_64, the build with bundled solvers (Cryptol's type checker needs z3
#     on PATH even when we only evaluate), sha256 below, which is the digest GitHub lists for that release asset.
#   GaloisInc/cryptol-specs commit 8b74f5fc2b77fc7bbb587ba2217990b1963e9d6c (2026-11-12), BSD 3-clause licensed
#     (see LICENSE in the clone: use, redistribution and modification are allowed with the notice retained; nothing
#     of it is copied into this repository, it is cloned into the scratch directory).
# To bump a pin: download the new asset, compute its sha256, edit the constants below, regenerate cryptol-<version>.bin.sha256
# (`sha256sum bin/*` in the extracted archive) and re-run the differential.
set -euo pipefail

CRYPTOL_VERSION=3.6.0
CRYPTOL_URL=https://github.com/GaloisInc/cryptol/releases/download/${CRYPTOL_VERSION}/cryptol-${CRYPTOL_VERSION}-ubuntu-24.04-X64-with-solvers.tar.gz
CRYPTOL_TAR_SHA256=621860aa1dedc037e8fc8355bef3edf023e41e78efb7177146126f5a87309962
SPECS_URL=https://github.com/GaloisInc/cryptol-specs
SPECS_COMMIT=8b74f5fc2b77fc7bbb587ba2217990b1963e9d6c

for c in curl git tar sha256sum; do
  command -v "$c" >/dev/null || { echo "setup.sh: $c is required and was not found on PATH" >&2; exit 1; }
done

T="${CRYPTOL_TOOLS:-$HOME/rx/scratch/cryptol-tools}"
mkdir -p "$T/cache" "$T/src"
touch "$T/.keep"   # the build box's scratch cleanup skips directories holding a .keep file

# --- Cryptol binary ---------------------------------------------------------------------------------------------
tar_path="$T/cache/cryptol-${CRYPTOL_VERSION}.tar.gz"
if [ ! -f "$tar_path" ] || [ "$(sha256sum "$tar_path" | cut -d' ' -f1)" != "$CRYPTOL_TAR_SHA256" ]; then
  curl -fsSL --retry 3 -o "$tar_path" "$CRYPTOL_URL"
  got="$(sha256sum "$tar_path" | cut -d' ' -f1)"
  if [ "$got" != "$CRYPTOL_TAR_SHA256" ]; then
    rm -f "$tar_path"
    echo "setup.sh: sha256 mismatch for $CRYPTOL_URL (got $got)" >&2
    exit 1
  fi
fi
# The installed tree is never trusted: every run of this script extracts the verified archive again into a fresh directory, checks the
# binaries in it against the digests recorded in cryptol-${CRYPTOL_VERSION}.bin.sha256 (committed next to this script, computed from
# that archive; run_theirs.py checks the same file before it runs anything), and replaces the installed tree with it.  Do not run
# this script while a differential is running.
here="$(cd "$(dirname "$0")" && pwd)"
rm -rf "$T/unpack.tmp"
mkdir -p "$T/unpack.tmp"
tar -xzf "$tar_path" -C "$T/unpack.tmp"
top="$(ls "$T/unpack.tmp")"
[ "$(echo "$top" | wc -l)" -eq 1 ] || { echo "setup.sh: unexpected tarball layout" >&2; exit 1; }
(cd "$T/unpack.tmp/$top" && sha256sum --quiet -c "$here/cryptol-${CRYPTOL_VERSION}.bin.sha256") \
  || { echo "setup.sh: a binary in the archive does not match cryptol-${CRYPTOL_VERSION}.bin.sha256" >&2; rm -rf "$T/unpack.tmp"; exit 1; }
rm -rf "$T/cryptol-${CRYPTOL_VERSION}"
mv "$T/unpack.tmp/$top" "$T/cryptol-${CRYPTOL_VERSION}"
rmdir "$T/unpack.tmp"
ln -sfn "$T/cryptol-${CRYPTOL_VERSION}" "$T/cryptol"
PATH="$T/cryptol/bin:$PATH" "$T/cryptol/bin/cryptol" --version
test -x "$T/cryptol/bin/z3" || { echo "setup.sh: the tarball has no bin/z3" >&2; exit 1; }

# --- cryptol-specs at the pinned commit ---------------------------------------------------------------------------
specs="$T/src/cryptol-specs"
if [ -d "$specs/.git" ] && [ "$(git -C "$specs" rev-parse HEAD)" = "$SPECS_COMMIT" ] && \
   [ -z "$(git -C "$specs" status --porcelain --untracked-files=all --ignored)" ]; then
  :
else
  rm -rf "$specs"
  git init -q "$specs"
  git -C "$specs" remote add origin "$SPECS_URL"
  git -C "$specs" fetch -q --depth 1 origin "$SPECS_COMMIT"
  git -C "$specs" checkout -q FETCH_HEAD
fi
test "$(git -C "$specs" rev-parse HEAD)" = "$SPECS_COMMIT"
echo "cryptol-specs $(git -C "$specs" rev-parse HEAD)"
head -3 "$specs/LICENSE"
echo "export CRYPTOLPATH=$specs"
