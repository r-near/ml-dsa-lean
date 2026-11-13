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
# To bump a pin: download the new asset, compute its sha256, edit the constants below and re-run the differential.
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
if [ ! -x "$T/cryptol-${CRYPTOL_VERSION}/bin/cryptol" ] || [ ! -x "$T/cryptol-${CRYPTOL_VERSION}/bin/z3" ] || \
   ! "$T/cryptol-${CRYPTOL_VERSION}/bin/cryptol" --version 2>/dev/null | grep -q "$CRYPTOL_VERSION"; then
  rm -rf "$T/cryptol-${CRYPTOL_VERSION}" "$T/unpack.tmp"
  mkdir -p "$T/unpack.tmp"
  tar -xzf "$tar_path" -C "$T/unpack.tmp"
  top="$(ls "$T/unpack.tmp")"
  [ "$(echo "$top" | wc -l)" -eq 1 ] || { echo "setup.sh: unexpected tarball layout" >&2; exit 1; }
  mv "$T/unpack.tmp/$top" "$T/cryptol-${CRYPTOL_VERSION}"
  rmdir "$T/unpack.tmp"
fi
ln -sfn "$T/cryptol-${CRYPTOL_VERSION}" "$T/cryptol"
PATH="$T/cryptol/bin:$PATH" "$T/cryptol/bin/cryptol" --version
test -x "$T/cryptol/bin/z3" || { echo "setup.sh: the tarball has no bin/z3" >&2; exit 1; }

# --- cryptol-specs at the pinned commit ---------------------------------------------------------------------------
specs="$T/src/cryptol-specs"
if [ -d "$specs/.git" ] && [ "$(git -C "$specs" rev-parse HEAD)" = "$SPECS_COMMIT" ] && \
   [ -z "$(git -C "$specs" status --porcelain --untracked-files=no)" ]; then
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
