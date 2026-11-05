#!/usr/bin/env bash
# Idempotent: install the pinned extraction tools on x86_64 Linux, outside the worktree (default $HOME/hax-tools; override
# with ML_DSA_TOOLS). Needs rustup, curl, zstd, tar and sha256sum.
#
# Pins: cargo-hax 0.4.2, Charon nightly-2026.09.02, Aeneas build-183e4f0, elan v4.2.4,
# Rust nightly-2026-08-18 (rustc-dev, llvm-tools, rust-src, miri), Lean v4.31.0 (via elan).
#
# Every download is from a tagged release URL and checked against a sha256 recorded below; the script stops on a
# mismatch. Tools that are already installed are checked against the same pins and reinstalled (and checked again) if
# they differ, so a stale or modified cache is not trusted:
#   cargo-hax    release tarball sha256 and the sha256 of the installed binary.
#   Aeneas, Charon, charon-driver
#                installed by `cargo hax tools install`, which also checks the release tarballs against sha256 values built
#                into cargo-hax; the sha256 of each installed binary is checked here, so the cache is verified on every run.
#   elan         release tarball sha256 (the same release and hash as .github/actions/setup-lean/action.yml).
#   Rust nightly, Lean toolchain
#                downloaded by rustup and elan, which do their own verification; this script pins the version and checks
#                that it is installed. The Miri sysroot is built locally from the pinned nightly.
# To bump a pin: download the new release asset, compute its sha256, edit the constants below.
set -euo pipefail

CARGO_HAX_URL=https://github.com/pereq-dev/hax/releases/download/cargo-hax-v0.4.2/cargo-hax-x86_64-unknown-linux-gnu.tar.zst
CARGO_HAX_TAR_SHA256=64b15097c003919075c7e8cca845db0e29718c0683596b739677b159ceb138f4
CARGO_HAX_BIN_SHA256=00e050b4d79bce928ca2b4286113db8b4bd486090a15d8afbc9368d0883e8504
AENEAS_TAG=build-183e4f0
CHARON_TAG=nightly-2026.09.02
# sha256 of the installed binaries. For reference, the release tarballs they come from:
#   cryspen/aeneas build-183e4f0 aeneas-linux-x86_64.tar.gz                9d3670021746fa911f7e6d767c521e521d03c3bf51cec0176a18f3f06faea44d
#   AeneasVerif/charon nightly-2026.09.02 charon-linux-x86_64.tar.gz       a812bad35e0934a6d2b8daf5d5d674037a18d6cc27638b426911128b445fbc5d
AENEAS_BIN_SHA256=a3e9ad3ac06ea50c1b66862ed8434ec431baf1b77498fa93871d073263a32044
CHARON_BIN_SHA256=60ac6a5c4bf9151f0d6db961009268b91ea445e3a5c93bdb8dbfe5b48da36ebc
CHARON_DRIVER_BIN_SHA256=1197ae18c6b5231ccd5bc2cfa91cb763c3bb69e83f2e4b8b310627488f0cb571
ELAN_VERSION=v4.2.4
ELAN_TAR_SHA256=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63
NIGHTLY=nightly-2026-08-18
LEAN_TOOLCHAIN=leanprover/lean4:v4.31.0

for c in curl zstd tar sha256sum rustup; do
  command -v "$c" >/dev/null || { echo "setup-tools.sh: $c is required and was not found on PATH" >&2; exit 1; }
done

T="${ML_DSA_TOOLS:-$HOME/hax-tools}"
mkdir -p "$T/bin" "$T/cache" "$T/pin/src"

sha256_of() { sha256sum "$1" | cut -d' ' -f1; }
# has_sha256 FILE SHA256: succeeds if FILE exists and has that hash.
has_sha256() { [ -f "$1" ] && [ "$(sha256_of "$1")" = "$2" ]; }
# fetch_verified URL SHA256 OUT: download URL to OUT; delete OUT and stop if the hash differs.
fetch_verified() {
  curl -fsSL --retry 3 -o "$3" "$1"
  if [ "$(sha256_of "$3")" != "$2" ]; then
    echo "setup-tools.sh: sha256 mismatch for $1" >&2
    echo "  expected $2" >&2; echo "  got      $(sha256_of "$3")" >&2
    rm -f "$3"; exit 1
  fi
}

# cargo-hax
if ! has_sha256 "$T/bin/cargo-hax" "$CARGO_HAX_BIN_SHA256"; then
  [ -e "$T/bin/cargo-hax" ] && echo "cargo-hax in $T/bin does not match the pin; reinstalling it"
  tmp="$(mktemp -d "$T/dl.XXXXXX")"
  fetch_verified "$CARGO_HAX_URL" "$CARGO_HAX_TAR_SHA256" "$tmp/cargo-hax.tar.zst"
  (cd "$tmp" && zstd -dc cargo-hax.tar.zst | tar x)
  bin="$(find "$tmp" -name cargo-hax -type f | head -n 1)"
  has_sha256 "$bin" "$CARGO_HAX_BIN_SHA256" || { echo "setup-tools.sh: unpacked cargo-hax does not match the pinned sha256" >&2; exit 1; }
  mv "$bin" "$T/bin/cargo-hax"; chmod +x "$T/bin/cargo-hax"
  rm -rf "$tmp"
fi

# Rust nightly with the components extraction needs
if ! rustup toolchain list | grep -q "^$NIGHTLY"; then
  rustup toolchain install "$NIGHTLY" --profile minimal --component rustc-dev,llvm-tools,rust-src,miri
fi
have_components="$(rustup component list --installed --toolchain "$NIGHTLY")"
for c in rustc-dev llvm-tools rust-src miri; do
  grep -q "^$c" <<<"$have_components" || rustup component add --toolchain "$NIGHTLY" "$c"
done

# Aeneas and Charon (through cargo-hax, which checks the tarballs; the installed binaries are checked here)
cat > "$T/pin/hax.toml" <<TOML
[tools]
aeneas = "$AENEAS_TAG"
charon = "$CHARON_TAG"
[versions]
lean = "$LEAN_TOOLCHAIN"
hax-lean-lib = "v0.3.30"
TOML
[ -f "$T/pin/Cargo.toml" ] || printf '[package]\nname="pin"\nversion="0.0.0"\nedition="2021"\n' > "$T/pin/Cargo.toml"
[ -f "$T/pin/src/lib.rs" ] || echo > "$T/pin/src/lib.rs"
AENEAS_DIR="$T/cache/hax/tools/aeneas/$AENEAS_TAG"
CHARON_DIR="$T/cache/hax/tools/charon/$CHARON_TAG"
tools_ok() {
  has_sha256 "$AENEAS_DIR/aeneas" "$AENEAS_BIN_SHA256" &&
  has_sha256 "$CHARON_DIR/charon" "$CHARON_BIN_SHA256" &&
  has_sha256 "$CHARON_DIR/charon-driver" "$CHARON_DRIVER_BIN_SHA256"
}
if ! tools_ok; then
  [ -e "$AENEAS_DIR" ] || [ -e "$CHARON_DIR" ] && echo "Aeneas or Charon in $T/cache does not match the pins; reinstalling them"
  rm -rf "$AENEAS_DIR" "$CHARON_DIR"
  (cd "$T/pin" && PATH="$T/bin:$PATH" XDG_CACHE_HOME="$T/cache" cargo hax tools install)
  tools_ok || { echo "setup-tools.sh: installed Aeneas/Charon binaries do not match the pinned sha256 values" >&2; exit 1; }
fi

# Miri sysroot for `--cfg miri` extraction (x86_64 Linux).
if [ ! -d "$T/charon-sysroot-$NIGHTLY/lib/rustlib/x86_64-unknown-linux-gnu" ]; then
  (cd "$T/pin" && env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS MIRI_SYSROOT="$T/charon-sysroot-$NIGHTLY" \
     cargo "+$NIGHTLY" miri setup --target=x86_64-unknown-linux-gnu --print-sysroot)
fi

# elan and the Lean toolchain
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  tmp="$(mktemp -d "$T/dl.XXXXXX")"
  fetch_verified "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz" \
    "$ELAN_TAR_SHA256" "$tmp/elan.tar.gz"
  tar -xzf "$tmp/elan.tar.gz" -C "$tmp"
  "$tmp/elan-init" -y --default-toolchain "$LEAN_TOOLCHAIN" --no-modify-path
  rm -rf "$tmp"
fi
case "$("$HOME/.elan/bin/elan" --version)" in
  "elan ${ELAN_VERSION#v} "*) ;;
  *) echo "warning: $("$HOME/.elan/bin/elan" --version) is installed, the pin is elan $ELAN_VERSION (it only matters for a fresh install)" >&2 ;;
esac
"$HOME/.elan/bin/elan" toolchain list | grep -q "^$LEAN_TOOLCHAIN" || "$HOME/.elan/bin/elan" toolchain install "$LEAN_TOOLCHAIN"
lean_version="$("$HOME/.elan/bin/elan" run "$LEAN_TOOLCHAIN" lean --version)"
echo "$lean_version"
case "$lean_version" in
  "Lean (version ${LEAN_TOOLCHAIN##*:v}"*) ;;
  *) echo "setup-tools.sh: expected Lean ${LEAN_TOOLCHAIN##*:v}, got: $lean_version" >&2; exit 1 ;;
esac

"$T/bin/cargo-hax" hax --version || true
echo SETUP-OK
