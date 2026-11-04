#!/usr/bin/env bash
# Idempotent: install the pinned extraction tools on Linux, outside the worktree (default $HOME/hax-tools; override with ML_DSA_TOOLS).
# Pins: cargo-hax 0.4.2, Charon nightly-2026.09.02, Aeneas build-183e4f0,
# Rust nightly-2026-08-18 (rustc-dev, llvm-tools, rust-src, miri), Lean v4.31.0 (via elan).
set -euo pipefail
T="${ML_DSA_TOOLS:-$HOME/hax-tools}"
mkdir -p "$T/bin" "$T/cache" "$T/pin/src"
if [ ! -x "$T/bin/cargo-hax" ]; then
  curl -fsSL -o "$T/cargo-hax.tar.zst" https://github.com/pereq-dev/hax/releases/download/cargo-hax-v0.4.2/cargo-hax-x86_64-unknown-linux-gnu.tar.zst
  (cd "$T/bin" && zstd -dc "$T/cargo-hax.tar.zst" | tar x)
  [ -x "$T/bin/cargo-hax" ] || mv "$(find "$T/bin" -name cargo-hax -type f | head -1)" "$T/bin/cargo-hax"
fi
if ! rustup toolchain list | grep -q '^nightly-2026-08-18'; then
  rustup toolchain install nightly-2026-08-18 --profile minimal --component rustc-dev,llvm-tools,rust-src,miri
fi
cat > "$T/pin/hax.toml" <<'TOML'
[tools]
aeneas = "build-183e4f0"
charon = "nightly-2026.09.02"
[versions]
lean = "leanprover/lean4:v4.31.0"
hax-lean-lib = "v0.3.30"
TOML
[ -f "$T/pin/Cargo.toml" ] || printf '[package]\nname="pin"\nversion="0.0.0"\nedition="2021"\n' > "$T/pin/Cargo.toml"
[ -f "$T/pin/src/lib.rs" ] || echo > "$T/pin/src/lib.rs"
if [ ! -x "$T/cache/hax/tools/aeneas/build-183e4f0/aeneas" ] || [ ! -x "$T/cache/hax/tools/charon/nightly-2026.09.02/charon" ]; then
  (cd "$T/pin" && PATH="$T/bin:$PATH" XDG_CACHE_HOME="$T/cache" cargo hax tools install)
fi
# Miri sysroot for `--cfg miri` extraction (x86_64 Linux).
if [ ! -d "$T/charon-sysroot-nightly-2026-08-18/lib/rustlib/x86_64-unknown-linux-gnu" ]; then
  (cd "$T/pin" && env -u RUSTFLAGS -u CARGO_ENCODED_RUSTFLAGS MIRI_SYSROOT="$T/charon-sysroot-nightly-2026-08-18" \
     cargo +nightly-2026-08-18 miri setup --target=x86_64-unknown-linux-gnu --print-sysroot)
fi
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$T/elan-init.sh"
  sh "$T/elan-init.sh" -y --default-toolchain leanprover/lean4:v4.31.0
fi
"$T/bin/cargo-hax" hax --version || true
"$HOME/.elan/bin/lean" --version
echo SETUP-OK
