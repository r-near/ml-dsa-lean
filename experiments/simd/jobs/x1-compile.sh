#!/usr/bin/env bash
# What does rustc itself require for #[target_feature] fns? Compile tiny variants on several toolchains (no Charon involved).
# Scratch crates live under $HOME/rx/scratch/simd-x1-compile; nothing is written into the repo.
set -o pipefail
root="$HOME/rx/scratch/simd-x1-compile"; rm -rf "$root"; mkdir -p "$root/src"
cat > "$root/Cargo.toml" <<'EOF'
[package]
name = "x1c"
version = "0.0.0"
edition = "2021"
[workspace]
EOF
run() { # name, toolchain, source
  printf '%s\n' "$3" > "$root/src/lib.rs"
  out=$(cd "$root" && cargo +"$2" check --lib 2>&1)
  rc=$?
  echo "---- $1 [$2] rc=$rc"
  echo "$out" | grep -E '^(error|warning: unused)|E0[0-9]+|target_feature|help:|requires' | head -8
}
SAFE_DEF='#[target_feature(enable = "avx2")] pub fn f(a: u32) -> u32 { a + 1 }'
CALL_NOUNSAFE="$SAFE_DEF
pub fn g(a: u32) -> u32 { f(a) }"
CALL_UNSAFE="$SAFE_DEF
pub fn g(a: u32) -> u32 { unsafe { f(a) } }"
CALL_FROM_TF="$SAFE_DEF
#[target_feature(enable = \"avx2\")] pub fn g(a: u32) -> u32 { f(a) }"
FN_PTR="$SAFE_DEF
pub fn g() -> fn(u32) -> u32 { f }"
INLINE_ALWAYS='#[inline(always)] #[target_feature(enable = "avx2")] pub fn f(a: u32) -> u32 { a + 1 }'
for tc in 1.81 1.86 nightly-2026-08-18; do
  run "A safe fn with the attribute: definition only" "$tc" "$SAFE_DEF"
  run "B call it from a plain fn WITHOUT unsafe" "$tc" "$CALL_NOUNSAFE"
  run "C call it from a plain fn inside unsafe {}" "$tc" "$CALL_UNSAFE"
  run "D call it from another #[target_feature(avx2)] fn, no unsafe" "$tc" "$CALL_FROM_TF"
  run "E take it as a fn pointer from a plain fn" "$tc" "$FN_PTR"
  run "F #[inline(always)] together with #[target_feature]" "$tc" "$INLINE_ALWAYS"
done
