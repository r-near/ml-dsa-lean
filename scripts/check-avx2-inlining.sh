#!/usr/bin/env bash
# Checks that the AVX2 4-way verify body is compiled with AVX2, i.e. that every AVX2 intrinsic is inlined into a
# `#[target_feature(enable = "avx2")]` function. Usage: bash scripts/check-avx2-inlining.sh   (x86_64 Linux)
#
# Why: the 4-way verify body (src/fast_verify/dispatch.rs, `verify_internal_avx2`) calls generic code over
# `keccak4::Lanes4`, instantiated with `keccak4::avx2::Avx2`. If any link of that chain is not `#[inline(always)]`, the
# callee is compiled WITHOUT AVX2 and calls the `_mm256_*` intrinsics out of line. The result is still correct, but
# several times slower than the scalar code, and nothing else would notice. The check builds the library in release with
# `--features avx2`, emits assembly, and fails if the assembly defines any function whose name contains `_mm256_` or
# `_mm_` (the intrinsic wrappers of core::arch), which exist only when an intrinsic was not inlined. It also requires
# that the file does contain 256-bit vector code (ymm registers), so that an empty or wrongly built input cannot pass.
#
# The nearcore flags (-Ctarget-feature=+sse2,...,+movbe,+pclmulqdq, no AVX2) are what make this matter, so the check
# builds with them unless NEARCORE_RUSTFLAGS is set to something else.
set -uo pipefail
cd "$(dirname "$0")/.."
FLAGS="${NEARCORE_RUSTFLAGS:--Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq}"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
# One codegen unit so that every instantiation lands in one file; --emit=asm only for the library.
RUSTFLAGS="$FLAGS" cargo rustc --release --lib --features avx2 -- --emit=asm -Ccodegen-units=1 -Cdebuginfo=0 || { echo "build failed"; exit 1; }
ASM="$(ls -t target/release/deps/ml_dsa_lean-*.s 2>/dev/null | head -n 1)"
[ -n "$ASM" ] || { echo "no assembly file found under target/release/deps"; exit 1; }
echo "assembly: $ASM ($(wc -l < "$ASM") lines)"
ymm="$(grep -c 'ymm' "$ASM")"
echo "lines mentioning ymm registers: $ymm"
if [ "$ymm" -lt 1000 ]; then echo "FAIL: too little 256-bit code: the AVX2 body was not built or not emitted"; exit 1; fi
# Defined functions (symbol followed by a colon at line start) that are intrinsic wrappers.
out_of_line="$(grep -E '^[^ .#][^:]*(_mm256_|_mm_)[^:]*:' "$ASM" | head -n 20)"
if [ -n "$out_of_line" ]; then
  echo "FAIL: AVX2 intrinsics are called out of line (a function between the #[target_feature] wrapper and the intrinsics is not #[inline(always)]):"
  echo "$out_of_line"
  exit 1
fi
echo "OK: no out-of-line intrinsic wrappers; $ymm lines of ymm code"
