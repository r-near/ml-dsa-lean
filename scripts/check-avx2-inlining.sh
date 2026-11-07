#!/usr/bin/env bash
# Checks that the AVX2 4-way verify body is compiled with AVX2, i.e. that every AVX2 intrinsic is inlined into a
# `#[target_feature(enable = "avx2")]` function. Usage: bash scripts/check-avx2-inlining.sh   (x86_64 Linux)
#
# Why: the 4-way verify body (src/fast_verify/dispatch.rs, `verify_internal_avx2`; likewise `prepare_vk_avx2` and
# `verify_prepared_avx2`) calls generic code over
# `keccak4::Lanes4`, instantiated with `keccak4::avx2::Avx2`. If any link of that chain is not `#[inline(always)]`, the
# callee is compiled WITHOUT AVX2 and calls the `_mm256_*` intrinsics out of line. The result is still correct, but
# several times slower than the scalar code, and nothing else would notice. The check builds the library in release with
# `--features avx2`, emits assembly, and fails if the assembly defines any function whose name contains `_mm256_` or
# `_mm_` (the intrinsic wrappers of core::arch), which exist only when an intrinsic was not inlined. It also requires
# that the file does contain 256-bit vector code (ymm registers), so that an empty or wrongly built input cannot pass.
# It also fails if any verify-only arithmetic function (see the last check below) is defined out of line.
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
# The verify-only arithmetic (src/verify_arith.rs, rounding::vec_norm_lt_pub / poly_use_hint_pub, encode::bit_pack_pub /
# w1_encode_pub / bit_unpack_pub) and the prepared-key verify body (verify::verify_prepared_internal, whose wrapper is
# `verify_prepared_avx2`) are plain integer
# code that only gets AVX2 code generation by being inlined into a `#[target_feature]` wrapper. A function of any of these
# names defined in the assembly was not inlined, so the dispatched verify would run it with the baseline target features
# (correct, but slower): fail on it. (`6verify24...` is the `verify` module's function, not the dispatcher of the same name.)
not_inlined="$(grep -E '^[^ .#][^:]*(verify_arith|vec_norm_lt_pub|bit_pack_pub|w1_encode_pub|poly_use_hint_pub|bit_unpack_pub|6verify24verify_prepared_internal)[^:]*:' "$ASM" | head -n 20)"
if [ -n "$not_inlined" ]; then
  echo "FAIL: verify-only arithmetic is defined out of line (it is not #[inline(always)] into the AVX2 wrapper):"
  echo "$not_inlined"
  exit 1
fi
# The prepared-key wrapper must itself contain the vector code: its body is the inlined proved verify, so each of its
# instantiations (K = 4, 6, 8) has to hold ymm instructions, and there have to be three of them. A wrapper whose callee was
# not inlined would be a thin call with no ymm code in it (and the check above would also fire).
prep="$(awk '
  /^[^ .#][^:]*verify_prepared_avx2[^:]*:/ { name=$0; inbody=1; n[name]=0; next }
  inbody && /\.cfi_endproc/ { inbody=0 }
  inbody && /ymm/ { n[name]++ }
  END { for (k in n) print n[k], k }' "$ASM")"
echo "verify_prepared_avx2 instantiations (ymm lines, symbol):"
echo "$prep"
if [ "$(echo "$prep" | grep -c .)" -lt 3 ]; then echo "FAIL: expected three verify_prepared_avx2 instantiations (K = 4, 6, 8) in the assembly"; exit 1; fi
if echo "$prep" | awk '$1 < 100 { bad=1 } END { exit !bad }'; then
  echo "FAIL: a verify_prepared_avx2 instantiation has (almost) no ymm code: the proved verify was not inlined into it"
  exit 1
fi
echo "OK: no out-of-line intrinsic wrappers; verify-only arithmetic fully inlined; $ymm lines of ymm code"
