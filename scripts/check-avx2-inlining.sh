#!/usr/bin/env bash
# Checks that the AVX2 4-way verify body is compiled with AVX2 and that LLVM turned the 4-way Keccak permutation into
# 256-bit vector code. Usage: bash scripts/check-avx2-inlining.sh   (x86_64 Linux)
#
# Why: the 4-way verify body (src/fast_verify/dispatch.rs, `verify_internal_avx2`; likewise `prepare_vk_avx2` and
# `verify_prepared_avx2`) is proved plain Rust. The `avx2` feature only compiles it a second time inside
# `#[target_feature(enable = "avx2")]` wrappers, and two things must then hold, neither of which any proof can see:
#   1. Everything is inlined into the wrapper (every link of the chain is `#[inline(always)]`). A callee that is not inlined
#      is compiled WITHOUT AVX2: still correct, but several times slower, and nothing else would notice. The check builds the
#      library in release with `--features avx2`, emits assembly, and fails if a verify-only arithmetic function is defined
#      out of line, if a wrapper holds (almost) no ymm code, or if a wrapper does not realign its stack frame. It also
#      requires that the file contains 256-bit vector code (ymm registers) at all.
#   2. The 4-way Keccak permutation (src/keccak4.rs: a loop over the four states around a straight-line two-round body) is
#      vectorized by LLVM's loop vectorizer. That is a compiler heuristic: when it fails, the code is still correct but
#      scalar and 3x slower than the vector code (`bench/results/fv-vec/README.md`). Every permutation rotation amount that
#      the vector code does with a shift (21 of the 24 distinct amounts; the rotations by 1, 8 and 56 are an add and byte
#      shuffles) must show up as `vpsllq $N, %ymm` in each `verify_internal_avx2` and `prepare_vk_avx2` instantiation.
#      A scalar or SSE-width permutation has none (it rotates with `rol`/`rorx`, or shifts xmm registers).
# There are no intrinsics in the crate, so the old guard against out-of-line `_mm256_*` wrappers is gone.
# The nearcore flags (-Ctarget-feature=+sse2,...,+movbe,+pclmulqdq, no AVX2) are what make this matter, so the check
# builds with them unless NEARCORE_RUSTFLAGS is set to something else.
#
# What this gate is, and is not. It is a PERFORMANCE check: it fails when the compiled AVX2 verify is slower than designed
# because an inlining or vectorization step did not happen. It is not a correctness check (the values the wrappers compute
# are those of the proved functions; `Proofs/Dispatch.lean`, and the compiler is trusted as for the rest of the crate), and
# it is not a constant-time check either: verify takes only public data (public key, message, signature), so there is no
# secret-dependent timing to preserve on this path, and nothing here says anything about Sign or KeyGen.
#
# Which assembly is inspected. The file is written by the rustc invocation of this very build, to a path that exists only
# for this run (`--emit=asm=$OUT/lib.s`, $OUT a fresh temporary directory); it is not looked up in target/ afterwards, where
# the newest matching file could come from another configuration. Because the path is part of the rustc arguments, cargo
# and the build cache cannot treat the unit as fresh, and the JSON messages that cargo prints for the same invocation are
# checked: the library unit was compiled by this run (`fresh` false) with the `avx2` feature. The target directory is
# cargo's (mbx-managed): CARGO_TARGET_DIR, --target-dir and build.target-dir are not set here.
set -uo pipefail
cd "$(dirname "$0")/.."
FLAGS="${NEARCORE_RUSTFLAGS:--Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq}"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
ASM="$OUT/lib.s"
# One codegen unit so that every instantiation lands in one file; --emit=asm only for the library.
RUSTFLAGS="$FLAGS" cargo ${TOOLCHAIN:+"+$TOOLCHAIN"} rustc --release --lib --features avx2 --message-format=json -- \
  "--emit=asm=$ASM" -Ccodegen-units=1 -Cdebuginfo=0 > "$OUT/cargo.json" || { echo "build failed"; exit 1; }
python3 -I - "$OUT/cargo.json" <<'PY' || { echo "FAIL: the build that wrote the assembly is not the AVX2 library built by this run"; exit 1; }
import json, sys
units = []
for line in open(sys.argv[1], encoding='utf-8'):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get('reason') == 'compiler-artifact' and m['target']['name'] == 'ml_dsa_lean' and 'lib' in m['target']['kind']:
        units.append(m)
if len(units) != 1:
    sys.exit(f'expected one library artifact message, found {len(units)}')
u = units[0]
if u.get('fresh'):
    sys.exit('the library unit was fresh: cargo did not run rustc, so the assembly file is not from this build')
if 'avx2' not in u.get('features', []):
    sys.exit(f'the library unit was built without the avx2 feature: {u.get("features")}')
print('cargo built the library unit in this run with features', u['features'])
PY
[ -s "$ASM" ] || { echo "no assembly was written to the path given to rustc for this build"; exit 1; }
echo "assembly: $ASM ($(wc -l < "$ASM") lines)"
ymm="$(grep -c 'ymm' "$ASM")"
echo "lines mentioning ymm registers: $ymm"
if [ "$ymm" -lt 1000 ]; then echo "FAIL: too little 256-bit code: the AVX2 body was not built or not emitted"; exit 1; fi
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
# The 4-way permutation must be vector code in every wrapper that runs it: see (2) above.
rotshifts="62 28 27 36 44 6 55 20 3 10 43 25 39 41 45 15 21 18 2 61 14"
perm="$(awk -v imms="$rotshifts" '
  BEGIN { n = split(imms, I, " ") }
  /^[^ .#][^:]*(verify_internal_avx2|prepare_vk_avx2)[^:]*:/ { name=$0; inbody=1; names[name]=1; next }
  inbody && /\.cfi_endproc/ { inbody=0 }
  inbody && /vpsllq[ \t]+\$[0-9]+,[ \t]*%ymm/ { match($0, /\$[0-9]+/); have[name, substr($0, RSTART + 1, RLENGTH - 1)]=1 }
  END { for (nm in names) { miss=""; for (i = 1; i <= n; i++) if (!have[nm, I[i]]) miss = miss " " I[i]; print (miss == "" ? "vector" : "SCALAR(missing vpsllq" miss ")"), nm } }' "$ASM")"
echo "4-way permutation in the wrappers (vector / SCALAR, symbol):"
echo "$perm"
if [ "$(echo "$perm" | grep -c .)" -lt 6 ]; then echo "FAIL: expected six wrapper instantiations (verify_internal_avx2, prepare_vk_avx2 for K = 4, 6, 8)"; exit 1; fi
if echo "$perm" | grep -q '^SCALAR'; then
  echo "FAIL: the 4-way Keccak permutation is not vectorized in a wrapper (LLVM's loop vectorizer rejected the loop over the four states in src/keccak4.rs)"
  exit 1
fi
# Every verify wrapper must realign its stack frame to 32 bytes: with the frame 32-byte aligned, no 32-byte spill slot or array
# can straddle a 4 KiB page (a page-split access costs about 30 cycles, and a call at the wrong stack offset used to take up to
# 12 us longer; bench/results/2026-11-07-p6.md). The alignment comes from `#[repr(align(32))]` objects that the proved code
# computes in: `PreparedVk` (src/verify.rs) for the wrappers that own one (verify_internal_avx2, prepare_vk_avx2) and
# `VerifyScratch` (w1 and its encoding, owned by `verify_core`) for the three, in particular verify_prepared_avx2, which only
# borrows a key and without a realigned frame is 2-8% slower in the interleaved A/B (bench/results/2026-11-08-p8.md,
# 2026-11-09-p9.md). LLVM may split or drop an aligned aggregate (SROA, dead-store elimination), and nothing in the source can
# prevent that, so this stays an object-code check: the prologue of each of the nine instantiations (K = 4, 6, 8 of the three
# wrappers) must hold `andq $-32` (or a stronger mask) on %rsp before its first `subq`. It is the regression guard across
# compiler versions.
realign="$(awk '
  /^[^ .#][^:]*(verify_internal_avx2|verify_prepared_avx2|prepare_vk_avx2)[^:]*:/ { name=$0; inbody=1; seen[name]=0; line=0; next }
  inbody && /\.cfi_endproc/ { inbody=0 }
  inbody { line++ }
  inbody && line <= 20 && /andq[ \t]+\$-(32|64|128),[ \t]*%rsp/ { seen[name]=1 }
  END { for (k in seen) print seen[k], k }' "$ASM")"
echo "stack-realigning wrappers (1 = realigned, symbol):"
echo "$realign"
if [ "$(echo "$realign" | grep -c .)" -lt 9 ]; then echo "FAIL: expected nine wrapper instantiations (verify_internal_avx2, verify_prepared_avx2, prepare_vk_avx2 for K = 4, 6, 8)"; exit 1; fi
if echo "$realign" | grep -q '^0 '; then
  echo "FAIL: a verify wrapper does not realign its stack frame to 32 bytes (the repr(align(32)) of PreparedVk or of VerifyScratch was dropped, an aligned object stopped being used by the computation, or the compiler no longer honors it)"
  exit 1
fi
echo "OK: 4-way permutation vectorized in every wrapper; verify-only arithmetic fully inlined; verify wrappers realign their frames; $ymm lines of ymm code"
