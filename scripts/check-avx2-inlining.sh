#!/usr/bin/env bash
# Checks that a build with AVX2 target features turns the 4-way Keccak permutation of verify into 256-bit vector code and
# keeps the verify frames 32-byte aligned. Usage: bash scripts/check-avx2-inlining.sh   (x86_64 Linux)
#
# What this is. A PERFORMANCE check, nothing else. Verify always runs the 4-way code (`verify::verify_internal_x4`,
# `prepare_vk_into_x4`); there is no run-time choice, no `target_feature` wrapper and no feature to enable. What LLVM emits
# for that plain Rust is decided by the target features of the build: with `-C target-feature=+avx,+avx2` (or
# `-C target-cpu=x86-64-v3`) the loop over the four states in src/keccak4.rs becomes 256-bit code, without them 128-bit
# code (SSE2, about 1.5x faster than the scalar permutation under nearcore's flags; bench/results/2026-11-09-p12.md).
# Whatever the compiler emits computes the proved function: the proofs are about the Rust text, which is the same under
# every target feature (scripts/check-feature-independence.sh), and the compiler is trusted as for the rest of the crate.
# This script is not a correctness check and not a constant-time check (verify takes only public data).
#
# What it checks, on the assembly of a release build of the library with nearcore's target features plus +avx,+avx2:
#   1. The build is the one this run made (see "Which assembly" below) and contains 256-bit code at all.
#   2. The 4-way Keccak permutation is vectorized to 256 bits: LLVM's loop vectorizer is a heuristic, and when it fails the
#      code is still correct but scalar and about 3x slower than the vector code. The verify chain is `#[inline(always)]` from the
#      public functions down to the permutation (`keccak4::keccak_f1600_x4` has no symbol of its own), so the check is made in
#      the nine public functions that run a 4-way ExpandA (`api::verify_NN`, `api::verify_internal_NN` and
#      `api::verifying_key_NN`): every permutation rotation amount that the vector code does with a shift (21 of the 24 distinct
#      amounts; the rotations by 1, 8 and 56 are an add and byte shuffles) must show up as `vpsllq $N, %ymm` in each of them.
#      (If a `keccak_f1600_x4` symbol exists, it must show all 21 too.)
#   3. Every public verify function (the nine above and `api::verify_prepared_NN`, `api::verify_internal_prepared_NN`) inlines
#      its whole chain and owns a `PreparedVk` or a `VerifyScratch` (`#[repr(align(32))]`), so it realigns its stack frame to 32
#      bytes. With the frame 32-byte aligned and every 256-bit spill slot in that one frame (no out-of-line callee that spills
#      ymm registers into a frame that is only 16-byte aligned), no 32-byte spill slot or array straddles a 4 KiB page (a
#      page-split access costs about 30 cycles, and a call at the wrong stack offset used to take up to 12 us longer;
#      bench/results/2026-11-07-p6.md, 2026-11-09-p12.md). LLVM may split or drop an aligned aggregate, and nothing in the source
#      can prevent that, so this stays an object-code check: the prologue must hold `andq $-32` (or a stronger mask) on %rsp
#      within its first 30 lines, and the two prepared-key functions must hold ymm code (they run no ExpandA, so no shifts).
# The old checks that every callee is inlined into a `#[target_feature]` wrapper are gone with the wrappers: a function that
# is not inlined is compiled with the same target features as its caller now.
#
# The nearcore flags (-Ctarget-feature=+sse2,...,+movbe,+pclmulqdq, no AVX2) are the base; +avx,+avx2 is added here. Set
# NEARCORE_RUSTFLAGS to override the base, or AVX2_RUSTFLAGS to override the whole flag string.
#
# Which assembly is inspected. The file is written by the rustc invocation of this very build, to a path that exists only
# for this run (`--emit=asm=$OUT/lib.s`, $OUT a fresh temporary directory); it is not looked up in target/ afterwards, where
# the newest matching file could come from another configuration. Because the path is part of the rustc arguments, cargo
# and the build cache cannot treat the unit as fresh, and the JSON messages that cargo prints for the same invocation are
# checked: the library unit was compiled by this run (`fresh` false). The target directory is cargo's (mbx-managed):
# CARGO_TARGET_DIR, --target-dir and build.target-dir are not set here.
set -uo pipefail
cd "$(dirname "$0")/.."
BASE="${NEARCORE_RUSTFLAGS:--Ctarget-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq}"
FLAGS="${AVX2_RUSTFLAGS:-$BASE,+avx,+avx2}"
case "$FLAGS" in *avx2*) ;; *) echo "FAIL: the flags '$FLAGS' do not enable avx2"; exit 1 ;; esac
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT
ASM="$OUT/lib.s"
# One codegen unit so that every instantiation lands in one file; --emit=asm only for the library.
RUSTFLAGS="$FLAGS" cargo ${TOOLCHAIN:+"+$TOOLCHAIN"} rustc --release --lib --message-format=json -- \
  "--emit=asm=$ASM" -Ccodegen-units=1 -Cdebuginfo=0 > "$OUT/cargo.json" || { echo "build failed"; exit 1; }
python3 -I - "$OUT/cargo.json" <<'PY' || { echo "FAIL: the assembly was not written by a library build of this run"; exit 1; }
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
if units[0].get('fresh'):
    sys.exit('the library unit was fresh: cargo did not run rustc, so the assembly file is not from this build')
print('cargo built the library unit in this run with features', units[0].get('features'))
PY
[ -s "$ASM" ] || { echo "no assembly was written to the path given to rustc for this build"; exit 1; }
echo "assembly: $ASM ($(wc -l < "$ASM") lines), flags: $FLAGS"
ymm="$(grep -c 'ymm' "$ASM")"
echo "lines mentioning ymm registers: $ymm"
if [ "$ymm" -lt 1000 ]; then echo "FAIL: too little 256-bit code: the build did not emit AVX2 code"; exit 1; fi
# The 4-way permutation must be 256-bit vector code in every function that runs the 4-way ExpandA: see (2) above.
rotshifts="62 28 27 36 44 6 55 20 3 10 43 25 39 41 45 15 21 18 2 61 14"
perm="$(awk -v imms="$rotshifts" '
  BEGIN { n = split(imms, I, " ") }
  /^[^ .#][^:]*ml_dsa_lean(3api(9verify_|18verify_internal_|16verifying_key_)(44|65|87)|7keccak415keccak_f1600_x4[^:]*):/ { name=$0; sub(/:.*/, "", name); inbody=1; names[name]=1; next }
  inbody && /\.cfi_endproc/ { inbody=0 }
  inbody && /vpsllq[ \t]+\$[0-9]+,[ \t]*%ymm/ { match($0, /\$[0-9]+/); have[name, substr($0, RSTART + 1, RLENGTH - 1)]=1 }
  END { for (nm in names) { miss=""; for (i = 1; i <= n; i++) if (!have[nm, I[i]]) miss = miss " " I[i]; print (miss == "" ? "vector" : "SCALAR(missing vpsllq" miss ")"), nm } }' "$ASM")"
echo "4-way permutation (vector / SCALAR, symbol):"
echo "$perm"
if [ "$(echo "$perm" | grep -c 'api')" -ne 9 ]; then echo "FAIL: expected the nine functions api::verify_NN, api::verify_internal_NN and api::verifying_key_NN (NN = 44, 65, 87) in the assembly"; exit 1; fi
if echo "$perm" | grep -q '^SCALAR'; then
  echo "FAIL: the 4-way Keccak permutation is not vectorized to 256 bits in a function that runs it (LLVM's loop vectorizer rejected the loop over the four states in src/keccak4.rs, or the permutation is no longer inlined)"
  exit 1
fi
# Stack realignment: see (3) above.
realign="$(awk '
  /^[^ .#][^:]*ml_dsa_lean3api(9verify_|18verify_internal_|16verifying_key_|18verify_prepared_|27verify_internal_prepared_)(44|65|87):/ { name=$0; sub(/:.*/, "", name); inbody=1; seen[name]=0; line=0; ymm[name]=0; next }
  inbody && /\.cfi_endproc/ { inbody=0 }
  inbody { line++; if ($0 ~ /ymm/) ymm[name]++ }
  inbody && line <= 30 && /andq[ \t]+\$-(32|64|128),[ \t]*%rsp/ { seen[name]=1 }
  END { for (k in seen) print seen[k], ymm[k], k }' "$ASM")"
echo "stack-realigning functions (1 = realigned, lines mentioning ymm, symbol):"
echo "$realign"
if [ "$(echo "$realign" | grep -c .)" -ne 15 ]; then echo "FAIL: expected fifteen functions (api::verify_NN, verify_internal_NN, verifying_key_NN, verify_prepared_NN, verify_internal_prepared_NN, NN = 44, 65, 87)"; exit 1; fi
if echo "$realign" | grep -q '^0 '; then
  echo "FAIL: a verify function does not realign its stack frame to 32 bytes (the repr(align(32)) of PreparedVk or of VerifyScratch was dropped, an aligned object stopped being used by the computation, or the compiler no longer honors it)"
  exit 1
fi
if echo "$realign" | awk '$3 ~ /prepared_(44|65|87)$/ && $2 < 1000 { bad=1 } END { exit !bad }'; then
  echo "FAIL: a prepared-key verify function holds too little 256-bit code (its loops are no longer vectorized with AVX2)"
  exit 1
fi
echo "OK: 4-way permutation vectorized to 256 bits in the nine functions that run it; the fifteen verify functions realign their frames; $ymm lines of ymm code"
