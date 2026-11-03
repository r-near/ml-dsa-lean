#!/usr/bin/env bash
# Re-run selected probes with a long timeout (cargo-checkct has no entrypoint filter). From the repository root:
#   rx submit ct4 -- 'set -o pipefail; ONLY="hint_step|vec_power2round" TIMEOUT=7200 bash checkct/run-select.sh 2>&1 | tee sel.log'
# Environment:
#   ONLY     extended regex over the entrypoint names (driver__module__probe); required
#   EXCLUDE  optional extended regex over the entrypoint names to leave out of the selection (the censuses of a sweep that
#            runs several probes in parallel: they need more than 64 GB, so they run alone)
#   TIMEOUT  seconds per probe (default 7200)
#   TARGETS  space separated target list (default: all three)
#   JOBS     parallel BINSEC instances (default 4: they share the container cap, and 16 at 64g got large probes killed).
#            A probe killed at the cap reports "error", never "secure"; check `journalctl -k -g "Killed process"` (ISSUES T-8)
#   OUT      as in run.sh (copies the compiled drivers)
#   PROFILE  as in run.sh (nearcore = opt-level 3, fat LTO, one codegen unit), plus the dispatch profiles:
#            dispatch          the checkct profile with the driver's `avx2` cargo feature, which turns on the crate's
#                              `cfg(feature = "avx2")`: the runtime AVX2 dispatch of src/ntt.rs is compiled in (x86_64 only)
#            nearcore-dispatch the nearcore settings plus the same feature
#            nearcore-exact    the exact nearcore release build (see the block comment below): nearcore's [profile.release] incl.
#                              overflow-checks = true, nearcore's x86_64 target features and Rust 1.95.0 (CT_TOOLCHAIN)
#            nearcore-exact-dispatch  nearcore-exact plus the driver's `avx2` feature, cache pre-set as in nearcore-dispatch
#            In a dispatch profile the dispatch cache (a static in .bss) is pre-set to "no AVX2" in every x86_64 BINSEC
#            script, see run_one below; the run fails if the static or the script anchor is not found. In every other
#            profile no dispatch is compiled and nothing is pre-set (the log says so).
#   NAME     container name (default ct-select)
#   CT_MEMORY / CT_CPUS  docker --memory / --cpus caps for the container (default 64g / 24). BINSEC runs can grow to
#            tens of GB each; without a cap they have pushed the box out of memory and killed unrelated Lean builds.
# Builds the drivers and generates the BINSEC scripts through `cargo-checkct run --timeout 1`, then runs BINSEC
# on the matching scripts with the same command line cargo-checkct uses. Prints a "Summary:" block in the same
# shape as run.sh, so checkct/leaks.sh can map the leak addresses to source lines.
set -o pipefail
: "${ONLY:?set ONLY to a regex over the probe names}"
TIMEOUT="${TIMEOUT:-7200}"
NAME="${NAME:-ct-select}"
TARGETS="${TARGETS:-riscv32imac-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-linux-gnu}"
JOBS="${JOBS:-4}"
MOUNT=""
if [ -n "$OUT" ]; then
  mkdir -p "$OUT" && chmod 777 "$OUT" && MOUNT="-v $OUT:/out"
fi
PENV=""
DISPATCH=""
case "$PROFILE" in
  ""|nearcore|nearcore-novec|avx2|nearcore-avx2) ;;
  nearcore-exact) ;;
  dispatch|nearcore-dispatch|nearcore-exact-dispatch) DISPATCH=1 ;;
  *) echo "unknown PROFILE=$PROFILE (known: nearcore, nearcore-novec, avx2, nearcore-avx2, dispatch, nearcore-dispatch, nearcore-exact, nearcore-exact-dispatch)" >&2; exit 2 ;;
esac
case "$PROFILE" in nearcore|nearcore-novec|nearcore-dispatch)
  PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort" ;; esac
# BINSEC cannot lift some SSE2 instructions (movmskpd) that LLVM emits when it vectorizes the loops at opt-level 3.
# cargo-checkct drops RUSTFLAGS, so use the per-target variable, which replaces the x86_64 rustflags of checkct/.cargo/config.toml, so repeat them.
if [ "$PROFILE" = nearcore-novec ]; then
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false"
  PENV="$PENV -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
fi
# PROFILE=nearcore-exact, nearcore-exact-dispatch: the build settings of nearcore's release binary, read from the
# nearcore clone at commit cd5a94457 (2026-11-03). The older "nearcore" profiles above stay as they were (historical
# numbers refer to them).
#   Cargo.toml:388-392      [profile.release] overflow-checks = true, panic = 'abort', lto = "fat", codegen-units = 1
#                           (opt-level is not set: the release default 3; debug-assertions: default off)
#   .cargo/config.toml:8-9  [target.'cfg(target_arch = "x86_64")'] rustflags = ["-Ctarget-feature=+sse2,+ssse3,+sse4.1,
#                           +sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq", "-Cforce-unwind-tables=y"] (no AVX2)
#   rust-toolchain.toml:12  channel = "1.95.0"
# overflow-checks = true is set for the driver package only ([profile.release.package.driver], appended to the container's
# copy of checkct/.cargo/config.toml below), NOT through CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS: -Zbuild-std takes the
# release profile for core and compiler_builtins too (verified with `cargo build -v`: overflow-checks=on for every std
# crate), whereas nearcore links the prebuilt core, whose own MIR has no overflow checks (only `rustc_inherit_overflow_checks`
# operators take the user's setting). The driver includes the crate sources as modules, so the package override covers
# exactly what nearcore compiles with checks: the crate.
# cargo-checkct drops RUSTFLAGS, so the x86_64 flags go through the per-target variable, which replaces the x86_64
# rustflags of checkct/.cargo/config.toml: its linker flags are repeated here. The other targets are not changed.
# Toolchain: CT_TOOLCHAIN (default 1.95.0, installed in the image by checkct/Dockerfile) through RUSTUP_TOOLCHAIN, which
# overrides checkct/rust-toolchain.toml; RUSTC_BOOTSTRAP=1 lets that stable compiler take the -Zbuild-std of
# checkct/.cargo/config.toml (the driver is no_std and needs build-std's compiler-builtins-mem for memcpy/memset;
# RUSTC_BOOTSTRAP does not change code generation). CT_TOOLCHAIN=nightly-2026-10-06 builds with the checkct nightly instead.
case "$PROFILE" in nearcore-exact|nearcore-exact-dispatch)
  PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort -e CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=false -e RUSTUP_TOOLCHAIN=${CT_TOOLCHAIN:-1.95.0} -e RUSTC_BOOTSTRAP=1 -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C target-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -C force-unwind-tables=y" ;; esac
# PROFILE=avx2: the default profile with `-C target-feature=+avx2` (nearcore-avx2: plus the nearcore settings). The
# crate then takes its static-AVX2 arm (src/ntt.rs "Dispatch"): no cpuid, one compilation of each NTT body, compiled
# for AVX2. BINSEC 0.11.3 cannot lift the VEX-encoded vector instructions LLVM emits there (status unknown at the
# first one, "uninterpreted KO"), so this profile is only a check that the scalar parts stay secure.
case "$PROFILE" in nearcore-avx2) PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort" ;; esac
if [ "$PROFILE" = avx2 ] || [ "$PROFILE" = nearcore-avx2 ]; then
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C target-feature=+avx2"
  PENV="$PENV -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
fi
EXACT=""
case "$PROFILE" in nearcore-exact|nearcore-exact-dispatch) EXACT=1 ;; esac
docker run --rm -e DISPATCH="$DISPATCH" -e EXACT="$EXACT" -e PROFILE_NAME="${PROFILE:-default}" --memory "${CT_MEMORY:-64g}" --memory-swap "${CT_MEMORY:-64g}" --cpus "${CT_CPUS:-24}" --name "$NAME" $MOUNT $PENV -e ONLY="$ONLY" -e EXCLUDE="$EXCLUDE" -e TIMEOUT="$TIMEOUT" -e TARGETS="$TARGETS" -e JOBS="$JOBS" \
  -v "$PWD":/src:ro ct-binsec bash -c '
  mkdir /home/opam/w && cp -r /src/src /src/checkct /src/Cargo.toml /home/opam/w/ &&
  rm -rf /home/opam/w/checkct/target && cd /home/opam/w && eval $(opam env) &&
  if [ -n "$EXACT" ]; then
    printf "\n[profile.release.package.driver]\noverflow-checks = true\n" >> checkct/.cargo/config.toml
  fi &&
  echo "toolchain for PROFILE=$PROFILE_NAME (RUSTUP_TOOLCHAIN=${RUSTUP_TOOLCHAIN:-unset}, RUSTC_BOOTSTRAP=${RUSTC_BOOTSTRAP:-unset}):" &&
  (cd checkct && rustc -vV | sed "s/^/  /") &&
  echo "x86_64 rustflags: ${CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS:-(checkct/.cargo/config.toml)}; CARGO_PROFILE_RELEASE_*: $(env | grep ^CARGO_PROFILE_RELEASE_ | tr "\n" " ")" &&
  # Dispatch profiles: make `avx2` a default feature of the driver (cargo-checkct has no --features option). The
  # feature is declared in checkct/driver/Cargo.toml; the #[path]-included sources see it as cfg(feature = "avx2").
  if [ -n "$DISPATCH" ]; then
    sed -i "s/^avx2 = \[\]\$/avx2 = []\ndefault = [\"avx2\"]/" checkct/driver/Cargo.toml &&
    grep -q "^default = \[\"avx2\"\]\$" checkct/driver/Cargo.toml || { echo "PRESET FAILED: could not enable the avx2 feature in checkct/driver/Cargo.toml"; exit 1; }
  fi
  cargo-checkct run --dir /home/opam/w --timeout 1 --jobs 60 --skip-unknown >/dev/null 2>&1
  cd /home/opam/w/checkct/target || exit 1
  # The dispatch static of src/ntt.rs (mod dispatch, static AVX2: AtomicU8): print the address of exactly that symbol.
  # v0 mangling _RNvNtNtC<crate hash>_6driver3ntt8dispatch4AVX2 (legacy: _ZN6driver3ntt8dispatch4AVX217h<hash>E), plus
  # the suffixes LTO adds (.0, .llvm.<number>). No other symbol of the binary matches (the NTT bodies are functions, type t).
  avx2_sym() { nm "$1/release/driver" 2>/dev/null | grep -E "^[0-9a-f]+ [bBdD] (_RNvNtNtC[A-Za-z0-9]+_6driver3ntt8dispatch4AVX2|_ZN6driver3ntt8dispatch4AVX217h[0-9a-f]{16}E)(\.[0-9]+)?(\.llvm\.[0-9]+)?\$" | cut -d" " -f1; }
  export -f avx2_sym
  rm -f /tmp/preset-failed
  for t in $TARGETS; do
    case "$t" in x86_64*) ;; *) echo "preset $t: no AVX2 dispatch on this architecture, nothing to pre-set"; continue ;; esac
    n=$(avx2_sym "$t" | wc -l)
    if [ -n "$DISPATCH" ]; then
      if [ "$n" -eq 1 ]; then echo "preset $t: PROFILE=$PROFILE_NAME: dispatch compiled in, AVX2 cache static at 0x$(avx2_sym "$t"); every script gets @[0x..., 1] := 1"
      else echo "PRESET FAILED $t: PROFILE=$PROFILE_NAME is a dispatch profile but $n symbols match driver::ntt::dispatch::AVX2 (expected 1)" | tee -a /tmp/preset-failed; fi
    else
      if [ "$n" -eq 0 ]; then echo "preset $t: PROFILE=$PROFILE_NAME: no dispatch compiled (driver built without the avx2 feature), nothing to pre-set"
      else echo "PRESET FAILED $t: PROFILE=$PROFILE_NAME is not a dispatch profile but the binary has the dispatch static" | tee -a /tmp/preset-failed; fi
    fi
  done
  [ -e /tmp/preset-failed ] && exit 1
  run_one() {
    t=$1; s=$2; isa=""
    case "$t" in thumb*) isa="-isa armv7:thumb" ;; esac
    ep=$(basename "$s" .binsec); ep=${ep#driver.}; ep=$(echo "$ep" | sed "s/__/::/g")
    # The runtime AVX2 dispatch (src/ntt.rs, compiled only in the dispatch profiles) caches its CPUID answer in a
    # static. BINSEC leaves .bss symbolic, so it would explore the AVX2 arm, whose VEX instructions it cannot lift
    # ("KO", status unknown). cargo-checkct models cpuid as "no optional features"; do the same for the cache: pre-set
    # it to 1 ("checked, no AVX2") on x86_64. The symbol is matched exactly (avx2_sym); a missing symbol or anchor
    # fails the run.
    pre=""
    case "$t" in x86_64*) if [ -n "$DISPATCH" ]; then
      sym=$(avx2_sym "$t"); mod="/tmp/mod.$$.$ep.binsec"
      sed "/^@\[rsp, 8\] :=/a @[0x$sym, 1] := 1" "$s" > "$mod"
      if [ -n "$sym" ] && grep -q "^@\[0x$sym, 1\] := 1\$" "$mod"; then
        s="$mod"; pre=" (AVX2 cache 0x$sym pre-set to 1)"
      else
        echo "PRESET FAILED $t $ep: anchor @[rsp, 8] := not found in $s (symbol 0x$sym)" | tee -a /tmp/preset-failed
        { echo "  driver  $t  $ep  error"; echo "      note: AVX2 cache pre-set failed (anchor not found in the BINSEC script)"; } > "/tmp/sel.$t.$ep.out"
        return 0
      fi
    fi ;; esac
    out=$(binsec -sse -checkct -sse-depth 1000000000 -sse-jump-enum 64 -sse-script "$s" -sse-timeout "$TIMEOUT" \
      -checkct-leak-info instr $isa -checkct-features control-flow,memory-access,dividend,divisor "$t/release/driver" 2>&1)
    st=$(echo "$out" | sed -n "s/.*Program status is : \([a-z]*\).*/\1/p" | head -1)
    {
      echo "  driver  $t  $ep  ${st:-error}"
      echo "$out" | sed -n "s/.*\[checkct:result\] Instruction \(.*\)/      \1/p"
      echo "$out" | grep -E "visited instructions \(unrolled\)|branching points|checks pass|pending paths" | sed "s/^ */      stat: /"
      [ "$st" = secure ] || echo "$out" | grep -iE "warning|error|unsupported|unknown|undefined|abort|not executable|cannot|failed" | sort | uniq -c | sort -rn | head -8 | sed "s/^ */      note: /"
    } > "/tmp/sel.$t.$ep.out"
    echo "done $t $ep ${st:-error}$pre"   # streamed as each probe finishes
  }
  export -f run_one
  for t in $TARGETS; do for s in $t/release/driver.*.binsec; do
    n=$(basename "$s" .binsec); n=${n#driver.}
    echo "$n" | grep -Eq "$ONLY" && { [ -z "$EXCLUDE" ] || ! echo "$n" | grep -Eq "$EXCLUDE"; } && echo "$t $s"
  done; done > /tmp/jobs.txt
  echo "selected $(wc -l < /tmp/jobs.txt) probes"
  xargs -P "$JOBS" -L1 bash -c "run_one \$0 \$1" < /tmp/jobs.txt
  echo "Summary:"
  cat /tmp/sel.*.out
  if [ -d /out ]; then
    for t in $TARGETS; do cp /home/opam/w/checkct/target/$t/release/driver /out/$t.driver; done
  fi
  [ -e /tmp/preset-failed ] && { echo "PRESET FAILED for some probes:"; cat /tmp/preset-failed; exit 1; }
  exit 0'
