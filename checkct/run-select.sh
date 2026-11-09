#!/usr/bin/env bash
# Re-run selected probes with a long timeout (cargo-checkct has no entrypoint filter). From the repository root:
#   ONLY="hint_step|vec_power2round" TIMEOUT=7200 bash checkct/run-select.sh 2>&1 | tee sel.log
# Environment:
#   ONLY     extended regex over the entrypoint names (driver__module__probe); required
#   EXCLUDE  optional extended regex over the entrypoint names to leave out of the selection (the censuses of a sweep that
#            runs several probes in parallel: they need more than 64 GB, so they run alone)
#   TIMEOUT  seconds per probe (default 7200)
#   TARGETS  space separated target list (default: all three)
#   JOBS     parallel BINSEC instances (default 4: they share the container cap, and 16 at 64g got large probes killed).
#            A probe killed at the cap reports "error", never "secure"; check `journalctl -k -g "Killed process"` (checkct/README.md, "Reading `error` results")
#   OUT      as in run.sh (copies the compiled drivers)
#   PROFILE  as in run.sh (nearcore = opt-level 3, fat LTO, one codegen unit), plus:
#            avx2, nearcore-avx2  the same with -C target-feature=+avx2 (BINSEC cannot lift the VEX instructions; a check that
#                              the scalar parts stay secure)
#            nearcore-exact    the exact nearcore release build (see the block comment below): nearcore's [profile.release] incl.
#                              overflow-checks = true, nearcore's x86_64 target features and Rust 1.95.0 (CT_TOOLCHAIN)
#            nearcore-exact-novec     nearcore-exact plus -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false
#            There is no run-time AVX2 dispatch in the crate any more (round 12), so there are no dispatch profiles and nothing is
#            pre-set in the BINSEC scripts.
#   TRACE    1 runs BINSEC with -sse-debug-level 3 -sse-loglevel debug and keeps only the last executed instruction and the
#            executed-instruction count of each probe (a "last:" line in the Summary): where a path was cut or stuck
#   ZEROIZE  1 builds the driver with the crate's `zeroize` feature, whatever the profile: the
#            `cfg(feature = "zeroize")` code of src/ (the wipes of Sign's attempt, the in-place decoders' `.zeroize()`
#            calls, `Drop` of the prepared key) is then compiled. No default driver contains it. The container adds the
#            optional `zeroize` dependency (the version of Cargo.lock) to its working copy of checkct/driver/Cargo.toml and
#            makes the feature a default one; the repository's file is unchanged. Needs network access for the crate download.
#   EXPERIMENTS  1 compiles driver/src/experiments.rs (the throwaway rewrite probes `exp_*`) via its cargo feature
#   NAME     container name (default ct-select)
#   CT_MEMORY / CT_CPUS  docker --memory / --cpus caps for the container (default 64g / 24). BINSEC runs can grow to
#            tens of GB each; without a cap they can exhaust the host's memory.
# Builds the drivers and generates the BINSEC scripts through `cargo-checkct run --timeout 1`, then runs BINSEC
# on the matching scripts with the same command line cargo-checkct uses. Prints a "Summary:" block in the same
# shape as run.sh, so checkct/leaks.sh can map the leak addresses to source lines.
set -o pipefail
: "${ONLY:?set ONLY to a regex over the probe names}"
TIMEOUT="${TIMEOUT:-7200}"
NAME="${NAME:-ct-select}"
case "$PROFILE" in nearcore-exact|nearcore-exact-novec) TARGETS="${TARGETS:-x86_64-unknown-linux-gnu}"
  case " $TARGETS " in *" x86_64-unknown-linux-gnu "*) ;; *) echo "PROFILE=$PROFILE is x86_64 only (nearcore's settings); TARGETS=$TARGETS" >&2; exit 2 ;; esac ;; esac
TARGETS="${TARGETS:-riscv32imac-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-linux-gnu}"
JOBS="${JOBS:-4}"
MOUNT=""
if [ -n "$OUT" ]; then
  mkdir -p "$OUT" && chmod 777 "$OUT" && MOUNT="-v $OUT:/out"
fi
PENV=""
case "$PROFILE" in
  ""|nearcore|nearcore-novec|avx2|nearcore-avx2) ;;
  nearcore-exact|nearcore-exact-novec) ;;
  *) echo "unknown PROFILE=$PROFILE (known: nearcore, nearcore-novec, avx2, nearcore-avx2, nearcore-exact, nearcore-exact-novec)" >&2; exit 2 ;;
esac
case "$PROFILE" in nearcore|nearcore-novec)
  PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort" ;; esac
# BINSEC cannot lift some SSE2 instructions (movmskpd) that LLVM emits when it vectorizes the loops at opt-level 3.
# cargo-checkct drops RUSTFLAGS, so use the per-target variable, which replaces the x86_64 rustflags of checkct/.cargo/config.toml, so repeat them.
if [ "$PROFILE" = nearcore-novec ]; then
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false"
  PENV="$PENV -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
fi
# PROFILE=nearcore-exact: the build settings of nearcore's release binary, read from the
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
# operators take the crate's own setting). The driver includes the crate sources as modules, so the package override covers
# exactly what nearcore compiles with checks: the crate.
# cargo-checkct drops RUSTFLAGS, so the x86_64 flags go through the per-target variable, which replaces the x86_64
# rustflags of checkct/.cargo/config.toml: its linker flags are repeated here. The other targets are not changed.
# Toolchain: CT_TOOLCHAIN (default 1.95.0, installed in the image by checkct/Dockerfile), written into the container's
# copy of checkct/rust-toolchain.toml. RUSTUP_TOOLCHAIN does NOT work: cargo-checkct removes it from the environment of its
# cargo (src/run.rs:263, `.env_remove("RUSTUP_TOOLCHAIN")`) so that rust-toolchain.toml decides; the first nearcore-exact
# drivers were built with the nightly that way. The run therefore reads the compiler back from the driver's .comment section
# and fails if it is not the requested one. RUSTC_BOOTSTRAP=1 lets that stable compiler take the -Zbuild-std of
# checkct/.cargo/config.toml (the driver is no_std and needs build-std's compiler-builtins-mem for memcpy/memset;
# RUSTC_BOOTSTRAP does not change code generation). CT_TOOLCHAIN=nightly-2026-10-06 builds with the checkct nightly instead.
case "$PROFILE" in nearcore-exact|nearcore-exact-novec)
  PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort -e CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=false -e RUSTC_BOOTSTRAP=1 -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C target-feature=+sse2,+ssse3,+sse4.1,+sse4.2,+popcnt,+fma,+bmi1,+bmi2,+lzcnt,+movbe,+pclmulqdq -C force-unwind-tables=y"
  # nearcore-exact-novec: nearcore-exact plus the loop and SLP vectorizers off (as nearcore-novec), to see which unknowns are VEX artifacts
  [ "$PROFILE" = nearcore-exact-novec ] && CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="$CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false" ;; esac
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
case "$PROFILE" in nearcore-exact|nearcore-exact-novec) EXACT=1 ;; esac
docker run --rm -e EXACT="$EXACT" -e EXPERIMENTS="$EXPERIMENTS" -e ZEROIZE="$ZEROIZE" -e TRACE="$TRACE" -e PROFILE_NAME="${PROFILE:-default}" --memory "${CT_MEMORY:-64g}" --memory-swap "${CT_MEMORY:-64g}" --cpus "${CT_CPUS:-24}" --name "$NAME" $MOUNT $PENV -e ONLY="$ONLY" -e EXCLUDE="$EXCLUDE" -e TIMEOUT="$TIMEOUT" -e TARGETS="$TARGETS" -e JOBS="$JOBS" \
  -v "$PWD":/src:ro ct-binsec bash -c '
  mkdir /home/opam/w && cp -r /src/src /src/checkct /src/Cargo.toml /home/opam/w/ &&
  rm -rf /home/opam/w/checkct/target && cd /home/opam/w && eval $(opam env) &&
  if [ -n "$EXACT" ]; then
    printf "[toolchain]\nchannel = \"%s\"\nprofile = \"minimal\"\ncomponents = [\"rust-src\"]\n" "${CT_TOOLCHAIN:-1.95.0}" > checkct/rust-toolchain.toml &&
    printf "\n[profile.release.package.driver]\noverflow-checks = true\n" >> checkct/.cargo/config.toml &&
    echo "driver package override appended to checkct/.cargo/config.toml: $(tail -2 checkct/.cargo/config.toml | tr "\n" " ")"
  fi &&
  echo "toolchain for PROFILE=$PROFILE_NAME (checkct/rust-toolchain.toml: $(grep ^channel checkct/rust-toolchain.toml), RUSTC_BOOTSTRAP=${RUSTC_BOOTSTRAP:-unset}):" &&
  (cd checkct && rustc -vV | sed "s/^/  /") &&
  echo "x86_64 rustflags: ${CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS:-(checkct/.cargo/config.toml)}; CARGO_PROFILE_RELEASE_*: $(env | grep ^CARGO_PROFILE_RELEASE_ | tr "\n" " ")" &&
  # ZEROIZE=1: the `zeroize` feature of the crate, as an optional dependency added to the working copy of the driver manifest
  # (the repository manifest does not declare it). The version is the one of the crate lock file.
  if [ -n "$ZEROIZE" ]; then
    zv=$(grep -A1 "^name = \"zeroize\"\$" /src/Cargo.lock | sed -n "s/^version = \"\\(.*\\)\"\$/\\1/p" | head -1)
    [ -n "$zv" ] || { echo "ZEROIZE: no zeroize version in Cargo.lock"; exit 1; }
    sed -i "s/^\\[dependencies\\]\$/[dependencies]\nzeroize = { version = \"=$zv\", default-features = false, optional = true }/; s/^experiments = \\[\\]\$/experiments = []\nzeroize = [\"dep:zeroize\"]\ndefault = [\"zeroize\"]/" checkct/driver/Cargo.toml &&
    grep -q "^default = \\[\"zeroize\"\\]\$" checkct/driver/Cargo.toml && grep -q "^zeroize = { version" checkct/driver/Cargo.toml || { echo "ZEROIZE: could not add the zeroize feature to checkct/driver/Cargo.toml"; exit 1; }
    echo "zeroize feature enabled (zeroize =$zv); driver manifest: $(grep -E "^(zeroize|default)" checkct/driver/Cargo.toml | tr "\n" " ")"
  fi
  # EXPERIMENTS=1: also compile driver/src/experiments.rs (throwaway rewrite probes, off in every other run so the
  # sweep drivers stay byte-identical to a build without it).
  if [ -n "$EXPERIMENTS" ]; then
    if grep -q "^default = " checkct/driver/Cargo.toml; then sed -i "s/^default = \[/default = [\"experiments\", /" checkct/driver/Cargo.toml
    else printf "default = [\"experiments\"]\n" >> checkct/driver/Cargo.toml; fi &&
    grep -q "experiments" checkct/driver/Cargo.toml || { echo "could not enable the experiments feature"; exit 1; }
  fi
  cargo-checkct run --dir /home/opam/w --timeout 1 --jobs 60 --skip-unknown >/dev/null 2>&1
  cd /home/opam/w/checkct/target || exit 1
  for t in $TARGETS; do case "$t" in x86_64*)
    cm=$(readelf -p .comment "$t/release/driver" 2>/dev/null | sed -n "s/^ *\[ *[0-9a-f]*\] *//p" | tr "\n" "|")
    echo "driver .comment ($t): $cm"
    if [ -n "$EXACT" ] && [ "${CT_TOOLCHAIN:-1.95.0}" = 1.95.0 ] && ! echo "$cm" | grep -q "rustc version 1.95.0 "; then
      echo "TOOLCHAIN MISMATCH: PROFILE=$PROFILE_NAME wants rustc 1.95.0 but the driver was built by something else"; exit 1; fi ;; esac; done
  run_one() {
    t=$1; s=$2; isa=""
    case "$t" in thumb*) isa="-isa armv7:thumb" ;; esac
    ep=$(basename "$s" .binsec); ep=${ep#driver.}; ep=$(echo "$ep" | sed "s/__/::/g")
    # TRACE=1: BINSEC prints every executed instruction ([sse:step] lines); only the last one and the count are kept.
    # That is the instruction a path was at when the run ended (a cut path, or the query a timed-out path is stuck in).
    trace=""; [ -n "$TRACE" ] && trace="-sse-debug-level 3 -sse-loglevel debug"
    out=$(binsec -sse -checkct -sse-depth 1000000000 -sse-jump-enum 64 -sse-script "$s" -sse-timeout "$TIMEOUT" \
      -checkct-leak-info instr $isa -checkct-features control-flow,memory-access,dividend,divisor $trace "$t/release/driver" 2>&1 |
      awk '"'"'/^\[sse:step\]/ { last=$0; n++; next } { print } END { if (n) print "LASTSTEP " n " " last }'"'"')
    st=$(echo "$out" | sed -n "s/.*Program status is : \([a-z]*\).*/\1/p" | head -1)
    {
      echo "  driver  $t  $ep  ${st:-error}"
      # SHA-256 of the ELF that BINSEC analyzed and of the script it was given , so that a later
      # rerun can be compared with this one by file identity instead of by instruction counts.
      echo "      sha256: elf $(sha256sum < "$t/release/driver" | cut -d" " -f1) script $(sha256sum < "$s" | cut -d" " -f1)"
      echo "$out" | sed -n "s/.*\[checkct:result\] Instruction \(.*\)/      \1/p"
      echo "$out" | grep "^LASTSTEP" | sed "s/^LASTSTEP /      last: /"
      echo "$out" | grep -E "visited instructions \(unrolled\)|branching points|checks pass|pending paths" | sed "s/^ */      stat: /"
      [ "$st" = secure ] || echo "$out" | grep -iE "warning|error|unsupported|unknown|undefined|abort|not executable|cannot|failed" | sort | uniq -c | sort -rn | head -8 | sed "s/^ */      note: /"
    } > "/tmp/sel.$t.$ep.out"
    echo "done $t $ep ${st:-error}"   # streamed as each probe finishes
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
  exit 0'
