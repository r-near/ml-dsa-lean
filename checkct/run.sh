#!/usr/bin/env bash
# Run all probes. From the repository root (needs docker; build the image once with
#   docker build -t ct-binsec checkct):
#   rx submit ct4 -- 'set -o pipefail; bash checkct/run.sh'   # TIMEOUT=900 by default
# Environment:
#   TIMEOUT  seconds per probe (default 900)
#   JOBS     parallel BINSEC instances (default: all CPUs)
#   OUT      a directory to receive the three compiled driver binaries (named <target>.driver), for mapping leak
#            addresses to source lines with checkct/leaks.sh
#   PROFILE  "nearcore-novec" is "nearcore" plus -C llvm-args=-vectorize-loops=false and -vectorize-slp=false (BINSEC cannot lift movmskpd);
#            "nearcore" builds with opt-level 3, lto = "fat", codegen-units = 1, panic = "abort" (default: the
#            checkct workspace profile, release + debug info + panic = "abort")
#   NAME     docker container name (default ct-run); `rx kill` does not stop containers, use `docker kill $NAME`
# CT_MEMORY / CT_CPUS: docker --memory / --cpus caps (default 64g / 24); uncapped BINSEC runs have pushed the box
# out of memory and killed unrelated Lean builds.
#            The dispatch profiles ("dispatch", "nearcore-dispatch": the driver built with its `avx2` feature, so the runtime
#            AVX2 dispatch of src/ntt.rs is compiled in) are only supported by checkct/run-select.sh, which pre-sets the
#            dispatch cache in the BINSEC scripts; this script refuses them (without the pre-set BINSEC would explore the
#            AVX2 arm and stop at its first VEX instruction). Use e.g.
#            PROFILE=dispatch ONLY='.' bash checkct/run-select.sh, or bash checkct/select-ntt.sh dispatch.
set -o pipefail
case "$PROFILE" in dispatch|nearcore-dispatch|nearcore-exact|nearcore-exact-dispatch|nearcore-exact-novec)
  echo "run.sh does not support PROFILE=$PROFILE: use checkct/run-select.sh (dispatch cache pre-set, nearcore-exact toolchain and flags); see the header of this file" >&2
  exit 2 ;; esac
TIMEOUT="${TIMEOUT:-900}"
NAME="${NAME:-ct-run}"
JOBS_ARG=""
[ -n "$JOBS" ] && JOBS_ARG="--jobs $JOBS"
MOUNT=""
if [ -n "$OUT" ]; then
  mkdir -p "$OUT" && chmod 777 "$OUT" && MOUNT="-v $OUT:/out"
fi
PENV=""
case "$PROFILE" in nearcore|nearcore-novec)
  PENV="-e CARGO_PROFILE_RELEASE_OPT_LEVEL=3 -e CARGO_PROFILE_RELEASE_LTO=fat -e CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 -e CARGO_PROFILE_RELEASE_PANIC=abort" ;; esac
# BINSEC cannot lift some SSE2 instructions (movmskpd) that LLVM emits when it vectorizes the loops at opt-level 3.
# cargo-checkct drops RUSTFLAGS, so use the per-target variable, which replaces the x86_64 rustflags of checkct/.cargo/config.toml, so repeat them.
if [ "$PROFILE" = nearcore-novec ]; then
  export CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="-C linker=rust-lld -C linker-flavor=ld.lld -C relocation-model=static -C llvm-args=-vectorize-loops=false -C llvm-args=-vectorize-slp=false"
  PENV="$PENV -e CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS"
fi
docker run --rm --memory "${CT_MEMORY:-64g}" --memory-swap "${CT_MEMORY:-64g}" --cpus "${CT_CPUS:-24}" --name "$NAME" $MOUNT $PENV -v "$PWD":/src:ro ct-binsec bash -c "
  mkdir /home/opam/w && cp -r /src/src /src/checkct /src/Cargo.toml /home/opam/w/ &&
  rm -rf /home/opam/w/checkct/target && cd /home/opam/w && eval \$(opam env) &&
  cargo-checkct run --dir /home/opam/w --timeout $TIMEOUT $JOBS_ARG \
    --checks control-flow,memory-access,dividend,divisor --skip-unknown --all-leaks 2>&1
  rc=\$?
  if [ -d /out ]; then
    for t in riscv32imac-unknown-none-elf thumbv7em-none-eabihf x86_64-unknown-linux-gnu; do
      cp /home/opam/w/checkct/target/\$t/release/driver /out/\$t.driver
    done
  fi
  exit \$rc"
