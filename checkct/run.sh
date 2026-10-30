#!/usr/bin/env bash
# Run all probes. From the repository root (needs docker; build the image once with
#   docker build -t ct-binsec checkct):
#   rx submit ct -- 'bash checkct/run.sh'   # about 20 minutes with the 900 s riscv timeouts
set -o pipefail
TIMEOUT="${TIMEOUT:-900}"
docker run --rm -v "$PWD":/src:ro ct-binsec bash -c "
  mkdir /home/opam/w && cp -r /src/src /src/checkct /src/Cargo.toml /home/opam/w/ &&
  rm -rf /home/opam/w/checkct/target && cd /home/opam/w && eval \$(opam env) &&
  cargo-checkct run --dir /home/opam/w --timeout $TIMEOUT \
    --checks control-flow,memory-access,dividend,divisor --skip-unknown --all-leaks 2>&1"
