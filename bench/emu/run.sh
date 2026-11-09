#!/usr/bin/env bash
# Instruction counts of the verify paths of the current checkout on 32-bit targets, under the Unicorn emulator in docker.
#   bash bench/emu/run.sh [ARCH...]        ARCH: arm (thumbv7em-none-eabi, Cortex-M4, soft float) and/or riscv (riscv32imac-unknown-none-elf)
# Output: one table per ARCH, `SEL instructions loads stores result` (SEL in bench/emu/fw/src/main.rs). Instruction counts are not cycles.
# Needs the nightly of checkct/ (rust-src for -Zbuild-std) and docker (builds the image `emu-unicorn:1` from bench/emu/Dockerfile).
set -euo pipefail
cd "$(dirname "$0")"

ARCHES=${*:-arm riscv}
docker image inspect emu-unicorn:1 >/dev/null 2>&1 || docker build -t emu-unicorn:1 .
cargo run --release -q -p emu-gen -- "$PWD/data.rs"
SELS="440 441 442 443 444 650 651 652 653 654 870 871 872 873 874"
for a in $ARCHES; do
  case $a in
    arm) T=thumbv7em-none-eabi; CPU="-Ctarget-cpu=cortex-m4" ;;
    riscv) T=riscv32imac-unknown-none-elf; CPU="" ;;
    *) echo "unknown arch $a" >&2; exit 2 ;;
  esac
  mkdir -p out
  RUSTFLAGS="-Clink-arg=-T$PWD/fw/link.ld $CPU" cargo build --release -p emu-fw --target $T \
    -Zbuild-std=core,compiler_builtins -Zbuild-std-features=compiler-builtins-mem --message-format=json-render-diagnostics >"out/build-$a.json"
  python3 -I - "out/build-$a.json" "out/emu-fw-$a.elf" <<'PY'
import json, shutil, sys
exe = None
for line in open(sys.argv[1]):
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if m.get("reason") == "compiler-artifact" and m.get("executable") and m["target"]["name"] == "emu-fw":
        exe = m["executable"]
shutil.copy(exe, sys.argv[2])
PY
  ELF=out/emu-fw-$a.elf
  sha256sum "$ELF" | cut -d' ' -f1 | sed "s/^/elf sha256 ($a): /"
  echo "== $a: SEL instructions loads stores result   (44/65/87 x: 0 scalar verify_internal, 1 4-way verify_internal_x4, 2 api::verify, 3 verifying_key, 4 prepared verify)"
  docker run --rm --name "emu-$a" --memory 4g --cpus 2 -v "$PWD:/w:ro" emu-unicorn:1 python3 /w/run.py "${a/riscv/riscv}" "/w/$ELF" $SELS
done
