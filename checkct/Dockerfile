# BINSEC + cargo-checkct, the same pins as the RustCrypto signatures CI action
# (Ledger-Donjon/cargo-checkct @ 85271e5, binsec 0.11.3, unisim_archisec 0.0.14, OCaml 5.4).
FROM ocaml/opam:debian-12-ocaml-5.4
USER root
RUN apt-get update && apt-get install -y --no-install-recommends libgmp-dev libmpfr-dev pkg-config git curl ca-certificates build-essential && rm -rf /var/lib/apt/lists/*
USER opam
RUN opam install -y binsec.0.11.3 unisim_archisec.0.0.14 bitwuzla-cxx && opam clean -a -c -s --logs
RUN curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain stable
ENV PATH=/home/opam/.cargo/bin:$PATH
RUN git clone https://github.com/Ledger-Donjon/cargo-checkct /home/opam/cargo-checkct \
 && cd /home/opam/cargo-checkct && git checkout 85271e5ce9eab9ba895c62c8b5d4129810a635a0 \
 && cargo install --locked --path .
RUN rustup toolchain install nightly-2026-10-06 --profile minimal -c rust-src \
    -t riscv32imac-unknown-none-elf -t thumbv7em-none-eabihf -t x86_64-unknown-linux-gnu
# Rust 1.95.0, the toolchain nearcore builds with (nearcore rust-toolchain.toml, cd5a94457). The nearcore-exact profiles of
# run-select.sh select it by rewriting the container's copy of checkct/rust-toolchain.toml (RUSTUP_TOOLCHAIN does not work:
# cargo-checkct removes it from its cargo's environment) and set RUSTC_BOOTSTRAP=1 for the driver's -Zbuild-std (README
# "Toolchain"). The nightly above stays the default for every other profile.
RUN rustup toolchain install 1.95.0 --profile minimal -c rust-src \
    -t riscv32imac-unknown-none-elf -t thumbv7em-none-eabihf -t x86_64-unknown-linux-gnu
