# checkct: binary-level constant-time checks (BINSEC)

Port of the RustCrypto `ml-dsa/checkct` harness (signatures repo, rev a3690c4) to this crate. The driver
`#[path]`-includes `src/{params,field,rounding,ntt,keccak,encode}.rs` unchanged (the crate is `no_std` with no
dependencies, so no shims are needed), marks every probe input secret through the `__checkct_private_rand`
hook, and lets BINSEC (via `cargo-checkct`) symbolically execute the compiled release binary, flagging any
secret-dependent branch, memory access, or division operand.

This directory is its own workspace (`[workspace]` in `checkct/Cargo.toml`). It is not a member of the main
crate's workspace and the main `Cargo.toml` needed no `exclude`. `src/` is not edited.

## Running

Linux only (BINSEC). On the build box, via Docker:

    docker build -t ct-binsec checkct          # once; compiles BINSEC from opam, ~10 min
    rx submit ct -- 'bash checkct/run.sh'      # TIMEOUT=900 by default (seconds per probe)
    rx wait ct

`cargo-checkct run --dir <repo>` expects `<repo>/checkct`. Toolchain: `nightly-2026-10-06` with `rust-src`
(`checkct/rust-toolchain.toml`), `-Zbuild-std=core,panic_abort` with `compiler-builtins-mem`
(`.cargo/config.toml`, copied from upstream). BINSEC 0.11.3, unisim_archisec 0.0.14, cargo-checkct @ 85271e5.
Checks: `control-flow,memory-access,dividend,divisor`. Building only (no BINSEC) works anywhere with the
toolchain: `cd checkct && cargo build --release -p driver --target x86_64-unknown-linux-gnu`.

`checkct_macros/src/lib.rs` and `.cargo/config.toml` are copied from upstream (Apache-2.0 OR MIT), as
`cargo-checkct init` generates them. `driver/src/rng.rs` is the same hook pair without the `rand_core` impls.

## Probes (40 entrypoints x 3 targets: riscv32imac-unknown-none-elf, thumbv7em-none-eabihf, x86_64-unknown-linux-gnu)

- field/mask (`probes.rs`): `field_small_reduce`, `barrett_reduce`, `field_add`, `field_sub`, `field_neg`,
  `field_mul`, `ct_lt_mask`, `ct_select` (mask taken from a secret bit).
- rounding: `power2round`, `decompose`/`high_bits`/`low_bits`/`make_hint` (`_44` for gamma2 = (q-1)/88 and
  `_65_87` for (q-1)/32), `infinity_norm`, `vec_infinity_norm` (4 polynomials).
- `ntt`, `ntt_inverse`, `multiply_ntt` on secret polynomials; `keccak_f1600` with a secret state.
- encode: `bit_pack_{3,4,13,18,20}` (inputs masked to c bits), `sk_encode_{44,65,87}` (secret key, s1, s2, t0;
  public rho and tr), `sk_decode_{44,65,87}` on a secret sk.
- `signing.rs`: `response_{44,65,87}` (z = y + cs1, cs2, r0 = LowBits(w - cs2), both vector norms) and
  `hint_step_{44,65,87}` (ct0, MakeHint(-ct0, w - cs2 + ct0), hamming weight, ct0 norm). c-hat is public.
  These call the production `sign::response` and `sign::hint_step` (`pub(crate)`, included via `#[path]`);
  the norms are taken on the returned vectors, as `attempt` does before its rejection `if`s.

Not probed on purpose: rejection samplers' accept/reject branching, `sample_in_ball` on public c-tilde, and
the two rejection `if`s of `attempt` (public-outcome branches).

## Results (nightly-2026-10-06, BINSEC 0.11.3, 900 s per probe)

Baseline (unmodified `src/`):

| target | secure | insecure | unknown (timeout) |
|---|---|---|---|
| x86_64-unknown-linux-gnu | all 40 rows | 0 | 0 |
| thumbv7em-none-eabihf | all 40 rows | 0 | 0 |
| riscv32imac-unknown-none-elf | 22 | 12 | 6 |

riscv32imac insecure (control-flow leaks; no memory-access, dividend or divisor leaks anywhere):
`ct_lt_mask` (0x192fa), `ct_select` (0x22352), `decompose_44/65_87`, `high_bits_44/65_87`, `low_bits_44/65_87`,
`make_hint_44/65_87`, `infinity_norm`, `vec_infinity_norm`. riscv `response_*` and `hint_step_*` are unknown
(BINSEC timed out at 900 s; they complete on the other two targets, so the timeouts follow the riscv branches).

Cause (disassembly): RV32IMAC has no conditional move (no Zicond), and LLVM recognizes the
`a ^ ((a ^ b) & mask)` select and the `(x - y) >> 63` mask and lowers them to branches, e.g. in `ct_select`
`andi a0, a0, 1; beqz a0, ...` on the secret mask bit, in `decompose_44` `bltu a3, a1, ...` and
`bltu a5, a4, ...` on secret data, and `beq hi_a, hi_b; sltu` for the 64-bit compare in `ct_lt_mask`.
x86_64 and thumbv7em keep the branch-free form.

Experiment (a patched copy inside the container only; `src/` untouched): wrapping the mask in
`core::hint::black_box` in `ct_select` (`... & black_box(mask)`) and in `ct_lt_mask`
(`0u64.wrapping_sub(black_box(a.wrapping_sub(b) >> 63))`) makes every probe secure on all three targets except
(a) the standalone `ct_lt_mask` probe on riscv (0x19820, 64-bit compare with inputs the compiler knows are
below 2^63; its in-crate callers, which pass u32-widened values, are secure after the patch), and
(b) riscv `response_*`/`hint_step_*`, still unknown at 900 s (no leak found, no proof). This is the same
hardening ctutils applies upstream. Recommended: land the `black_box` barriers in `field::ct_select` and
`field::ct_lt_mask`. Check the Lean extraction first: `black_box` is not modeled by Aeneas, so it needs a
`#[cfg(not(...))]` or extraction-time shim. The change is semantically the identity.

Cosmetic: `field_add` and `field_small_reduce` compile to identical bodies, so LLVM merges them and cargo-checkct lists the merged symbol (`field_small_reduce`) twice per target; both are secure.

## Not covered

- Only the listed straight-line steps, on the target/opt-level above (release, debug info). Other compilers,
  versions, opt-levels and inlining contexts (the real `sign_internal` build) can differ. The riscv result in
  particular depends on LLVM's select lowering, so re-run after toolchain bumps.
- `sign::attempt` itself (the two rejection `if`s, `expand_mask`, the commitment hash) is not probed; the probes
  call the `response` and `hint_step` pieces it is built from, so the analyzed code is the production code.
- Not probed: `expand_mask` (bit-unpack of secret y from XOF output; recommended once `Shake` is probed as a
  whole, since the squeeze path takes a secret rho'), `sk_decode` consumers, Shake absorb/squeeze with secret
  input (only `keccak_f1600` is probed), `use_hint`/verify (public data), zeroization (outside this tool).
- BINSEC proves absence of secret-dependent control flow/memory/division operands, not absence of
  data-dependent instruction timing (e.g. variable-latency multiplies on some cores; the `multiplication`
  check is experimental and not enabled).
