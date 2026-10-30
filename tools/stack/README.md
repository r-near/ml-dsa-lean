# tools/stack: worst-case stack use of the public `api` functions

STATUS.md says Sign for ML-DSA-87 "keeps roughly 60 KB of arrays on the stack". Measured: **about 239 KB** in a
release build (the 60 KB figure is just the expanded matrix Â; see "Biggest frames"). This directory measures every
public `api` function (keygen / sign / verify / sign_internal / verify_internal / sk_is_well_formed for 44, 65, 87)
two independent ways and checks that they agree.

It is its own workspace (`[workspace]` in `Cargo.toml`), not a member of the main crate's. `src/` is not edited.

## Running

    rx submit stack -- 'set -o pipefail; bash tools/stack/run.sh 2>&1 | tee stack.log'    # about 6 minutes
    rx wait stack

Needs a Linux machine with the nightly in `rust-toolchain.toml` (`rust-src`, for `-Zbuild-std`) and the floating
nightly's `llvm-tools` (`llvm-readobj`, `llvm-objdump`; `run.sh` looks them up). Reports land in `out/`
(git-ignored), the same text goes to stdout.

## Method

**Static** (`walker`, a small std-only Rust program): build with `-Zemit-stack-sizes`, read each function's frame size
(`llvm-readobj --stack-sizes`), read the call graph from the disassembly (`llvm-objdump -d`), then take the longest
path from each `api` symbol. Every direct call and every direct jump to another function's start is an edge (a tail
call replaces the frame, so counting it as a call over-estimates). x86_64 adds 8 bytes per call for the return
address; ARM and RISC-V save the link register inside the frame. wasm has no `.stack_sizes`: the frame is the
shadow-stack prologue (`global.get 0; i32.const N; i32.sub`) and calls are `call <index>` edges. The walker prints
instead of silently dropping: functions with no frame size, indirect calls, direct recursion, graph cycles. For all
four targets in both variants there are none of any of these, except the std harness (below). Core and
compiler-builtins are built from source (`-Zbuild-std=core,compiler_builtins`) so `memcpy`/`memset`/`__multi3` have
sizes too. The report also has a "without panic paths" column (drops `core::panicking`, slice-index failure and `core::fmt`
callees); the tables below use the worst case including them, which adds up to about 120 bytes for Verify and
`sk_is_well_formed` on x86_64 and nothing elsewhere.

**Dynamic** (`dynamic`, x86_64 Linux, std): each function runs on a fresh 16 MiB thread; the 12 MiB below the current
frame are first painted with a pattern, and after the call the lowest overwritten word is the high-water mark. The
number is measured from the stack pointer at the call instruction, so it includes the return address and everything
the function calls, but not the caller's frame or the caller's result slot. Valid inputs are used (real key from
`keygen`, real signature), so Sign and Verify run the full path. Best of three runs.

**Agreement.** For the same binary, static and painted agree to within 40 bytes for all 18 functions (for example
`sign_87`: 238,656 static from the std harness's own `.stack_sizes`, 238,696 painted; the no_std harness gives 238,664).
The static walk of the std harness binary treats its calls through the GOT as libc leaf functions (`memcpy`, `memset`,
`memmove`, `bcmp`); the painting confirms nothing hides there.

**Variants.** Frame sizes depend on inlining, so everything is built twice: `default` is this workspace's release
profile (16 codegen units, no LTO), `lto` is `codegen-units = 1` and fat LTO. Under LTO the api functions are inlined
into the harness wrappers, so the static root is the exported wrapper (`stk_*`), whose frame also holds the result
array; the painted LTO column excludes the inlined api frame (it sits above the mark), so compare LTO rows on the static
column only. `-Zemit-stack-sizes` does not change code generation; the plain build (no extra flags) is also painted
(`out/default/dynamic-plain.txt`) and is identical to the stack-sizes build.

## Results (bytes, default release profile)

The x86_64 static column includes up to about 120 bytes of panic-path frames (Verify, `sk_is_well_formed`) that the
painting never runs; otherwise static and painted agree to 50 bytes. The dev profile column is x86_64 painted at opt-level 0 with debug assertions (`cargo test` without
`--release`).

| function | x86_64 static | x86_64 painted | thumbv7em | riscv32imac | wasm32 (shadow stack) | x86_64 dev profile (painted) |
|---|---|---|---|---|---|---|
| `keygen_44` | 57,992 | 58,008 | 58,040 | 57,968 | 57,856 | 93,440 |
| `keygen_65` | 89,800 | 89,816 | 89,864 | 89,808 | 89,696 | 143,008 |
| `keygen_87` | 134,312 | 134,328 | 125,692 | 125,680 | 134,272 | 221,792 |
| `sign_44` | 114,584 | 114,632 | 114,576 | 114,448 | 114,160 | 174,896 |
| `sign_65` | 166,696 | 166,728 | 166,768 | 166,656 | 166,272 | 244,768 |
| `sign_87` | 238,664 | 238,696 | 230,696 | 231,632 | 238,320 | 340,080 |
| `sign_internal_44` | 114,056 | 114,104 | 114,056 | 113,920 | 113,648 | 174,080 |
| `sign_internal_65` | 166,168 | 166,200 | 166,240 | 166,128 | 165,760 | 243,968 |
| `sign_internal_87` | 238,136 | 238,168 | 230,168 | 231,120 | 237,808 | 339,264 |
| `verify_44` | 58,728 | 58,616 | 58,632 | 58,592 | 58,512 | 102,000 |
| `verify_65` | 87,416 | 87,304 | 87,288 | 87,280 | 87,088 | 151,664 |
| `verify_87` | 131,448 | 131,336 | 131,328 | 131,328 | 131,120 | 231,024 |
| `verify_internal_44` | 58,176 | 58,056 | 58,088 | 58,048 | 58,000 | 101,136 |
| `verify_internal_65` | 86,864 | 86,744 | 86,744 | 86,736 | 86,576 | 150,800 |
| `verify_internal_87` | 130,896 | 130,776 | 130,784 | 130,784 | 130,608 | 230,160 |
| `sk_is_well_formed_44` | 2,288 | 2,168 | 2,216 | 2,224 | 2,112 | 4,712 |
| `sk_is_well_formed_65` | 2,288 | 2,168 | 2,216 | 2,240 | 2,112 | 4,712 |
| `sk_is_well_formed_87` | 2,288 | 2,168 | 2,216 | 2,256 | 2,112 | 4,920 |

The same with `codegen-units = 1` and fat LTO (static column is the exported wrapper, so it also includes the result
array, up to 4.6 KB for sign):

| function | x86_64 static | thumbv7em | riscv32imac | wasm32 |
|---|---|---|---|---|
| `keygen_44` / `65` / `87` | 64,072 / 89,736 / 143,464 | 64,124 / 89,788 / 134,880 | 64,080 / 89,776 / 134,864 | 64,000 / 89,696 / 143,488 |
| `sign_44` / `65` / `87` | 116,856 / 169,768 / 243,080 | 116,924 / 169,892 / 234,576 | 116,864 / 169,840 / 236,048 | 116,656 / 169,760 / 243,184 |
| `verify_44` / `65` / `87` | 55,448 / 83,576 / 125,016 | 55,436 / 83,580 / 116,392 | 55,360 / 83,504 / 116,320 | 55,424 / 83,488 / 125,008 |
| `sk_is_well_formed_44` / `65` / `87` | 2,136 / 2,136 / 2,136 | 2,136 / 2,120 / 2,136 | 2,112 / 2,128 / 2,112 | 2,048 / 2,048 / 2,064 |

Read: Sign ≈ 115 / 167 / 239 KB, Verify ≈ 59 / 87 / 131 KB, KeyGen ≈ 58 / 90 / 134 KB for 44 / 65 / 87. `sign_*` and
`sign_internal_*` differ by the 257-byte context prefix plus the result slot. Inlining moves the totals by a few percent
between toolchains, targets and profiles; treat each number as ±5%. None of the paths has recursion, function pointers
or indirect calls. The caller additionally holds the inputs and outputs (for `sign_87`: sk 4,896 B, signature 4,627 B,
and the `Option` result).

## Biggest frames

Single functions with the largest frames (x86_64 default; the ML-DSA-87 numbers, other sets scale with K and L):

| function | frame | what is in it |
|---|---|---|
| `sign_internal::<8, 7>` | 223,096 | see below; this single frame is 93% of `sign_87` |
| `keygen_internal::<8, 7>` | 116,424 | Â 57,344; s1 7,168, s2 8,192, t 8,192, t0 8,192, t1 8,192; the NTT product 8,192; the by-value tuple results of `expand_s` (15,360) and `vec_power2round` (16,384) |
| `verify_internal::<8, 7>` | 114,120 | Â 57,344; w′ approx 8,192; w1 8,192; t1·2^d (NTT form) 8,192; Az (NTT form) 8,192; three z-sized arrays of 7,168 (decoded z, its NTT form, a copy); two 7,232-byte by-value tuple copies |
| `sig_decode::<8, 7>` | 16,632 | z 7,168, h 2,048, and the by-value `Option<(c̃, z, h)>` return copy; nested inside `verify_internal`'s deepest path |
| `matrix_vector_ntt::<8, 7>` | 10,328 | result `w` 8,192 plus two 1,024-byte temporaries of `add_poly(&w[i], &multiply_ntt(..))`; it is the deepest callee of keygen, sign and verify, so it adds on top of the caller |
| `pk_decode::<8>` | 9,304 | t1 8,192 by value |

`sign_internal::<8, 7>` (223,096 B) holds, from the optimized IR (`out/allocas.md`, one alloca per source variable; stack
coloring merges some, the frame is about 9% below the sum):

| array | bytes | note |
|---|---|---|
| `a_hat` | 57,344 | Â = 8 × 7 × 256 × 4 bytes. This is the "roughly 60 KB" in STATUS.md, and it is a quarter of the frame |
| `key` (decoded sk) | 23,680 | s1, s2, t0 in plain form; only needed to make the NTT forms |
| `_64` (the three `ntt_vec` results) | 23,552 | a by-value temporary that is moved into `s1_hat`, `s2_hat`, `t0_hat` |
| `s1_hat`, `s2_hat`, `t0_hat` | 7,168 + 8,192 + 8,192 | the NTT forms that are actually used by every attempt |
| `attempt` locals (inlined) | about 83,000 | y 7,168; w_hat, w, w1, cs2, w_cs2, r0, ct0 8,192 each; cs1, z 7,168 each; hint 2,048; w1_enc 1,536; ĉ 1,024; temporaries |
| `Option<(c̃, z, hint)>` return slots | about 25,000 | `attempt`'s by-value return and its moves (`_82`, `_57`, `_90`: 10,240 + 7,232 + 7,232) |

## Where to cut stack (not measured, estimates)

In order of payoff per effort, for ML-DSA-87 (sets 44 and 65 scale roughly with K·L):

1. **Do not materialize Â in Verify and KeyGen** (about 57 KB each, 44%/43% of the frame). Both expand Â exactly once,
   so generating one row at a time (7 polynomials, 7 KB) and accumulating the matrix-vector product row by row costs
   no extra hashing and no extra time. For Sign, Â is reused across attempts: row streaming would redo ExpandA each
   attempt (K·L SHAKE128 absorbs per attempt, which is real time at 3 to 5 attempts on average), so for Sign the
   choice is time versus 57 KB; a caller-provided scratch buffer (heap or static) is the no-cost way to move it off the
   thread stack.
2. **NTT the secret vectors in place and drop the plain forms** in `sign_internal`: `key.s1/s2/t0` (23.6 KB) plus the
   by-value `ntt_vec` temporary (23.6 KB) disappear (about 47 KB). Keep only `rho`, `K`, `tr`.
3. **Fuse the per-polynomial loops of `attempt`/`response`/`hint_step`**: compute z_i, r0_i, ct0_i, hint_i one
   polynomial at a time and keep only the running norms; w, w1, w_cs2, r0, cs1, cs2, ct0 (about 55 KB) become
   one or two 1 KB scratch polynomials. `w1` can be packed into `w1_enc` as it is produced.
4. **Return big values through `&mut` out-parameters** (`attempt`, `sig_decode`, `pk_decode`, `ntt_vec`,
   `expand_s`, `expand_a`): removes the return slots and the moves (about 25 KB in Sign, 16 KB in `sig_decode`, 9 KB in
   `pk_decode`, 31 KB in KeyGen).
5. **`matrix_vector_ntt` accumulates in place** into the caller's buffer instead of returning `[[u32; 256]; K]` (it
   is the deepest callee of Sign, Verify and KeyGen; 10.3 KB).
6. `sk_is_well_formed` (2 KB, two 1 KB arrays from `unpack_signed`): check the bit fields directly. Minor.

Rough result if 1 to 5 are applied with Â kept for Sign (an estimate from the array sizes above, not a build):
`sign_87` ≈ 57 (Â) + 24 (ŝ1, ŝ2, t̂0) + about 25 (y, z, hint and a few scratch polynomials) ≈ 110 KB; with Â streamed
per attempt about 55 KB. Verify 87 and KeyGen 87 would fall from about 131 and 134 KB to roughly 30 to 40 KB.

## Notes for nearcore

- **Native threads.** The worst case is 239 KB (Sign 87) and 131 KB (Verify 87); Verify 44 is 59 KB. A Rust thread
  spawned with the default builder has a 2 MiB stack, so the release numbers fit with room to spare (Sign 87: 11%).
  Check for threads or tasks built with a reduced `stack_size` and for deep call chains above the call. A
  64 KB stack fits none of Sign, KeyGen or Verify 65/87 (Verify 44 needs 59 KB, which leaves almost nothing).
- **Debug builds are about 1.4 to 1.8 times larger** (Sign 87: 340 KB, Verify 87: 231 KB at opt-level 0). That is still
  inside the 2 MiB default of `cargo test` threads, with about 6x headroom for Sign 87.
- **As a host function called from wasm** the native frames add to whatever the VM already holds on the same thread; add the
  figures above to the VM's own depth. This was not measured with a VM.
- **Inside a wasm contract** (`wasm32-unknown-unknown`), the arrays live in the linear-memory shadow stack: Sign 87 needs
  about 238 KB of it, Verify 87 about 131 KB, against the 1 MiB default of rust-lld, so a contract linked with a smaller
  `-z stack-size` can overflow silently into its data. The wasm engine's own call stack (locals and operands per frame,
  what a stack-height limiter counts) is separate and was not measured: there is no recursion, but how many bytes
  the engine uses per frame depends on the engine. The numbers above are shadow-stack bytes only.
- Any rewrite that cuts stack (list above) should keep the `api` signatures: the fixed-size `[u8; N]` arrays already
  keep key and signature storage on the caller's side.

## Files

- `run.sh`: builds both variants for the four targets plus the std harness, runs the walker and the painting, writes `out/`.
- `stackbin/`: no_std crate with one exported `#[inline(never)]` wrapper per api function (`stk_<fn>_<set>`); a
  `_start` binary for the ELF targets, a `cdylib` (built with `cargo rustc --crate-type cdylib`) for wasm.
- `dynamic/`: the painting harness (std, x86_64 Linux).
- `walker/`: `elf`, `wasm` and `allocas` modes (see the header of `walker/src/main.rs`).
