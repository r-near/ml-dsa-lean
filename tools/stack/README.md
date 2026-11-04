# tools/stack: worst-case stack use of the public `api` functions

An earlier estimate said Sign for ML-DSA-87 "keeps roughly 60 KB of arrays on the stack". Measured: **about 239 KB** in a
release build (the 60 KB figure is just the expanded matrix Â; see "Biggest frames"). This directory measures every
public `api` function (keygen / sign / verify / sign_internal / verify_internal / sk_is_well_formed and the prepared-key
constructors and calls for 44, 65, 87) two independent ways and checks that they agree.

It is its own workspace (`[workspace]` in `Cargo.toml`), not a member of the main crate's. `src/` is not edited.

## Running

    bash tools/stack/run.sh 2>&1 | tee stack.log    # about 6 minutes

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

**Agreement.** For the same binary, static and painted agree to within 40 bytes for the 18 one-shot functions and to within 120 bytes (panic-path frames)
for the 18 prepared-key ones (for example
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

The x86_64 static column includes up to about 120 bytes of panic-path frames (Verify, `sk_is_well_formed`, the
key constructors) that the painting never runs; otherwise static and painted agree to 50 bytes. The dev profile
column is x86_64 painted at opt-level 0 with debug assertions (`cargo test` without `--release`).

Re-measured on the tree that has the prepared-key API, the in-place `prepare_sk_into` and the in-place
`prepare_vk_into`; the `keygen_*`, `sign_*` and `sk_is_well_formed_*` rows are the same functions as before. The
prepared-key refactor had made `verify_*` grow (`verify_87` from 131 KB to 159 KB): `verify_internal` built a whole
`PreparedVk` by value (the 57 KB Â plus the t1 NTT form) in its own frame, and `prepare_vk` kept a second copy of Â
as its own temporary on top of that. `verify_internal` now creates the key as a local and fills it in place
(`prepare_vk_into`, which expands Â straight into the key with `expand_a_into`), so Â exists once: `verify_87` is
115 KB, below the pre-refactor 131 KB (the deepest chain is the 75 KB frame of `api::verify_87`, which holds the key,
plus `verify_decoded` 29 KB plus `matrix_vector_ntt` 10 KB). `prepare_vk_into` and `prepare_vk` are `#[inline(never)]`; inlined, their temporaries stay in
the caller's frame (without the attribute, `verify_87` measured 132 KB). `verifying_key_*` still uses the by-value
`prepare_vk`; going through `prepare_vk_into` would first fill a 66 KB local and then copy it to the result (100 KB
for ML-DSA-87). The `*_prepared` rows are what a caller who keeps the key pays per call, unchanged by this work.
Before and after (x86_64 static): `verify_44` / `65` / `87` 57,400 / 95,800 / 158,904 became 49,576 / 75,688 /
115,112; `verifying_key_87` 83,464 became 25,976 (the compiler now builds Â in the result slot for this set only;
`verifying_key_44` and `65` are unchanged at 31,112 and 51,592 on x86_64, and 65 drops to 21,840 on riscv32imac and
wasm32: inlining luck, not something the source guarantees).

| function | x86_64 static | x86_64 painted | thumbv7em | riscv32imac | wasm32 (shadow stack) | x86_64 dev profile (painted) |
|---|---|---|---|---|---|---|
| `keygen_44` | 64,184 | 64,184 | 64,264 | 64,176 | 63,872 | 93,440 |
| `keygen_65` | 98,040 | 98,040 | 98,144 | 98,064 | 97,728 | 143,072 |
| `keygen_87` | 142,616 | 142,616 | 142,688 | 142,640 | 142,304 | 221,856 |
| `sign_44` | 115,704 | 115,736 | 115,768 | 115,680 | 115,168 | 163,728 |
| `sign_65` | 167,816 | 167,848 | 167,952 | 167,888 | 167,248 | 228,480 |
| `sign_87` | 239,784 | 239,816 | 240,032 | 240,000 | 239,232 | 317,648 |
| `sign_internal_44` | 115,176 | 115,208 | 115,248 | 115,152 | 114,656 | 162,912 |
| `sign_internal_65` | 167,288 | 167,320 | 167,424 | 167,360 | 166,736 | 227,680 |
| `sign_internal_87` | 239,256 | 239,288 | 239,504 | 239,488 | 238,720 | 316,832 |
| `verify_44` | 49,576 | 49,592 | 49,672 | 49,616 | 49,344 | 73,824 |
| `verify_65` | 75,688 | 75,704 | 75,800 | 75,728 | 75,456 | 103,008 |
| `verify_87` | 115,112 | 115,128 | 115,232 | 115,184 | 114,880 | 169,480 |
| `verify_internal_44` | 49,064 | 49,080 | 49,152 | 49,104 | 48,832 | 72,960 |
| `verify_internal_65` | 75,176 | 75,192 | 75,280 | 75,200 | 74,944 | 102,144 |
| `verify_internal_87` | 114,600 | 114,616 | 114,712 | 114,656 | 114,368 | 168,616 |
| `sk_is_well_formed_44` | 2,288 | 2,168 | 2,216 | 2,224 | 2,112 | 4,712 |
| `sk_is_well_formed_65` | 2,288 | 2,168 | 2,216 | 2,240 | 2,112 | 4,712 |
| `sk_is_well_formed_87` | 2,288 | 2,168 | 2,216 | 2,256 | 2,112 | 4,920 |
| `verifying_key_44` | 31,112 | 31,000 | 32,176 | 32,128 | 31,904 | 79,008 |
| `verifying_key_65` | 51,592 | 51,512 | 52,680 | 21,840 | 21,600 | 133,280 |
| `verifying_key_87` | 25,976 | 25,864 | 26,008 | 26,000 | 25,760 | 225,440 |
| `verify_prepared_44` | 34,216 | 34,248 | 34,320 | 34,256 | 33,984 | 53,264 |
| `verify_prepared_65` | 45,480 | 45,512 | 45,592 | 45,520 | 45,248 | 66,064 |
| `verify_prepared_87` | 58,792 | 58,824 | 58,912 | 58,864 | 58,560 | 83,984 |
| `verify_internal_prepared_44` | 33,704 | 33,720 | 33,800 | 33,728 | 33,472 | 52,400 |
| `verify_internal_prepared_65` | 44,968 | 44,984 | 45,072 | 44,992 | 44,736 | 65,200 |
| `verify_internal_prepared_87` | 58,280 | 58,296 | 58,392 | 58,336 | 58,048 | 83,120 |
| `signing_key_44` | 59,960 | 59,848 | 59,864 | 59,840 | 59,680 | 179,176 |
| `signing_key_65` | 98,872 | 98,760 | 98,768 | 98,768 | 98,592 | 286,696 |
| `signing_key_87` | 164,424 | 164,312 | 164,320 | 164,320 | 164,128 | 474,688 |
| `sign_prepared_44` | 73,384 | 73,416 | 73,504 | 73,376 | 72,960 | 134,768 |
| `sign_prepared_65` | 100,920 | 100,952 | 101,104 | 100,992 | 100,464 | 180,064 |
| `sign_prepared_87` | 133,976 | 134,008 | 134,272 | 134,192 | 133,536 | 236,464 |
| `sign_internal_prepared_44` | 72,856 | 72,888 | 72,976 | 72,864 | 72,448 | 133,952 |
| `sign_internal_prepared_65` | 100,392 | 100,424 | 100,584 | 100,480 | 99,952 | 179,248 |
| `sign_internal_prepared_87` | 133,448 | 133,480 | 133,752 | 133,680 | 133,024 | 235,648 |

The same with `codegen-units = 1` and fat LTO (static column is the exported wrapper, so it also includes the result
array, up to 4.6 KB for sign; for the key constructors the wrapper also holds the returned key, 20 to 81 KB):

| function | x86_64 static | thumbv7em | riscv32imac | wasm32 |
|---|---|---|---|---|
| `keygen_44` / `65` / `87` | 64,056 / 89,720 / 134,688 | 64,116 / 89,796 / 134,856 | 64,096 / 89,776 / 134,848 | 63,888 / 89,552 / 134,320 |
| `sign_44` / `65` / `87` | 102,120 / 149,016 / 207,752 | 102,180 / 149,156 / 205,796 | 102,144 / 149,120 / 205,744 | 101,808 / 148,704 / 207,376 |
| `sign_internal_44` / `65` / `87` | 101,592 / 148,488 / 207,240 | 101,660 / 148,628 / 205,268 | 101,632 / 148,608 / 205,232 | 101,280 / 148,192 / 206,848 |
| `verify_44` / `65` / `87` | 49,592 / 75,704 / 111,544 | 49,652 / 75,764 / 111,540 | 49,600 / 75,696 / 111,472 | 49,360 / 75,472 / 111,296 |
| `verify_internal_44` / `65` / `87` | 49,064 / 75,176 / 111,016 | 49,132 / 75,244 / 111,020 | 49,072 / 75,184 / 110,960 | 48,848 / 74,960 / 110,768 |
| `sk_is_well_formed_44` / `65` / `87` | 2,136 / 2,136 / 2,136 | 2,136 / 2,120 / 2,136 | 2,112 / 2,128 / 2,144 | 2,048 / 2,048 / 2,064 |
| `verifying_key_44` / `65` / `87` | 55,624 / 94,552 / 101,656 | 56,676 / 95,612 / 101,668 | 56,592 / 64,752 / 101,616 | 56,480 / 64,608 / 101,488 |
| `verify_prepared_44` / `65` / `87` | 34,232 / 45,496 / 50,632 | 34,292 / 45,556 / 50,692 | 34,240 / 45,488 / 50,608 | 34,000 / 45,264 / 50,384 |
| `verify_internal_prepared_44` / `65` / `87` | 33,704 / 44,968 / 50,120 | 33,772 / 45,036 / 50,172 | 33,712 / 44,976 / 50,096 | 33,488 / 44,752 / 49,872 |
| `signing_key_44` / `65` / `87` | 60,224 / 99,136 / 164,688 | 60,464 / 99,392 / 164,896 | 60,384 / 99,296 / 164,816 | 59,872 / 98,784 / 164,336 |
| `sign_prepared_44` / `65` / `87` | 75,768 / 104,088 / 131,384 | 75,836 / 104,244 / 129,428 | 75,808 / 104,208 / 129,392 | 75,456 / 103,792 / 131,008 |
| `sign_internal_prepared_44` / `65` / `87` | 75,240 / 103,560 / 130,856 | 75,316 / 103,716 / 128,900 | 75,280 / 103,680 / 128,864 | 74,944 / 103,280 / 130,480 |

Read: Sign ≈ 116 / 168 / 240 KB, Verify ≈ 50 / 76 / 115 KB, KeyGen ≈ 64 / 98 / 143 KB for 44 / 65 / 87. `sign_*` and
`sign_internal_*` differ by the 257-byte context prefix plus the result slot. Inlining moves the totals by a few percent
between toolchains, targets and profiles; treat each number as ±5%. None of the paths has recursion, function pointers
or indirect calls. The caller additionally holds the inputs and outputs (for `sign_87`: sk 4,896 B, signature 4,627 B,
and the `Option` result).

### Prepared-key API

`verifying_key_*`, `signing_key_*`, `verify_prepared_*`, `verify_internal_prepared_*`, `sign_prepared_*` and
`sign_internal_prepared_*` are measured the same way (the stackbin wrappers read the key from a zeroed static; the
painting harness builds real keys and asserts that the prepared calls agree with the one-shot ones).

- **The constructors return the key by value, and the number above is the callee only.** The result slot is in the
  caller's frame, on top: `VerifyingKey44/65/87` is 20,544 / 36,928 / 65,600 bytes and `SigningKey44/65/87` is
  28,768 / 48,224 / 80,992 bytes (the `a_hat` matrix, the NTT forms, K and tr). `signing_key_*` also keeps a
  working copy `out` of that size in its own frame and moves it into the result slot with `mem::replace`, which
  leaves zeros behind (that is the zeroize design, see `src/api.rs`), so the peak for `signing_key_87` is about
  164 KB below the caller's frame plus the 81 KB result slot, and for `verifying_key_87` about 26 KB plus 66 KB (Â is built in the result slot; for ML-DSA-44 and 65 the
  callee needs 31 and 52 KB).
  Keep the returned key out of a small stack by moving it to a `Box` right away (it is moved once more there).
- **Using a prepared key is cheaper than the one-shot call.** `sign_prepared_87` is 134 KB against 240 KB for
  `sign_87`; `verify_prepared_87` is 59 KB against 115 KB for `verify_87`. The key itself is held by the caller (heap
  or static) and is not part of these numbers.
- Dev profile (opt-level 0): `signing_key_87` painted at 475 KB, the largest of any function, still about 4x under the
  2 MiB default thread stack.

## Biggest frames

Single functions with the largest frames (x86_64 default; the ML-DSA-87 numbers, other sets scale with K and L):

| function | frame | what is in it |
|---|---|---|
| `sign_internal::<8, 7>` | 223,096 | see below; this single frame is 93% of `sign_87` |
| `keygen_internal::<8, 7>` | 116,424 | Â 57,344; s1 7,168, s2 8,192, t 8,192, t0 8,192, t1 8,192; the NTT product 8,192; the by-value tuple results of `expand_s` (15,360) and `vec_power2round` (16,384) |
| `api::verify_87` (with `verify_internal::<8, 7>` inlined) | 75,448 | the key `vk` 65,600 (Â 57,344, NTT(t1·2^d) 8,192, tr); the by-value `Option<(c̃, z, h)>` of `sig_decode` 9,280; decoded z 7,168; h 2,048 (stack coloring overlaps some of these) |
| `verify_decoded::<8, 7>` | 29,320 | w′ approx 8,192; w1 8,192; Az (NTT form) 8,192; the NTT of z 7,168; w1 encoding 1,536; a few 1,024-byte polynomial temporaries (`verify_core` is inlined into it) |
| `prepare_vk_into::<8, 7>` | 24,680 | the t1 decode, its 2^d scaling and the NTT result (three 8,192-byte arrays, partly overlapping); no Â (it lives in the caller's key) |
| `sig_decode::<8, 7>` | 16,632 | z 7,168, h 2,048, and the by-value `Option<(c̃, z, h)>` return copy; called before `prepare_vk_into` and `verify_decoded`, so it is not on the deepest chain (75,448 + 16,632 < 115,112) |
| `matrix_vector_ntt::<8, 7>` | 10,328 | result `w` 8,192 plus two 1,024-byte temporaries of `add_poly(&w[i], &multiply_ntt(..))`; it is the deepest callee of keygen, sign and verify, so it adds on top of the caller |
| `pk_decode::<8>` | 9,304 | t1 8,192 by value |

`sign_internal::<8, 7>` (223,096 B) holds, from the optimized IR (`out/allocas.md`, one alloca per source variable; stack
coloring merges some, the frame is about 9% below the sum):

| array | bytes | note |
|---|---|---|
| `a_hat` | 57,344 | Â = 8 × 7 × 256 × 4 bytes. This is the "roughly 60 KB" of the earlier estimate, and it is a quarter of the frame |
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
per attempt about 55 KB. Verify 87 and KeyGen 87 would fall from about 115 and 134 KB to roughly 30 to 40 KB.

## Notes for nearcore

- **Native threads.** The worst case is 239 KB (Sign 87) and 115 KB (Verify 87); Verify 44 is 50 KB. A Rust thread
  spawned with the default builder has a 2 MiB stack, so the release numbers fit with room to spare (Sign 87: 11%).
  Check for threads or tasks built with a reduced `stack_size` and for deep call chains above the call. A
  64 KB (65,536 B) stack fits none of Sign, KeyGen 65/87 or Verify 65/87. `keygen_44` (64,184 B) fits with about 1.3 KB to
  spare and Verify 44 (49,576 B) with about 16 KB, before any frame above the call.
- **Debug builds (opt-level 0) are larger by a factor that varies by function, from 1.3x to 8.7x**; use the dev-profile
  column of the results table, not a single ratio. Examples (release becomes dev): `sign_87` 239,784 becomes 317,648 B;
  `verify_87` 115,112 becomes 169,480 B; `keygen_87` 142,616 becomes 221,856 B; `signing_key_87` 164,424 becomes
  474,688 B; `verifying_key_87` 25,976 becomes 225,440 B (plus the 66 KB and 81 KB result slots of the key constructors).
  All of them fit the 2 MiB default of `cargo test` threads: `sign_87` leaves about 6.6x headroom, `signing_key_87`
  about 4.4x before its 81 KB result slot. The dev profile in nearcore: a crate vendored as a workspace member builds at
  opt-level 0, while a non-workspace dependency gets opt-level 1 from `[profile.dev.package."*"]`, which was not
  measured here (`docs/nearcore-integration.md` §4).
- **As a host function called from wasm** the native frames add to whatever the VM already holds on the same thread; add the
  figures above to the VM's own depth. This was not measured with a VM.
- **Inside a wasm contract** (`wasm32-unknown-unknown`), the arrays live in the linear-memory shadow stack: Sign 87 needs
  about 238 KB of it, Verify 87 about 115 KB, against the 1 MiB default of rust-lld, so a contract linked with a smaller
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
