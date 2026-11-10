# tools/stack: worst-case stack use of the public `api` functions

An earlier estimate said Sign for ML-DSA-87 "keeps roughly 60 KB of arrays on the stack". Measured: **about 209 KB** in a
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
shadow-stack prologue (`global.get 0; i32.const N; i32.sub`, or in a function with a 32-byte-aligned local `global.get 0; local.tee ..; local.set ..; local.get ..; i32.const N; i32.sub; i32.const -32; i32.and`; the walker missed the second form until round 14, which understated the wasm column of the verify rows, and it does not count the up to 16 bytes of realignment) and calls are `call <index>` edges. The walker prints
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
`sign_87`: 209,112 static from the std harness's own `.stack_sizes`, 209,272 painted; the no_std harness gives 209,120).
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

Re-measured on the final tree of the fast-verify branch (round 14; `src/` is the tree of round 13), with `nightly-2026-10-06`
and `bash tools/stack/run.sh`. **The verify and key-construction rows changed in round 12 and are larger than in every table
before it:** the always-4-way verify keeps its chain `#[inline(always)]`, in one 32-byte-aligned frame per public function
(`docs/assurance.md`, rounds 12 and 13), so `verify_44` / `65` / `87` are now 64.2 / 89.8 / 131.8 KB (x86_64 static; they were 49.6 /
75.7 / 115.1 KB) and `verifying_key_44` / `65` / `87` are 49.7 / 74.3 / 111.0 KB (were 31.1 / 51.6 / 26.0 KB; the ML-DSA-87 figure
includes a second copy of the key that the compiler does not elide, `bench/results/2026-11-09-p13.md` section 2). The prepared calls
got smaller (`verify_prepared_87` 49.6 KB, was 58.8). The `sign_*` rows are also lower than the table of 2026-11-01 (`sign_87` 209 KB,
was 240): that table predates the Sign changes of 2026-11-05 (`73ae026`, `d474a0c`), which are in 0.1.0; `keygen_*` and
`sk_is_well_formed_*` are unchanged within 50 bytes. The painted dev-profile figures for `verify_*` (259 / 313 / 399 KB) are the
opt-level 0 numbers; the same function in a release build with fat LTO takes 63.0 / 89.7 / 130.6 KB (second table).

History, not current: before round 12 the prepared-key refactor had made `verify_87` grow from 131 KB to 159 KB, and building the
key in place (`prepare_vk_into`, `#[inline(never)]`) brought it to 115 KB, with `verifying_key_87` at 26 KB because the compiler
built Â in the result slot. Those frames (`api::verify_87` 75 KB, `verify_decoded` 29 KB, `prepare_vk_into` 25 KB) no longer exist
as separate frames in the 4-way verify; the tables below are the current ones.

| function | x86_64 static | x86_64 painted | thumbv7em | riscv32imac | wasm32 (shadow stack) | x86_64 dev profile (painted) |
|---|---|---|---|---|---|---|
| `keygen_44` | 64,216 | 64,232 | 64,272 | 64,176 | 63,888 | 93,472 |
| `keygen_65` | 98,056 | 98,072 | 98,136 | 98,032 | 97,728 | 143,072 |
| `keygen_87` | 142,568 | 142,568 | 142,592 | 142,528 | 142,320 | 221,856 |
| `sign_44` | 99,344 | 99,496 | 99,516 | 99,440 | 98,784 | 160,784 |
| `sign_65` | 140,176 | 140,328 | 140,436 | 140,368 | 139,600 | 223,488 |
| `sign_87` | 209,120 | 209,272 | 208,444 | 208,368 | 207,376 | 310,608 |
| `sign_internal_44` | 98,816 | 98,968 | 98,996 | 98,912 | 98,272 | 159,968 |
| `sign_internal_65` | 139,648 | 139,800 | 139,908 | 139,840 | 139,088 | 222,688 |
| `sign_internal_87` | 208,592 | 208,744 | 207,916 | 207,856 | 206,864 | 309,792 |
| `verify_44` | 64,232 | 64,168 | 62,984 | 62,800 | 62,048 | 258,792 |
| `verify_65` | 89,816 | 89,752 | 89,616 | 89,424 | 88,672 | 313,480 |
| `verify_87` | 131,848 | 131,784 | 131,568 | 131,408 | 130,656 | 398,984 |
| `verify_internal_44` | 63,944 | 63,864 | 62,728 | 62,544 | 61,760 | 257,928 |
| `verify_internal_65` | 89,528 | 89,464 | 89,360 | 89,168 | 88,384 | 312,616 |
| `verify_internal_87` | 131,528 | 131,448 | 131,312 | 131,184 | 130,368 | 398,120 |
| `sk_is_well_formed_44` | 2,320 | 2,200 | 2,224 | 2,224 | 2,112 | 3,704 |
| `sk_is_well_formed_65` | 2,320 | 2,200 | 2,224 | 2,240 | 2,112 | 4,056 |
| `sk_is_well_formed_87` | 2,320 | 2,200 | 2,224 | 2,256 | 2,112 | 4,920 |
| `verifying_key_44` | 49,688 | 49,640 | 49,680 | 49,488 | 48,672 | 172,424 |
| `verifying_key_65` | 74,296 | 74,216 | 74,304 | 74,064 | 73,248 | 232,872 |
| `verifying_key_87` | 111,032 | 110,952 | 110,984 | 110,960 | 109,952 | 331,176 |
| `verify_prepared_44` | 31,144 | 31,064 | 31,080 | 31,152 | 30,816 | 129,424 |
| `verify_prepared_65` | 38,296 | 38,216 | 38,256 | 38,352 | 37,984 | 144,656 |
| `verify_prepared_87` | 49,576 | 49,496 | 49,520 | 49,616 | 49,248 | 168,552 |
| `verify_internal_prepared_44` | 30,856 | 30,776 | 30,824 | 30,896 | 30,528 | 128,592 |
| `verify_internal_prepared_65` | 38,008 | 37,928 | 38,000 | 38,096 | 37,696 | 143,824 |
| `verify_internal_prepared_87` | 49,288 | 49,208 | 49,264 | 49,360 | 48,960 | 167,720 |
| `signing_key_44` | 59,200 | 59,320 | 59,380 | 59,344 | 58,912 | 185,120 |
| `signing_key_65` | 98,112 | 98,232 | 98,292 | 98,272 | 97,824 | 302,880 |
| `signing_key_87` | 163,648 | 163,768 | 163,836 | 163,792 | 163,360 | 501,536 |
| `sign_prepared_44` | 57,024 | 57,176 | 57,244 | 57,120 | 56,576 | 131,824 |
| `sign_prepared_65` | 73,280 | 73,432 | 73,580 | 73,456 | 72,816 | 175,072 |
| `sign_prepared_87` | 103,312 | 103,464 | 102,676 | 102,544 | 101,680 | 229,424 |
| `sign_internal_prepared_44` | 56,496 | 56,648 | 56,716 | 56,608 | 56,064 | 131,008 |
| `sign_internal_prepared_65` | 72,752 | 72,904 | 73,060 | 72,944 | 72,304 | 174,256 |
| `sign_internal_prepared_87` | 102,784 | 102,936 | 102,156 | 102,032 | 101,168 | 228,608 |

The same with `codegen-units = 1` and fat LTO (static column is the exported wrapper, so it also includes the result
array, up to 4.6 KB for sign; for the key constructors the wrapper also holds the returned key, 20 to 81 KB):

| function | x86_64 static | thumbv7em | riscv32imac | wasm32 |
|---|---|---|---|---|
| `keygen_44` / `65` / `87` | 59,960 / 83,576 / 134,688 | 60,028 / 83,644 / 134,856 | 60,000 / 83,632 / 134,848 | 59,792 / 83,408 / 134,320 |
| `sign_44` / `65` / `87` | 86,760 / 126,504 / 183,112 | 86,852 / 126,652 / 181,800 | 86,800 / 126,640 / 190,048 | 86,448 / 126,176 / 188,144 |
| `sign_internal_44` / `65` / `87` | 86,232 / 125,976 / 182,600 | 86,332 / 126,124 / 181,272 | 86,288 / 126,128 / 189,536 | 85,920 / 125,664 / 187,616 |
| `verify_44` / `65` / `87` | 63,016 / 89,672 / 130,568 | 61,980 / 88,628 / 130,484 | 61,632 / 88,288 / 130,224 | 60,960 / 87,584 / 129,504 |
| `verify_internal_44` / `65` / `87` | 62,728 / 89,384 / 130,280 | 61,724 / 88,372 / 130,228 | 61,376 / 88,032 / 129,968 | 60,672 / 87,296 / 129,216 |
| `sk_is_well_formed_44` / `65` / `87` | 2,136 / 2,136 / 2,136 | 2,128 / 2,120 / 2,128 | 2,112 / 2,128 / 2,144 | 2,048 / 2,048 / 2,064 |
| `verifying_key_44` / `65` / `87` | 49,592 / 74,200 / 101,736 | 49,660 / 74,236 / 110,812 | 49,296 / 73,872 / 102,560 | 48,608 / 73,184 / 101,664 |
| `verify_prepared_44` / `65` / `87` | 29,896 / 37,064 / 48,328 | 29,980 / 37,172 / 48,436 | 30,048 / 37,216 / 48,464 | 29,728 / 36,896 / 48,096 |
| `verify_internal_prepared_44` / `65` / `87` | 29,608 / 36,776 / 48,040 | 29,724 / 36,916 / 48,180 | 29,760 / 36,960 / 48,176 | 29,472 / 36,640 / 47,840 |
| `signing_key_44` / `65` / `87` | 59,200 / 98,112 / 163,664 | 59,440 / 98,376 / 163,896 | 59,360 / 98,288 / 163,824 | 58,848 / 97,760 / 163,312 |
| `sign_prepared_44` / `65` / `87` | 60,408 / 81,576 / 106,744 | 60,508 / 81,740 / 105,432 | 60,464 / 81,728 / 113,696 | 60,096 / 81,264 / 111,776 |
| `sign_internal_prepared_44` / `65` / `87` | 59,880 / 81,048 / 106,216 | 59,988 / 81,212 / 104,904 | 59,936 / 81,200 / 113,168 | 59,584 / 80,752 / 111,248 |

Read: Sign ≈ 99 / 140 / 209 KB, Verify ≈ 64 / 90 / 132 KB, KeyGen ≈ 64 / 98 / 143 KB for 44 / 65 / 87. `sign_*` and
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
  164 KB below the caller's frame plus the 81 KB result slot, and for `verifying_key_87` about 111 KB plus the 66 KB result slot (for ML-DSA-44 and 65 the callee needs 50 and 74 KB plus
  20.5 and 36.9 KB; the 87 figure includes a second copy of the key that the compiler does not elide, `bench/results/2026-11-09-p13.md`
  section 2).
  Keep the returned key out of a small stack by moving it to a `Box` right away (it is moved once more there).
- **Using a prepared key is cheaper than the one-shot call.** `sign_prepared_87` is 103 KB against 209 KB for
  `sign_87`; `verify_prepared_87` is 50 KB against 132 KB for `verify_87`. The key itself is held by the caller (heap
  or static) and is not part of these numbers.
- Dev profile (opt-level 0): `signing_key_87` painted at 502 KB, the largest of any function, still about 4.2x under the
  2 MiB default thread stack (`verify_87` 399 KB, `verifying_key_87` 331 KB, `sign_87` 311 KB).

## Biggest frames

Single functions with the largest frames (x86_64 default release, ML-DSA-87; the other sets scale with K and L; round 14
measurement, the "Frames of at least 1024 bytes" list of `out/default/x86_64.report.md`):

| function | frame | what is in it |
|---|---|---|
| `keygen_internal::<8, 7>` | 114,472 | Â 57,344 and the vectors s1, s2, t, t0, t1, the NTT product and the by-value results of `expand_s` and `vec_power2round` |
| `api::verify_87` (the whole 4-way verify chain is inlined into it, as `#[inline(always)]`, and the frame is 32-byte aligned) | 114,008 | the prepared key (`VerifyingKey87`, 65,600: Â 57,344, NTT(t1·2^d) 8,192, tr) plus the inlined decode, 4-way ExpandA and verify temporaries; below it `sig_decode::<8, 7>` 16,616 gives the deepest chain, 131,848 with return address and `unpack_signed` |
| `sign_internal::<8, 7>` | 105,800 | called from `api::sign_87` (5,208); below it `sign_prepared_internal::<8, 7>` 95,864 |
| `api::verifying_key_87` | 101,592 | the key under construction and, as the compiler lays it out, a second copy of it (`bench/results/2026-11-09-p13.md` section 2); `pk_decode::<8>` 9,304 below |
| `prepare_sk_into::<8, 7>` and `api::signing_key_87` | 81,080 and 81,016 | the `SigningKey87` object (80,992) in each, as in `signing_key_87` of the table above |
| `api::verify_65`, `api::verify_44` | 76,600 and 53,560 | as `verify_87`, for K·L = 30 and 16 |
| `api::verify_prepared_87` | 31,736 | no key in the frame (the caller holds it); `sig_decode::<8, 7>` 16,616 below |

History, the tree of 2026-11-01 (before the Sign changes of 2026-11-05 and the 4-way verify; `sign_internal::<8, 7>` was a single 223,096-byte frame and is now 105,800 plus `sign_prepared_internal` 95,864): `sign_internal::<8, 7>` (223,096 B) held, from the optimized IR (`out/allocas.md`, one alloca per source variable; stack
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

The list below was written for the tree of 2026-11-01, before the Sign changes of 2026-11-05 and the 4-way verify of round 12; the frame sizes it quotes (Sign 87 about 239 KB, Verify 87 about 115 KB) are the old ones (now about 209 and 132 KB) and the estimates were not redone.

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

- **Native threads.** The worst case is 209 KB (Sign 87) and 132 KB (Verify 87); Verify 44 is 64 KB (static walk of a release
  build, bytes below the caller's frame; round 14). A Rust thread spawned with the default builder has a 2 MiB stack, so the
  release numbers fit with room to spare (Sign 87: 10.0%, Verify 87: 6.3%, Verify 65: 4.3%, Verify 44: 3.1%). Check for threads
  or tasks built with a reduced `stack_size` and for deep call chains above the call. **On a 64 KiB (65,536 B) stack** the one-shot
  `verify_44` (64,232 B) and `keygen_44` (64,216 B) leave only about 1.3 KB, which no VM or runtime frame above the call fits in,
  and Sign, KeyGen 65/87 and one-shot Verify 65/87 do not fit at all. `verify_prepared_44` / `65` / `87` (31.1 / 38.3 / 49.6 KB)
  leave 34.4 / 27.2 / 16.0 KB there, before the frames above the call and with the key held by the caller; the key constructors
  need the callee plus the key object in the caller's frame (`verifying_key_44`: 49.7 + 20.5 = 70.2 KB, more than 64 KiB; build
  keys on a larger stack and keep them on the heap). On a 128 KiB stack one-shot Verify 44 and 65 fit (66.8 and 41.3 KB to
  spare) and `verify_87` (131,848 B) does not, by 0.8 KB; on 256 KiB everything does, Sign 87 with 52.9 KB to spare. (Earlier
  versions of this file said one-shot Verify 44 left about 16 KB of 64 KiB; that was before the 4-way verify of round 12.)
- **Debug builds (opt-level 0) are larger by a factor that varies by function, from 1.5x to 4.2x**; use the dev-profile
  column of the results table, not a single ratio. Examples (release becomes dev): `sign_87` 209,120 becomes 310,608 B;
  `verify_87` 131,848 becomes 398,984 B; `keygen_87` 142,568 becomes 221,856 B; `signing_key_87` 163,648 becomes
  501,536 B; `verifying_key_87` 111,032 becomes 331,176 B (plus the 66 KB and 81 KB result slots of the key constructors).
  All of them fit the 2 MiB default of `cargo test` threads: `sign_87` leaves about 6.8x headroom, `verify_87` 5.3x,
  `signing_key_87` about 4.2x before its 81 KB result slot. The dev profile in nearcore: a crate vendored as a workspace member
  builds at opt-level 0, while a non-workspace dependency gets opt-level 1 from `[profile.dev.package."*"]`, which was not
  measured here (`docs/nearcore-integration.md` §4).
- **As a host function called from wasm** the native frames add to whatever the VM already holds on the same thread; add the
  figures above to the VM's own depth. This was not measured with a VM.
- **Inside a wasm contract** (`wasm32-unknown-unknown`), the arrays live in the linear-memory shadow stack: Sign 87 needs
  about 207 KB of it, Verify 87 about 131 KB, against the 1 MiB default of rust-lld, so a contract linked with a smaller
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
