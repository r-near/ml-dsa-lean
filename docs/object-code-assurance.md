# Object-code assurance: what exists, what we have, and the options

A study written on 2026-10-30 and revised on 2026-11-04. Nothing here changes code or proofs. Every statement about
another project cites a primary source; anything that could not be confirmed is marked **UNVERIFIED**. Effort estimates
are estimates. The current constant-time verdicts are in `checkct/README.md` and summarized in `docs/assurance.md`
section 4; this document keeps the argument and the method.

## 0. Bottom line

1. mldsa-native proves, in HOL Light and on the final object code, functional correctness, memory safety and
   (secret-independent) timing for about 20 AArch64 routines, about 20 x86_64 AVX2 routines and 5 RV32IM routines. Each
   proof is per routine. The functional statements are congruences mod q plus explicit output bounds on *signed,
   lazily reduced* int32 data, with precondition bounds, fixed twiddle tables, and (on x86_64) a non-FIPS coefficient
   order. There is no end-to-end proof from the C API through the assembly to FIPS 204. The link between the HOL Light
   statements and the CBMC contracts the C code relies on is a manual, comment-level "keep in sync", and the CBMC
   contract for the NTT states only a bound, so the functional postcondition does not reach the C callers at all.
2. Our BINSEC runs are a *bounded-verification* result in the BINSEC/Rel sense: when the tool says "secure" it has
   explored every path of that compiled probe to completion and found no secret-dependent branch, memory address or
   division operand, for all secret values and all public values of the probe's inputs. That is stronger than
   "tested", and weaker than "the signing function is constant time". "Unknown" is a failure to conclude, not a near
   miss. Section 3.4 gives the wording.
3. For a consensus system, the property that matters most is that Verify agrees across every node, architecture and
   backend, and Verify handles only public data. So object-code *constant time* matters for Sign (signing keys) and
   object-code *functional correctness* matters most for Verify. Different assurance goals suggest different options
   for each.
4. Position (section 5): keep the portable Rust path as the default and the only one the unconditional theorem
   covers. If SIMD is wanted, write it in Rust with Lean models of the intrinsics (the SymCrypt route) so the theorem
   stays at source level; treat mldsa-native assembly as an optional, clearly labeled, axiom-carrying backend. Leave
   rustc/LLVM, ISA lifting and hardware instruction timing as stated assumptions.

## 1. Sources and pins

| Project | Pin used | Notes |
|---|---|---|
| mldsa-native | `fe47bf8afdb548224f32e7ef04fe580188f2d972` (main, 2026-10-30). Blob base: `https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/` | Most files were read from `main` on the same day. |
| s2n-bignum | `9f2cd960e11892a582e7facb0c191b4a2959ea91` (main, 2026-10-27). Blob base: `https://github.com/awslabs/s2n-bignum/blob/9f2cd960e11892a582e7facb0c191b4a2959ea91/` | `SOUNDNESS.md`, `common/safety.ml`, `doc/program_equivalence.md`, `LICENSE`. |
| BINSEC | tag `0.11.3` (the version `checkct/README.md` pins). Master at `9749bd8aed7ee0a27959158b1e53e8789cb0e5ab` (2026-08-26). Blob base: `https://github.com/binsec/binsec/blob/0.11.3/` | Diffed `src/sse/plugin/binsec_sse_checkct.ml` and `doc/sse/relse.md` between the tag and master: identical. |
| cargo-checkct | `85271e5ce9eab9ba895c62c8b5d4129810a635a0` (2026-10-08; this is both `main` HEAD and the rev `checkct/README.md` pins). Blob base: `https://github.com/Ledger-Donjon/cargo-checkct/blob/85271e5ce9eab9ba895c62c8b5d4129810a635a0/` | `src/run.rs`, `template/driver.binsec`, README. |
| BINSEC/Rel paper | Daniel, Bardin, Rezk, IEEE S&P 2020, https://arxiv.org/pdf/1912.08788 | Read the arXiv text: Definition 1, Theorems 1 to 4, Section VIII. |
| SymCrypt | branch `feature/verifiedcrypto` at `c2e575ace0ea4b6b7a4184c1f19b81d1d5b2b5be` (2026-07-12); paper arXiv 2609.15648 (14 Sep 2026), https://arxiv.org/pdf/2609.15648 | `README-VERIFIEDCRYPTO.md`, `SymCRust/lean/Intrinsics/INTRINSICS.md`. |
| libcrux | commit `9d5290ec`; plus Cryspen's post and a third-party critique cited in section 4.5 | |


Our own files: `docs/assurance.md`, `checkct/README.md`, `checkct/run.sh`, `lean/Proofs/CorrNTT.lean`.

## 2. Part 1: what mldsa-native's HOL Light proofs establish

### 2.1 Routines covered

From `proofs/hol_light/README.md` ("Routines covered") and the directory listing at the pin:

| Arch | Arithmetic routines | FIPS 202 |
|---|---|---|
| AArch64 | forward NTT, inverse NTT, `poly_caddq`, `poly_chknorm`, `poly_use_hint` (gamma2 = (q-1)/32 and (q-1)/88 variants), `poly_decompose` (both), `polyz_unpack` (gamma1 = 2^17 and 2^19), pointwise Montgomery multiply, pointwise multiply-accumulate (l = 4, 5, 7), `rej_uniform`, `rej_uniform_eta2`, `rej_uniform_eta4` | Keccak-f1600 in five variants: scalar lazy-rotation x1, v8.4-A SHA3 x1, SHA3 x2, scalar/NEON hybrid x4, triple hybrid x4 |
| x86_64 (AVX2) | forward NTT, inverse NTT, `nttunpack`, `poly_caddq`, `poly_chknorm`, `poly_use_hint` (2), `poly_decompose` (2), `polyz_unpack` (2), pointwise, pointwise multiply-accumulate (l = 4, 5, 7), `rej_uniform`, `rej_uniform_eta2`, `rej_uniform_eta4` | 4-way Keccak-f1600 (AVX2) |
| RV32IM | forward and inverse NTT (each in standard and slow-multiplier variants), pointwise Montgomery multiply | none |

Source: https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/proofs/hol_light/README.md

Not in the HOL Light set, going by the README's list (the proofs directory was not searched for others): `poly_reduce`, sampling of the challenge polynomial (SampleInBall), packing and unpacking other
than `polyz_unpack`, the sponge (only the permutation is proved), rounding Power2Round, and every algorithm above the
polynomial level (ExpandA, KeyGen, Sign, Verify). These are C, covered by CBMC for undefined-behavior freedom only
(root README, https://github.com/pq-code-package/mldsa-native, "Formal Verification"; and
the related-work survey in `docs/assurance.md` section 10, which found no FIPS-level theorem for the whole algorithm).

### 2.2 Shape of the functional-correctness statement

Each routine has a Hoare-style triple `ensures arm|x86 pre post frame` in which the code is "the bytes at the PC": the
precondition asserts `aligned_bytes_loaded s (word pc) <mc>`, where `<mc>` is a bytecode list embedded at the top of the
`.ml` file and checked against the assembled object by `define_assert_from_elf`
(`proofs/hol_light/aarch64/proofs/mldsa_ntt_aarch64_asm.ml`; README "Primer": "Proofs are 'post-hoc' ... operate on the
final object code").

The spec is a HOL Light mathematical definition, not a transcription of the C. The shared definitions are in
`proofs/hol_light/common/mldsa_specs.ml`. Concretely, for the AArch64 forward NTT
(`aarch64/proofs/mldsa_ntt_aarch64_asm.ml`, `MLDSA_NTT_SUBROUTINE_CORRECT`):

```
precondition:  x_i : int32 at a+4i, for i < 256; zeta tables at z_012345, z_67; SP aligned 16; non-overlap
postcondition: (zetas_012345 = MAP iword ntt_zetas_layer012345 /\ zetas_67 = MAP iword ntt_zetas_layer67 /\
                (!i<256. abs(ival(x i)) <= 8380416)
                ==> !i<256. (ival z_i == arm_mldsa_forward_ntt (ival o x) i) (mod 8380417) /\ abs(ival z_i) <= 75423752)
frame:         ABI-permitted registers and flags, the 1024 bytes at a, 64 bytes below SP
```

with `arm_mldsa_forward_ntt f k = (SUM_{j<256} f j * 1753^((2 * bitreverse8 k + 1) * j)) rem 8380417`
(`mldsa_specs.ml`). Points that matter for any bridge to our Lean spec:

- **Congruence plus a bound, not equality.** Inputs are signed int32 with |x| <= 8380416; outputs are only congruent
  mod q and lie in |z| <= 75423752 (AArch64) or <= 42035261 (x86_64, README "Primer" example). Reduction to canonical
  form is a separate step (`poly_caddq` gives `ival(x) rem q` for |x| < q, per `mldsa_poly_caddq_aarch64_asm.ml`).
- **Twiddle tables are hypotheses.** The statement only holds when the table pointers hold exactly the proved constants
  (`zetas = MAP iword ntt_zetas_layer012345`). The C contract enforces this with `requires(zetas_l123456 == mld_aarch64_ntt_zetas_layer123456)`
  (`mldsa/src/native/aarch64/src/arith_native_aarch64.h`).
- **Order and scaling are backend specific.**
  - AArch64 NTT output follows the FIPS bit-reversed order (`bitreverse8 k` in the exponent).
  - x86_64 uses a custom order `mldsa_avx2_ntt_order` (bit-reverse composed with an 8x8 transpose, `mldsa_specs.ml`)
    and requires `aligned 32` buffers. The x86 `meta.h` defines `MLD_USE_NATIVE_NTT_CUSTOM_ORDER` and calls
    `mld_nttunpack_avx2_asm` to convert (`mldsa/src/native/x86_64/meta.h`). Every consumer of NTT-domain data on that
    path (pointwise, ExpandA output, NTT of s1, s2, t) lives in the custom order.
  - Pointwise multiply and accumulate compute `f * g * 2^-32 mod q` (`mldsa_pointwise`, `mldsa_pointwise_acc_l*`,
    Montgomery with R = 2^32).
  - The inverse NTT spec is `2^24 * SUM f(bitreverse8 j) * 731434^((2j+1)k) rem q`, which `poly.h` documents as
    `NTT^{-1} o mult(2^32)`. Composed with the 2^-32 of the pointwise product, the scalings cancel (this follows from the
    two specs; whether mldsa-native states the composition anywhere is **UNVERIFIED**, it was not searched for).
- **Other examples.** `poly_use_hint_88`: for all `x_i < q` and `h_i <= 1`, output `i` is `mldsa_use_hint_88 (h i) (x i)`
  (a HOL transcription of FIPS 204 UseHint, with a lemma tying it to the code-shaped version) and output `< 44`.
  `poly_chknorm`: `X0 = bitval(exists i. abs(x i) >= bound)` for public `0 <= bound < 2^31`.
  `rej_uniform`: output list is the first 256 elements of `REJ_SAMPLE inlist`, where each 24-bit word is masked to 23 bits
  and kept iff `< q`; the return value is the count. `rej_uniform_eta2/4`: nibble filter (`< 15`, resp. `< 9`) then map
  to `2 - n mod 5`, resp. `4 - n`. The `decompose`, `polyz_unpack`, Keccak and RV32 statements were not read.

### 2.3 The constant-time statement

The mechanism is s2n-bignum's "microarchitectural events" (`common/safety.ml`, https://github.com/awslabs/s2n-bignum/blob/9f2cd960e11892a582e7facb0c191b4a2959ea91/common/safety.ml):
the ISA model emits `EventLoad (address, length)`, `EventStore (address, length)` and `EventJump (src pc, dst pc)` for every
instruction whose timing could depend on data, plus x86 `EventX86PEXT`/`EventX86POPCNT` (instructions not on Intel's
DOIT list). The theorem for each routine is, in shape:

```
exists f_events. forall e <public args> ... ==> ensures arm
   (pre /\ read events s = e)
   (post /\ exists e2. read events s = APPEND e2 e /\ e2 = f_events <pointers, pc, sp, return address> /\
                       memaccess_inbounds e2 <read set> <write set>)
```

That is: the event trace is a function of the *pointers only*, never of memory contents, so there is no secret-dependent
branch, load address or store address, and the same trace proves memory safety. (Shown for NTT in
`mldsa_ntt_aarch64_asm.ml`, `MLDSA_NTT_SUBROUTINE_SAFE`.)

Exceptions, from the README: `rej_uniform` is proved correct and memory safe but is variable time by design (public
matrix). `rej_uniform_eta2/4` are proved secret-independent *relative to a public reject pattern*: `f_events` also takes
`REJ_MASK_ETA2 inlist`, one accept/reject bit per nibble, justified by citing Section 5.5 of the Dilithium round 3
specification (each acceptance decision is statistically independent of the accepted value). The x86 eta samplers fix
the buffer length (136 and 272 bytes). For RV32IM the model has no events for `MUL`/`MULH`, so the claim assumes fixed
latency or excludes operand-dependent latency from the attacker model (README).

### 2.4 What is assumed

From s2n-bignum's `SOUNDNESS.md` (https://github.com/awslabs/s2n-bignum/blob/9f2cd960e11892a582e7facb0c191b4a2959ea91/SOUNDNESS.md),
which mldsa-native's own `SOUNDNESS.md` says "applies to mldsa-native unchanged" (same tools, ISA models, TCB), apart from
spec and constant differences:

- **ISA model fidelity (B1).** Hand-written from the vendor manuals; checked by co-simulation against an independent
  backend, which the document itself calls "high confidence, but ... inherently incomplete". Underspecified behavior is
  modeled as nondeterminism.
- **ELF loader (B2), HOL Light kernel and OCaml runtime (C1).**
- **Model omissions (B3).** Sequential, single-core, user mode, flat memory, no speculation, no caches or TLBs.
  Spectre-class channels are not addressed.
- **Timing (A3).** The proof shows the instruction sequence and addresses are secret independent; it "does not and cannot
  guarantee that the hardware executes those instructions in constant time" (variable-latency instructions,
  Hertzbleed-style effects; DIT on Armv8.4-A and DOITM on Intel Ice Lake onward are opt-in mitigations; AMD has none).
- **Memory safety (A4).** Flat memory model; the safety proofs check declared read and write sets. The stack-discipline
  property (no access below SP) is *not* checked.
- **Environment (D1).** 64-bit, little endian, alignment checking off, caller-mapped memory.
- **Reassembly caveat (Gap B).** "When s2n-bignum `.S` files are imported into another project and assembled on a
  different system, there is currently no systematic check (e.g., hash comparison or watermarking) that the resulting
  object code matches the bytes the proofs were verified against." mldsa-native builds its proof objects from
  `proofs/hol_light/<arch>/mldsa/*.S` with a pinned nix toolchain (`proofs/hol_light/aarch64/Makefile`: `as -march=armv8.4-a+sha3`,
  `strip`; checks that x18 is unused, which matters on Apple platforms). `scripts/autogen` generates those files and the
  shipped `mldsa/src/native/*/src/*.S` from the same `dev/` sources (`gen_hol_light_asm_file`, `update_via_simpasm`), with
  different flags and namespace. No check was found that a *consumer's* assembled bytes equal the proved bytes;
  that check would have to be ours (section 4.1).
- **Preconditions at call sites (D3).** The caller must satisfy bounds, alignment, non-aliasing and table identity.

### 2.5 How the assembly connects to the C, and is anything end to end

No. Three separate facts:

1. s2n-bignum's `SOUNDNESS.md` D3: "For mlkem-native, a manual (non-machine-checked) bridge connects the HOL Light assembly
   postconditions to the CBMC contracts used for C-level verification. There is no end-to-end machine-checked proof from
   the C API through assembly to the cryptographic specification." mldsa-native's `SOUNDNESS.md` states the analysis
   applies unchanged (https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/SOUNDNESS.md).
2. The bridge is a comment: each asm prototype in `arith_native_aarch64.h` carries "This must be kept in sync with the
   HOL-Light specification in proofs/hol_light/aarch64/proofs/mldsa_ntt_aarch64_asm.ml", and the HOL file says the
   reverse ("This must be kept in sync with the CBMC specification"). No script that compares them was found
   (`scripts/check-contracts` checks that contracts have CBMC proofs; `scripts/check-hol-light-imports` lints imports).
   Not exhaustive: not every script was read.
3. The CBMC harness for the native wrapper replaces the assembly by its contract
   (`proofs/cbmc/ntt_native_aarch64/Makefile`: `CHECK_FUNCTION_CONTRACTS=mld_ntt_native`, `USE_FUNCTION_CONTRACTS=mld_ntt_aarch64_asm`),
   and that contract is bounds only: `requires array_abs_bound(r, 0, N, 8380417)`, `ensures array_abs_bound(r, 0, N, 75423753)`.
   `mld_poly_ntt` in `poly.h` likewise ensures only `array_abs_bound(..., MLD_NTT_BOUND)`; "Implements FIPS 204 Algorithm 41" is a
   doc comment (`@spec`). So the functional claim "this is the NTT" never reaches the C layer, even informally in a
   machine-readable form. The same holds up the stack: no theorem relates ExpandA, KeyGen, Sign or Verify to FIPS 204
   (`docs/assurance.md` section 10).

AWS-LC's ML-DSA imports only the C-only variant of mldsa-native (`docs/assurance.md` section 10), so it inherits the CBMC proofs but not
the assembly proofs.

## 3. Part 2: what our BINSEC checks establish

### 3.1 The tool and what it was asked

`checkct/` uses `cargo-checkct` (Ledger Donjon) driving BINSEC's `checkct` plugin (relational symbolic execution, RelSE, from
the BINSEC/Rel line of work). Per entrypoint, cargo-checkct writes a BINSEC script from `template/driver.binsec`:

```
load sections ... from file
starting from <entrypoint>
with concrete stack pointer
<lr> := <fixed return address>
(x86_64: DF := 0; cpuid replaced by "no optional features")
replace <__checkct_private_rand> () by  res := secret ; return res  end
replace <__checkct_public_rand>  () by  res := nondet ; return res  end
halt at <__checkct_panic>      (if present)
halt at <return address>
explore all
```

and runs `binsec -sse -checkct -sse-depth 1000000000 -sse-jump-enum 64 -sse-timeout <T> -checkct-leak-info instr|halt
-checkct-features <list>` (`src/run.rs`, `template/driver.binsec`, cargo-checkct pin above). Our `checkct/run.sh` uses
`--timeout 900`, `--checks control-flow,memory-access,dividend,divisor`, `--skip-unknown`, `--all-leaks`. The SMT solver
timeout is BINSEC's default of 5 s per query (cargo-checkct does not override it; `doc/sse/relse.md`).

### 3.2 Soundness claim and its fine print

- **Property.** BINSEC/Rel Definition 1: a program is constant time up to k steps iff any two low-equivalent initial
  configurations (equal public registers and public memory) that run k steps produce equal *leakage*. Leakage is the
  sequence of branch outcomes / jump targets and load and store addresses. The checkct plugin inserts a check at every
  load and store address, every branch condition and every computed jump target, and optionally at multiplication
  operands and at dividend and divisor (`binsec_sse_checkct.ml`: `Ct_check (addr, Memory_access)`, `(expr, Control_flow)`;
  multiplication is "experimental" per the CLI help, and our run does not enable it).
- **Theorem.** BINSEC/Rel Theorem 3 (bounded verification): if the symbolic evaluation never gets stuck on a satisfiable
  insecurity query, the program is constant time with respect to the symbolic initial configuration; "if s0 is fully
  symbolic, then P is constant-time". Theorem 2 (correctness of RelSE) and Theorem 4 (bug finding: a stuck state implies a
  real violation) complete the picture. The proofs are pen and paper (appendix B of the paper), and they are about the 2020
  prototype's method, not a verified statement about the shipped code: the 0.11.3 `checkct` plugin is a reimplementation that
  runs a cascade of taint analysis, chosen-value sampling and RelSE (options `Taint`, `ChosenValues`, `Relse` in the CLI source).
  By construction the first two answer only when trivially right (`taint_analysis` returns Secure only for an untainted
  expression; `cv_analysis` returns Insecure only with a concrete witness pair) and RelSE decides the rest, so the cascade should
  preserve the soundness argument, but that was not audited. The OCaml plugin, the lifter and the SMT solver are not verified.
- **When it says "secure".** BINSEC's own table (`doc/sse/relse.md`, "Threat to completeness"): `secure` iff no leak was
  found *and* exploration was complete; `unknown` if no leak was found but exploration was cut off; `insecure` if any leak
  was found. In code, an unknown report results from any of: pending paths (timeout), unknown check statuses, non-executable
  code, max-depth cuts, jump-enumeration limit hit, unresolved formulas, errors (`is_unknown_report` in
  `binsec_sse_checkct.ml`). cargo-checkct sets depth to 10^9 and jump enumeration to 64, so "secure" for our probes means
  exploration finished within those limits. The documentation's reminder that BINSEC "only performs bounded verification.
  The result is valid given the initial assumption" applies to *assumptions on inputs* (e.g. `assume n < 10`); our probes make
  secrets `secret` and publics `nondet` (unconstrained), so there are no input assumptions beyond the harness.
- **So:** a "secure" verdict is a result over all secret values and all public values of the probe's inputs, for that exact
  compiled binary, covering the whole function (every path from entry to return), not a sampled or depth-truncated
  analysis. This is the strongest reading, and it holds only if the exploration was complete.
- **Trusted.** (i) The instruction lifting (BINSEC DBA lifter; unisim_archisec for non-x86 targets); No
  co-simulation or fidelity argument comparable to s2n-bignum's, **UNVERIFIED** either way. (ii) The SMT solver and the
  plugin. (iii) The leakage model: control flow and addresses only. Not modeled: operand-dependent instruction latency
  (cargo-checkct README: "the analysis is predicated on the fact that all instructions have data-independent timing";
  the Ledger blog says soundness holds "under the assumption that instructions themselves execute in time independent
  from their operands"), caches beyond address leakage, speculation, power. (iv) The harness: concrete stack pointer; x86_64
  `cpuid` stubbed to "no optional features", so runtime-dispatched SIMD paths are *never explored* (relevant in the
  performance phase); a secret-dependent panic is still reported as a leak (README), but panic-path internals are cut at
  `__checkct_panic`. (v) The bytes: the binary analyzed is the driver built by cargo-checkct with the pinned nightly,
  `-Zbuild-std`, `compiler-builtins-mem`, release, not what nearcore will link.

### 3.3 What our runs cover and do not

BINSEC checks compiled probes of every secret-touching step of KeyGen and Sign (field and mask primitives, rounding, the NTT
and pointwise product, Keccak-f and the SHAKE paths with secret input, ExpandS, ExpandMask, bit packing, skEncode/skDecode,
`sk_is_well_formed`, the KeyGen steps, the Sign steps, `prepare_sk` and `signing_key`; the list is in `checkct/README.md`),
two whole-Sign censuses and positive controls. The whole KeyGen, Sign and `pk_from_sk` functions have no verdict, and the
glue between steps is covered by code reading only. The probes ran on x86_64-unknown-linux-gnu (several profiles), thumbv7em-none-eabihf, riscv32imac-unknown-none-elf and AArch64 built
without NEON. The counts per target and profile, the unknowns and the out-of-memory ledger are in `checkct/README.md` and
`docs/assurance.md` section 4; they change when the code or the tools change, so they are not repeated here.

What the runs cannot cover:

- **Whole Sign:** the censuses either report only the public `sample_in_ball` accept branch or have no verdict (out of memory).
  Sign is covered by its secret-touching pieces (`response_*`, `hint_step_*`, the hash and ExpandMask probes, `prepare_sk`).
- **Unknowns:** probes where BINSEC did not finish or cannot lift an instruction (VEX forms under `+fma`, some AArch64 solver
  queries, some riscv32imac pieces). No leak was found in them and no conclusion is drawn.
- **Builds with AVX2 target features:** BINSEC cannot lift VEX instructions, so a build with `-C target-feature=+avx2` has no verdict for the probes that contain vector code (3.5).
- **AArch64 with NEON** (the default AArch64 build): BINSEC 0.11.3 cannot lift the vector `umax`/`umin` instructions, so probes stop `unknown` at the first one. macOS is
  not covered at all.
- **Other builds:** other rustc versions, flags and inlining contexts. Verdicts depend on code shape (CT-1 and CT-2 in
  `docs/assurance.md` section 6), so they hold for the builds measured.
- **zeroize builds:** not probed (the wipes run after the outputs are written).

### 3.4 How to state the result

The result is *verified by BINSEC*, not "proved": the verdict comes from a tool whose implementation, lifter and solver are
trusted, unlike a Lean or HOL Light theorem. A sentence that stays inside the evidence: "For the compiled probe functions
listed in `checkct/README.md`, BINSEC checkct 0.11.3 explored every execution path to completion and found no secret-dependent
branch, memory address or division operand, for all secret values and all public values of the probe's inputs, under the
probe harness's input shapes (a bounded-verification result in the BINSEC/Rel sense), on the targets and profiles listed
there." Not claimed: constant time of the whole `sign_internal` as linked into an application, of other compiler versions or
flags, of macOS or AArch64-with-NEON builds, or of hardware (variable-latency instructions, speculation, power). Trusted:
BINSEC's instruction lifting, solver and plugin; "all instructions take operand-independent time".

### 3.5 AVX2 target features (round 12; there is no dispatch any more)

Until round 12 the opt-in `avx2` cargo feature compiled the NTT bodies twice on x86_64 and picked one at run time (a CPUID check, a cache static and `#[target_feature]` copies), and
dispatched `verify` to a 4-way body the same way. That dispatch, its `unsafe` and `src/cpu.rs` are gone: the crate has one compilation of every function per build, `#![forbid(unsafe_code)]` holds
in every configuration, and the Cargo feature `avx2` is a deprecated no-op. A build that wants AVX2 code compiles with `-C target-feature=+avx2` (or `-C target-cpu=x86-64-v3`), which changes what
LLVM emits for the same Rust text and nothing else (the extraction is identical under both, `scripts/check-feature-independence.sh`; `docs/assurance.md` section 0, Round 12). What this section used to record
(the dispatch builds `dispatch` and `nearcore-dispatch`, the dispatch cache pre-set, `scan-avx2.sh` on the four `*_avx2` functions) describes trees up to fv-p11 and is not repeated; the
sweep tables in `checkct/README.md` that name those profiles are marked as history there.

**What BINSEC covers.**
- The default build, the `nearcore` build (opt-level 3, fat LTO, one codegen unit; no AVX2) and `nearcore-novec` are the builds with verdicts in the sweep of 1a72d9e (section 3.2 and `checkct/README.md`).
  **On the final tree the full sweep was rerun in round 13** (tree 1d8b5c5, whose `src/` is the final tree's; `checkct/results/sweep-1d8b5c5/`, `docs/assurance.md` section 4, "Round 13 BINSEC sweep"): every profile except the removed dispatch ones, on x86_64,
  thumbv7em, riscv32imac and AArch64 without NEON. The default-build code of the driver is identical to fv-p11's in every function on all three targets (`checkct/compare-code.sh`, an address-masked comparison, not a verdict; `ntt::dispatch` was restored in round 13),
  and 1,018 of the 1,024 probes of the nine cells that have a counterpart in the sweep of 1a72d9e are equal in verdict and counts, the other six being listed, with the reruns, in that section. The `avx2` and `nearcore-avx2` profiles ran only their 26 NTT probes.
  The smaller rerun of round 12 and the 39 of 233 differing x86_64 functions that came with it describe the tree before the wrapper module was restored; they are superseded.
- BINSEC 0.11.3 cannot lift VEX-encoded instructions. A build with `-C target-feature=+avx2` (`bash checkct/select-ntt.sh avx2`) therefore ends `unknown` for
  every probe that reaches vectorized code; the scalar probes (`field_mul_shoup`, `field_mont_reduce`, `field_mul_mont`) stay `secure` there. `nearcore`'s own flags have `+fma`, which implies AVX in LLVM, so the
  `nearcore-exact` profile is in the same position for 49 of 113 probes. No claim is made about BINSEC verdicts for AVX or AVX2 code.
- There is no substitute static scan of vector code any more: `checkct/scan-avx2.sh` scanned the `*_avx2` functions of the dispatch driver, which no longer exist.

**The 4-way verify.** Verify handles only public data, so the 4-way body (plain Rust, `src/keccak4.rs`, `src/sampling.rs`, `src/verify.rs`) and the verify-only `poly_use_hint_pub` and `bit_unpack_pub` have no BINSEC probes
and need none. The functional evidence for them is in `docs/assurance.md` section 1.9 and the tests it lists, run in the default configuration and with AVX2 target features.

A reminder from the first version of the dispatch: it marked the field functions `#[inline(always)]` on every target, which made
the riscv32imac `response_*` and `hint_step_*` probes `unknown` (one pending path after an hour) where the Shoup/Montgomery tree
without it finishes them in about ten minutes. BINSEC completion depends on code shape, not only on the source.

## 4. Part 3: options for object-code functional correctness of our crate

Framing. Our theorem is about the Rust source; rustc/LLVM output is trusted (`docs/assurance.md` section 2). An object-code
functional-correctness claim needs, for each hot function, a machine-checked or tool-checked link between the *bytes that
run* and a spec that is (or is connected to) our Lean spec. For nearcore, "the bytes that run" is what rustc emits when
nearcore builds the crate from source, with nearcore's toolchain and flags, unless we ship precompiled objects. That fact
dominates options (b) and (c).

### 4.1 (a) Adopt mldsa-native's verified assembly as optional backends via FFI

**What it gives.** For the chosen kernels, object-code functional correctness, memory safety and secret-independent
timing under s2n-bignum's TCB (section 2.4), with the Rust or Lean side stating the expected behavior.

**What we would have to build and trust:**

1. *Transcribe each HOL postcondition into a Lean statement.* The mathematical content is small. For the NTT, our
   `CorrNTT.lean` already proves `NTT_eval : (NTT w)[k] = SUM_i w[i] * rt 8 k ^ i`; the HOL formula is
   `SUM_j f j * 1753^((2 * bitreverse8 k + 1) * j)`. What remains is `rt 8 k = zeta ^ (2 * BitRev8 k + 1)`; This was checked
   numerically for all 256 k with the Lean definitions of `rt` and `zeta` transcribed to Python (true); a
   `decide +kernel` proof like the existing `zeta_sq` is expected but was not run in Lean. The real work is the *representation*
   lemma: signed lazily reduced int32 with bounds on one side, canonical `u32` in `[0, q)` on ours, Montgomery factors
   (pointwise: 2^-32; inverse NTT: 2^32), and on x86_64 the custom order. Each transcription is one more trusted statement
   (below).
2. *FFI glue and provenance.* `extern "C"` (or `global_asm!` on the flattened `proofs/hol_light/*/mldsa/*.S` files; whether
   those are directly usable that way is **UNVERIFIED**). Alignment (`#[repr(align(32))]` on x86_64), non-aliasing,
   table pointers equal to the exact constants (the spec requires the constants), calling convention. A *byte-identity
   check*: assemble in our build, extract `.text` and compare with the bytecode list in the matching `.ml`
   (`proofs/hol_light/aarch64/proofs/dump_bytecode.ml` shows how they dump it). That is a script, not a proof, and it closes
   the reassembly caveat above. The `mld_` namespace prefix in proof objects versus the shipped prefix means comparison
   must be on section bytes, not symbols.
3. *Runtime feature dispatch.* mldsa-native guards each call with `mld_sys_check_capability` and falls back to C. Ours must
   fall back to the portable, fully proved Rust, and the dispatch itself is outside every proof.
4. *Extraction.* An FFI function is external to Aeneas, which emits an opaque declaration. That breaks our extraction gate
   ("no referenced external axiom", `docs/assurance.md` section 0). The honest design is the SymCrypt pattern: a `cfg`-gated backend,
   with the kernel represented in Lean by an axiom that states the transcribed postcondition (SymCrypt's `#[verify::opaque]`
   shims paired with Lean `[step]` axioms; `INTRINSICS.md` P3/P4). The headline theorem for that build becomes *conditional on
   N named axioms*; the portable build's theorem stays unconditional. A Verify-focused kernel set is roughly NTT, inverse NTT,
   pointwise, pointwise-accumulate (three sizes), use_hint (two), chknorm, caddq: on the order of 10 axioms per architecture
   (an estimate, not a measurement), plus the layout adapter on x86_64.

**Trust list for this option** (everything not kernel-checked in our repo):
the transcription of each HOL statement into Lean (reviewable, small, but not machine linked: it is the same "manual bridge"
mldsa-native has between HOL and CBMC); the byte-identity script; the FFI glue and calling convention; s2n-bignum's ISA
model, ELF loader, HOL Light and OCaml (section 2.4); runtime feature dispatch; table constants; data-layout adapters; the
numerical bound lemmas if we state them as axioms rather than prove them in Lean (we can prove the arithmetic side ourselves
since we own the Lean spec). The interface spec for each kernel is *their* statement; if their spec has a mistake that does
not break their own use, ours inherits it.

**Licenses.** mldsa-native: `Apache-2.0 OR ISC OR MIT`; its `LICENSE` says it is a fork of the public-domain Dilithium
reference code, and "Every file states its own SPDX-License-Identifier" (test and benchmark helpers differ) (https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/LICENSE).
s2n-bignum: `Apache-2.0 OR ISC or MIT-0` (https://github.com/awslabs/s2n-bignum/blob/9f2cd960e11892a582e7facb0c191b4a2959ea91/LICENSE;
the HOL Light proof files in mldsa-native carry `Apache-2.0 OR ISC OR MIT-0` or `... OR MIT`). nearcore is `MIT OR Apache-2.0`
(workspace `Cargo.toml`, `licenses/LICENSE-MIT` and `LICENSE-APACHE`; read at cd5a94457). Vendoring either under MIT or Apache-2.0 is compatible with
a `MIT OR Apache-2.0` crate; keep SPDX headers and notices.

**Effort and maintenance (estimates, wide error bars).** First backend (AArch64 or x86_64, about 10 kernels, Lean statements,
representation lemmas, glue, byte check, differential tests against the portable path): a few person-weeks. Second
architecture: roughly the same again, mostly the x86_64 order adapter. Every mldsa-native or s2n-bignum bump means re-running
the byte check and diffing the HOL statements, because the asm is regenerated from `dev/` by `autogen` and proofs are
re-run in CI only when `proofs/hol_light/**` changes (`.github/workflows/hol_light.yml`). Proof effort in their repo, as scale:
the x86_64 NTT proof file is 267 KB, the x86_64 eta2 sampler proof 874 KB, the AArch64 NTT 50 KB (including the embedded
bytecode listing); the full proofs directory is about 6 MB, and running it "may take hours" (README).

**What we could then claim.** "For the named kernels, in builds that enable `backend-mldsa-native-<arch>`, the machine code
that runs is the object code verified in HOL Light against the following mathematical statements, which we have transcribed to
Lean and show imply the Lean spec step, under s2n-bignum's model assumptions; the end-to-end FIPS 204 theorem for that build is
conditional on these N axioms and the glue." Not claimed: anything for the C parts of mldsa-native we do not use, or for
the default build.

**Gaps that stay open even then.** The kernels are not the algorithm: they cover NTT-domain arithmetic and a few polynomial
maps, not SampleInBall, bit packing, hashing, or the control flow of Sign and Verify, which stay as compiled Rust.
Also `rej_uniform` is variable time by design on both architectures (the AArch64 proof file says it proves "memory safety
alone, _not_ constant-time"), and the eta samplers leak the reject pattern by design. Treating acceptance as public is our
checkct harness's policy too ("Not probed on purpose: rejection samplers' accept/reject branching ... public-outcome
branches", `checkct/README.md`); it is not a property of the Lean spec, and `RejTerm` is only a termination premise.

### 4.2 (b) Prove the compiled output of our own hot functions in HOL Light with s2n-bignum

**Feasibility.** s2n-bignum is built for hand-written and SLOTHY-scheduled assembly: its README states "All routines are
written in pure machine code". The infrastructure symbolically simulates instruction sequences and proves loops with
invariants, and it has a relational logic (`doc/program_equivalence.md`, citing Mazzucato et al., CAV 2025, arXiv 2505.14348)
that was used to prove NEON-vectorized and SLOTHY-reordered variants equivalent to scalar reference code. No
instance of compiler-emitted code was found in the s2n-bignum tree; that is a negative result from a directory listing, **UNVERIFIED**.
Rust-emitted code would add spills and stack traffic, calls to `memcpy`/`memset`, panic branches for each bounds check we
have not eliminated, loop unrolling and vectorization chosen by LLVM, and symbol and ABI details that vary.

**Structural problem (the decisive one).** A proof is about exact bytes. nearcore compiles our crate from source, with its own
`rustc`, profile, LTO, `target-cpu`, and inlining across the crate boundary. A HOL Light proof of the object produced by our
CI is a proof about an artifact nearcore never links, unless (i) we ship a precompiled object (then it is option (a) with
worse provenance and no hand-optimized code), or (ii) nearcore CI regenerates the bytes and re-runs the proofs on every
toolchain bump (hours; the mldsa-native setup gates it on changed files for that reason). Brittleness across rustc versions is
therefore not an inconvenience but the normal case: every nightly would invalidate it.

**Verdict.** Not recommended as a standing guarantee. It could be justified only as a one-off audit of a pinned release
object for a single kernel. Effort (estimate): months per nontrivial kernel plus re-proof per compiler change.

### 4.3 (c) Translation validation or binary-level equivalence against the Lean model

None of the existing tools connect to a Lean model, so each closes at most the "compiler" part of the gap and needs a *second*
specification language:

| Tool | What it checks | Fit |
|---|---|---|
| Alive2 | refinement between LLVM IR before and after optimization passes; loops unrolled once; experimental AArch64 extension "arm-tv" for the backend ([Regehr, Alive2 part 1](https://blog.regehr.org/archives/1722); [talk on arm-tv](https://talks.cam.ac.uk/talk/index/231601/)) | IR-level only; we would still need IR to Lean; does not see rustc's MIR-to-IR step |
| SAW with Macaw | x86_64 machine code (experimental) against Cryptol specs; used for AWS-LC proofs ([SAW manual](https://galoisinc.github.io/saw-script/master/saw-user-manual/verifying-code.html), [Macaw paper](https://arxiv.org/pdf/2407.06375)) | x86_64 only; spec in Cryptol, i.e. a second spec to keep faithful to FIPS 204 and to our Lean spec |
| seL4-style translation validation | decompile a gcc binary and prove refinement to the C semantics ([Sewell, Myreen, Klein, PLDI 2013](https://www.cl.cam.ac.uk/~mom22/pldi13.pdf)) | built around C and one compiler version; no Rust analogue known |
| s2n-bignum `equiv.ml` / relational Hoare logic | binary versus binary equivalence (e.g. optimized versus reference assembly) | would prove two *binaries* equal; the reference binary still needs a functional proof |

Our own `impl-eval` differential (`docs/assurance.md` section 2: 345,360 cases, 100% agreement, 4 injected bugs detected) checks that the extracted
model and the native build agree on sampled inputs. It is testing, but it is the realistic form of (c) today: it exercises
rustc's actual output and the Lean model together, and it can be rerun against nearcore's exact toolchain and flags. A cheap
strengthening is to run the same corpus (plus ACVP and Wycheproof, already in `tests/`) through every backend and optimization
profile nearcore uses, and to exhaustively test the small-domain kernels (field operations over all of Z_q, rounding over
all of Z_q, which the VCVio differential already does for the spec).

Whether BINSEC (or another symbolic executor) could be turned into a functional equivalence checker between two binaries
is **UNVERIFIED**; its documented use is the constant-time and secret-erasure checks.

### 4.4 (d) SymCrypt's approach: Aeneas/Lean with a Lean model of AVX2 and NEON

Primary sources: arXiv 2609.15648 and `README-VERIFIEDCRYPTO.md` / `INTRINSICS.md` at the pinned commit.

- **What it is.** Rust source, extracted by Charon/Aeneas, proved against Lean specs of FIPS 202/203 (and others). Hardware
  intrinsics are modeled, preferably as Rust shims under `src/verify/` (a transcription of the vendor pseudocode, itself extracted
  and proved against a lane-level Lean spec, with differential tests against the real `core::arch` intrinsic on capable hardware),
  and as Lean axioms only for AES, SHA-2 rounds and PCLMULQDQ. Their table shows 23 AVX2 and 26 NEON shims with 0 axioms; the
  claim is that the shipped ML-KEM path "introduces no hardware trust-boundary axioms" (`INTRINSICS.md` section 2).
- **Object code?** No. They state: "we trust the Rust toolchain, notably its compiler and its platform-specific back-ends for
  x86-64 (including SSE2/AVX2) and AArch64 (including NEON)", and "we verify only functional correctness, not leakage
  resistance" (README section 3; paper section 3). Side channels are handled by "leakage-specific fuzzing and symbolic execution
  on compiled binaries", i.e. the same class of evidence as our BINSEC probes, and informal.
- **ML-DSA status.** The paper's Figure 4 lists ML-DSA as "experimental", meaning "the Rust source is not distributed as part
  of SymCrypt"; the branch README lists only SHA-3 and ML-KEM as verified primitives. So there is no inspectable ML-DSA
  proof there . The paper reports ML-DSA Rust matching SymCrypt C for
  signing and 2.3 to 2.5x faster for verification "owing to vectorization and the more optimized Keccak", with the Formosa
  AVX2 implementation 4 to 5x ahead for signing and about 3x for verification (section 8.3). That is the performance ceiling
  to expect from intrinsics-in-Rust versus hand-tuned assembly.
- **What it gives us for the perf phase.** It is the same toolchain we use, so a SIMD kernel written in Rust with `core::arch`
  intrinsics keeps the end-to-end theorem at source level with no FFI, no axiom per kernel, no layout adapter at the ABI, and
  a feature-detection precondition that is modeled (`featurePresent` as an opaque Boolean). Costs: a Lean model of each
  intrinsic we use (their AVX2 and NEON models are available in the branch, MIT licensed, though how
  reusable they are outside their tree was not checked: **UNVERIFIED**), lane-level proofs for each vector kernel, and the intrinsic models
  join the trusted base (reviewed and differentially tested rather than machine-linked to hardware).
- **A cautionary example for axiomatized intrinsics:** see 4.5, where a wrong intrinsic specification sat unnoticed in a
  "verified" libcrux proof set. SymCrypt's Rust-shim-first policy is the mitigation: a shim is executable, so it can be
  tested against hardware.
- **BINSEC interplay (our gotcha).** cargo-checkct models `cpuid` as reporting no optional features. A runtime-dispatched
  AVX2 path is therefore never entered. Constant-time probes for SIMD kernels must force the path at compile time (for
  example with `#[target_feature(enable = "avx2")]` or `-C target-feature=+avx2` in the driver build) and BINSEC must
  support the instructions involved (**UNVERIFIED** for AVX2; it did not complain on the scalar probes).

### 4.5 (e) libcrux's hax/F* approach, briefly

Rust source is extracted by hax to F*; the maintainers say Rust is "directly verified for runtime safety and functional
correctness using the hax toolchain" for verified modules, that "the verification guarantees for libcrux code only extends to
the verified modules", and that executables "are not verified to be side-channel resistant" (libcrux README;
https://cryspen.com/post/strengths-and-limitations/). The ML-DSA proof set (per the survey behind `docs/assurance.md` section 10) is
leaf modules of the portable and AVX2 SIMD layers; the top-level Sign, Verify and KeyGen modules are admitted. AVX2 intrinsics
are specified by F* `val` lemmas in `Spec.Intrinsics.fsti`, i.e. axioms. A third-party report (Symbolic Software, 17 Feb
2026, https://symbolic.software/blog/2026-02-17-cryspen-mldsa/) says one of those specs (`i16_mul_32extended`) computed
x * x instead of x * y, making the axioms logically false, and that a dead verifier norm check and a hint decoding bound
bug existed; the report records fixes for the latter two (PRs merged 2026-03-04) and no fix for the specification error. Those claims were not
re-verified against the code and are treated as third-party. Comparison: hax/F* gives the same
source-level, compiler-trusting guarantee as ours, with SMT instead of a small kernel, no end-to-end ML-DSA theorem, and
axiomatized intrinsics; the lesson is the one from 4.4, that an unchecked intrinsic axiom is where an otherwise formal
argument quietly stops being one.

### 4.6 Summary of options

| | Object-code FC? | Spec link to our Lean theorem | Trust added | Effort (estimate) | Fit for nearcore |
|---|---|---|---|---|---|
| (a) mldsa-native asm via FFI | yes, named kernels, under s2n-bignum TCB | manual transcription + Lean axioms; end-to-end theorem becomes conditional | HOL-to-Lean transcription, byte check, glue, ISA model | weeks per backend; recurring sync | good as optional backend with provenance check |
| (b) HOL Light on rustc output | in principle yes | would need its own bridge | toolchain-version-specific | months per kernel, redo per compiler change | poor |
| (c) TV / equivalence tools | partial (compiler step) | none off the shelf | second spec language | high, tool-building | poor today; testing is the realistic form |
| (d) SymCrypt route | no (compiler trusted) | direct, same toolchain, no FFI | intrinsic models | proportional to kernels written | best for keeping the theorem unconditional |
| (e) hax/F* | no | no top-level theorem | F* axioms, SMT | n/a | comparison only |

## 5. Part 4: position

### 5.1 Open items

1. **Land the NTT bridge lemma in Lean:** `rt 8 k = zeta ^ (2 * BitRev8 k + 1)` and the corollary
   `(NTT w)[k] = SUM_j w[j] * zeta ^ ((2 * BitRev8 k + 1) * j)`. It is small, has standalone documentation value (it states our
   NTT in the same closed form as every external NTT spec), and is the first prerequisite for any future import of an external
   kernel.
2. **Keep the consensus view explicit.** For a consensus system, differential agreement of Verify across architectures and
   backends is the safety property. When a second backend exists, every test and fuzz target should run both and compare bytes.
3. **Open constant-time gaps:** the vectorized x86_64 NTT under `+fma`, AArch64 with NEON and the whole-Sign censuses (see
   section 3.3 and `docs/assurance.md` section 7).

### 5.2 If performance work continues

1. Write SIMD as Rust intrinsics with Lean shims in the SymCrypt style (section 4.4), starting with the kernels that
   dominate Verify (NTT, pointwise multiply and accumulate, ExpandA via 4-way Keccak), so the end-to-end theorem stays
   unconditional. Prioritize Verify: public data, so no constant-time obligation, only functional agreement.
2. If object-code guarantees for specific kernels are wanted, add mldsa-native assembly as an *opt-in* backend
   (option (a)), one kernel at a time, each with: the Lean transcription, a recorded axiom, the byte-identity check in CI, and
   a runtime fall back to the Rust path. Do not make it the default and do not let it silently change the headline.
3. For any SIMD secret-handling kernel (Sign), force the path at compile time in the BINSEC driver (section 4.4) and keep the
   probes as a CI gate with a pinned toolchain.
4. Do not pursue (b) or (c) as standing programs.


### 5.3 Leave as stated assumptions

rustc/LLVM correctness for functional properties; BINSEC's lifter, solver and plugin; that instructions have
operand-independent timing (and on Intel, DOITM/DIT status of the deployment); speculative and microarchitectural channels;
the ISA models if (a) is adopted; runtime CPU feature dispatch; Charon/Aeneas and the Lean kernel (already listed).

### 5.4 Claim wording for each outcome

Unchanged parts of the claim stay as in `docs/assurance.md` section 12. These are the sentences to use for the assurance axis only.

**A. Portable path today.** The wording in `docs/assurance.md` section 12 (proved at source level, compiled code trusted, constant
time checked by BINSEC on compiled probes for the builds and targets listed in `checkct/README.md`, not for the whole signing
function as linked into an application, not for hardware timing).


**B. SIMD in Rust with Lean intrinsic models (SymCrypt style).** "As A, with the vectorized kernels written in Rust with
`core::arch` intrinsics and proved against the same Lean specification using Lean models of those intrinsics. The models are
reviewed against the vendor manuals and differential-tested on hardware; they, and the compiler's translation of intrinsics, are
trusted. Runtime dispatch between paths is outside the proof. Constant time of the SIMD paths is verified only for builds
where the path was forced in the BINSEC driver."

**C. mldsa-native assembly via FFI.** "In builds with feature `<backend>`, the named kernels (NTT, inverse NTT, ...) run
assembly whose functional correctness, memory safety and secret-independent timing are proved in HOL Light on the object code by
the mldsa-native project, under the s2n-bignum model (sequential user-mode ISA model, no speculation; timing claim excludes
operand-dependent instruction latency). We state each kernel's HOL Light postcondition as a Lean axiom (N axioms, listed in
`<file>`); the FIPS 204 theorem for that build holds conditional on those axioms, on a byte-for-byte check that the linked
kernels match the proved object code, and on the FFI glue. The default build and its unconditional theorem are unchanged."

**D. What we explicitly do not claim, in all outcomes.** No claim that rustc output was proved; no claim about hardware timing,
power, speculation or fault attacks; no claim for platforms or toolchains not named; no claim that "secure" probes imply the
whole signing function is constant time.

## 6. UNVERIFIED list

- Whether the flattened `proofs/hol_light/*/mldsa/*.S` files assemble and link under `global_asm!` or the `cc` crate without
  changes, and whether a consumer's assembled bytes equal the proved bytes (no check was found; the script is ours to write).
- Whether BINSEC 0.11.3 can lift AArch64 and AVX2 code well enough for the probes; whether its lifters have a fidelity
  argument comparable to s2n-bignum's co-simulation.
- Whether any script in mldsa-native machine-checks HOL statements against CBMC contracts (none found; not exhaustive).
- That `rt 8 k = zeta ^ (2 * BitRev8 k + 1)` is provable by `decide +kernel` in Lean (checked numerically only).
- That HOL Light's `rem` on integers is the non-negative remainder (assumed for the `caddq` reading).
- That no compiler-generated code appears in s2n-bignum (only the tree listing was scanned).
- Whether SymCrypt's AVX2/NEON Lean models are reusable outside that repository.
- The libcrux/Symbolic Software findings (third-party; fixes for two of three recorded by that source, none for the
  intrinsic specification).
- The effort estimates.