# Verified ML-DSA landscape (survey as of 2026-10-30)

Purpose: say precisely what every other formally verified or partially verified ML-DSA / CRYSTALS-Dilithium
implementation proves, so that we can state our own claim without overreaching.

Method: primary sources only (project READMEs, proof directories, CI files, papers, vendor blog posts). Where I read
code or proof files I pinned the commit or tag. I did not re-run anyone's proofs (see "Could not verify"). Facts about
our own project come from `STATUS.md` and were not re-checked here.

Evidence labels used throughout:

- **proved**: a machine-checked theorem exists in a released artifact I inspected (I read the statement; I did not rebuild it).
- **tested**: KATs, ACVP, Wycheproof, fuzzing, valgrind and similar. Not a proof.
- **claimed**: a paper or blog says it, but I could not inspect the artifact.
- **stated, admitted**: the theorem statement exists but its proof, or a dependency of it, is `admit`/`sorry`/lax.

## 1. Bottom line

**Our end-to-end claim is not unique in kind.** At least three other efforts target (or claim) end-to-end functional
correctness of a whole ML-DSA implementation against a mechanized FIPS 204 specification:

1. **Apple corecrypto** (released May 2026): production C and ARM64 assembly; KeyGen/Sign/Verify refine an Isabelle
   transcription of FIPS 204 for all three parameter sets. Coverage of Sign/Verify is bounded to specific message sizes.
2. **Microsoft SymCrypt Rust ML-DSA** (arXiv, September 2026): same toolchain as ours (Charon, Aeneas, Lean). **Claimed**;
   the ML-DSA Rust code and proofs are not in the public branch.
3. **ocaml-pq** (a pure OCaml library, September to October 2026): Lean proofs of `mldsa44/65/87_endToEnd` and
   `sign_verify`, 0 `sorry`, 0 axioms. The Lean models of the OCaml code are **hand-transcribed**, not extracted.

One more is in flight: **Formosa Crypto's EasyCrypt proof of their Jasmin AVX2 ML-DSA-65** (top-level equivalences
for keygen/sign/verify are stated, but there are 67 `admit`/`admitted` lines in 17 files, including NTT, samplers and
rounding). Everything else I found (libcrux, mldsa-native, AWS-LC) is component-level, and the remainder is tested only.

What is left that distinguishes our result (each clause is checked against the evidence in sections 3 and 5):
a **Rust** implementation, a Lean model **mechanically extracted** from it, theorems that cover **every message and
context length and every pk/sk/signature byte string** (modulo two named probabilistic premises), **all three
parameter sets**, plus **Verify(Sign) = true**, **publicly released** and re-checkable on standard Lean axioms.
The defensible statement is therefore a conjunction of those properties, not "first" or "only formally verified ML-DSA".
Proposed wording and wording to avoid are in section 5.

## 2. Snapshot (what I looked at)

| Project | Pin |
|---|---|
| libcrux (now under `celabshq`; `cryspen/libcrux` redirects) | commit 9d5290ec8e432caad9172e4e02c9062e8fcf4b7f (2026-10-15); `libcrux-ml-dsa` 0.0.11 |
| mldsa-native | commit fe47bf8afdb548224f32e7ef04fe580188f2d972 (2026-10-30) |
| AWS-LC | `main` as of 2026-10-30 (no SHA recorded) |
| Apple corecrypto | tag `2026-05` |
| SymCrypt | branch `feature/verifiedcrypto`; arXiv 2609.15648 |
| formosa-mldsa-correctness | commit 2dc59703c38bb29bb3f6e3a765f0a9934e143263 (2026-06-18) |
| formosa-mldsa | `main`, last push 2026-09-30 |
| VCVio | commit aae1c9cbd6c00311091d691b74f2d0032d76d9bd |
| ocaml-pq | commit ceeb2782e033148fc2bf773c2053752f7de5a1cd (release 0.2.1, 2026-10-11) |
| Galois cryptol-specs | `master`, last commit 2026-10-05 |

## 3. Project by project

### 3.1 Apple corecrypto (C + ARM64; Cryptol/SAW + Isabelle)

- **Toolchain.** C routines are modeled in Cryptol and checked with SAW (bounded model checking with SMT solvers). The
  Cryptol models are machine-translated to Isabelle (`cryptol-to-isabelle`) and proved to refine an Isabelle
  transcription of FIPS 204. Each hand-optimized ARM64 routine is proved equivalent (Isabelle, AutoCorres2, a custom
  `refine_arm64`) to the C routine it replaces.
- **What is covered.** "key generation, signature generation, and signature verification for ML-DSA" (blog). The top-level
  theorems are in `ccmldsa_MT_refines_FIPS.thy`: `keygen_refine`, `sign_internal_refine` (for valid sk, `IsValidSk`) and
  `comp_verify_internal_refine`, against `FIPS204_ML_DSA_KeyGen`, `FIPS204_ML_DSA_Sign` and `FIPS204_ML_DSA_Verify`.
  SAW scripts exist per parameter set (`sign65.saw`, `sign87.saw`, `verify65.saw`, ...; I did not locate the 44 variants
  in the listing).
- **Properties.** Functional correctness. Memory safety / absence of undefined behavior is checked with SAW "in particular
  ways" and complemented by conventional practices. Side channels are explicitly **not** formally verified.
- **End to end?** Yes in structure (entry point to FIPS spec), **but bounded**: "Our top-level ML-DSA SAW verification scripts
  by default only check our composed implementations of ML-DSA.Sign and ML-DSA.Verify on messages and configurations of
  specific sizes." The `sign65.saw`/`sign87.saw` scripts I read instantiate `msg_nbytes = 1` with `ctx_nbytes` in
  {0, 1, 255, 256}. The paper's footnote: "We presently verify ML-DSA on all messages of the sizes that we pick, but not all
  messages of all sizes." (I did not determine the verify-side message sizes.)
- **Trusted base** (their `soundness.md`): Isabelle, AutoCorres2, SAW and its SMT solvers, Cryptol, cryptol-to-isabelle,
  Apple Clang; hand-maintained SAW contracts and Isabelle preconditions; assumed specs for memory-management primitives and
  intrinsics; `ccrng_generate` is an uninterpreted function; SAW "cutpoints" for samplers and Sign/Verify "rel[y] on manual
  termination arguments"; the C that SAW checks is compiled differently than production C. The FIPS transcription "must
  themselves be correct" (internal review plus a third-party audit, which I have not seen).
- **Spec validation.** Manual line-by-line translation, internal review and a third-party audit (claimed).
- **Verify(Sign).** I found no Verify-of-Sign correctness theorem in the `CCMLDSA` theory list.
- **Findings reported.** A missing reduction before an inverse NTT in an early ML-DSA version, caught by SAW.
- **Licensing.** corecrypto is under an "Internal Use License"; Isabelle theories partly under restricted terms, FIPS
  specification theories carry a BSD-2 license file (`FIPS_Specifications/LICENSE_BSD2`). Re-checking needs macOS and, per their README, 20+ hours for the SAW run.
- **Status.** Released 2026-05-22 (tag `2026-05`).
- Sources: https://security.apple.com/blog/formal-verification-corecrypto/ ;
  https://github.com/apple/corecrypto/blob/2026-05/corecrypto_verify/technical_overview/formal-verification-for-apple-corecrypto.md ;
  https://github.com/apple/corecrypto/blob/2026-05/corecrypto_verify/technical_overview/soundness.md ;
  https://github.com/apple/corecrypto/blob/2026-05/corecrypto_verify/README.md ;
  https://github.com/apple/corecrypto/blob/2026-05/corecrypto_verify/isabelle/CCMLDSA/ccmldsa_MT_refines_FIPS.thy ;
  https://github.com/apple/corecrypto/blob/2026-05/corecrypto_verify/ccmldsa/sign65.saw

### 3.2 Microsoft SymCrypt (Rust; Charon/Aeneas/Lean): the same toolchain as ours

- **ML-KEM and SHA-3: proved, public.** `feature/verifiedcrypto` README: "formal proofs of functional correctness and
  panic freedom for selected Rust implementations"; the table lists only SHA-3/SHAKE, ML-KEM and the intrinsics model.
  Trust list: Rust toolchain, Charon/Aeneas extraction and its std axiomatization, runtime platform, Lean kernel and
  native tactics such as `bv_decide`.
- **ML-DSA: claimed, not inspectable.** arXiv 2609.15648 (14 September 2026) §7.5: SymCrypt "provides a portable C
  implementation, so we jointly produced and verified an experimental Rust implementation, coded by an agent". "ML-DSA’s
  signing algorithm may independently fail to terminate (with negligible probability), so we prove that its implementation,
  which is parameterized by a maximal number of pseudo-random attempts (as in the C code) succeeds on valid arguments iff
  any of these attempts succeeds at the specification level." Figure 4 lists ML-DSA (FIPS 204) as "experimental" with
  4,192 spec text lines, 500 core spec lines, 4,076 Rust lines, 3,352 property lines and 12,427 / 35,006 proof lines
  (the caption says experimental "means the Rust source is not distributed as part of SymCrypt"). The paper also says
  "we do not claim our experimental code is production-ready", and that a "significant subset" (ML-KEM, SHA-3) was released,
  with "further parts" planned.
- I grepped the `feature/verifiedcrypto` and `main` trees: there is no ML-DSA Rust or Lean file there (only the C
  `lib/mldsa.c`, which is unverified).
- **What this means for us.** A near-identical claim (Rust, Aeneas, Lean, FIPS-literal spec, termination handled by
  an attempt bound) exists from a production library, but I cannot compare theorem statements. The paper's text does not say
  whether all of KeyGen/Sign/Verify, all parameter sets, or Verify(Sign) are covered, or whether the sampler premises
  match ours.
- Sources: https://arxiv.org/abs/2609.15648 ;
  https://github.com/microsoft/SymCrypt/blob/feature/verifiedcrypto/README-VERIFIEDCRYPTO.md ;
  https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/
  (13 July 2026; names ML-DSA only as future work: "verified Rust code for, e.g., AES-GCM, FrodoKEM, and ML-DSA").

### 3.3 ocaml-pq (pure OCaml FIPS 203/204/205; Lean 4 + Mathlib, TLA+)

- **What is claimed.** `formal/README.md`: "Lean 4 with Mathlib ... proves functional correctness for every input. Each
  OCaml function is modelled in Lean, the corresponding FIPS pseudo-code is transcribed independently, and a theorem states
  that the model equals the specification". ML-DSA end-to-end theorems `mldsa44_endToEnd`, `mldsa65_endToEnd`,
  `mldsa87_endToEnd`: KeyGen equals Alg 1/6; `sign_mu_with_randomness` returns Alg 7's signature "exactly when Algorithm 7
  finishes within 821 iterations"; `sign`, `sign_deterministic`, `verify` equal Alg 2/3/8; `sign_verify`: the code's verifier
  accepts every signature the code's signer returns; key import accepts exactly keys Alg 6 could produce.
- **Checked in the repo (not rebuilt by me).** Over `formal/lean` at the pinned commit: 33,252 Lean lines, no `sorry`, no
  `axiom` declarations (the three `native_decide` hits are comments). Lean `v4.34.0`. `formal/check.sh` is the re-check
  entry point (their README: about 5 minutes on a 10-core laptop).
- **Trusted base** (their words): "Each model was transcribed by hand and cites the file and lines it models" and "The
  compiler, the runtime and the garbage collector are outside the proof"; the FIPS transcription; OCaml semantics; the Lean
  kernel and Mathlib. Sampler termination and the ML-KEM noise bound are hypotheses.
- **Not covered / caveats.** Timing ("They say nothing about timing, cache or other side channels"). The code-to-model gap is
  closed only by review and by running some models against the OCaml code, **not** by extraction.
- **Status.** Repository created 2026-09-12; release 0.2.1 on 2026-10-11; two GitHub contributors; the README says it is
  unaudited and gives no independent review of the proofs.
- Sources: https://github.com/thevilledev/ocaml-pq/blob/ceeb2782e033148fc2bf773c2053752f7de5a1cd/formal/README.md ;
  https://github.com/thevilledev/ocaml-pq/blob/ceeb2782e033148fc2bf773c2053752f7de5a1cd/formal/lean/OcamlPq/EndToEnd/MLDSA.lean ;
  https://ocaml.org/p/mldsa/0.2.0/CHANGES.html

### 3.4 libcrux-ml-dsa (Cryspen, now celabs; hax to F*)

- **Claim.** README: "The portable and AVX2 code for field arithmetic, NTT polynomial arithmetic, and serialization is
  formally verified using hax and F*." The workspace README defines the badge as "most (or all) of the Rust code ... is
  verified" and adds: "executables compiled from the code in this repository are *not* verified to be side-channel
  resistant". Cryspen's blog: "the verification guarantees for libcrux code only extends to the verified modules."
- **What is actually in the proof set** (`proofs/fstar/extraction/Makefile`, `VERIFIED_MODULES`): `Simd.Portable.*`
  (arithmetic, NTT, inverse NTT, vector type, rejection sampling, the encoding modules for commitment, error, gamma1, t0, t1),
  the same for `Simd.Avx2.*`, `Simd.Traits*`, `Constants`, `Types`, `Arithmetic`, `Polynomial`. Everything else is
  `ADMIT_MODULES` by the Makefile's definition (every extracted `.fst` not listed), which would include `ml_dsa_generic`, the top-level `sample`, `ntt`, `matrix`, `encoding`
  and `hash_functions` modules. The top-level `ml_dsa_generic.rs` carries no hax requires/ensures (I grepped).
  NEON/simd128 is not in the list.
- **Within the verified set**, 12 `verification_status(lax)` and 4 `verification_status(panic_free)` annotations remain in
  `src/` (counts over the whole crate source; e.g. AVX2 `invert_ntt_montgomery` is lax).
- **Spec.** `proofs/fstar/spec/` has only `Spec.MLDSA.Math.fst` (mont_mul, Barrett, decompose, power2round, rejection
  sampling) and `Spec.MLDSA.Ntt.fst`, plus an intrinsics spec. There is no F* transcription of KeyGen/Sign/Verify.
  I found no document validating this spec against FIPS 204 or ACVP.
- **Properties.** Bounds / overflow / panic freedom and functional equivalence to the math spec at the leaf level; secret
  independence is enforced by types (`libcrux-secrets`) and optional valgrind checks, not proved.
- **CI evidence.** `.github/workflows/mldsa-hax.yml` runs `./hax.sh extract` and `./hax.sh prove --admit`; the full
  `./hax.sh prove` job is commented out ("XXX: Is the caching ... enough to get CI minutes down for paid runners?"). The
  sibling `sha3-hax.yml` does run an unadmitted `prove`. So I **could not confirm from CI** that the ML-DSA F* proofs are
  currently re-checked on every change (they may be checked manually).
- **Bug history that bears on scope** (`CHANGELOG.md`): 0.0.8 "Fix incorrect hint decoding" and "Fix incorrect norm check
  of signer response during verification"; 0.0.9 "Fix incorrect AVX2 use_hint implementation". I did not determine which of
  those functions are inside the proof set. They show that functional bugs existed in released code in a crate with a
  "verified" badge, consistent with the partial scope above.
- **End to end?** No, and the project does not claim it. The hax paper (ePrint 2025/142) is the toolchain paper; its abstract
  does not mention ML-DSA. The SymCrypt paper's related-work section describes libcrux as verifying "SHA-3, ML-KEM, and
  parts of ML-DSA".
- Sources: https://github.com/celabshq/libcrux/blob/9d5290ec8e432caad9172e4e02c9062e8fcf4b7f/libcrux-ml-dsa/README.md ;
  https://github.com/celabshq/libcrux/blob/9d5290ec8e432caad9172e4e02c9062e8fcf4b7f/libcrux-ml-dsa/proofs/fstar/extraction/Makefile ;
  https://github.com/celabshq/libcrux/blob/9d5290ec8e432caad9172e4e02c9062e8fcf4b7f/.github/workflows/mldsa-hax.yml ;
  https://github.com/celabshq/libcrux/blob/9d5290ec8e432caad9172e4e02c9062e8fcf4b7f/libcrux-ml-dsa/CHANGELOG.md ;
  https://github.com/celabshq/libcrux/blob/9d5290ec8e432caad9172e4e02c9062e8fcf4b7f/README.md ;
  https://cryspen.com/post/strengths-and-limitations/ (12 February 2026) ;
  https://eprint.iacr.org/2025/142

### 3.5 mldsa-native (PQ Code Package) and AWS-LC / liboqs

- **CBMC (C code).** README: "prove absence of various classes of undefined behaviour in C, including out of bounds memory
  accesses and integer overflows", covering `mldsa/src/*` and `mldsa/src/fips202/*` "except for the Armv8.1-M backend and
  the debug code". The public entry points' contracts in `mldsa/src/sign.h` are return-code and memory shapes
  (`ensures(return_value == 0 || ... MLD_ERR_SIGN_ATTEMPTS_EXHAUSTED ...)`, output untouched on error); there is no FIPS 204
  functional postcondition on KeyGen/Sign/Verify. Some low-level contracts are functional (e.g. `mld_poly_add`
  `ensures r[k] == old(r)[k] + b[k]`).
- **HOL Light + s2n-bignum (assembly, object-code level).** `proofs/hol_light/README.md`: "for each assembly routine listed
  below, we prove three properties: 1. Functional correctness ... 2. Memory safety ... 3. Secret-independent timing", and
  "Proofs are 'post-hoc' in the sense that HOL-Light/s2n-bignum operate on the final object code". Exceptions: `rej_uniform`
  (public matrix sampler) is deliberately not constant-time; `rej_uniform_eta{2,4}` are constant-time relative to a public
  reject pattern. Routines covered: AArch64 (NTT, inverse NTT, poly_caddq, poly_chknorm, use_hint, decompose, polyz_unpack,
  pointwise and accumulate, three rejection samplers, five Keccak-f1600 variants), x86_64 AVX2 (the same arithmetic set,
  nttunpack, three rejection samplers, Keccak-f1600 x4), and RV32IM (NTT, inverse NTT, pointwise multiply). The
  specifications are per-routine (e.g. "`mldsa_ntt` computes the ML-DSA forward NTT modulo q"), not whole-algorithm.
- **Isabelle/HOL.** Barrett-division proofs for `Decompose` and a Neon NTT modular-arithmetic formalization; the README calls
  the scalar-decomposition work "still experimental" and not operating on source level.
- **Honest summary.** Memory/type safety for all C; functional correctness plus constant time for leaf assembly routines; no
  proof relating KeyGen/Sign/Verify to FIPS 204. Their `SOUNDNESS.md` documents scope and shared TCB with mlkem-native and
  s2n-bignum. An advantage over us: the assembly proofs are at the object-code level, so the compiler is not in the TCB for
  those routines, and timing is proved in the s2n-bignum model.
- **AWS-LC.** `crypto/fipsmodule/ml_dsa/` is imported from mldsa-native, and "At present, importer.sh imports only the
  C-only version" (no native backends), so AWS-LC inherits the CBMC proofs of the C code but not the HOL Light assembly
  proofs. `aws-lc-verification` says ML-DSA "proof artefacts ... lie alongside the code in the mldsa-native repository";
  I found no ML-DSA SAW proof there. A 2026 talk on AWS-LC formal verification is about ML-KEM.
- **liboqs.** Its ML-DSA documentation lists mldsa-native as the source; it makes no verification claim of its own.
- Sources: https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/README.md ;
  https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/proofs/hol_light/README.md ;
  https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/SOUNDNESS.md ;
  https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/mldsa/src/sign.h ;
  https://github.com/pq-code-package/mldsa-native/blob/fe47bf8afdb548224f32e7ef04fe580188f2d972/proofs/isabelle/README.md ;
  https://github.com/aws/aws-lc/blob/main/crypto/fipsmodule/ml_dsa/README.md ;
  https://github.com/awslabs/aws-lc-verification/blob/main/README.md ;
  https://github.com/open-quantum-safe/liboqs/blob/main/docs/algorithms/sig/ml_dsa.md

### 3.6 Formosa Crypto (Jasmin + EasyCrypt)

- **`formosa-mldsa`** (Jasmin ML-DSA, x86-64 ref and AVX2, ARMv7M ref and low-RAM): its README states the code "has **not been
  formally verified or proven** with respect to: Memory safety, Constant-time behavior, Speculative constant-time behavior,
  Functional correctness" and "MUST NOT be used in production". `libjade`'s README lists Dilithium only inside an HTML
  comment; its `proof/crypto_sign/dilithium/*` directories contain only `.gitkeep` files.
- **`formosa-mldsa-correctness`** (no README; created 2025-09-08, last commit 2026-06-18): EasyCrypt proofs about the
  `jasmin2ec` extraction of the **ML-DSA-65 AVX2** code (`submodules/formosa-mldsa`). Top-level statements exist:
  `ml_dsa_65_keygen_correct` (`MLDSA(...).keygen_derand ~ M.ml_dsa_65_keygen`), `ml_dsa_65_sign_correct`
  (`sign_derand ~ ml_dsa_65_sign`, with `kappa_max` and ctx-length premises) and `ml_dsa_65_verify_correct`, against an
  EasyCrypt ML-DSA spec in `proofs/specs/MLDSA.ec`. But `grep admit` finds **67 lines across 17 files**, e.g. `poly add/sub`,
  `ntt`/`invert ntt`, `montgomery multiply`, `decompose`, `use hint`, `make hint`, `power2round`, `sample challenge`,
  matrix-A / error-vector / mask sampling, and several bridge lemmas in `specs/`. **Stated, admitted**; the repository itself
  makes no completeness claim. ML-DSA-65 only; x86-64 AVX2 only.
- **Security.** Nothing for FIPS 204 in these repositories. Formosa's only ML-DSA-family security mechanization I found is the
  Dilithium ROM proof in 3.7.
- **Advantage if completed:** Jasmin has a certified compiler (Rocq), and Formosa's workflow also covers constant time.
- Sources: https://github.com/formosa-crypto/formosa-mldsa ;
  https://github.com/formosa-crypto/formosa-mldsa-correctness/tree/2dc59703c38bb29bb3f6e3a765f0a9934e143263/proofs ;
  https://github.com/formosa-crypto/libjade/blob/main/README.md

### 3.7 Security-proof side (no implementation)

- **EasyCrypt, Dilithium in the ROM** (ePrint 2023/246; CRYPTO 2023, Barbosa et al.): finds and fixes a gap in the CMA-to-NMA
  reduction for Fiat-Shamir with aborts and gives "a fully mechanized ROM proof for the CMA-security of Dilithium in the
  EasyCrypt proof assistant". Round-3 Dilithium, ROM only, abstract scheme; no implementation. Artifact:
  https://github.com/formosa-crypto/dilithium . (A QROM mechanization is not claimed.)
- **VCVio** (Lean 4, `LatticeCrypto/MLDSA`): FIPS-style definitions (`Signature.lean`: `fipsKeyGen`, `fipsSign`,
  `fipsVerify`), a `Concrete` NTT/rounding/encoding layer, ACVP test vectors, and an FFI to mldsa-native used for differential
  tests. **Proved** (0 `sorry` in `Signature.lean`, `SecurityHVZK.lean`, `SecurityNMA.lean`): spec-level
  `fipsSign_fipsVerify_correct` under `Primitives.Laws` hypotheses, HVZK, and the NMA to SelfTargetMSIS extraction.
  **Not proved:** `euf_cma_security` and both reductions are `sorry`; the file says "**WARNING: this is a placeholder
  statement with no security content.**" and "The proof is intentionally deferred." No implementation is verified against
  the Lean spec. (Our STATUS.md already records a component differential against VCVio.)
  https://github.com/Verified-zkEVM/VCVio/blob/aae1c9cbd6c00311091d691b74f2d0032d76d9bd/LatticeCrypto/MLDSA/Security.lean ;
  https://github.com/Verified-zkEVM/VCVio/blob/aae1c9cbd6c00311091d691b74f2d0032d76d9bd/LatticeCrypto/MLDSA/Signature.lean
- **Galois `cryptol-specs`**: an executable Cryptol FIPS 204 spec (ML-DSA-44/65/87) that "prioritizes readability and obvious
  correctness over efficiency", tested with ACVP and other KATs and Cryptol properties. A spec, not an implementation proof.
  https://github.com/GaloisInc/cryptol-specs/blob/master/Primitive/Asymmetric/Signature/ML_DSA/README.md
- I found no machine-checked security proof of FIPS 204 ML-DSA proper (QROM or ROM) in any source above. Self-published
  "ML-ADSA" and similar sites claim EasyCrypt/Coq proofs for modified schemes; I did not rely on them.

### 3.8 Tested only, or no ML-DSA proof found

| Project | Evidence |
|---|---|
| Go `crypto/mldsa` (stdlib) | Implementation and ACVP-style tests in the tree, no verification claim. https://github.com/golang/go/tree/master/src/crypto/internal/fips140/mldsa |
| RustCrypto `ml-dsa` | "The implementation contained in this crate has never been independently audited!" https://github.com/RustCrypto/signatures/blob/master/ml-dsa/README.md (tests only; we use it as a differential oracle) |
| PQClean | Retired; points to mldsa-native; "No branching on secret data (dynamically checked using valgrind)"; says only that code is a "suitable target" for verification. https://github.com/PQClean/PQClean |
| BoringSSL, OpenSSL | Testing (Wycheproof etc.); I found no verification claim. OpenSSL's design doc says its base is derived from BoringSSL's C++. |
| Bouncy Castle | **Not checked** beyond a failed search for a claim. |
| HACL* / hacl-packages, fiat-crypto | No ML-DSA implementation or proof found in web searches (the HACL* tree itself was not inspected). |
| CryptoLine | Web searches found NTT-multiplication proofs for Kyber/SABER/NTRU only; no ML-DSA proof found (a 2025 TCHES paper on NTT analysis was not read). |
| Galois SAW for AWS-LC | The AWS-LC SAW repo covers other algorithms; no ML-DSA proof found. (Apple uses SAW, see 3.1.) |

## 4. Comparison table

"E2E FC" = functional correctness of the implementation's KeyGen/Sign/Verify against a mechanized FIPS 204 spec, covering the
whole implementation, not leaves. All cells are about ML-DSA only.

| Project | Tool | Scope (code) | E2E FC? | Memory / panic safety | Constant time | Optimized backends | Security proof | Trusted base (main items) |
|---|---|---|---|---|---|---|---|---|
| **This project** | Charon/Aeneas to Lean 4 | Rust `no_std`, public `api` for 44/65/87 (portable code only) | **proved**: KeyGen, Sign, Verify = FIPS-literal Lean spec (all message/ctx lengths, all pk/sk/sig byte strings), plus Verify(Sign) = true; premises: `RejTerm` (sampler termination), Sign's kappa budget, parameter facts | Panic freedom: Aeneas `step` specs for the extracted `api` functions (inferred from the spec style; STATUS.md does not use the words); Rust type safety | **tested** (BINSEC probes on x86_64, thumbv7em, riscv32, 6 unknown), not proved | None | None | Spec fidelity (reviews, ACVP, Wycheproof, VCVio differential), Charon/Aeneas, rustc/LLVM, Lean kernel; zeroize and anything above `api` outside proof |
| Apple corecrypto | SAW/Cryptol, Isabelle, AutoCorres2 | Production C + ARM64 asm; 44/65/87 | **proved, bounded**: entry points refine Isabelle FIPS 204; Sign/Verify checked at specific message/ctx sizes; no Verify(Sign) theorem found | SAW checks (with caveats) | not formally verified (DIT, review, testing) | ARM64 asm proved equivalent to C | None | Isabelle, SAW + SMT solvers, Clang, hand-kept SAW contracts, uninterpreted RNG, manual termination arguments |
| SymCrypt Rust (experimental) | Aeneas/Lean | Rust (portable + SHAKE x4 AVX2) | **claimed** (paper); code not public | **claimed** (safety, panic-freedom) | not claimed ("defensive constant-time style") | AVX2 4-way SHAKE for sampling (claimed) | None | per the SymCrypt list: rustc, Charon/Aeneas, Lean kernel, intrinsic models |
| ocaml-pq | Lean 4 + Mathlib, TLA+ | OCaml `mldsa_engine.ml`; 44/65/87 | **proved** against models: KeyGen, Sign, Verify, sign_verify; sign loop bounded at 821 | bounds / no-overflow lemmas on the models | not claimed | None | None | **hand-transcribed** OCaml models, OCaml semantics/compiler, FIPS transcription, Lean kernel |
| libcrux-ml-dsa | hax to F* | Rust; portable + AVX2 (NEON not in proof set) | **No** (leaf modules only; top level admitted) | partial: verified modules, some lax/panic_free | enforced by types, **not** proved for binaries | portable, AVX2, NEON | None | hax, F*, Z3, rustc; CI shows only `prove --admit` |
| mldsa-native (and AWS-LC) | CBMC, HOL Light + s2n-bignum, Isabelle | C; AArch64, x86_64 AVX2, RV32IM asm | **No** (no FIPS-level theorem; leaf asm routines proved) | CBMC: UB-freedom for C; HOL Light: memory safety for asm | proved for asm routines (s2n-bignum model); C hardened/tested | AArch64, x86_64, RV32IM (AWS-LC: C only) | None | CBMC, HOL Light, ISA models, C compiler for the C frontend |
| Formosa `formosa-mldsa-correctness` | EasyCrypt, Jasmin | Jasmin ML-DSA-65 AVX2 | **stated, admitted** (67 admit lines) | not stated | not stated | AVX2 only | None | EasyCrypt, Jasmin extraction; certified Jasmin compiler |
| VCVio | Lean 4 | Lean spec + concrete models (no verified implementation) | n/a (spec-level correctness proved) | n/a | n/a | n/a | **stated, admitted** (`euf_cma_security` is `sorry`; HVZK/NMA pieces proved) | Lean kernel |
| EasyCrypt Dilithium (2023/246) | EasyCrypt | Abstract round-3 scheme | n/a | n/a | n/a | n/a | **proved**, ROM, not FIPS 204 | EasyCrypt |
| Go, RustCrypto, PQClean, BoringSSL, OpenSSL, liboqs | none | implementations | tested only | tested/fuzzed | valgrind or review | various | None | n/a |

## 5. Is our end-to-end claim unique?

### 5.1 Property by property

| Ingredient of our claim | Apple | SymCrypt (paper) | ocaml-pq | Formosa WIP | libcrux | mldsa-native |
|---|---|---|---|---|---|---|
| (a) Whole implementation, KeyGen + Sign + Verify, vs a mechanized FIPS 204 spec | yes (bounded sizes) | claimed | yes (against hand models) | stated, admitted | no | no |
| (b) Code-to-model link is mechanical (extraction or SAW), not hand transcription | yes (SAW + translator) | claimed (Aeneas) | **no** | yes (jasmin2ec) | n/a | n/a |
| (c) Rust implementation | no (C/ARM64) | claimed | no (OCaml) | no (Jasmin) | yes (partial) | no (C) |
| (d) All three parameter sets | yes | not stated | yes | no (65 only) | n/a | n/a |
| (e) Every message / context length, every key / signature byte string | **no** (specific sizes; valid sk) | not stated | not stated (bounded loop) | not stated | n/a | n/a |
| (f) Verify(Sign) = true proved | not found | not stated | yes (`sign_verify`) | no | no | no |
| (g) Artifact public and re-checkable by outsiders | partly (license, macOS, 20+ h) | **no** (ML-DSA not released) | yes | partly (admits) | n/a | n/a |
| (h) Proofs depend only on standard Lean axioms | n/a (Isabelle, SMT) | not stated | yes (audit file) | n/a | n/a | n/a |

Our row: (a) yes, (b) yes (Charon/Aeneas, trusted), (c) yes, (d) yes, (e) yes subject to `RejTerm` and the kappa budget,
(f) yes, (g) yes, (h) yes.

Notes on rows I could not fully pin down: for ocaml-pq, (e) holds only for "every input the code can receive" modulo sampler
termination; its theorems are parametric in the parameter set and quantified over inputs, but I did not read them closely
enough to rule out hidden range hypotheses beyond the ones its README lists. For SymCrypt, a version of (a) to (f) may well
hold; the paper just does not say.

### 5.2 What we cannot claim

- That nobody else has proved end-to-end functional correctness of a whole ML-DSA implementation. Apple's and ocaml-pq's
  artifacts are public and say they do, within the stated bounds; SymCrypt claims it for Rust with the same toolchain.
- That we are first. Apple released in May 2026 and ocaml-pq in September 2026; the SymCrypt paper is dated 14 September 2026.
  I do not know our own public release date relative to these; only claim "first" if that can be shown.
- That our result covers things the others do better: Apple (production C, ARM64 refinement, shipped hardware), mldsa-native
  (assembly proofs at object-code level including timing), libcrux (verified AVX2 leaves).
- Anything about constant time, compilers, or hardware beyond what STATUS.md says.

### 5.3 Wording we could defensibly use

Short form:

> KeyGen, Sign and Verify (FIPS 204 Algorithms 1-3, via 6-8) of this Rust ML-DSA are proved in Lean 4, for ML-DSA-44/65/87
> and for every message and context length, to compute exactly a FIPS-literal Lean transcription of the standard, and
> Verify(Sign) = true is proved for honestly generated keys. The Lean model of the Rust code is extracted mechanically by
> Charon/Aeneas. The theorems depend only on standard Lean axioms plus two named probabilistic premises (the rejection
> samplers return on the seeds used, and Sign's kappa budget).

Comparative form (only with a date and "to our knowledge"):

> To our knowledge, as of 2026-10-30 this is the only publicly released proof that combines (i) a Rust implementation,
> (ii) an implementation model extracted mechanically from its source, (iii) end-to-end theorems for KeyGen, Sign and Verify
> against a FIPS 204 transcription for all three parameter sets and all message lengths, and (iv) Verify(Sign) = true.
> Related work with overlapping goals: Apple corecrypto (C/ARM64, Isabelle/SAW, bounded message sizes), SymCrypt's
> experimental Rust ML-DSA (Aeneas/Lean, not released), and ocaml-pq (Lean, hand-written models).

The comparative form is a conjunction of four ingredients. If any one is dropped, another project matches the remainder, so
keep all four. Re-check it if SymCrypt releases its ML-DSA artifacts.

Always attach, near any such claim: the two premises (`RejTerm`, kappa budget), "FIPS-literal Lean transcription written by
us (reviewed and cross-checked, not itself proved to equal the standard)", "portable Rust only", "constant time is tested
(BINSEC), not proved", and "zeroize wipes and stack use are outside the proof".

### 5.4 Wording we must not use

- "First", "the only", or "the only end-to-end" formally verified ML-DSA, or any unqualified uniqueness claim.
- "Fully verified", "unconditional", "for all inputs" without the `RejTerm`/kappa premises and the sampler-fuel gap in
  `STATUS.md`.
- "Verified against FIPS 204" without "our transcription of"; the standard itself is not mechanized by NIST.
- "Constant-time verified/proved", "side-channel safe".
- "Production-ready", "audited", or any claim about the compiler, hardware, or the Charon/Aeneas translation being verified.
- Statements that libcrux, mldsa-native or AWS-LC are "unverified" or "not really verified". They prove real things at
  the leaf level (and mldsa-native proves timing for assembly); say "component-level" instead.
- Any claim about what SymCrypt's unreleased ML-DSA proofs do or do not cover.

## 6. Could not verify

- **hax paper full text** (ePrint 2025/142): the PDF returned HTTP 403; I only saw the abstract, which does not mention ML-DSA.
- **SymCrypt ML-DSA**: no code, spec or theorem statements are public; everything comes from the arXiv text.
- **Re-running any competitor's proofs** (Apple's SAW + Isabelle, ocaml-pq's `check.sh`, libcrux's F*, mldsa-native's CBMC
  and HOL Light, Formosa's EasyCrypt, VCVio). Statements are read, not rebuilt. For ocaml-pq I did only grep-level checks
  (`sorry`, `axiom`, `native_decide`).
- **Apple**: the verify-side message sizes; whether the `44` scripts match the `65`/`87` ones; the third-party audit report
  of the Isabelle FIPS transcription.
- **libcrux**: whether the F* proofs pass today (CI runs `--admit` only); which functions the CHANGELOG fixes touch relative
  to the proof set; the `Makefile.base` semantics of `ADMIT_MODULES` beyond the naming.
- **Formosa**: whether the admitted lemmas are all on the dependency path of the three top-level lemmas (very likely, since
  they cover NTT, samplers and rounding, but I did not trace it).
- **AWS-LC**: its pinned mldsa-native commit and whether its CI runs the CBMC proofs on the imported copy.
- **Bouncy Castle**, wolfSSL, leancrypto and other C libraries: no search beyond a failed claim lookup.
- **Spec validation of every competitor's spec** beyond what they state (ACVP and KATs for Cryptol specs and Go; audit claims
  for Apple).
- Whether any other group has unreleased work (for example the Formosa team's draft paper, or additional SymCrypt algorithms).
- Our own statements are from `STATUS.md` and have not been re-run for this survey.
