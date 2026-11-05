# Assurance case for reviewers

What `ml-dsa-lean` establishes about its public `api`, under which assumptions, what it does not cover, and how to
reproduce each piece of evidence. Every statement cites a Lean source, a script, a test or a checked-in result. Nothing
here is a FIPS validation or certification: ACVP vectors are test vectors, not a CMVP validation, and the crate has
neither. The crate is unaudited by third parties.

**Vocabulary.** "Proved" means a Lean theorem that passes the axiom gate (`scripts/check-axioms.sh`: only `propext`,
`Classical.choice`, `Quot.sound`; no `sorry`). "Checked" means a tool or test run found no counterexample on the
inputs it covered. "Spec" is `lean/Spec`, our transcription of FIPS 204 (Algorithms 1–3 and 6–48) and FIPS 202
(SHAKE). "Rust" is the code extracted by Charon/Aeneas into `lean/Impl` and modeled there (`RustM` = `ok`, `fail` or
`div`).

## 0. Gates and pins

The Lean gates last passed at 47bd3dc (the proof-hygiene pass; `lean-check.sh` and `witness-check.sh` each run twice,
by the author and by a separate review pass, which also confirmed that every headline and witness statement and every
extracted definition elaborates byte-identically to the previous gated tree). `scripts/ci.sh` and the extraction check last
passed at 9d51b57 (after the Lake package rename to `MlDsaLean`; extraction byte-identical to the committed `lean/Impl`);
`src/` and `lean/Impl` are unchanged since, and the later commits touch only docs, comments, `lean/Proofs`, the witness and
Wycheproof generator scripts, one echo string in `scripts/ci.sh`, `SECURITY.md` and `.github/`:

| Gate | Result |
|---|---|
| `scripts/lean-check.sh` | `LEAN CHECK OK`, 770 declarations (pipefail `lake build` exits 0, no `error:` or `sorry` in the log, axiom gate over every extracted def and every name in `lean/headline-theorems.txt`; axioms used: `propext`, `Classical.choice`, `Quot.sound`) |
| `scripts/witness-check.sh` | `WITNESS CHECK OK: Proofs.TopWitnessCorrect`, 146 names |
| `scripts/ci.sh` | 17 of 17 steps passed |

A module counts as proved only after `lean-check.sh` passes. Exact steps to rerun everything are in
[reproduce.md](reproduce.md).

Pins and decisions:

| Item | Choice | Why |
|---|---|---|
| Crate | `ml-dsa-lean` (`ml_dsa_lean`), `no_std`, no core dependencies; MSRV 1.86 | extraction closure = this crate + `core` |
| Lean layout | Lake package `MlDsaLean` in `lean/`: extracted code `lean/Impl/` (Aeneas namespace `Impl`), spec `lean/Spec/`, proofs `lean/Proofs/` | names are fixed so proofs don't churn |
| M′ | `sign_internal(p, sk, m_prefix, m, rnd, sig)` and `verify_internal(p, pk, m_prefix, m, sig)`, with M′ = `m_prefix ‖ m` absorbed in two calls | the external API builds 0 ‖ \|ctx\| ‖ ctx (≤ 257 bytes) on the stack, no alloc; the proof needs one sponge lemma (absorbing two slices = absorbing their concatenation) |
| Charon | generic (no `--monomorphize`) | 0 external axioms; `--monomorphize` adds 9 unmodeled index axioms |
| Extraction toolchain | Charon nightly-2026.09.02, Aeneas build-183e4f0, Rust nightly-2026-08-18, Lean v4.31.0 | pinned in `scripts/setup-tools.sh` and `lean/lean-toolchain` |
| Extraction gate | Aeneas exit 0, no `[Error]`/`[Warning]`, no local opaque function, no referenced external axiom, every extracted def on standard axioms only | any failure is fixed in the Rust code, not worked around |
| Out of scope | HashML-DSA (Algorithms 4/5) and external μ | no differential oracle for the first; the second is an allowed variant of Algorithms 7/8 that would need its own spec entry and theorems (deferred, not ruled out) |

## 1. What is proved

### 1.1 The `*_exact` theorems: the API against the Lean transcription of the unbounded FIPS 204 algorithms, no premises

For each parameter set NN ∈ {44, 65, 87} and every value of the API argument types:

| Rust function | Theorem (Lean file) |
|---|---|
| `api.verify_NN`, `api.verify_internal_NN` | `verify_NN_exact`, `verify_internal_NN_exact` (`Proofs/PartialAPI.lean`) |
| `api.keygen_NN` | `keygen_NN_exact` (`Proofs/PartialKeyGen.lean`) |
| `api.sign_NN`, `api.sign_internal_NN` | `sign_NN_exact`, `sign_internal_NN_exact` (`Proofs/PartialSign.lean`) |
| `api.pk_from_sk_NN` | `pk_from_sk_NN_exact` (`Proofs/PkFromSk.lean`) |

In words, for Verify: (a) the Rust never returns `fail`, i.e. no panic, arithmetic overflow or out-of-bounds access in
the Aeneas model (stack exhaustion and out-of-memory are not modeled, and the Rust can diverge, `div`, exactly when the
spec returns no result at any fuel, 1.2); (b) if it returns `ok b`, then `Spec.Verify … F = some b` for some fuel `F`; (c) if `Spec.Verify … F =
some b` at any fuel, it returns `ok b`. The verdict is therefore unique across fuels, and the statement holds for every
`pk`, `m`, `ctx` and `σ` of the API types (a wrong length cannot occur: the API takes fixed-size arrays; `verify_internal`
also returns false on any slice length that is not `pk_len`/`sig_len`). KeyGen has the same shape with `(pk, sk)`. For Sign,
(b) and (c) hold with `some σ`, and `api.sign_NN … = ok none` exactly when |ctx| > 255 or the spec's `Exhausted` holds at some
fuel (all `kappaBudget` attempts rejected). The Rust's cap κ + ℓ ≤ 2¹⁶ is the same as `kappaBudget`; it is an implementation
bound FIPS 204 allows (κ is encoded in 16 bits by ExpandMask).

"Fuel" is how the spec makes the FIPS rejection-sampling loops (ExpandA, ExpandS, SampleInBall) total: the spec
returns `none` if a loop runs out of fuel; the Rust loops are unbounded. The older theorems that were stated with premises
(`keygen_internal_spec`, `sign_internal_spec_some`, `verify_internal_spec`, …) still exist and carry them:

- `RejTerm`: the rejection samplers receive enough accepted samples from SHAKE (probabilistic, not provable). Concretely, the
  theorem takes "the spec returns `some` at fuel F" as the hypothesis.
- The κ budget: Sign is compared with `Sign_internal_bounded B`, B = ⌊(2¹⁶ − ℓ)/ℓ⌋ + 1.
- `Params.Std` = `Params.Valid` ∧ `StdParams` (d = 13, γ1/γ2/η of the standard sets, τ ≤ 64, k + ℓ < 256, k ≤ 8, ℓ ≥ 1,
  ω ≤ 255, …), kernel-checked for ML-DSA-44/65/87 (`ML_DSA_NN_std`).

### 1.2 `Divergence.lean`: when the Rust does not terminate

`Proofs/Divergence.lean` (`rustM_div_iff`, `verify_NN_div_iff`, `keygen_NN_div_iff`, `sign_NN_div_iff`,
`pk_from_sk_NN_div_iff`, and the prepared-key analogues): the Rust returns `div` exactly when the spec returns no
result at any fuel, i.e. when FIPS 204's unbounded ExpandA or SampleInBall would never terminate on that input. This
is not a termination proof; termination is probabilistic. Sign's κ loop is bounded, so Sign diverges only through a
sampler. The generic loop lemmas are proved by fixpoint induction in `Proofs/Partial.lean`.

### 1.3 Correctness for honest keys

`Proofs/Correctness.lean`: `correct_internal` and `correct_external` at spec level, and `correct_44`, `correct_65`,
`correct_87` for the Rust: `api.keygen_NN` then `api.sign_NN` then `api.verify_NN` returns true. Premises: `StdParams`,
and that KeyGen and Sign return `some` at the same fuel (`RejTerm`, the κ budget). Building blocks: NTT algebra and
convolution, ‖c·s‖∞ ≤ β, Power2Round/HighBits/UseHint lemmas, codec round trips, SampleInBall weight = τ.

### 1.4 Prepared keys

`Proofs/PreparedVerify.lean` and `PreparedSign.lean`: `verify_prepared_NN_eq`, `verify_internal_prepared_NN_eq`,
`sign_prepared_NN_eq`, `sign_internal_prepared_NN_eq` say that for a key object returned by `verifying_key_NN pk` or
`signing_key_NN sk`, the prepared call equals the one-shot call as a computation (including `fail` and divergence);
`*_exact` versions against the spec exist too. `verifying_key_NN` and `signing_key_NN` never fail and diverge only where
ExpandA does (`Divergence.lean`, `verifying_key_NN_div_iff`). The key structs have private fields and are only built by
those constructors, so the hypothesis `verifying_key_NN pk = ok vk` covers every key a caller can hold. The `Drop` wipe of a
prepared signing key is not in the model.

### 1.5 `SkWellFormed` and `PkFromSk` (optional checks, not FIPS steps)

`Proofs/SkWellFormed.lean` (`skWellFormedAPI_spec`, `skWellFormed_keygen`): `sk_is_well_formed_NN` returns whether every
s1/s2 coefficient that skDecode yields lies in [−η, η]; keys from KeyGen pass. `Proofs/PkFromSk.lean`
(`pk_from_sk_NN_exact`, `skConsistent_keygen`, `skConsistent_sound`): `pk_from_sk_NN` returns `Some pk` iff the range
check passes and recomputing KeyGen steps 5–9 reproduces the stored t0 and tr (K is a free seed, unchecked). `sign_NN`
follows FIPS 204 Algorithm 25 literally and does not call either (E-4 below). `pk_from_sk_NN` agrees with
mldsa-native's `pk_from_sk` on 14 variants per set.

### 1.6 Proof inventory

Each row is a `@[step]` refinement spec of an extracted function against its `lean/Spec` algorithm, under the
representation relations of `Proofs/Repr.lean`.

| Module | What is proved | Extra hypotheses |
|---|---|---|
| `Field`, `Repr` | field ops, masks, infinity norm vs ‖·‖∞, `Params.Valid` for 44/65/87 | canonical inputs |
| `NTT*` | NTT, NTT⁻¹ (Alg 41/42); zeta table by `decide +kernel` | canonical inputs |
| `NTTOps`, `Coeff` | Alg 44–48, vector NTT, CoeffFromThreeBytes/HalfByte (Alg 14/15) | η ∈ {2, 4} |
| `Rounding*` | Power2Round, Decompose, HighBits, LowBits, MakeHint, UseHint (Alg 35–40) and polynomial maps | γ2 ∈ {95232, 261888} |
| `Encode*` | bit accumulator = SimpleBitPack/BitPack and unpack (Alg 16–19), w1Encode, pk/sk encode/decode (Alg 22–25); decoders for every byte string of the right length | coefficient ranges for the encoders |
| `Hint` | HintBitUnpack for every byte string incl. all ⊥ cases; HintBitPack (Alg 20/21) | weight ≤ ω for packing |
| `Keccak*` | Keccak-f[1600]; SHAKE128/256 absorb, finalize, squeeze vs `Spec.SHAKE*`; absorbing a then b = absorbing a ‖ b | none |
| `SampleA`, `SampleS`, `SampleBall`, `ExpandMask` | RejNTTPoly, ExpandA (Alg 30/32), RejBoundedPoly, ExpandS (Alg 31/33), SampleInBall (Alg 29), ExpandMask (Alg 34) | `RejTerm`; η ∈ {2, 4}; τ ≤ 64; κ + ℓ ≤ 2¹⁶ |
| `SigCodec`, `Steps`, `Bridge` | sigDecode for every byte string of length sigLen, sigEncode; Sign steps 18–21 and 25–26, KeyGen t and Power2Round, Verify t1·2^d and c̃ compare, API ctx prefix; Z_q norm bridges | γ1 ∈ {2¹⁷, 2¹⁹}, γ2, d = 13 |
| `KeyGen`, `Verify`, `Sign` | KeyGen_internal (Alg 6), Verify_internal (Alg 8), Sign_internal (Alg 7, bounded) against the spec | `Params.Std`, `RejTerm`; unconditional versions in `PartialKeyGen`, `PartialAPI`, `PartialSign` |
| `API`, `APIInternal` | Public API (Alg 1/2/3) and internal API for 44/65/87, and the "only if" for `none` | the spec returns `some` (or `Exhausted`) |
| `Witnesses`, `SampleBallWitness`, `TopWitness*` | kernel witnesses for the premises (below) | none |

Internal reviews covered the leaf proofs, the three internal top theorems, the API theorems, the `verify_internal` length guard
and the Sign exhaustion change, and the optional-check proofs: no blockers, findings folded in. These reviews were separate review
passes within this project, not third-party reviews.

### 1.7 Witnesses for the premises

- Parameter premises (`Params.Std`): kernel-checked for 44/65/87.
- Sampler premises at the leaves: kernel witnesses on zero seeds (RejNTTPoly and ExpandA for 44, RejBoundedPoly and ExpandS for
  44 and 65, SampleInBall for 44).
- Top-level `some` premises: for ML-DSA-44 with ξ = 0..31, rnd = 0³², M = [0], ctx = [] and the default fuel, all hypotheses of
  `correct_44` hold on a kernel-checked instance: `Spec.KeyGen` returns a key pair, `Spec.Sign` returns `some` (the first attempt
  is accepted), and `Spec.Verify` returns `some true`. `Proofs.TopWitnessCorrect.correct_44_nonvacuous` bundles these with the
  Rust chain `api.keygen_44` → `api.sign_44` → `api.verify_44 = ok true`. Kernel evaluation runs on list-based equivalents of
  BytesToBits, the bit packers and the Array loops, each proved equal to the spec for all inputs (`TopWitnessFast`); the
  literals come from a native generator and each is re-derived by `decide +kernel`. Checked by `scripts/witness-check.sh` (146
  names, standard axioms), outside the default build: about 47 min cold and about 46 GB peak across modules (about 24 GB for the
  largest declaration). One parameter set and one input only.
- `Exhausted` (Sign's `false` case, all κ attempts rejected): satisfiable only by a counting argument; no witness, probability
  about 2^-thousands per input, untestable in practice.

### 1.8 Cross-check of the spec: `xspec`

The Rust theorems are only as good as the spec. `xspec/` is a separate Lean v4.34 project that vendors `lean/Spec`
byte-identically and proves it equal to ocaml-pq's independent Lean transcription (standard axioms only; 144 headline
names in `xspec/headline-theorems.txt`, 142 equivalence theorems and 2 kernel known-answer tests; gate
`scripts/xspec/check-axioms.sh`; details in `xspec/README.md`). Top level, both directions, all three parameter sets, with
these scope qualifiers:

- **KeyGen**: equivalence of the public key and secret key.
- **Verify**: the Boolean verdict (accept and reject), for a right-length pk and σ.
- **Sign** (`Sign_internal` and `Sign`): on the key our `skDecode` produces, composed with their `decodeSk` where it
  accepts.
- **Sign loop bound**: their Sign loop stops after 821 attempts (a probability argument, not a proved bound), ours
  after the κ budget. If ours returns σ at attempt a, theirs returns the same σ iff a < 821 and none otherwise.
- **Key import**: their import also rejects keys with inconsistent tr/t0, which FIPS 204 and our spec accept.
- **Samplers**: the theirs-to-ours directions assume their rejection samplers terminate on the given input (they
  return a default otherwise); the ours-to-theirs theorems derive those premises whenever ours returns.
- Not compared: the default fuel when ours returns `none`.

**Keccak** is cross-checked: our Keccak-f[1600] and SHAKE128/256 are proved equal to ocaml-pq's independent FIPS 202
transcription (bit strings, every input and output length, round by round) and to its `Mldsa_keccak` model, and
KeyGen, Verify and Sign are restated on ocaml-pq's own SHAKE (`*_ocaml`). Limits: two reject-case Verify lemmas that
hold for any XOF are not restated, and the `keyGen_*_ocaml` premises still name a seed computed with our H. The check
is only as independent as ocaml-pq's FIPS 202 transcription is of ours; its anchor is their published-digest proofs. The
two kernel known-answer tests (empty message) are tests, not an equivalence.

This is a proof about specs, not about the Rust. Other fidelity evidence for the spec: ACVP (`spec-acvp` 63/63 in Lean; the
Rust runs ACVP keyGen 75/75, sigGen 60/60 and sigVer 30/30 of the vendored 120 and 60 cases, with the preHash and external-μ
cases skipped), Wycheproof (below), a component differential against VCVio (1,345,635
in-precondition cases, 0 mismatches, plus a FIPS-literal Python reference; the only difference is HintBitPack with more than ω
ones, which is outside Algorithm 20's precondition and handled differently by the two sides), and three spec reviews against the FIPS PDFs (every
`lean/Spec` def checked step by step; whole-domain rounding check against a FIPS-literal Python reference; SHAKE vs hashlib
around the rate; no transcription errors). Those reviews were internal and the notes of the third are not committed. **No
third-party audit and no CMVP or other validation of this crate or its spec exists.**

## 2. What each result assumes: the trusted base

1. **Spec fidelity** of `lean/Spec` against FIPS 204/202. Evidence is the list in 1.8 (internal reviews, test vectors, and
   equivalence to other transcriptions); none of it is a proof that the spec is the standard.
2. **Charon/Aeneas translation** (pins in section 0). Extraction runs with `--cfg miri`, so the proved code is the source with
   the `cfg(miri)` variants: `field::opaque_u32` and the RISC-V `black_box` are the identity there, and the AVX2 dispatch is
   absent (CT-1, CT-2 below; `docs/object-code-assurance.md` §3.5). Evidence: the extracted code compiled and run against the
   native Rust on 345,360 cases (Keccak, field, NTT, rounding, samplers, codecs and the full public API incl. 225 ACVP-derived
   cases), 100% agreement; 4 injected bugs all detected (`scripts/impl-eval.sh`, `lean/SpecTests/ImplEval.lean`).
3. **rustc/LLVM** compile the source faithfully. The theorems are about source semantics, not object code. The compiled code
   differs from the proved code by the `black_box` barriers of item 2 (and, with the `avx2` feature, the dispatch); `black_box`
   is trusted to be the identity on values.
4. **The Lean kernel** with `propext`, `Classical.choice`, `Quot.sound`.

Zeroize, the opt-in AVX2 dispatch shim and anything above `api` are outside the proof.

## 3. What is NOT covered

See also section 7 (known limitations).

- **Stack exhaustion and out-of-memory are not modeled.** Worst-case stack was measured, not proved (release, statically and by
  stack painting, `tools/stack/`): Sign 116/168/240 KB, Verify 50/76/115 KB, KeyGen 64/98/143 KB for 44/65/87 on x86_64; other
  targets within 4%. Prepared keys: `verifying_key_*` 31/52/26, `signing_key_*` 60/99/164, `verify_prepared_*` 34/45/59,
  `sign_prepared_*` 73/101/134 KB, plus the 20.5–81 KB key object in the caller's frame (`tools/stack/README.md`).
- **Positive existence for most inputs.** The `_exact` theorems say the Rust never panics and agrees with the spec whenever
  either returns; that the spec returns `some` for a given input has a kernel witness only for the ML-DSA-44 instance in 1.7.
- **The opt-in `avx2` feature** (runtime CPUID dispatch, the crate's only `unsafe`: `forbid(unsafe_code)` without the feature,
  `deny` plus one `allow` on the shim with it) and **the `zeroize` feature** are outside the proof. The AVX2 copy of the NTT is
  covered by `tests/dispatch.rs`, the KAT suites run with the feature and a static scan, not by BINSEC
  (`docs/object-code-assurance.md` §3.5). `-C target-cpu=x86-64-v3` is 4–9% faster again with no `unsafe` and no dispatch, but
  the binary then requires AVX2 and BINSEC cannot lift its vector code either.
- **Crate-private internals** exposed by the `internals` feature (`verify_internal` with a `Params` inconsistent with its
  `K`/`L`; `sign_internal`/`keygen_internal` on wrong-length slices) can panic (E-1). Without the feature the public surface is
  `api` only and every `api` function has a theorem.
- **Out of scope by decision:** HashML-DSA (Algorithms 4/5) and external μ.
- **Randomness** is the caller's: `keygen_NN` takes ξ and `sign_NN` takes `rnd` (`src/api.rs` module docs).
- **Test harnesses** (ACVP, Wycheproof, differentials, fuzzers) were not themselves reviewed; their sensitivity was checked by
  planting bugs (below).

## 4. Constant-time evidence and its scope

Constant time is checked on compiled probes with BINSEC (relational symbolic execution), not proved in Lean.
"Secure" means BINSEC explored the compiled probe to completion and found no secret-dependent branch, memory address
or division operand for all secret values; the lifter, the solver and "instructions take operand-independent time" are
trusted (`docs/object-code-assurance.md` §3.2). Verify handles only public data; the property matters for KeyGen and Sign.

Full sweep at 15b4ce2 (November 4, 2026): 113 entrypoints per run (114 on riscv32imac and in the `dispatch` build) plus two whole-Sign censuses, on x86_64 (checkct profile,
`nearcore`, `avx2` dispatch, `nearcore-dispatch`, `nearcore-exact*`), thumbv7em, riscv32imac and AArch64 without NEON. BINSEC
checks compiled probes of every secret-touching step of KeyGen and Sign (listed in `checkct/README.md`): `sk_is_well_formed`,
the SHAKE paths with secret input, ExpandS, NTT, t, Power2Round, skEncode/Decode, the Sign steps, `prepare_sk`/`signing_key`,
plus positive controls. ExpandS is covered only through its per-nibble helper (`coeff_from_half_byte_eta{2,4}`); the sampler
loop itself (`rej_bounded_poly_eta{2,4}`) branches on its public accept/reject outcome, is an expected-insecure probe and has
no constant-time verdict. The whole KeyGen, Sign and `pk_from_sk` functions have no verdict (`sign::attempt` and `sign_internal`
are not probed whole), and the glue between steps is covered by code reading only. Counts
secure / expected insecure / unexpected insecure / unknown / no verdict (OOM), on the 87-probe basis (85 entrypoints and the
two censuses):

| target / profile | secure / expected insecure / unexpected insecure / unknown / OOM |
|---|---|
| x86_64 default | 80 / 6 / 0 / 0 / 1 |
| x86_64 `nearcore` | 80 / 7 / 0 / 0 / 0 |
| x86_64 `avx2` dispatch | 80 / 6 / 0 / 0 / 1 |
| x86_64 `nearcore-dispatch` (note 3) | 80 / 6 / 0 / 0 / 1 |
| thumbv7em (note 3) | 81 / 4 / 0 / 0 / 2 |
| riscv32imac (notes 1 and 3) | 78 / 6 / 0 / 2 / 1 |
| AArch64 without NEON (note 2) | 73 / 3 / 0 / 11 / 0 |
| x86_64 `nearcore-exact` (113 entrypoints + 2 censuses, not the 87-probe basis) | 61 / 3 / 0 / 51 / 0 |
| x86_64 `nearcore-exact-novec` (same flags, vectorizers off; 113 entrypoints + 2 censuses) | 108 / 7 / 0 / 0 / 0 |

1. The riscv32imac row counts `control_prepared_branch_44` as expected insecure from its 7200 s rerun alone (`JOBS=2`); in the
   sweep run it is `unknown`, and the sweep alone gives 78 / 5 / 0 / 3 / 1. The result depends on exploration order.
2. AArch64 has 13 `unknown` rows in all: the 11 above (on the 87-probe basis, two of them censuses) plus the two split pieces
   `split_prepare_sk_87_{7x1,col}`.
3. Not rerun at 15b4ce2: the thumbv7em and riscv32imac censuses and the `nearcore-dispatch` prepared census. Their cells are the
   results of the previous sweep (e9a1c74), whose `field.rs` differs from this one (`checkct/README.md`, "Not rerun, and why").

No unexpected leak. Details, the split-probe results and the stop-site evidence for every unknown are in `checkct/README.md`.
Three real leaks were found and fixed (CT-1, CT-2, CT-3 in section 6). Limits:

- **Whole-Sign** has no verdict: the censuses report only the public `sample_in_ball` accept branch, run out of memory
  (thumbv7em, riscv32imac, and the x86_64 default and `dispatch` prepared census at 120 GB), or are cut at the NTT under
  nearcore's exact build (the riscv32imac internal census is unresolved, with 4 pending paths at 7200 s). Sign is covered by its secret-touching pieces (`response_*`, `hint_step_*`, ExpandMask, hashing,
  `prepare_sk`, `signing_key`).
- **Unknowns** (no leak found, no conclusion): under nearcore's exact build (`nearcore-exact`) the NTT, `compute_t`,
  `prepare_sk`/`signing_key`, `hint_step`, `response` and the two censuses have no verdict, because BINSEC 0.11.3 cannot lift the
  VEX instructions (`vinsertps`, `vblendvps`, `vblendps` on `ymm`) that `+fma` (which implies AVX) lets LLVM emit; one more probe
  is a solver stall (T-9 in section 7). With the vectorizers off all 113 entrypoints get a verdict (108 secure, 5 expected insecure; 7 with the two censuses), which is
  evidence about a different binary, not about nearcore's. Elsewhere: two on riscv32imac (`vec_power2round_87`, one census), the
  three `split_vec_power2round_{5,6,7}` capacity probes there, three riscv32imac `split_prepare_sk` pieces (a solver stall at one
  store; the full-size probes they split are secure) and eleven on AArch64 (one stuck solver query each; thirteen `unknown` rows with the two `split_prepare_sk_87_{7x1,col}`
  pieces), partly covered by split probes.
- **The `nearcore-exact` CT profile is nearcore's exact release build for the crate in isolation** (`overflow-checks = true`,
  nearcore's x86_64 target features, Rust 1.95.0, read from nearcore cd5a94457). It is not nearcore's binary: callers, allocator,
  glibc `memcpy` and the prebuilt `core` differ (`checkct/README.md`, "What this does and does not show").
- **AVX2 and NEON code:** the AVX2 NTT copy is covered by a static scan only; AArch64 builds with NEON cannot be lifted, so macOS and Apple Silicon builds have no BINSEC coverage.
- **Other builds:** verdicts depend on code shape and hold for the builds measured; `zeroize` builds are not probed.
- Hardware timing (variable-latency instructions, speculation, power) is outside the model.

## 5. Other evidence (tests, differentials, fuzzing)

| Evidence | Result |
|---|---|
| ACVP (NIST, vendored subset) | keyGen 75/75, sigGen 60/60 (pure internal and external, deterministic and hedged), sigVer pure 30/30 (`tests/acvp.rs`). The vendored subset has 120 sigGen and 60 sigVer cases; the other half of each (preHash and external-μ groups) is skipped because HashML-DSA and external μ are not implemented |
| Wycheproof (C2SP, d17cc89) | Rust: 1063 vectors pass, 0 fail, 6 known (E-4: out-of-range secret keys), 69 skipped (external-μ only, out of scope); Lean spec: 928/928 agree (631 verify, 236 sign, 61 keygen) (`tests/wycheproof.rs`, `lean/SpecTests/Wycheproof.lean`) |
| RustCrypto `ml-dsa` a3690c4 (oracle) | pk and sk match on 30 seeds per set; Sign matches on 25 cases per set; Verify agrees on 1,260 cases per set (valid, bit flips in c̃/z/h, wrong M, wrong pk); randomized: 200 keygen + 200 sign/verify (M′ up to 10 kB) + 2,000 sign per set; hint-region differential 30k per set; the public API matches upstream's external interface on 72 cases incl. \|ctx\| = 0, 255, 256 (`tests/diff.rs`, `keygen.rs`, `verify.rs`, `random_diff.rs`, `api.rs`) |
| aws-lc-rs 1.18.2 (aws-lc-sys 0.46.0), the backend nearcore calls for ML-DSA-65 | 0 verdict differences in about 3.22M verify comparisons on fixed-length and wrong-length inputs (2.54M also through `api::verify_NN` and `verify_prepared_NN`): bit flips, multi-bit, fill and splice of σ, pk and M; hint encodings; wrong lengths; c̃; edge-value keys; valid cross-signing both ways; forged z at and beyond ±(γ1−β) and ω hints. 610 empty-ctx Wycheproof verify vectors agree. KeyGen from 15,000 seeds byte-identical. aws-lc signs hedged, so signatures are cross-verified, not compared; aws-lc-rs has no ctx parameter, so only ctx = "" is compared. Known API difference: aws-lc-rs also accepts a DER-SPKI-wrapped pk. Limit: verdict-level testing cannot see a dropped "decreasing count" hint check (c̃ rejects anyway); that check is proved (HintBitUnpack) and unit-tested (`tests/leaf.rs`). 4 of 5 injected verifier weaknesses detected (`tests/awslc_diff.rs`). A test, not an equivalence proof |
| libcrux-ml-dsa 0.0.11 (portable + AVX2), mldsa-native v2.0.0 (C + AVX2), RustCrypto | 0 disagreements, 0 crashes: 1.05M keygens and 1.5M signatures byte-identical; 15.4M verify cases (every single-bit flip of σ and pk for 60 cases per set, plus mutation classes covering c̃, z, hint encodings, pk; about 185M verify calls), all 150k honest signatures accepted by all; fuzzing 3.66M `verify_xdiff` and 195k `sign_xdiff` executions. Sensitivity: with the hint zero-padding check removed, 4,012 disagreements. Malformed sk (FIPS-undefined): ours, libcrux and mldsa-native sign identically; RustCrypto panics; mldsa-native's `pk_from_sk` also rejects inconsistent t0/tr/ρ (`crosscheck/`) |
| Differential fuzzing vs RustCrypto (`fuzz/`) | about 50 minutes per target, 0 crashes, 0 disagreements: `verify_diff` 12.1M execs (mutated c̃/z/hints/pk, ctx 0–256, wrong lengths; 96.7% region coverage of `src`), `sign_diff` 787k (98.2%), `decode_roundtrip` 1.1M (Sign on arbitrary sk bytes never panics; matches upstream wherever upstream accepts the key). Sensitivity: with the hint zero-padding check removed, `verify_diff` found it after about 3,800 runs; a removed `count > ω` check was not found in 180 s (it rarely changes the verdict). The κ-exhaustion path was never reached |
| Proof mutation testing | 29 semantic mutants of `src` (rounding edge cases, hint checks, norm bounds, NTT⁻¹ layers and scale, sampler indices, seeds and hash inputs, κ budget, ctx and length guards, parameter constants): every one breaks the Lean build at the spec theorem of the mutated function. `cargo test` missed 5 (λ/4-byte c̃ compare, `infinity_norm` threshold, HintBitUnpack's count > ω check, Verify's ‖z‖∞ `<`, κ budget); regression tests now kill four (`tests/mutants.rs`, the `prefix_eq` unit test in `src/verify.rs`); the κ budget guard (`while κ + ℓ − 1 ≤ 0xFFFF`, now the function `sign::more_attempts`) is tested at its boundary by `sign_loop_guard_allows_the_last_attempt` (the `<` variant of the guard fails it), while that Sign's loop calls the guard is shown by the proof only. Of the 29 mutants, about a third fail the Lean build as unprovable goals and the rest as proof-script shape breaks (the per-mutant record is not kept). The mutation harness itself is not committed, so this row cannot be re-run |
| Leaf and API tests | round trips on upstream bytes, naive references, every HintBitUnpack ⊥ case (`tests/leaf.rs`); optional key checks against 200 random mutations per set (`tests/sk_well_formed.rs`, `tests/pk_from_sk.rs`); SHAKE KATs (`tests/shake_kat.rs`, `shake_lanes.rs`); dispatch vs portable NTT (`tests/dispatch.rs`) |
| zeroize | `tests/zeroize.rs` scans the stack below `keygen`, `pk_from_sk`, `signing_key`, `sign`, `sign_prepared` and single Sign attempts (rejected early, rejected late, accepted) for residue of K, s1, s2, t0, ρ″, the mask y and the values derived from it (ŷ, Â ∘ ŷ, w, ĉ, ⟨⟨cs1⟩⟩, ⟨⟨cs2⟩⟩, r0, ⟨⟨ct0⟩⟩, and z and c̃ of rejected attempts), and checks the drop wipe; see Z-1 for the optimization-level caveat |
| Rust CI (`scripts/ci.sh`) | tests for default, `zeroize` (all 24 scans in release; the 3 `signing_key` scans at opt-level 0) and `avx2`; thumbv7em; MSRV 1.86; wasm32; nearcore profile on 1.95.0 (fat LTO, overflow checks, panic = abort for the build) incl. zeroize; 60 s fuzz smoke of three targets; the aws-lc differential; `cargo deny` |

### Benchmarks

ML-DSA-87, microseconds, median of 15 rounds over 256 messages (64 seeds for keygen), `bench/compare.sh`, nearcore profile
(opt-level 3, fat LTO, one codegen unit, panic = abort), measured on 2026-10-31 on one pinned core of an AMD EPYC 9B14 (Zen 4)
virtual machine at 3.40 GHz, rustc 1.99.1, shared with other jobs (load average 2.2–2.5):

| operation | default | `avx2` feature | `-C target-cpu=x86-64-v3` |
|---|---|---|---|
| keygen | 229 | 193 | 180 |
| sign (deterministic) | 714 | 466 | 429 |
| sign, prepared key | 543 | 312 | 285 |
| verify | 235 | 189 | 175 |
| verify, prepared key | 82 | 39 | 35 |

Uncached ML-DSA-87 for comparison on the same machine and profile: libcrux AVX2 sign 219 / verify 109; mldsa-native AVX2 sign 122
/ verify 55. Prepared-key verify skips pk decoding, ExpandA and the NTT of t1, so it is a different operation from the uncached
one; uncached sign and verify here are 1.7–3.8× behind the AVX2 implementations. Spread over the 15 rounds is at most 0.55% for
this crate; one key pair per set, hot caches. The C libraries were built with gcc 13.3 `-O3` and no LTO (a different C compiler
or flags would change their columns). Sign medians depend on the message set through the number of attempts and move by a few
percent with it, the same for all implementations because their signatures are byte-identical. A 4-way Keccak without
intrinsics was measured and not adopted: plain loops reached at most 1.2–1.3× over four scalar permutations, below the 1.6× bar,
and intrinsics would need hand-written AVX2 in the dispatch that Lean could only model, not prove. Not measured: aarch64, wasm32, Intel. Reproduce with `bench/build.sh`, `bench/run.sh`
and `bench/compare.sh` ([reproduce.md](reproduce.md)).

## 6. Found and fixed

- **CT-1** (riscv32imac): the mask-select idiom (`ct_select`, `ct_lt_mask` and callers) was turned back into branches on secret
  data because RISC-V has no conditional move. Fixed with a `core::hint::black_box` barrier compiled only for RISC-V and not under
  `cfg(miri)`, so the proved code is unchanged. Applying it on every target cost about 25% in signing. The standalone `ct_lt_mask` probe is insecure on riscv32imac
  anyway: the probe masks its inputs below 2^63, so LLVM folds the compare back into a branch; every in-crate caller is secure.
- **CT-2** (x86_64): LLVM turned the `diff == q − 1` edge select in `rounding::decompose` into a branch around the multiply that
  computes r1, visible only in the inlined signing-step probes. Fixed in 069b439 by `field::opaque_u32` (`black_box` on every
  target, identity under `cfg(miri)`). Cost about +2–3% in Sign.
- **CT-3** (all targets with overflow checks): `sk_is_well_formed` branched on the sign of secret s1/s2 coefficients because the
  `&&` in the old `poly_in_eta` stayed a conditional branch (its right operand could panic). The six `sk_is_well_formed` and
  `encode_sk_is_well_formed` probes were `insecure` under `nearcore-exact` on the earlier tree
  (`checkct/results/nearcore-exact.stage1-600s.txt`) and are `secure` at 15b4ce2. Fixed in ae6023c: per-coefficient
  mask bits from wrapping differences, one compare at the end, and `wrapping_*` arithmetic where the proofs already exclude
  overflow, so no overflow-check guard remains on a secret value. Affected only the optional key check and `pk_from_sk_*`; Sign
  never called it. Proofs changed only in bodies.
- **E-2:** upstream's `Signature::decode` also rejects ‖z‖∞ ≥ γ1 − β, which FIPS 204 Algorithm 27 does not (Algorithm 8 does).
  Same final verdict; this crate follows FIPS and checks in `verify_internal`.
- **E-3:** the rejection loops have no provable bound (Verify runs RejNTTPoly and SampleInBall on attacker-chosen seeds). Resolved
  for every input by partial correctness plus panic-freedom: the `*_exact` theorems.
- **T-1:** Aeneas colors its log tags, so a substring gate never matched `[Error]`; `scripts/extract.py` strips ANSI escapes.
- **T-2:** see the extraction constraints below (`return` from a loop followed by another loop).
- **T-4, T-5:** extraction runs with `--no-default-features`, so optional wrapper features (`zeroize`) stay out of the extraction
  closure; the Lake `defaultTargets` include `Spec` and `Proofs`, so the axiom check no longer depends on a warm build directory.
- **T-6:** gate pipelines without `pipefail` reported success on failed builds. `scripts/lean-check.sh` is the done-gate (pipefail;
  fails on a nonzero lake exit, any `error:` or `declaration uses 'sorry'` in the full log, or the axiom gate), and
  `scripts/extract-and-build.sh` greps its build log too.

## 7. Known limitations

- **Z-1 (open): zeroize stack-residue scans fail in unoptimized builds.** `tests/zeroize.rs` has 24 stack scans (eight per
  parameter set: `keygen`, `pk_from_sk`, `signing_key`, `sign`, `sign_prepared` and one Sign attempt each rejected early,
  rejected late and accepted) and four wipe tests (drop wipe per set, SHAKE wipe), 28 tests in all. At opt-level 0, 21 of the 24
  scans find copies of secrets in dead stack frames (K, s1, s2, ŝ1, t0, y or the values derived from it); `signing_key` passes
  for all three sets. At dev opt-level 1 (the whole crate and test at opt-level 1) 26 of 28 pass on a Linux x86_64 machine (`keygen_44` and
  `keygen_65` fail, as before; results at opt-level 1 moved with code layout during this work) and 28 of 28 on an aarch64 macOS
  machine. Release passes 28 of 28 on both machines. The stack-residue claims in `src/api.rs`
  hold for optimized builds only; drop and explicit wipes are unaffected. A copy vendored as a workspace member would build at
  opt-level 0 in a dev profile. Open: add wipes at those locals, or keep the scope. `scripts/ci.sh` runs the 3 passing scans at
  opt-level 0 and all 24 in release and under the nearcore profile. Not wiped by design, as documented in `src/api.rs`: moves
  of returned structs, the accepted signature (z, c̃, h), one copy of K and t0 in keygen, t0 in `pk_from_sk`, and anything
  skipped by a panic or `mem::forget`; registers, swap and core dumps are out of reach. The scans look for the first 16
  coefficients of each vector, so a copy the compiler stores in pieces would be missed.
- **T-9: two BINSEC limits decide what a `nearcore-exact` sweep can show.** (1) *Overflow-check guards on secret values stall
  BINSEC*: with `overflow-checks = true`, the conditional jump to the panic path after arithmetic such as `a + Q - b` left 65 probes
  at one pending path through 600 to 3600 s on the earlier tree (68 `unknown` at 600 s, 3 of them `secure` at 3600 s;
  `checkct/results/nearcore-exact.stage1-600s.txt`, `.stage2-trace-300s.txt` and `.stage3-trace-3600s.txt`; in the traced pass 48 of the 68
  stopped at the overflow-check guard in `field.rs:39`, nearly all the others at other lines of `field.rs`). The crate no longer has those guards on secret values (CT-3), and
  those probes are no longer stuck there; source that keeps such guards could stall the same way (not tested). One probe,
  `prepare_sk_1x1_65`, still ends with one pending path at 600 s and 3600 s at a `movdqu` store in `ntt_body_mut`, and is `secure`
  under `-novec` with overflow checks on, so the cause is unknown. (2) *BINSEC 0.11.3 cannot lift AVX/VEX instructions.* nearcore
  builds x86_64 with `+fma`, which implies AVX, so LLVM emits VEX forms; under `nearcore-exact` 48 of 113 probes are cut paths at
  `vinsertps`, `vblendvps` or `vblendps` on `ymm` (the NTT, `hint_step`, `response`, `prepare_sk`, `signing_key` family). So
  nearcore's exact build has no BINSEC verdict for the NTT, `hint_step` and `response`; the `-novec` result is evidence about a
  different binary. Workaround: build the analyzed binary without vectorization, or check the VEX code by another route; neither is
  done for the vectorized NTT/product code.
- **T-8: BINSEC out-of-memory kills look like tool errors.** A probe killed at the container's memory cap shows only `error`. Every
  `error` is presumed an OOM kill, with no verdict, unless the kernel log shows no kill in its run window; a census killed alone at
  120 GB is recorded as "needs more than 120 GB". Whole-Sign censuses on thumbv7em and riscv32imac, and the x86_64 default and
  dispatch prepared census, have no verdict for this reason.
- **Other CT unknowns:** riscv32imac `vec_power2round_87` and one census; the three `split_vec_power2round_{5,6,7}` capacity probes;
  three riscv32imac `split_prepare_sk` pieces (solver stall at a store in `ntt_body_mut`, cause not pinned down); eleven AArch64
  probes (and two split pieces, `split_prepare_sk_87_{7x1,col}`: thirteen rows in all) stuck in one solver query. AArch64 `prepare_sk_87`/`signing_key_87` are covered only stage by stage (skDecode, then the
  in-place NTT of 8 polynomials, both secure); the K = 8 glue has no single verdict. Split pieces are separate monomorphizations,
  so that argument is about the source, not the full-size machine code. The AVX2 copy of the dispatched NTT, AArch64 NEON builds
  and nearcore's vectorized x86_64 NTT cannot be lifted.
- **E-1:** the core decoders index slices directly. `verify_internal` starts with a length guard (valid when `p` agrees with `K`/`L`),
  but `sign_internal` and `keygen_internal` still panic on wrong-length slices and their older theorems keep the length hypotheses;
  the API's fixed-size arrays discharge them. Every module except `api` is crate-private (public only under the `internals` feature
  for tests and fuzzing), so none of these entry points is reachable by a downstream user unless something in the dependency graph
  turns that feature on (Cargo unifies features).
- **E-4: out-of-range secret keys are accepted.** Six Wycheproof sign vectors (two per set) use an expanded secret key whose s1 or
  s2 has a coefficient outside [−η, η] and expect signing to fail. This crate and the Lean spec both sign with them (FIPS 204
  Algorithm 25 says such coefficients "may lie outside [−η, η] if input is malformed", and Section 7.2 says skDecode should run only on
  trusted input); RustCrypto panics. It is a hardening gap for callers who load untrusted expanded keys. `tests/wycheproof.rs`
  counts these as `known`. Sign stays FIPS-literal; `api::sk_is_well_formed_NN` is a separate, proved check that agrees with
  upstream's panic on 200 random mutations per set.
- **Hint check in verdict-level tests:** see the aws-lc row in section 5.
- **No third-party audit, no FIPS or CMVP validation.**

## 8. Extraction constraints (code shape)

The core follows rules learned from extraction failures; each is enforced by the extraction gate:

1. `while i < N { …; i += 1 }` loops over fixed-size arrays. No `for`, ranges, iterator adapters or closures (`for` pulls in `Step`
   axioms; iterator chains and closures fail to extract).
2. Free functions named after the FIPS algorithm, with the step numbers in comments. No operator-trait impls.
3. Native `[u32; 256]`, `[[u32; 256]; K]`, `[u8; N]` and `&[u8]`. No `hybrid-array`, `typenum` or `module-lattice`.
4. `K`/`L` const generics plus a `Params` value; Charon runs without `--monomorphize`.
5. Lift an inner per-coefficient loop into its own function when it reads data the outer body just wrote (nested loops that read
   freshly written outer data are unsupported in Aeneas).
6. One returning loop per function, as the function's last statement before a plain tail value (`return` from a loop followed by
   another loop makes Aeneas drop the function body; T-2: `hint_bit_unpack_rows` / `_row` / `_padding`).
7. Avoid `copy_from_slice`, `to_le_bytes`, `chunks_exact`, `windows` and `rotate_left` (opaque or unmodeled); write the byte loops out.
8. Keep mask idioms for secret-dependent selects (`ct_lt_mask`, `ct_select`, `opaque_u32`) and branch only on public data.

## 9. Rust ↔ FIPS 204 map

Each function's doc comment names its algorithm (`grep -n "Algorithm [0-9]" src/*.rs`). By module:

| Module | FIPS 204 / 202 |
|---|---|
| `api.rs` | Alg 1 KeyGen, Alg 2 Sign, Alg 3 Verify (ctx prefix M′ = 0 ‖ \|ctx\| ‖ ctx ‖ M), prepared keys, `sk_is_well_formed`, `pk_from_sk` |
| `keygen.rs`, `sign.rs`, `verify.rs` | Alg 6 KeyGen_internal, Alg 7 Sign_internal (loop body in `sign::attempt`), Alg 8 Verify_internal (includes sigDecode and the ‖z‖∞ check) |
| `encode.rs` | Alg 16–19 (bit packing via an accumulator, with a Lean lemma relating it to the bit-string spec), Alg 20/21 HintBitPack/Unpack, Alg 22/23 pkEncode/Decode, Alg 24/25 skEncode/Decode, Alg 26/27 sigEncode/Decode, Alg 28 w1Encode |
| `sampling.rs` | Alg 14 CoeffFromThreeBytes, Alg 15 CoeffFromHalfByte, Alg 29 SampleInBall, Alg 30 RejNTTPoly, Alg 31 RejBoundedPoly, Alg 32 ExpandA, Alg 33 ExpandS, Alg 34 ExpandMask |
| `rounding.rs` | Alg 35 Power2Round, Alg 36 Decompose, Alg 37 HighBits, Alg 38 LowBits, Alg 39 MakeHint, Alg 40 UseHint |
| `ntt.rs` | Alg 41 NTT, Alg 42 NTT⁻¹, Alg 44–48 (AddNTT … MatrixVectorNTT); the zeta table is a literal that Lean checks against ζ^BitRev8(k); optional AVX2 dispatch |
| `field.rs` | arithmetic in Z_q (reduction is Barrett/Montgomery; FIPS 204 allows any equivalent reduction; Alg 49 is not used), mask helpers |
| `keccak.rs` | FIPS 202 Keccak-f[1600], SHAKE128/256 |

Algorithms 9–13 (bit/byte conversions) and 43 (BitRev8) exist only in the Lean spec. HashML-DSA (Alg 4/5) is not implemented.

## 10. Related work

A survey of public READMEs, proof directories and papers on 2026-10-30; it was not re-run afterwards, no one's proofs were
rebuilt, and the descriptions below can be out of date or wrong. "Related" does not mean equivalent in scope.

- **Apple corecrypto** (C; Cryptol/SAW and Isabelle): reported to refine an Isabelle transcription of FIPS 204 for KeyGen, Sign
  and Verify, with Sign/Verify coverage bounded to specific message sizes.
- **Microsoft SymCrypt** (Rust, Charon/Aeneas/Lean, the same toolchain as this crate): described in a September 2026 paper
  (arXiv 2609.15648); the ML-DSA Rust code and proofs were not in the public branch at the survey date.
- **ocaml-pq** (OCaml; Lean 4 proofs over hand-transcribed models): end-to-end theorems for 44/65/87 against models of the OCaml
  code. `xspec/` proves this crate's spec equal to its transcription (section 1.8).
- **libcrux-ml-dsa** (Rust, hax to F\*): proofs cover leaf modules of the portable and AVX2 arithmetic, NTT and serialization
  layers; the top-level modules were not in the proof set at the survey date, and the project does not claim an end-to-end
  proof.
- **mldsa-native** (C; AWS-LC uses its C-only variant): CBMC proofs of absence of undefined behavior for the C code, and HOL
  Light proofs on the object code of selected assembly routines (functional correctness, memory safety and secret-independent
  timing, per routine). The survey found no theorem relating KeyGen, Sign or Verify as a whole to FIPS 204.
- **Formosa Crypto** (EasyCrypt/Jasmin AVX2 ML-DSA-65): in progress at the survey date, with `admit`s in the proofs.

This crate does not claim to be the first or the only formally verified ML-DSA. Its claim is the specific combination in section 1:
a Rust implementation, a Lean model extracted mechanically from it, theorems over every API input for all three parameter sets with
the premises named above, and `Verify(Sign) = true`, re-checkable on standard Lean axioms. Where the other projects prove things
this crate does not (for example object-code properties), they go further.

## 11. Reproducing each piece

[reproduce.md](reproduce.md) has the exact steps and the tool pins.

| Evidence | Command |
|---|---|
| `*_exact`, prepared, correctness, SkWellFormed, PkFromSk, Divergence; axiom gate | `scripts/lean-check.sh` |
| Witnesses | `scripts/witness-check.sh` |
| Extraction is clean and `lean/Impl` is current | `python3 scripts/extract.py` then `git diff lean/Impl`; `scripts/extract-and-build.sh` for extraction, build and axiom gate |
| Spec against ocaml-pq | `scripts/xspec/check-axioms.sh`; executable differential `scripts/xspec/run-diff.sh all` |
| Spec against VCVio | `scripts/diff-vcvio/run.sh all` |
| Spec against ACVP | `lake build spec-acvp && .lake/build/bin/spec-acvp` in `lean/` |
| Extracted Lean vs native Rust | `scripts/impl-eval.sh lean`, `rs`, then `compare` |
| Rust tests and builds on thumbv7em, MSRV, nearcore profile, wasm32, fuzz smoke, `cargo deny` | `scripts/ci.sh` |
| Cross-implementation differential and fuzzing | `crosscheck/README.md` ("How to run") |
| Differential fuzzing vs RustCrypto | `fuzz/` (`cargo fuzz run verify_diff`, `sign_diff`, `decode_roundtrip`) |
| Constant time | `checkct/README.md` |
| Stack | `tools/stack/run.sh` (`tools/stack/README.md`) |
| Performance | `bench/compare.sh` |

## 12. Wording that stays inside the evidence

Safe: "the extracted Rust for every `api` function is proved, with no premises, to never fail (in the Aeneas model: stack
exhaustion and out-of-memory are not modeled, and the Rust can diverge exactly when the spec returns no result at any
fuel, §1.2) and to agree with the Lean transcription of FIPS 204 whenever either returns (`*_exact`), with the trusted
base in §2"; "constant time is checked by BINSEC on compiled probes for the builds and targets in §4". Not supported:
"formally verified" without that scope; "constant time" for whole-Sign; any statement about aws-lc equivalence; "FIPS validated"
or "FIPS certified"; "first" or "only"; "production-ready" or "audited".

The Lean theorems are about source semantics, not object code, and the agreement of Verify verdicts across nodes and builds is a
consensus property that §1.1 gives only for code with the semantics of the extracted source. With the `avx2` feature the
dispatched and portable NTT copies are tested equal (`tests/dispatch.rs`), not proved. The nearcore-profile test run in
`scripts/ci.sh` (`nearcore-test`, overflow checks on) is an empirical check of the compiled code, not a proof.
