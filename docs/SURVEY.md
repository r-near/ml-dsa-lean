# Re-pin survey: RustCrypto ml-dsa master vs the campaign pin, and the extraction picture

Lane: `repin-survey-20261029/`.

- **Inputs.** Upstream master **`a3690c4a0bd861fcf2bde0e38b3609e86c3fe89e`** (2026-10-29, "ml-dsa: expand `cargo checkct`
  to cover signing (#1490)"), cloned into `upstream-master/`. Its git dir was moved to `upstream-master.gitdir/` so rx
  sees one worktree. The pin is `cf99f5e`.
- **Tools** (installed on the box by `box/setup-tools.sh`, at the earlier lanes' pins): cargo-hax 0.4.2, Charon
  nightly-2026.09.02, Aeneas build-183e4f0, Rust nightly-2026-08-18 with a Miri sysroot for `--cfg miri`, and Lean
  v4.31.0.
- **Reproduce** with `./run.sh`.
- **Direction change, mid-lane.** The plan is now a proof-first fork. Steps 1, 2 and 5 are as briefed, the upstream PR
  grouping is replaced by `FORK-DESIGN.md`, step 4 (factoring master) was skipped (`patches/README.md`), and
  `fork-skeleton/` was added.

## 1. What changed on master since `cf99f5e`

There are 13 commits (`diff/commits-since-pin.txt`). Seven of them touch ml-dsa code or behavior:

| Commit | Title |
|---|---|
| #1444 | private matrix storage offloaded one row at a time |
| #1461 | reuse the public key during key generation |
| #1484 | initial `cargo checkct` |
| #1481 | error on rejection-sampling exhaustion |
| #1483 | `ct_div` comment |
| #1488 | `signing_nonces` |
| #1489 | `compute_mu` context guard |
| #1490 | `checkct` covers signing, adding `signing/steps.rs` |

#1444 and #1461 were not in the brief's list. The rest are dependency, README and MSRV changes: #1475, #1476, #1477 and
#1487. `module-lattice` (0.2.3) and `hybrid-array` (0.4.15) are unchanged. Lockfile bumps that matter: **ctutils 0.4.2 →
0.4.7** (the Cargo.toml floor is now 0.4.7; `ct_gt.rs` and `ct_lt.rs` changed, `diff/ctutils-0.4.2-to-0.4.7.diff`) and
**keccak 0.2.0 → 0.2.2** (soft-backend round-constant handling rewritten, `diff/keccak-0.2.0-to-0.2.2.diff`). Also
zeroize 1.9.1 and cpufeatures 0.3.1. The full diff is in `diff/ml-dsa-src.diff`.

| File | Change | Class |
|---|---|---|
| `signing.rs` | `raw_sign_mu` becomes `try_raw_sign_mu(..) -> Result` with `Err` on exhaustion (#1481); `raw_sign_mu` and `sign_mu_deterministic` `expect()` it (HAZ-2's panic stays on those); `sign_deterministic`, `sign_randomized` and `DigestSigner` return the error. The loop is now `for kappa in signing_nonces::<P>()` = `(0..=u16::MAX-(L-1)).step_by(L)` (#1488), which **drops** the overflowing last batch, where the campaign's ML-2 fix wraps. The loop body calls `steps::response` / `steps::hint_polynomials` (#1490). `from_seed` builds `VerifyingKey::new(rho.clone(), t1, A_hat.clone(), Some(enc))` directly (#1461). | extraction (new `StepBy` iterator, B-A16/17); already-proved: SIGN-01/02/03 and KEYGEN-01 re-check |
| `signing/steps.rs` (new) | straight-line `response` (steps 18–21) and `hint_polynomials` (25 plus the sum) | extraction-neutral as such (they call the §B operators); SIGN-01 re-check |
| `sampling.rs` | `expand_a` uses the new `NttMatrix::from_fn` (#1444); `expand_mask` calls the new `expand_mask_xof` (#1484) with `mu + r` (checked add; no overflow given the #1488 bound) | extraction (B-C1/C3); SAMPLE-04 re-check |
| `algebra.rs` | `NttMatrix` is now an ml-dsa struct `Array<MaybeBox<NttVector<L>>, K>`, with its own `Mul` impl (`iter().map().collect()`) and `from_fn` (#1444); `ct_div` comment (#1483) | extraction (B-B1, B-C1); VERIFY-01 / KEYGEN re-check (`A_hat * v` now resolves to the new impl); the comment is cosmetic |
| `verifying.rs` | `compute_mu` rejects `ctx.len() > 255` before calling `Mp` (#1489). The text is identical to the campaign's local fix. | already-proved: none (the campaign source already has it); VERIFY-02 wording only |
| `lib.rs` | tests only | cosmetic |
| `ntt.rs` | test only (`NttMatrix::from_fn` in a test) | cosmetic |
| `encode.rs`, `crypto.rs`, `param.rs`, `hint.rs`, `pkcs8.rs` | byte-identical to the pin | none (but see §5 for hint.rs and pkcs8.rs vs the *campaign* source) |
| `Cargo.toml` | `rust-version` 1.87, `ctutils = "0.4.7"` | already-proved: the ctutils-based CT proofs need a re-check |

## 2. Extraction of master, before any rewrite

Roots are `cfg(hax)` call-through wrappers appended **to a per-run copy** of master, for extraction only:

- *signing:* `sign_internal`, `try_raw_sign_mu`, `sign_deterministic` and `Signer::try_sign`, for 44/65/87;
- *verification:* `verify_internal`, `verify_mu`, `verify_with_context`, `VerifyingKey::decode` and
  `Signature::decode`.

Opaque by flag: `ml_dsa::crypto` and `hybrid_array` except `Array`. The flags are otherwise the keygen and skencode
lanes': `--monomorphize`, `--cfg miri`, no default features (`extract/variants.json`, `extract/probe.py`).

| Run | Charon | Aeneas | Result |
|---|---|---|---|
| `sign-open` (12 roots) | LLBC OK, 1,143 functions | exit 2: 90 error lines, 88 "could not translate" items in 25 groups, then **`Uncaught exception: Not_found`**; no Lean written | `logs/master-sign-open/` |
| `verify-open` (15 roots) | OK, 1,292 functions | exit 2: 67 errors, 65 items in 23 groups, `Not_found` | `logs/master-verify-open/` |
| `r-try-raw-sign-mu`, `r-sign-internal`, `r-raw-verify-mu`, `r-vk-decode` (single ML-DSA-44 roots) | OK | exit 2, `Not_found` in every one | `logs/master-r-*/` |
| `r-sig-decode` | OK | exit 1, Lean written, but with **5 "Name clash … the generated code will be incorrect"** errors over 3 names (`Iterator::{all,collect,map}.default`, from `Hint::bit_unpack`) | `logs/master-r-sig-decode/` |

`cargo hax` exits 1 on every master run, and on fork-mono. In each case the failure is its built-in Aeneas step (bypassed per TOOL-6); the `charon_errors` field in `result.json` counts those lines. Charon itself reports no errors, and the LLBC is complete in every run. There are no "extracted code may be incorrect" (TOOL-7) warnings in any run. The region failures show up as internal
errors instead. The Charon LLBC has no local opaque function apart from `ml_dsa::crypto`. Everything else is either
core or hybrid-array, or failed in Aeneas.

The `Not_found` is observed, not diagnosed. It is raised in Aeneas's pure micro-passes over transparent functions,
after translation errors, in every run that reaches SHAKE, NTT or matrix code, and it is absent from `r-sig-decode`.
That it cascades from functions whose signatures failed to translate is a hypothesis this lane did not test.

**Blockers before: 35 distinct source locations** (29 from the static LLBC inventory, 5 more seen by Aeneas, 1 added
by hand), plus the `hybrid_array` trusted-model family and three tool failure modes. The full list, with every field,
is in `BLOCKERS.md`. By class:

| Class | Count | Where |
|---|---|---|
| A. `iter().map/zip/fold/sum/collect` over `hybrid_array`, plus the `StepBy` nonce iterator | 19 | 17 ml-dsa, 2 module-lattice |
| B. Operator-trait impls on references, with iterator bodies | 8 | 1 ml-dsa (the new `NttMatrix` `Mul`), 7 module-lattice |
| C. Closures, `Array::from_fn`, `flatten`/`unflatten` | 5 | ml-dsa and hybrid-array |
| O. `for m in Mp` over `&[&[u8]]` (MuBuilder) | 2 | ml-dsa |
| S. `chunks_exact` in `rej_ntt_poly` | 1 | ml-dsa |

Ten of these already have a lane-copy factoring in the campaign (keygen F-NTT/F-INTT/F-ADD/F-DOT/F-MAT, sampling
F-NTT/F-EXA/F-EXS, skencode F-VPACK/F-BENC). Two of those, F-EXA and F-MAT, no longer apply as written because #1444
replaced the code they factor.

## 3. Fork skeleton extraction, after (the step-4 replacement)

`fork-skeleton/` (1,022 lines; style rules in BLOCKERS.md §F, design in FORK-DESIGN.md) implements Sign_internal for all
three sets with plain arrays and loops. That covers skDecode, NTT and NTT⁻¹, ExpandA (RejNTTPoly), ExpandMask,
SampleInBall, rounding, MakeHint, w1Encode, sigEncode, and an in-crate Keccak/SHAKE.

- **Differential:** it is byte-identical to master's `sign_internal(..).encode()` on 25 cases per set
  (`cargo test --release`, on the box).
- **Extraction, `fork-generic`** (no `--monomorphize`, nothing opaque by flag):
  - Charon gives 99 functions, none local-opaque; the 20 opaque ones are core primitives that Aeneas models.
  - Aeneas exits 0 with **0 errors, 0 warnings, 0 name clashes**.
  - `lake build` against Aeneas `build-183e4f0` succeeds (`logs/master-fork-generic/lake.log`).
  - `#print axioms` over **all 180** extracted definitions: only `propext`, `Classical.choice`, `Quot.sound`.
  - `FunsExternal_Template.lean` declares 4 `core::iter::range::Step` defaults that no definition references.
- **Blockers after: 0** in the fork.
- **Two runs needed fixes on the way:**
  - The first generic run failed on one construct, B-F1: `[Error] Unimplemented`, `Source: 'src/sign.rs', lines 40:8-42:9`,
    "Could not translate the body of function `ml_dsa_fork_skeleton::sign::attempt`". That was a nested loop reading
    `w[i][j]` right after the outer body assigned `w[i]`. Lifting the inner loop into `poly_high_bits` and
    `poly_low_bits` fixed it.
  - `for` ranges were replaced by `while` (B-F2).
- **`fork-mono`** (`--monomorphize`) also has 0 errors from the direct Aeneas run but **9** unmodeled instantiated slice/array index axioms
  (B-X3). So the fork does not monomorphize.

Performance on that path (box, release): the fork's Sign_internal runs 1.01× (44), 1.00× (65) and 1.07× (87) of
upstream, even though it redoes skDecode, NTT(s1, s2, t0) and ExpandA on every call (`logs/fork-bench.log`).

## 4. PR grouping → replaced

There are no upstream PRs under the new direction. The blocker classes become the fork's style rules (BLOCKERS.md
"Fork style rules"). For the record, had upstreaming continued, the natural single-concern groups would have been:

- A-ml-dsa: vector and polynomial map loops in `algebra.rs`, `ntt.rs` and `hint.rs`;
- A16/17: the nonce loop;
- B-B1/C1: the `NttMatrix` struct;
- module-lattice A/B: free vector functions with forwarding operator impls;
- O1/O2: MuBuilder;
- S1 and B-A14: decoders.

## 5. Carry-over of proved components onto master

Function bodies (whitespace- and comment-normalized) compared between `campaign/source` and master, from
`diff/fn-identity.md` (`tools/fn_identity.py`). "Carries" means the source text the proof extracted is unchanged and its
dependencies are unchanged.

| Obligation | Functions | campaign == master | Dependency change | Verdict on master |
|---|---|---|---|---|
| NTT-01 | `ZETA_POW_BITREV` | yes | — | **carries** |
| NTT-02/03 | `ntt_layer`, `ntt_inverse_layer`, polynomial `ntt` / `ntt_inverse` | yes | — | **carries** (the refactor bridges are on the same text) |
| NTT-04 | vector `ntt`/`ntt_inverse`, `multiply_ntt` | yes | — | **carries** for the wrappers; matrix lifting re-check (new `NttMatrix`) |
| ARITH-02/03 | module-lattice `small_reduce`/`barrett_reduce`/`Elem` ops | yes (0.2.3) | — | **carries** |
| ARITH-01 | `reduce`, `ct_div` (comment only), `decompose`, `mod_plus_minus`, `infinity_norm` | yes | **ctutils 0.4.2 → 0.4.7** (`ct_gt`, `ct_lt` changed) | **re-check** the portable ctutils leaves |
| HINT-01 | `make_hint`, `use_hint`, `high_bits`, `low_bits` | yes | ctutils, as above | **re-check** (ctutils only) |
| BACKEND-01 | cmov 0.5.4 asm templates | — | cmov unchanged; ctutils 0.4.7 may route differently | **re-check** the call path |
| SAMPLE-01 | `coeff_from_three_bytes`, `coeff_from_half_byte` | yes | — | **carries** |
| SAMPLE-02 | `rej_ntt_poly`, `rej_bounded_poly` | yes | keccak 0.2.2 under the XOF premise | **carries** (XofSim premise unchanged) |
| SAMPLE-03 | `sample_in_ball` | yes | as above | **carries** |
| SAMPLE-04 | `expand_a`, `expand_mask` **changed**; `expand_s` same | no / no / yes | — | **re-check**: F-EXA must be redone over `NttMatrix::from_fn`, and ExpandMask is split into `expand_mask_xof` with a non-wrapping nonce |
| HASH-01 | keccak soft backend | — | **keccak 0.2.0 → 0.2.2** | **re-check** (round-constant code rewritten) |
| HASH-02 | `crypto.rs` ShakeState | yes | — | **carries** |
| HASH-03 | `MuBuilder::{new, internal, message, finish}` | yes | — | **carries** |
| PARSE-01 | `Hint::bit_unpack` | **no**. Master equals the pin; the campaign's proof used its `decode_hint_row` factoring | — | **re-bridge** (master never had the factoring) |
| PARSE-02/03/05, skEncode | `bit_pack`, encode.rs `pack`/`unpack`, all `param.rs` codecs, `to_expanded` | yes | — | **carries** |
| PARSE-04 | `Signature::decode`/`encode` | yes | — | **carries** |
| PARSE-06 | pkcs8.rs | master == pin, **campaign differs** (local F1/F2 fixes) | — | the campaign's F1/F2 fixes are **not upstream** (PR #1482 and issue #1479 are open, per `../ISSUES-AND-FIXES.md`) |
| KEYGEN-01 | `SigningKey::from_seed` **changed** (#1461); `ExpandedSigningKey::new`, `new_expand_a` same | no / yes | `A_hat` type changed | **re-check** (verifying key now built from `rho.clone(), t1, A_hat.clone(), Some(enc)`) |
| SIGN-01 | `try_raw_sign_mu` body (now via `steps`) | **no** | — | **re-do** the candidate-body relation on the new body (same arithmetic, new call boundaries) |
| SIGN-02/03 | `signing_nonces` (new), `raw_sign_deterministic` changed | no | — | **re-check**. The bound differs from the campaign's ML-2 fix: master drops the last batch where the campaign wraps the nonce. Exhaustion now returns `Err` (it matches the campaign's ML-3 fix in effect, not in text) |
| VERIFY-01 | `raw_verify_mu` | yes (text) | `A_hat * z_hat` now resolves to the new ml-dsa `Mul` | **re-check** the matrix-product leaf only |
| VERIFY-02 | wrappers; `compute_mu` | yes (the campaign already had the guard) | — | **carries** |

Summary: NTT, the field arithmetic, the samplers below ExpandA/Mask, SHAKE wrappers, MuBuilder, the encodings and
Signature decode carry by source identity. The CT leaves (ctutils 0.4.7) and Keccak (0.2.2) need a re-check through
their dependencies. SAMPLE-04, KEYGEN-01, SIGN-01/02/03 and VERIFY-01's matrix leaf change in the source. PARSE-01 needs
its factoring re-bridged against master's unfactored text.

## 6. Proposed proof plan

The fork plan is in FORK-DESIGN.md §4. Target statements (fork functions, FIPS spec in `FIPS204/Spec.lean`):

- `sign_internal_correct`: for a well-formed sk (= skEncode of a key-generation output) and under `RejTerm` for
  ExpandA and SampleInBall,
  `Fork.sign_internal p sk M′ rnd = ok (true, σ) ↔ Spec.Sign_internal_bounded p B sk M′ rnd = some σ`, and
  `ok (false, _) ↔ none`, with B = 16384 / 13107 / 9362. A spec lemma: Alg 7's unbounded loop agrees with the bounded
  one whenever the first accepting κ lies within B attempts. Premises: `RejTerm` (probabilistic termination), Spec
  fidelity, and the translation trust base.
- `verify_internal_correct`: for **all** byte strings pk and σ, under `RejTerm` for ExpandA and SampleInBall,
  `Fork.verify_internal p pk M′ σ = ok (Spec.Verify_internal p pk M′ σ)`. No signature-invariant premise is needed,
  because sigDecode and the ‖z‖∞ check are inside Alg 8 in the fork.
- Then `keygen_internal_correct` for Alg 6, the external Alg 1–3 corollaries, and the stretch theorem
  `Verify(pk, M, Sign(sk, M)) = true` on Spec.

To prove the same on **master** instead, you would need: the 35 rewrites (or ten-plus Kani bridges), the PARSE-01
re-bridge, the SIGN-01 re-do over `steps`, an F-EXA redo for `NttMatrix::from_fn`, and the ctutils/keccak re-checks.
That is why the fork is the cheaper end-to-end route.

## 7. Honest effort estimate

The estimate is **10–15 person-weeks** to the three top theorems on the fork, plus **3–5** for the correctness
stretch (phase table in FORK-DESIGN.md §7). Most of the campaign's mathematical lemmas carry: field, rounding, hint, NTT
schedule, sampler output specs, FIPS 202 spec and XofSim. None of its extracted-Lean theorems carry as-is, since the
fork's text is new. What disappears is every ADAPTER hypothesis, every Kani-to-Lean join, and the `hybrid_array`
trusted models. The main risk is Lean proof performance on 256-element arrays inside `loop` bodies (NTT).

## Files

- `UPSTREAM-MASTER-SHA`, `diff/`: commit list, stat, source diff, lockfile diff, dependency diffs, file and function
  identity.
- `extract/`: probe, variants and generator. `box/`: tool setup, lake build, Lean manifest. `tools/`: classify,
  inventory, identity, scrub, pull.
- `logs/master-*/`:
  - `result.json`, `classified.json`, `aeneas.log`, `hax.log` and `inventory.{txt,json}` (the LLBC is kept locally and
    gitignored);
  - `logs/master-fork-*/lean/` and `lake.log`;
  - `logs/fork-bench.log` and `logs/box-setup.log`.
- `fork-skeleton/`: crate, differential test, bench, and `extracted-lean/` (the accepted generic extraction).
- `BLOCKERS.md`, `FORK-DESIGN.md`, `patches/README.md`, `run.sh`.
