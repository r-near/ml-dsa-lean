# Differential check of `lean/Spec` against Galois's Cryptol specification of FIPS 204

**What this is.** `lean/Spec` is our transcription of FIPS 204 (and the Keccak/SHAKE parts of FIPS 202). Every proof in this
repository relates the Rust to that transcription, so a misreading of the standard in `lean/Spec` would carry through. This
directory runs `lean/Spec` and an *independent* transcription, the Cryptol specification
[`GaloisInc/cryptol-specs`, `Primitive/Asymmetric/Signature/ML_DSA`](https://github.com/GaloisInc/cryptol-specs/tree/master/Primitive/Asymmetric/Signature/ML_DSA)
(written for final FIPS 204 by other people, in another language, with its own bit-string representation), on the same inputs and
compares the outputs byte for byte.

**Scope.** It is a differential on a finite number of cases (the counts are in `results/`), not an equivalence proof, and it
finds places where the two transcriptions read the standard differently; where they agree it says just that two independent
readings agree on those inputs. It is not a required check and has no CI job.

## Pins

| Piece | Pin |
|---|---|
| `GaloisInc/cryptol-specs` | commit `8b74f5fc2b77fc7bbb587ba2217990b1963e9d6c` (2026-11-12), `Primitive/Asymmetric/Signature/ML_DSA` and the SHA-3 specification it imports. BSD 3-clause license (`LICENSE` in that repository): use and redistribution in source and binary form are allowed with the copyright notice kept. Nothing of it is copied into this repository; `setup.sh` clones it into the scratch directory. |
| Cryptol | 3.6.0, release asset `cryptol-3.6.0-ubuntu-24.04-X64-with-solvers.tar.gz`, sha256 `621860aa1dedc037e8fc8355bef3edf023e41e78efb7177146126f5a87309962` (the digest GitHub lists for the asset; `setup.sh` checks it). The README of `ML_DSA` names Cryptol 3.2.0; the specification loads and evaluates unchanged under 3.6.0, and the results below show it agreeing with ours (which agrees with ACVP) on key generation and signing, so the newer interpreter is not producing different values. |
| Lean | the repository's pin (`lean/lean-toolchain`). |

`setup.sh` installs both under `$CRYPTOL_TOOLS` (default `~/rx/scratch/cryptol-tools` on the build box), touches a `.keep` file there
so that the box's scratch cleanup leaves it alone, and is idempotent. It does not change anything else. It never trusts an earlier
install: each run extracts the verified archive again, checks every binary in it against `cryptol-3.6.0.bin.sha256` (committed here,
computed from that archive) and replaces the installed tree; `run_theirs.py` checks the installed binaries against the same file before
it starts Cryptol. Do not run `setup.sh` while a differential is running.

## How to run

On the Linux build box, from the repository root:

```sh
bash scripts/diff-cryptol/setup.sh          # once
export ML_DSA_SCRATCH=$HOME/rx/scratch LEAN_PACKAGES_SEED=<a directory of built lake packages, as for scripts/diff-vcvio>
DIFF_SCALE=2 DIFF_JOBS=50 bash scripts/diff-cryptol/run.sh all     # 82 minutes in the recorded run (results/)
bash scripts/diff-cryptol/inject.sh                                # the sensitivity check, 8 minutes in the recorded run, after `run.sh all`
bash scripts/diff-cryptol/inject.sh --summarize                    # recompute its table from the saved outputs
```

`run.sh all` is three stages. Each stage is: `gen_vectors.py` writes vector files, `spec-diff-cryptol` (`lean/SpecTests/DiffCryptol.lean`,
not a default target of the Lean project) runs `lean/Spec` on them, `run_theirs.py` runs Cryptol on them in parallel, and at the end
`compare.py` compares line by line.

1. Stage 0: SHAKE, NTT, rounding functions, packers, hint packing, codecs, samplers, key generation.
2. Stage 1: signing cases. They need secret keys, which are taken from our side's key generation in stage 0 (Cryptol's key generation
   is compared with ours in stage 0, so the two sides sign with the same key). Also our side's attempt counts and the forged boundary
   signatures (below).
3. Stage 2: verification cases, built from the signatures our side produced in stage 1.

Knobs: `DIFF_SCALE` (multiplies the random-case counts; the recorded run used 2), `DIFF_JOBS` (parallel Cryptol
processes, one per chunk of cases; a Cryptol start-up is about one second, a signature takes 3 to 10 minutes), `DIFF_SEED`,
`DIFF_RUN` (work directory, default `$ML_DSA_SCRATCH/cryptol-diff/run`). Output: `$DIFF_RUN/report.txt` (counts per component),
`$DIFF_RUN/mismatches.txt` (every mismatch, deviation and harness error with its input), `$DIFF_RUN/theirs/timing.log`.

Outputs are bound to their inputs. Next to every `ours/<name>.out` and `theirs/<name>.out` is a `<name>.stamp` (sha256 of the vector
file it was computed from, and a digest of the program: our executable, or the Cryptol evaluator, binaries and specification commit).
A side reuses an output only if the stamp matches, so a changed `DIFF_SEED`, generator, build or Cryptol install recomputes it; the
generator's later stages and `compare.py` refuse an output without a matching stamp. Chunk and merged outputs are renamed into place
only on success. A Cryptol worker that exits nonzero (even after printing some results) or times out (`CRYPTOL_TIMEOUT`, default 7200 s)
fails its file: `run_theirs.py` writes no output for it, lists it, and exits 1.

`compare.py` classifies each line as `match`, `deviation` (a difference explained by a documented deviation of `lean/Spec`, listed
below and always printed, never silently accepted), `mismatch` (a finding until a person has classified it) or `harness-error`
(Cryptol printed no result for the line, or an output is missing or stale: the run fails closed). The exit code is 0 iff there is no mismatch and no harness error.

## What is compared with what

`lean/Spec` against four entry points of the Cryptol repository (all four are in `cry/Drv<NN>.cry`):

| Prefix | Cryptol module | Used for |
|---|---|---|
| `S::` | `Specification.cry` (the readable transcription, "closely resembles the standard") | every component, `KeyGen_internal`, `Sign_internal`, `Verify_internal` |
| `O::` | `OptimizedSpecification.cry` (what the public `ML_DSA.cry` is built on; it re-implements `KeyGen_internal` and the bit packers, and reuses `Specification`'s `Sign_internal` and `Verify_internal`) | `KeyGen_internal` |
| `D::` | `Instantiations/ML_DSA_NN.cry`, i.e. `ML_DSA.cry` | `Sign` and `Verify`: Algorithms 2 and 3 with a context and `rnd` as an `Option` |
| `T::` | the `TestAPI` submodule of the same | `KeyGen_internal`, `Sign_internal` |

The three parameter sets are instantiated in `cry/Spec<NN>.cry` and `cry/Opt<NN>.cry` with the values of FIPS 204 Table 1 (the same
values as `Instantiations/ML_DSA_<NN>.cry`). `cry/DiffDrv.cry` has the flat encoders: each Cryptol result is printed as **one**
hexadecimal word prefixed by a 32-bit case number, so nothing depends on Cryptol's pretty printer and a missing or misplaced result is
detected by the case number.

Components (one vector line = one Cryptol evaluation; rounding functions take `k * 256` scalars per line):

- SHAKE128, SHAKE256 (`G`, `H`): input lengths 0, 1, 2, 31, 32, 64, 100, 134-138, 166-170, 271-273, 335-337, 504, 1000, 2500 bytes;
  output lengths 1, 32, 64, 135-137, 167-169, 200, 336, 337, 672 bytes (rate boundaries and several blocks).
- `NTT`, `NTTInv`, `MultiplyNTT` on zero, constant, ramp, unit and random polynomials.
- `Power2Round`, `Decompose`, `HighBits`, `LowBits`, `MakeHint`, `UseHint`: every edge value (0, 1, 2, 3, q-1, q-2, q-3, (q±1)/2, 2^13
  multiples ± 1, multiples of 2γ₂ and 2γ₂·m ± γ₂, ± 1, ± 2, the `Decompose` corner `r - r₀ = q - 1`), `UseHint` with h = 0 and 1 for each
  of them (so with r₀ = 0 and r₁ ∈ {0, m-1}), `MakeHint` on the cross product of edge values, and uniform random scalars.
- `SimpleBitPack`, `BitPack` (all bounds used by FIPS 204), `SimpleBitUnpack`, `BitUnpack` (all-zero, all-0xFF, random bytes: also out of range),
  `HintBitPack`, `HintBitUnpack` (valid hints, hints with a leading index at or below the previous row's last index, and one violation each:
  a decreasing or repeated index, a count byte below the previous one, a count byte above ω or 255, nonzero padding, a count byte that
  claims indices of the next row; random bytes), `pkEncode`/`pkDecode`, `skEncode`/`skDecode`, `sigEncode`/`sigDecode`, `w1Encode` (range
  extremes and random; the decoders also on all-zero, all-0xFF and random bytes, and signatures with a malformed hint section).
- `SampleInBall`, `RejNTTPoly`, `RejBoundedPoly`, `ExpandA`, `ExpandS`, `ExpandMask` (counters from 0 to 65540, including κ + r ≥ 2^16).

Top level, all three parameter sets:

- `KeyGen_internal` from seeds (all-zero, 0..31, random) through `S::`, `O::` and `T::`; our side is one function.
- `Sign` (Algorithm 2) with `rnd` zero and random, on several keys, messages (0 to 100 bytes) and contexts (empty, 1, 5, 255 bytes), and with a
  256-byte context (both sides refuse); `Sign_internal` on a raw M′.
- `Verify` (Algorithm 3) on: the valid signatures (true), and, per valid signature, mutations of the message, the context, c̃ (leading, trailing
  and random bit), z (random bits, the last bit, one coefficient set to ±(γ₁-β-1), ±(γ₁-β), ±(γ₁-β+1), γ₁, -(γ₁-1)), the hint (a flipped
  byte, a flipped count, **the same hint re-encoded non-canonically**: two indices swapped, an index repeated, nonzero padding, a repeated
  index in the padding, a count byte of ω+1; a hint with exactly ω ones; an empty hint), the public key (ρ, leading and trailing byte, random bit),
  and a signature under another key. The non-canonical re-encodings matter: without them a missing check in `HintBitUnpack` could not
  change a verdict.
- **Signatures at the boundary of the z-norm check.** A `z` with ‖z‖∞ = γ₁-β-1 or γ₁-β cannot be produced by flipping bits (the commitment
  hash would fail first), so `spec-diff-cryptol` has a test-only copy of Algorithm 7's loop (`signLoop`) that stops at the earliest attempt with
  ‖z‖∞ exactly γ₁-β-1 (a valid signature: both sides must accept) or exactly γ₁-β, or γ₁-β+1 (a signature that Algorithm 7 would reject, whose
  commitment hash is consistent: both sides must reject it at step 13). `signLoop` is not part of `lean/Spec`; if it were wrong, the forged
  signatures would simply not verify as expected on both sides.

## Mapping between the two representations

| | `lean/Spec` | Cryptol | Handling |
|---|---|---|---|
| Byte string | `List UInt8` | `[n]Byte` (`[n][8]`) | hex |
| Message M, M′ | byte string | bit vector `[m]` | `M = join bytes` (most significant bit of each byte first). Cryptol's `HBits (join x)` equals `H x` and `SHAKE256 x` (the SHAKE tests at the rate boundaries cover it). Messages that are not whole bytes (FIPS 204 allows them) are expressible in Cryptol alone, so they are not tested. |
| Elements of R, R_q, T_q | `Vector Int 256`, `Vector (ZMod q) 256` | `[256]Integer`, `[256](Z q)` | decimal in the vector files; R is printed signed, Z q in [0, q) |
| Hint polynomial | `Vector Bool 256` | `[256]` bit vector, element 0 the most significant bit | rows as index lists in the vector files (`-` for an empty row) |
| Key/signature lengths | `Verify_internal` step 0 returns `false` for a wrong length (FIPS 204 §6.3) | `PublicKey`, `Signature` are fixed-length types: a wrong length is a type error | **not testable here**; just the correct lengths are compared |
| Rejection loops | fuel-bounded, `Option`; `none` on exhaustion | unbounded (lazy infinite streams, recursion) | `none` on our side with a value on Cryptol's is reported as a `mismatch` (not as a deviation) for a person to classify; it has not occurred |
| Algorithm 7's loop | at most `kappaBudget p` attempts, refuses to start an attempt with κ + ℓ > 2^16 | unbounded | not reachable by the cases; ExpandMask itself (`IntegerToBytes (κ + r) 2`, modulo 2^16 on both sides) is compared for κ up to 65540 |
| `rnd`, ξ | an argument (`List UInt8`) | `Option [32]Byte` for `Sign`/`KeyGen` (`None` gives `None`), `[32]Byte` for the internal functions | `Some rnd`; deterministic (all zero) and random `rnd` are both used |
| Algorithm 3, \|ctx\| > 255 | `some false` (NIST's erratum to FIPS 204: step 2 returns `false`) | `None` (the text of the original pseudocode, `⊥`) | `deviation (erratum-alg3)`, always listed. Algorithm 2 with \|ctx\| > 255 returns `none`/`None` on both sides and is compared normally. |
| HashML-DSA, external μ | not in `lean/Spec` | not in the Cryptol specification either | out of scope |
| NTT | the loop of Algorithms 41, 42 | the naive transform of Equation 16 of the NTT guide, bit-reversed output order (`Specification.cry`) | compared on 200+ polynomials; they agree |

## Vector and output formats

One case per line, fields separated by single spaces; byte strings are lower-case hex (`-` for the empty string), integers decimal.
`S` is 44, 65 or 87. The output of both sides is one line in the same canonical text:

| Tag and fields | Output |
|---|---|
| `H256 L hex`, `H128 L hex` | `L` bytes of SHAKE256/SHAKE128 |
| `P2R S r..`, `DEC S r..` (`k * 256` values) | `r1.. ; r0..`, and for `DEC` also `; HighBits.. ; LowBits..` |
| `MH S z.. r..`, `UH S bits r..` | a `0`/`1` string; the integers `UseHint` returns (`bits` is a `0`/`1` string, `k * 256` characters) |
| `NTT c..`, `INTT c..`, `MUL a.. b..` (256 values each) | 256 integers |
| `SBP b w..`, `SBU b hex`, `BP a b w..`, `BU a b hex` | hex; 256 integers |
| `HBP S rows..`, `HBU S hex` | hex; `none` or the rows (comma-separated indices, `-` for an empty row) |
| `PKE`, `PKD`, `SKE`, `SKD`, `SGE`, `SGD`, `W1E` | the encodings or the decoded fields separated by ` ; `; `none` for a malformed hint |
| `SIB S hex`, `RNTT hex`, `RBP S hex`, `EXA S hex`, `EXS S hex`, `EXM S hex κ` | integers (`none` if our fuel ran out) |
| `KG S ξ`, `KGO`, `KGT` | `pk ; sk` (the three Cryptol entry points; ours is the same function) |
| `SGN S sk M ctx rnd`, `SGI S sk M′ rnd` | the signature or `none` |
| `VER S pk M σ ctx` | `true`, `false` or `none` |
| `SGF S sk M ctx rnd lt/eq/gt`, `SGA S sk M ctx rnd` | our side only: a forged boundary signature; the number of attempts |

## Sensitivity: injected bugs

`inject.sh` copies `lean/` to a scratch project (never edits the committed `lean/Spec`), applies one textual edit from `inject.py`,
rebuilds `spec-diff-cryptol`, runs it on the vectors of the last run and compares with the saved Cryptol outputs. The edits: UseHint's
`r₀ > 0` as `r₀ ≥ 0`; `CoeffFromHalfByte` accepting 9 for η = 4; c̃ hashed as `w1Encode ‖ μ` in Sign and Verify; `HintBitUnpack` without
the strictly-increasing check; `HintBitUnpack` without the zero-padding check; Verify's `‖z‖∞ < γ₁-β` as `≤`; Algorithms 2 and 3 refusing
255-byte contexts (it affects `Sign` cases with a 255-byte context as well as `Verify` cases: the table in `results/` has both).
Every injection gets one row: `YES` (at least one mismatching line), `no` (the bug survived) or `ERROR` (the edit, the build or a run
failed, the injected executable is byte-identical to the pristine one, or the comparison had harness errors). The exit status is
nonzero unless every row is `YES`.

`$INJECT_DIR` (the scratch project, default `$ML_DSA_SCRATCH/cryptol-diff/inject-lean`) is validated before anything is written, and
`rsync --delete` runs in it: it must be absent, empty or created by an earlier `inject.sh` (`.inject-scratch` marker), must not be a
symbolic link, `/`, `$HOME` or an ancestor of it, and must not equal, contain or lie inside the repository, a git work tree of it or the
run directory.

`bash scripts/diff-cryptol/selftest.sh` checks the harness against the failures it must not hide (no Lean, no real Cryptol, seconds): a
worker exiting 1 or timing out fails the run and leaves no output, stale outputs are recomputed and refused by `compare.py`, a changed
binary fails the digest check, unsafe `INJECT_DIR` values are refused, a surviving injection is a `no` row and a nonzero exit.

## Files

`setup.sh`, `run.sh`, `inject.sh`, `selftest.sh`, `lib.sh` (shared shell functions), `cryptol-3.6.0.bin.sha256` (digests of the Cryptol
binaries); `stamp.py` (output stamps); `gen_vectors.py` (cases), `cryptol_eval.py` (vector line to Cryptol expression, result word to canonical
text), `run_theirs.py` (parallel driver), `compare.py`, `inject.py`, `common.py`; `cry/` (instantiations and encoders);
`../../lean/SpecTests/DiffCryptol.lean` (our side); `results/` (dated results).
