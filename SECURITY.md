# Security policy

`ml-dsa-lean` is a personal, best-effort project. It is not audited, not FIPS-validated, and not an official product
of any company or organization. See "Status" below before relying on it.

## Reporting a vulnerability

Please report privately through GitHub's private vulnerability reporting:

1. Open the repository's **Security** tab.
2. Choose **Report a vulnerability**.
3. Describe the problem, ideally with a minimal reproducer (inputs, parameter set, commit or version).

Please do not open a public issue or pull request for a suspected vulnerability, and do not post details elsewhere
until a fix or an advisory is out. There is no email address for reports; if the Security tab does not show **Report a
vulnerability**, open a public issue that says only that you need a private channel, without any details.

## What to expect

This is maintained in spare time, so there is no SLA. The aim is to acknowledge a report within about a week and to say
whether it is in scope, but that is not a promise. A confirmed issue is fixed on `main`, then published as a GitHub
security advisory (with a CVE where one applies) that credits you unless you prefer otherwise. If a fix needs more
time than you can wait, say so in the report; coordinated disclosure with a deadline you propose is fine.

## Supported versions

Only the latest release and `main`. There are no backports.

## In scope

- **The crate's cryptography**: KeyGen, Sign and Verify (FIPS 204 ML-DSA-44, -65 and -87) in `src/`. Examples: a
  signature that verifies when it should not, a valid signature rejected, a panic, hang or out-of-bounds access on
  attacker-chosen input, a disagreement with FIPS 204 or with a known-answer vector, and memory-safety problems in the
  `unsafe` AVX2 dispatch (feature `avx2`).
- **Secret handling**: secret-dependent timing or branches in the compiled code that the documentation says are not
  there, and secret material left behind that the `zeroize` documentation says is wiped. The constant-time evidence
  and its limits are in `docs/object-code-assurance.md`; the wipe claims are in the `api` module documentation.
- **The proofs' claimed scope**: a Lean theorem listed in `lean/headline-theorems.txt` that is wrong about what it
  says, a use of `sorry` or a non-standard axiom that the axiom gate (`scripts/check-axioms.sh`) misses, or a mismatch
  between the Lean specification (`lean/Spec`) and FIPS 204 that makes a documented claim false. The claims, their
  premises and what they do not cover are in `docs/assurance.md`. A gap that the documentation already lists as not
  covered is not a vulnerability, but a correction to the documentation is welcome as a normal issue.
- **The build and CI configuration** in this repository (workflows, scripts) if it could let someone run code or
  read secrets they should not be able to.

## Out of scope

- Vulnerabilities in other software: report them to the project concerned (for example `aws-lc-rs`, RustCrypto
  `ml-dsa`, the Lean toolchain, Mathlib or Aeneas). The first two are used as test oracles only.
- Test, benchmark and measurement tooling (`tests/`, `fuzz/`, `bench/`, `checkct/`, `crosscheck/`, `tools/`) unless the
  problem reaches the library or its proofs.
- Properties the project does not claim: for example the theorems are about the source semantics, not the compiled
  object code, the Lean model does not cover stack exhaustion or out-of-memory, and constant-time evidence is for the
  targets and builds listed in `docs/object-code-assurance.md`.
- Side channels that need physical access, fault injection or a hostile co-resident process beyond the documented model.
- Denial of service from resource exhaustion through intended, documented behavior.

## Status

Not audited and not for production use unless you have reviewed it yourself. "Verified" in the repository means Lean
proofs of stated properties under stated assumptions (`docs/assurance.md`), and there is no third-party audit or
CMVP validation. A proof does not rule out a mistake in the specification, in the toolchain that extracted the code, or in the
compiler.
