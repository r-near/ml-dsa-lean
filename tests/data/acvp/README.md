# ACVP ML-DSA vectors (vendored subset)

These are NIST ACVP test vectors (public data published by NIST in the ACVP-Server repository). They are vendored as a
subset, gzipped, and used only by the tests; they are not part of the published crate. For the terms of use, see the
repository's license and notices at the commit below.

- Source: https://github.com/usnistgov/ACVP-Server, directory `gen-val/json-files/`
  (`ML-DSA-keyGen-FIPS204`, `ML-DSA-sigGen-FIPS204`, `ML-DSA-sigVer-FIPS204`).
- Commit: `975de31eb83d87039ec88934fdc47d8c312b892d` (commit date 2026-08-12), fetched 2026-10-29 with
  `git clone --depth 1 --filter=blob:none --sparse`.
- Files used: `internalProjection.json` from each folder (prompt and expected results merged, includes `sk`/`rnd`).
- Subset: made by `make_subset.py` (`make_subset.py <json-files dir> tests/data/acvp 5`).
  - All test groups are kept: 3 parameter sets x internal/external x pure/preHash x deterministic/hedged x externalMu.
  - `keyGen.json.gz`: complete (3 groups x 25 cases).
  - `sigGen.json.gz`: first 5 cases per group (24 groups, 120 cases).
  - `sigVer.json.gz`: 5 cases per group (12 groups, 60 cases), chosen round-robin over `reason` so the valid case and
    every failure mode (message, commitment, z, hint) are present. The unused `sk` field is dropped.
- Format: compact JSON of the original `internalProjection.json` structure, gzipped (read with `flate2` in `tests/acvp.rs`).
- Encoding notes: hex is upper case. sigGen/sigVer `signatureInterface: internal` carries `message` = M' directly (or `mu`
  when `externalMu`); `external` carries `message` + `context` (+ `hashAlg` for preHash). Hedged sigGen cases carry `rnd`;
  deterministic ones use rnd = 32 zero bytes. sigGen provides the expanded `sk` (not a seed) and `pk`.

## Upstream notice

The vectors are NIST-developed material from the ACVP-Server repository. Modifications: on 2026-10-29 the files listed above
were reduced to the subset described above, re-serialized as compact JSON (the unused `sk` field dropped from sigVer) and
gzipped by `make_subset.py`; no vector values were changed. Source: the National Institute of Standards and Technology.
The ACVP-Server license notice at the commit above, reproduced in full:

> NIST-developed software is provided by NIST as a public service. You may use, copy, and distribute copies of the software in any medium, provided that you keep intact this entire notice. You may improve, modify, and create derivative works of the software or any portion of the software, and you may copy and distribute such modifications or works. Modified works should carry a notice stating that you changed the software and should note the date and nature of any such change. Please explicitly acknowledge the National Institute of Standards and Technology as the source of the software.
>
> NIST-developed software is expressly provided "AS IS." NIST MAKES NO WARRANTY OF ANY KIND, EXPRESS, IMPLIED, IN FACT, OR ARISING BY OPERATION OF LAW, INCLUDING, WITHOUT LIMITATION, THE IMPLIED WARRANTY OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, NON-INFRINGEMENT, AND DATA ACCURACY. NIST NEITHER REPRESENTS NOR WARRANTS THAT THE OPERATION OF THE SOFTWARE WILL BE UNINTERRUPTED OR ERROR-FREE, OR THAT ANY DEFECTS WILL BE CORRECTED. NIST DOES NOT WARRANT OR MAKE ANY REPRESENTATIONS REGARDING THE USE OF THE SOFTWARE OR THE RESULTS THEREOF, INCLUDING BUT NOT LIMITED TO THE CORRECTNESS, ACCURACY, RELIABILITY, OR USEFULNESS OF THE SOFTWARE.
>
> You are solely responsible for determining the appropriateness of using and distributing the software and you assume all risks associated with its use, including but not limited to the risks and costs of program errors, compliance with applicable laws, damage to or loss of data, programs or equipment, and the unavailability or interruption of operation. This software is not intended to be used in any situation where a failure could cause risk of injury or damage to property. The software developed by NIST employees is not subject to copyright protection within the United States.
