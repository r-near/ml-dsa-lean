# ACVP ML-DSA vectors (vendored subset)

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
