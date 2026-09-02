# Provenance

Every pin this repository relies on, with its digest, how it was fetched, the
cross-check performed, and its license. `SPEC-MANIFEST.md` owns what each pin
is for; this file owns that the bytes are what they are claimed to be.

Digest cross-check protocol at P0: every digest is computed by the in-tree
`lake exe sha256` and independently by PowerShell `Get-FileHash -Algorithm
SHA256`; both spellings must agree. The in-tree implementation is executable
evidence until `docs/SHA256-DAG.md` closes; the second implementation is the
reason a wrong in-tree digest could not have entered this file silently.

## Vendored, sealed

| Pin | Fetched | Command | Cross-check |
| --- | --- | --- | --- |
| `whatwg/streams` @ `b9ba9f49d95b4280be0dc2372377a006c3a91c18` (2026-08-18T11:17:34Z, "Review Draft Publication: August 2026") | 2026-09-01 | `git clone --filter=blob:none https://github.com/whatwg/streams` then `git checkout b9ba9f49…`; copied `index.bs`, `LICENSE`, `README.md`, and `reference-implementation/{lib/**, package.json, README.md, LICENSE.md, COPYING.txt, run-web-platform-tests.js, compile-idl.js}` | every one of the 54 files matches the upstream git blob object hash from `git ls-tree -r b9ba9f49…` (checked with `git hash-object --no-filters`); `index.bs` `24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440`, 417,076 bytes, agrees between both SHA-256 implementations and with `raw.githubusercontent.com` at the commit; every file's digest is in `generated/vendor-manifest.tsv` |
| `web-platform-tests/wpt` @ `480fdfcd85d043c23875665f464c35c0043dff52` (committer date 2026-09-02T02:49:23Z) | 2026-09-01 | sparse clone: `git sparse-checkout set streams`, `git fetch --depth 1 --filter=blob:none origin 480fdfcd…`, `git checkout FETCH_HEAD`; copied `streams/**` and `LICENSE.md` | every one of the 123 files matches the upstream git blob object hash from `git ls-tree -r 480fdfcd…`; per-file digests in `generated/vendor-manifest.tsv`; `LICENSE.md` `5fac07febb0e2a97fb0d7b0def149ec08b642e1ba4b9c345283ab1cbd2af6570`; `streams/piping/general.any.js` also agrees with `raw.githubusercontent.com` at the commit |

Vendored licenses: WHATWG Streams Standard, CC-BY 4.0 with BSD-3-Clause for
portions incorporated into source code (`vendor/whatwg-streams-b9ba9f49/LICENSE`,
`85dc6f5ccb57a6fe8c33d158f9fc8fc7ee5655a5d3db2cdd131c6a3d0f48a864`); reference
implementation, dual CC0 / MIT (`reference-implementation/LICENSE.md`,
`2d301992ca987e748f1b9d6eb2d591acf074fff828883887228eee3732fc0f79`); WPT,
BSD-3-Clause. All three permit retention with attribution; the upstream
license files are retained in place.

`.gitattributes` disables end-of-line conversion for the whole repository
(`* -text`), so a checkout on any host reproduces the committed bytes and the
seal holds without a host-specific `core.autocrlf` setting.

**Why the blob-hash check exists.** The first P0 vendoring copied the
whatwg/streams files out of a Windows working tree, where that repository's
own `text` attributes had converted every text file to CRLF on checkout;
`git archive` applied the same conversion. The in-tree SHA-256 and
`Get-FileHash` agreed with each other on those bytes, and the seal passed,
because both were measuring the converted file. Only a comparison against
GitHub's raw content exposed the 8,401-byte difference in `index.bs`. The
vendored files were then rewritten directly from the upstream blob objects
(`git cat-file blob <sha>`), and every file in both trees is now verified
against `git ls-tree` object hashes, which cannot be affected by any
attribute or host setting. Two agreeing digests of the same wrong bytes are
not provenance; the reference point has to be upstream's own identity of the
object.

The reference implementation's `node_modules` and its own test runner
dependencies are not vendored. Running it as a host profile installs its
pinned npm dependencies outside `vendor/` (P8).

## Not vendored, digest only

| Pin | Fetched | Command | Digest | Cross-check | Why not vendored |
| --- | --- | --- | --- | --- | --- |
| EffHOL: Liron Cohen, Ariel Grunfeld, Dominik Kirst, Étienne Miquey, *Syntactic Effectful Realizability in Higher-Order Logic*, arXiv:2506.09458v1, published 2025-06-11T07:02:23Z, LICS 2025 | 2026-09-01 | `Invoke-WebRequest https://arxiv.org/pdf/2506.09458v1`; metadata from `http://export.arxiv.org/api/query?id_list=2506.09458` | `a493e698895878136a71e9ffdaaf9ece786cdd30864f853149cd69cec774ad0c`, 777,345 bytes | both implementations agree | arXiv redistribution terms not verified; the digest identifies the exact bytes any reader can fetch |
| NIST FIPS 180-4, *Secure Hash Standard*, August 2015 | 2026-09-01 | `Invoke-WebRequest https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf` | `0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82`, 833,315 bytes | both implementations agree | US Government work; vendoring deferred to S1, where its Pass A transcription cites it section by section |

## Toolchain and hosts

| Pin | Evidence |
| --- | --- |
| `leanprover/lean4:v4.33.1` | `lean-toolchain` SHA-256 `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`, both implementations agree; `elan show` lists the toolchain as installed |
| Node v22.23.2 | `node --version` on the P0 host |
| Bun 1.4.0 | `bun --version` on the P0 host |
| P0 host | Windows 11 (NT 10.0.26200), AMD Ryzen 7 8700F |

## Process precedents (not semantic pins)

| Source | Commit | Used for |
| --- | --- | --- |
| `mepuka/lean4-effect4` | `e9075e192bb3065e3900ccabe7c0c2a6df1ddffc` | the router hierarchy, breaker/builder order, counterexample register, assurance threshold, the axiom gate (ported to `WhatwgStreamsTest/Audit/AxiomGate.lean`), the coverage-metric discipline |
| `mepuka/foldlab` `formal/fips202` | `8d36195970b83a1439ec705b9a504617554b8062` | the Pass A / Pass B contract shape and the spec-to-implementation refinement decomposition reused by `docs/SHA256-DAG.md`; its `TOOLING-NOTES.md` requirements on gates as checked programs |

## Pending

| Row | Needed by | State |
| --- | --- | --- |
| NIST CAVP `SHA256ShortMsg.rsp` (CAVS 11.0, generated 2011-03-15), SHA-256 `294ecec26959357405a621121bbfb01db4d45b9e834624b2d71aedd94ffde019`, 10,031 bytes, read from the lean-crypto-hash clone at `54e6068abd4658fd91203cae1c2316188ffa0e89` under foldlab `.reference/clones/` | S1.0 | digest recorded; vendored into this repository and sealed at S1.0 (`docs/SHA256-DAG.md` §3.4); `SHA224ShortMsg.rsp` from the same clone at S1.6 |
| kim-em/lean-crypto-hash prior art, commit `54e6068abd4658fd91203cae1c2316188ffa0e89`, Apache-2.0, toolchain v4.33.0 | S1 | read first-hand 2026-09-01; no code imported; API shapes and the streaming technique are credited in `docs/SHA256-DAG.md` §3.5 |
| foldlab `.staging/fips202-library/SPEC.md` (decision 45, R-1 approved 2026-09-01) | S1 | the staging discipline `docs/SHA256-DAG.md` adapts; at foldlab commit `8d36195970b83a1439ec705b9a504617554b8062` plus the uncommitted working-tree file read 2026-09-01 |
| wpt.fyi run identifiers for Chromium, Gecko, WebKit at the WPT pin | P8 | not recorded |
| reference implementation npm dependency lock at the pin | P8 | not installed |
| `mepuka/lean4-nlp` benchmark corpus commit | R0 | not yet read |
