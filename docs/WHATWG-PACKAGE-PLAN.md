# Plan: `lean4-whatwg`, one package for the WHATWG standards

Status: **EXECUTED W0–W5, 2026-09-02.** This is the reorganization the
HOLD in `COORDINATION.md` was placed for. It follows the family ruling in
lean4-effect4 `docs/EFFECTS-SPLIT-PLAN.md` §7: one repository per package
that Reservoir lists, so this repository becomes the single `whatwg`
package with one Lean library per standard, growing from the Streams work
here. It supersedes the packaging half of `docs/ALGEBRA-PACKAGE-PLAN.md`
(RS-D1) and executes step 6 of `docs/HASH-PACKAGE-PLAN.md`.

Facts were read at `main` `6e4c334`; `lean4-hash` at `0168306` (S6 landed,
requirable); `lean4-effects` at `v0.1.0` = `5611c3a`.

## 1. Target shape

```text
lean4-whatwg/                       renamed from lean4-WHATWG-streams (GitHub redirects)
  lakefile.toml                     name = "whatwg"; requires hash and effects by exact commit
  Whatwg.lean                       root: imports every standard's root
  Whatwg/
    Streams.lean  Streams/**        the Streams Standard (today's WhatwgStreams/**)
    Infra.lean    Infra/**          the Infra Standard (W5: pin and empty library, no declarations)
  WhatwgTest.lean, WhatwgTest/      Streams/** (today's WhatwgStreamsTest/**), Audit/** (the gate)
  Gates.lean, Gates/, bin/          unchanged names; root detection moves to Whatwg.lean
  census/, harness/, vendor/, generated/, test/, docs/   unchanged
```

Declaration namespaces: `WhatwgStreams.X` → `Whatwg.Streams.X`,
`WhatwgStreamsTest.X` → `WhatwgTest.Streams.X`; test infrastructure that is
not Streams-specific (the axiom gate, coverage rows) lives under
`WhatwgTest.Audit`. The `Sha256`/`Sha256Verified` libraries, the `sha256`
executable, the `Sha256/` tree, the `Sha` counterexample, and the three NIST
vendor pins leave: `lean4-hash` owns them and is required instead.

## 2. Rulings

| Id | Question | Ruling |
| --- | --- | --- |
| WP-1 | Repository name | `lean4-whatwg`, by GitHub rename of `lean4-WHATWG-streams`; old URLs redirect |
| WP-2 | Namespace and module casing | `Whatwg`, the casing Lean and this repository already use (`WhatwgStreams`), not `WHATWG` |
| WP-3 | Test tree | one `WhatwgTest` library; Streams batteries under `WhatwgTest/Streams/`, the gate and coverage under `WhatwgTest/Audit/` |
| WP-4 | Hash pin | `[[require]] hash` at exact commit `0168306`; a tag follows when lean4-hash's license switch lands; the vendor manifest must regenerate byte-identically through `Hash.Sha256.sha256` (the cutover proof HASH-PACKAGE-PLAN names) |
| WP-5 | Effects pin | `[[require]] effects` at `5611c3a` (`v0.1.0`), taken now with the S5 acceptance probe recorded (exact pin, license, zero transitive packages, build); PLAN's "when P4 opens" becomes "P4 imports it" |
| WP-6 | Infra | W5 pins the Infra Standard source at an exact `whatwg/infra` commit under the `docs/PROVENANCE.md` protocol and adds an empty `Whatwg.Infra` library; no census and no declarations until its own P1 |
| WP-7 | Evidence of the rename | a parity receipt over every constant of the renamed modules (name, module, kind, universes, `pp.all` type and value, axioms) with the prefixes normalised, byte-identical before and after, committed under `generated/` with its check in CI; the technique of lean4-effects `scripts/AlgebraParity.lean` |
| WP-8 | Streams-specific documents | keep their names; `SPEC-MANIFEST.md`, `docs/SPEC-COVERAGE.md`, and the census stay Streams-scoped until Infra has its own; each gains a one-line scope note |

## 3. Slices

| Slice | Work | Exit gate |
| --- | --- | --- |
| W0 | this plan; HOLD text in `COORDINATION.md` and `PLAN.md` replaced by a pointer here | `lake exe citations` |
| W1 | GitHub rename to `lean4-whatwg`; Mac remote updated; PC worktrees noted for later | `gh api repos/mepuka/lean4-whatwg` resolves; old URL redirects |
| W2 | package, tree, namespace, root, gate, census-generator, CI, fixture, and document rename; parity receipt | `lake --wfail build` of every target, all gate executables, `lake exe trustselftest`, parity check PASS, census and vendor seal byte-identical |
| W3 | hash step 6: require `hash`, delete the Sha256 lane and NIST pins, `Gates.Sha256` calls `Hash.Sha256`, CI drops the Sha256 steps, PROVENANCE names the new cross-check | vendor manifest and census regenerate byte-identically; `lake exe vendorseal` green; `lake-manifest.json` has exactly the hash package at an exact commit |
| W4 | effects: require and probe (S5 of the split) | manifest has exactly two packages; build green; probe receipts in `PLAN.md` |
| W5 | Infra pin and empty library | seal regenerated; `Whatwg.Infra` reachable and declaration-free; SPEC-MANIFEST and PROVENANCE rows |

Nothing semantic changes in any slice: no theorem statement, no body, no
census row, no counterexample ID. W2's parity receipt and W3's byte-identical
regenerations are the proof.

## 4. Ledger

| Slice | Commit | Result |
| --- | --- | --- |
| W0 | `f5dbad8` | plan landed; HOLD replaced by the pointer |
| W1 | GitHub rename, no commit | `mepuka/lean4-whatwg` resolves; `mepuka/lean4-WHATWG-streams` redirects to it; Mac remote repointed |
| W2 | this commit | 42 files rewritten by one ordered rule set plus the tree moves; `lake --wfail build` of every library and executable green; gate: 85 modules, 2404 declarations, ceiling unchanged; `trustselftest`, `census`, `census --report` (coverage block unchanged: denominator 410, green 12, partial 6), `vendorseal`, `citations`, `sha256 --self-test` all PASS; `generated/spec-algorithm-census.tsv` and `generated/vendor-manifest.tsv` byte-identical; parity receipt PASS over 963 constants against `f5dbad8` (`generated/whatwg-parity*.tsv`, `scripts/check-whatwg-parity.sh`, now a CI step). Excluded from the receipt by design: the gate module `WhatwgTest.Audit.AxiomGate`, whose message strings name the tree. Not edited: the frozen packets under `test/contracts/` (their `WhatwgStreams…` paths are the packets' original text), `docs/research/`, and the copied plans |
| W3a | this commit | `[[require]] hash` at `0168306b7068b97758e3f2d4307eeb97aa31a104` (one package in the manifest); `Sha256/`, `Sha256.lean`, `bin/Sha256.lean`, the `Sha256`/`Sha256Verified` libraries, the `sha256` executable, and the Sha mutants counterexample removed; `Gates/Sha256.lean` and `Gates/VendorSeal.lean` compute through `Hash.Sha256`; the gate audits two semantic trees; `lake --wfail build` green, gate 69 modules / 1636 declarations; **`lake exe vendorseal` PASS with `generated/vendor-manifest.tsv` byte-identical, the cutover proof**; census PASS; trust self-test PASS; parity PASS over 936 constants (the 27 Sha-mutant rows left the source receipt with the lane, noted in `generated/whatwg-parity.source.txt`). The three NIST vendor pins stay for W3b |
| W3b | this commit | `vendor/nist-fips-180-4`, `vendor/nist-cavp-sha256`, `vendor/nist-cavp-sha224` removed; `generated/vendor-manifest.tsv` regenerated with only their rows gone; `lake exe vendorseal` and `lake exe census` PASS; PROVENANCE and SPEC-MANIFEST rows point to lean4-hash |
| W4 | this commit | `[[require]] effects` at `5611c3a` (tag `v0.1.0`); manifest has exactly two packages; probe recorded in `PLAN.md` (exact pin, Apache-2.0 at the tag, zero transitive packages, same toolchain, `lake build effects/Effects` green); own build, trust self-test, vendor seal green |
| W5 | this commit | `vendor/whatwg-infra-3f984adc/{infra.bs,LICENSE}` at `whatwg/infra` `3f984adc` sealed; `vendorseal` digests equal an independent `shasum -a 256`; `Whatwg/Infra.lean` declaration-free and reached from `Whatwg.lean`; SPEC-MANIFEST, PROVENANCE, ARCHITECTURE, SPEC-COVERAGE scope notes; build, gates, and the parity receipt unchanged (no declarations added) |
