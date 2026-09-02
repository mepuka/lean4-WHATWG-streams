# Plan: one shared, proved hash library (`lean4-hash`)

Status: **steps 1–6 EXECUTED 2026-09-02** (step 6 here as slice W3 of `docs/WHATWG-PACKAGE-PLAN.md`: `[[require]] hash` at `0168306b7068b97758e3f2d4307eeb97aa31a104`, vendor manifest byte-identical through the package, `Sha256/` removed); step 7 is foldlab's. — `mepuka/lean4-hash` is public at commit `92cb0cf` (S1 skeleton; S2 `Sha256` from streams `a1383bc`; S3 `Sha3` from foldlab `64be4b2c`, both history-preserving; S4 `Hash` API aliases and the combined self-test; S5 assurance record), one ceiling under R-11, every gate rerun green by the coordinator including `leanchecker --fresh Hash.Verified`. Step 6 fired a stop condition on first contact (2026-09-02): Lake module names are global across a workspace, and the package, built from this repository's skeleton, shipped a `Gates.*` tree, `bin.*` executable roots, and executable names identical to this repository's, so `lake build` refused to disambiguate `Gates.Common`. The fix is lean4-hash S6: `Gates` → `HashGates`, `bin` → `hashbin`, executables prefixed `hash_`; step 6 resumes against that pin. Rule recorded in `docs/AGENT-ROUTING.md`: a package cloned from this skeleton prefixes its tooling tree and executable names with its own name. Step 7 (foldlab's consumer) follows; step 9 is optional backlog. Original status: PLAN, ready to execute on the operator's go. The
operator's direction: extract the SHA-256 work into a shared library that
this repository, and foldlab's consumers, depend on; the same library is the
home of the FIPS 202 SHA3-512 work whose S0–S2 cutover was accepted
2026-09-02 in foldlab (`.staging/fips202-library/runs/S2/REVIEW-FINAL.md`,
"ACCEPTED — functional S2 gates complete"; 1 MiB median 0.635 s; not yet
committed there).

Owner: the coordinator. Executing seat: one Opus seat per step 3 packet.

## 1. What is being unified

Two libraries with the same shape, read 2026-09-02:

| | foldlab `formal/fips202` (uncommitted S2 tree) | this repository `Sha256/` (`a8f08d0`, plus S1.5–S1.7 in flight) |
| --- | --- | --- |
| Layers | `Spec` (bit-level FIPS 202), `Impl` (lane-level `BitVec 64`, kernel-reducible), `Fast` (`UInt64`/`ByteArray`), `Bridge` (Impl = Spec), `Fast.sha3_512_eq_impl` | `Spec` (bit-level FIPS 180-4), `Impl` (`BitVec 32`/`List UInt8`), `Fast` (`UInt32`/`ByteArray`), `Bridge`, `Fast.sha256_eq_impl` |
| API | `sha3_512 : ByteArray → Digest 64`, `sha3_512String`, theorems `sha3_512_impl/_spec/_ofList` | `sha256 : ByteArray → Digest 32`, `sha256String`, theorems `sha256_impl/_spec/_ofList`; `Algorithm`/`digest`/`sha224` arriving with S1.6 |
| `Digest n` | `bytes`, `size_eq`; `toByteArray`, `toList`, `toHex`, `ofHex?`, `ext`, `size_toByteArray`, `length_toList`, `length_toHex`, `ofHex?_toHex`, `BEq`, `DecidableEq` | identical names |
| `Hex` | `encode`, `decode?`, `length_encode`, `decode?_encode`, `encode_lower`, lowercase-only | identical names, plus the `List Char` forms `encodeChars`, `decodeChars?`, `length_encodeChars`, `decodeChars?_encodeChars`, `encodeChars_lower` |
| Ceiling | `propext`, `Quot.sound`, `Classical.choice` tolerated | `propext`, `Quot.sound` only; R-3 list empty |
| KATs | four compiled CAVP guards; kernel KATs under `Sha3.Verified` | five compiled CAVP guards; `decide +kernel` W1; self-test replays every record of the sealed `.rsp` |
| Audit | `#sha3_axiom_audit` pinned by `#guard_msgs` | `#sha256_axiom_audit` pinned by `#guard_msgs` |
| Executable | `sha3_512sum` | `lake exe sha256` |
| Toolchain | v4.33.1, zero deps, `warningAsError` | same |

The shapes match because the streams lane copied fips202's A1.S1 on purpose.
Unification is therefore a rename plus one ceiling decision, not a redesign.

## 2. Target package

```text
lean4-hash/                            mepuka/lean4-hash (name to be ruled, HP-1)
  lakefile.toml                        name = "hash"; zero deps; leanOptions as here; testDriver = "HashVerified"
  lean-toolchain                       leanprover/lean4:v4.33.1
  Hash.lean                            root: Digest, Hex, Sha256, Sha3, Algorithm
  Hash/
    Digest.lean  Hex.lean              one shared copy AFTER step 9; until then Hash/Sha256/{Digest,Hex} and
                                       Hash/Sha3/{Digest,Hex} coexist under their own tree ceilings (HP-2)
    Algorithm.lean                     inductive Algorithm | sha256 | sha224 | sha3_512 (| sha3_256 … as S3 lands); outputBytes; digest
    Sha256/{Spec,Impl,Lengths,Bridge,Fast,Vec,Context,Sha224}.lean
    Sha3/{Spec,Impl,Lengths,Structural,Roundtrips,Bridge,BridgeEvidence,Fast}.lean
  HashVerified/                        Sha256/Kats, Sha3/Kats, Sha3/KeccakProbe, the two audits, Verified root
  HashTest/                            counterexample witnesses (WS-SHA-CE-*, the fips202 breaker batteries), axiom gate
  Gates/ + bin/                        sha256, sha3_512sum, vendorseal (for the CAVP files), citations, trustselftest
  vendor/nist-cavp-sha256/, vendor/nist-cavp-sha224/, vendor/nist-cavp-sha3/, vendor/nist-fips-180-4/, vendor/nist-fips-202/
  generated/vendor-manifest.tsv
  test/contracts/                      sha256.contract.md, the fips202 Pass A/Pass B documents, moved
  test/counterexamples/                REGISTER.md with a renumbering table from WS-SHA-CE-* and fips202's ids
  docs/{SHA256-DAG.md, SHA3-DAG.md, PROVENANCE.md, DESIGN-BASIS.md}
  AGENTS.md and the boundary routers, LICENSE (Apache-2.0), .github/workflows/ci.yml
```

Namespace `Hash`: `Hash.sha256`, `Hash.sha224`, `Hash.sha3_512`,
`Hash.Digest`, `Hash.Hex`, `Hash.Algorithm`, `Hash.digest`. Each algorithm's
`Spec`/`Impl`/`Fast`/`Bridge` keep their names under `Hash.Sha256.*` and
`Hash.Sha3.*`.

## 3. Steps, in order, each with its check

| Step | Act | Check |
| --- | --- | --- |
| 0 | Land what is in flight: the S1.5–S1.7 seat's delivery here (streaming, SHA-224, assurance), and the coordinator commits foldlab's S2 tree after its own review. Nothing is extracted from an uncommitted tree. **Half done 2026-09-02: foldlab's S2 tree is committed as `64be4b2c` (not pushed) after the coordinator's recheck: builds green, `leanchecker --fresh Sha3.Verified` exit 0 in 138 s, 1 MiB `sha3_512sum` median 0.823 s on this host.** | both repositories green at the commits the extraction will read |
| 1 | Create `lean4-hash` from this repository's P0 skeleton: six routers, Lean gates, trust self-test, citations gate, CI, LICENSE. | `lake build` green on the empty skeleton; trust self-test green |
| 2 | Move `Sha256/**`, `Sha256.lean`, the SHA counterexamples, contract, and the two NIST pins from this repository with `git filter-repo`, history preserved; rename `Sha256.` to `Hash.Sha256.` and the API to `Hash.sha256`. | `lake --wfail build`; the audit line reports the same declaration count; every receipt identical to `a8f08d0`'s |
| 3 | Move `formal/fips202` from foldlab the same way; rename `Sha3.` to `Hash.Sha3.`; keep every `Sha3` definition, bridge, KAT, `Digest`, and `Hex` statement byte-identical under its own tree ceiling (`propext`, `Quot.sound`, `Classical.choice` tolerated, as fips202 has it). **Strictness parity is deferred by operator ruling (2026-09-02):** the shared `Hash.Digest`/`Hash.Hex` and the restatement of the `String`-typed theorems are step 9, not a gate on extraction; until then `Hash.Sha3.Digest` and `Hash.Sha256.Digest` coexist with an explicit conversion. | `Sha3Verified` closure green; `leanchecker --fresh`; the S2 review's 13 steps re-run in the new package with the same results; the audit gate carries two tree ceilings, each pinned |
| 4 | `Hash.Algorithm` and `Hash.digest` over both families; one self-test that replays every record of every sealed `.rsp`. | compiled guards for every algorithm; self-test PASS lists every file |
| 5 | Dual-host (Windows here, macOS at the operator's coordinator, Ubuntu CI) and `leanchecker --fresh HashVerified`; lean4lean when it targets v4.33.1. | receipts as `(declaration, axiom-set)` pairs |
| 6 | This repository takes the dependency: `[[require]] hash` at an exact commit (the first dependency; `PLAN.md` acceptance probe), `Sha256/**` deleted, `Gates/Sha256.lean` and `Gates/VendorSeal.lean` and `Gates/Census.lean` call `Hash.sha256`. | `generated/vendor-manifest.tsv` and `generated/spec-algorithm-census.tsv` regenerate byte-identically; every gate green; the axiom gate's `Sha256` prefix row removed |
| 7 | foldlab's consumer (`experiments/entity-store-shell`) imports `Hash` instead of `formal/fips202`; `formal/fips202` becomes a pointer file. | its gate green; `mise run check` green |
| 8 | Tag `v0.1.0`; both consumers pin the tag's commit. | clean-clone builds in both |
| 9 | Strictness parity (deferred): unify `Digest`/`Hex`, restate the `String`-typed theorems on `List Char`, retire the `Sha3` tree's `Classical.choice` tolerance. | one package ceiling; audit admission list empty; every statement byte-identical except the five restated theorems, each with its old form kept under a `String`-suffixed name |

Steps 1–5 touch only the new repository. Step 6 is this repository's first
`[[require]]`. Step 7 is foldlab's.

## 4. What must not change

- No `Spec`, `Impl`, or `Bridge` definition body and no bridge or API theorem
  statement changes in either family during the move (steps 1–8; step 9 may
  change `Impl`/`Fast` bodies under ruling P-3 of `docs/HASH-PARITY-PLAN.md`); namespace and the
  `Digest`/`Hex` unification are the only edits, and the S2 review's exact
  refinement `sha3_512_eq_impl` and this repository's `sha256_eq_impl` are
  re-checked byte-for-byte against their landed forms.
- The counterexample witnesses move with their attacked statements and keep
  their `decide +kernel` closure.
- Zero dependencies. The hash library sits below the algebra package and
  below every standard library; it may depend on nothing.
- The CAVP and FIPS pins move as sealed bytes with their blob-hash evidence.

## 5. Rulings owed before step 1

| Id | Question | Default |
| --- | --- | --- |
| HP-1 | Repository name and namespace | `mepuka/lean4-hash`, namespace `Hash` |
| HP-2 | Whose `Digest`/`Hex` survives, and when | **ruled 2026-09-02, then simplified by R-11 the same day: one ceiling (`propext`, `Quot.sound`, `Classical.choice`) for the whole package, no admission lists; both `Digest`/`Hex` copies coexist and their unification is optional backlog.** Earlier text: parity later. Both survive at extraction, each under its tree's ceiling; step 9 unifies on this repository's choice-free forms and restates fips202's `String`-length theorems on `List Char`, after which the package ceiling is `propext`/`Quot.sound` with an empty admission list |
| HP-3 | History-preserving moves from both repositories, or fresh copies with provenance pins | history-preserving (`git filter-repo`), so blame and the fips202 breaker history survive |
| HP-4 | Does foldlab's S2 tree get committed by the coordinator before extraction | yes, after the coordinator's own review of the acceptance report and a gate rerun; no push |
| HP-5 | Order relative to the algebra package (RS-D1, held) | the hash package first: it has no dependency on the Mac work and unblocks step 6 here |
