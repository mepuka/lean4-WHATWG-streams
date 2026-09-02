# Specification manifest

This file owns the authority pins, the authority order, and the
section-by-section dispositions of the WHATWG Streams Standard for this
repository. `docs/PROVENANCE.md` owns the fetch record and cross-check of
every digest quoted here; `generated/vendor-manifest.tsv` owns the per-file
digests of the vendored bytes.

Status: P0 pins frozen, 2026-09-01. Dispositions below are the P0 survey;
from P1 the generated census owns every row and this table becomes its
authored input.

## Authority pins

| Authority | Exact pin | Role |
| --- | --- | --- |
| WHATWG Streams Standard source | `whatwg/streams` commit `b9ba9f49d95b4280be0dc2372377a006c3a91c18`, 2026-08-18, "Review Draft Publication: August 2026"; `index.bs` SHA-256 `24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440`, 417,076 bytes | **semantic owner** |
| Streams reference implementation | same commit, `reference-implementation/`; dual CC0 / MIT | second-tier evidence: candidate realizer and reading aid |
| Web Platform Tests `streams/` | `web-platform-tests/wpt` commit `480fdfcd85d043c23875665f464c35c0043dff52`, 2026-09-02; BSD-3-Clause | host conformance corpus |
| Node | v22.23.2 on Windows 11 x86-64 | local host profile via `node:stream/web` |
| Bun | 1.4.0 on Windows 11 x86-64 | local host profile |
| reference implementation under Node | the pinned tree above | local host profile, closest to the text |
| Lean | `leanprover/lean4:v4.33.1`; `lean-toolchain` SHA-256 `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71`; one dependency, `hash` (lean4-hash) at commit `0168306b7068b97758e3f2d4307eeb97aa31a104` | kernel, elaborator, compiler, standard library |
| EffHOL | arXiv:2506.09458v1, 2025-06-11; PDF SHA-256 `a493e698895878136a71e9ffdaaf9ece786cdd30864f853149cd69cec774ad0c` | logic-layer design basis |
| FIPS 180-4 | NIST, August 2015; PDF SHA-256 `0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82` | transcription source for the SHA-256 specification, owned by lean4-hash since the swap; pin moved to lean4-hash in slice W3b of `docs/WHATWG-PACKAGE-PLAN.md`; formerly the S1 SHA-256 specification |
| Process precedent | `mepuka/lean4-effect4` commit `e9075e192bb3065e3900ccabe7c0c2a6df1ddffc`; `mepuka/foldlab` commit `8d36195970b83a1439ec705b9a504617554b8062` (`formal/fips202`) | breaker/builder discipline and the SHA3 refinement precedent; not semantic pins |

The vendored trees are byte-identical to upstream at those commits. Nothing
under `vendor/` is edited; re-pinning moves a whole tree together.

## Authority order

1. `index.bs` at the pin. Where it states an algorithm, the model is that
   algorithm. Where it states requirements, the model is that specification,
   and any algorithm is a candidate realizer.
2. The reference implementation. Evidence, never authority.
3. WPT. Host conformance, never authority.
4. Local host profiles, then published browser results by run identifier.

## Disposition vocabulary

Every census row receives exactly one disposition.

| Disposition | Meaning |
| --- | --- |
| `owned` | modelled in Lean; must carry at least one witness before its coverage row can leave `absent` |
| `requirement` | stated as constraints rather than an algorithm (piping); modelled as a specification φ, realized by a named algorithm |
| `foreignBoundary` | a host-supplied body or host object whose behaviour enters only as typed decisions with a profile: underlying source, sink, and transformer methods; ArrayBuffer detachment; `AbortSignal` |
| `hostOnly` | Web IDL conversions, brand checks, and constructor overload resolution; enforced by the host's IDL layer, recorded as refusals at the boundary |
| `refused` | transferable streams and their `MessagePort` protocol; a refusal theorem states they are outside the model |
| `evidenceOnly` | examples, introductions, and the "other specifications" section; never counted in the denominator |
| `targetOnly` | rows that exist only for the P11 TypeScript profile |

## Section dispositions (P0 survey of `index.bs`)

The survey counted 248 algorithm-block openers beginning `<div algorithm`,
of which 229 are the bare `<div algorithm>` and 19 carry attributes, and
about 8,400 lines (the earlier figure of 7,041 was a non-blank line count).
The survey's "66 distinct internal slot names" was an overcount of four:
`[[FETCH]]`, `[[COMPRESSION]]`, `[[ENCODING]]`, and `[[WEBSOCKETS]]` are
Bikeshed bibliography citations that never occur in the escaped or
autolinked slot spelling (verified by the coordinator at P1 landing); the
census carries 62 `slot` rows. The P1 census keys on the `<div algorithm`
prefix, not the closing bracket, which is what keeps those 19 blocks. From
P1 the generated census owns every count. After P1.1: 248 `op`, 133 `idl`
across 20 IDL blocks (including six `typedef`, `enum`, and `includes`
statements), 62 `slot`, 7 `requirement`, denominator 410 with 40 excluded.
Do not quote these as coverage.

| Section id | Title | Disposition | Phase |
| --- | --- | --- | --- |
| `intro`, `model`, `conventions` | introduction, model, conventions | `evidenceOnly` (the model section is a reading aid for masks and backpressure) | — |
| `rs-class` | `ReadableStream` class | `owned`; IDL members `hostOnly` at the boundary | P4 |
| `generic-reader-mixin`, `default-reader-class` | reader mixin, default reader | `owned` | P4 |
| `byob-reader-class`, `rbs-controller-class`, `rs-byob-request-class` | BYOB reader, byte controller, BYOB request | `owned`, separate calculus; ArrayBuffer detach `foreignBoundary` | P9 |
| `rs-default-controller-class` | default controller | `owned` | P4 |
| `rs-all-abstract-ops` | readable abstract operations | `owned`; tee is P4-late; byte ops P9 | P4 / P9 |
| `ws-class`, `default-writer-class`, `ws-default-controller-class`, `ws-all-abstract-ops` | writable stream, writer, controller, abstract operations | `owned` | P5 |
| `ts-class`, `ts-default-controller-class`, `ts-all-abstract-ops` | transform stream, controller, abstract operations | `owned` | P6 |
| `pipe-chains` (model) and `ReadableStreamPipeTo` | piping requirements and the reference algorithm | `requirement` realized by the reference algorithm | P7 |
| `qs-api`, `blqs-class`, `cqs-class`, `qs-abstract-ops` | queuing strategies | `owned` | P3 |
| `queue-with-sizes` | queue-with-sizes | `owned` | P3 |
| `transferrable-streams` | transferable streams | `refused` | — |
| `misc-abstract-ops` | miscellaneous abstract operations | `owned` where used; `hostOnly` for IDL helpers | P3–P7 as consumed |
| `other-specs` | using streams in other specifications | `evidenceOnly` | — |
| `creating-examples`, `acks` | examples, acknowledgments | `evidenceOnly` | — |

Underlying source, sink, and transformer dictionaries (`UnderlyingSource`,
`UnderlyingSink`, `Transformer`) are `foreignBoundary`: their `start`,
`pull`, `cancel`, `write`, `close`, `abort`, `transform`, and `flush` members
are named operations whose invocations are decisions, with the spec's
"if it throws" and "wait for the promise" clauses modelled as answer kinds.

## Promise and job model

The specification is written over ECMAScript promises. Promise-job order is
deterministic under ECMAScript's FIFO job queue, so the job queue is state in
the configuration, not a decision kind. The only decisions are consumer calls,
foreign-boundary answers with their settlement timing, and abort signals. This
is a P0 ruling recorded in `docs/DESIGN-BASIS.md`; P8 tests it against WPT
ordering cases under mask M2.

## Rulings made at P1 landing (2026-09-02)

- ECMAScript promise and completion-record internals (`[[PromiseState]]`,
  `[[PromiseIsHandled]]`, `[[Value]]`) are `foreignBoundary`: they are host
  runtime objects the representation rules exclude from stored content; the
  job queue that settles them is state (DB-03).
- ArrayBuffer and ArrayBufferView internals read by the byte-stream
  algorithms are `foreignBoundary`, consistent with ArrayBuffer detachment.
- The `*-transfer` subsections of the three stream classes are `refused`
  with their two slots; `[[Detached]]` on `ReadableStream`, which exists
  only for that protocol, is `refused` too, by authored override (landed at
  P1.1).
- The three underlying-source, underlying-sink, and transformer dictionaries
  and their members are `foreignBoundary`; every other IDL member is
  `hostOnly` at the boundary.
- `ReadableStreamPipeTo` itself carries disposition `requirement` as the
  reference realizer of the seven piping requirements.
- `typedef`, `enum`, and `includes` statements in the IDL blocks (six at the
  pin) receive `idl` rows with disposition `hostOnly` (landed at P1.1). Two
  of them, the `ReadableStreamController` union typedef and the
  `ReadableStreamType` enum, sit inside the `underlying-source-api` IDL
  block whose section is `foreignBoundary`; they are Web IDL type
  declarations, not dictionary members with host-supplied bodies, so they
  are `hostOnly` by authored override. Ratified by the coordinator at the
  P2 landing, 2026-09-02.

## Open rows

- `ReadableStreamTee` and the async-iteration protocol are `owned` but are
  scheduled after the P4 representative closes.
- `AbortSignal` interaction in piping is `foreignBoundary` with a profile
  fixed at P7.
