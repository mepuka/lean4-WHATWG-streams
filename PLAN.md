# WHATWG Streams reification plan

Status: P0 bootstrap complete, 2026-09-01. Held before P1 for the R0 research
pass.

## Objective

Reify the WHATWG Streams Standard in Lean 4: every abstract operation,
internal slot, IDL member, and stated requirement of the pinned specification
becomes first-order Lean data with proved laws; execution meaning is a
relation over configurations and explicit decisions; an EffHOL-style logic
layer sits above the semantics; the piping requirements are realized by the
reference algorithm as a theorem; and a closed combinator alphabet lowers to
checked TypeScript. Host conformance is measured, never assumed.

## Non-negotiable semantic boundaries

- The specification text is the authority; hosts are evidence
  (`AGENTS.md` "Authority order").
- Authored stream programs and combinators are first-order, finite, versioned
  data.
- Underlying source, sink, and transformer bodies are foreign boundaries with
  profiles; their answers are decisions on the tape.
- Full execution meaning is a relation over configurations, decisions, and
  observations. A fixed compatible tape yields one replay path.
- Every theorem names its observation mask: M1 (chunk sequence plus terminal
  outcome) or M2 (full settlement order).
- Live frontiers are distinct from typed failure, cancellation, abort, and
  refusal.
- Byte streams arrive as their own calculus (P9); transferable streams are
  refused, never modelled.
- TypeScript tooling and runtime observations are evidence targets; Lean owns
  the model and theorem statements.
- Every gate is Lean.

## Ratified decisions (operator, 2026-09-01)

1. Public repository `mepuka/lean4-WHATWG-streams`, default branch `main`.
2. Gates are implemented in Lean; shell only orchestrates.
3. Observation masks M1 and M2 are pre-registered; every theorem names one.
4. Byte streams are deferred to P9; transferable streams are a refusal.
5. Vendored material is retained with its upstream licenses; the reference
   implementation's dual CC0 / MIT license was verified at P0.

## Phase gates

| Phase | Deliverable | Exit gate |
| --- | --- | --- |
| P0 — bootstrap | independent Lake package, exact toolchain, six routers, sealed pins, Lean gates, CI, provenance | `lake build` green; all four gate executables green; pins cross-checked |
| R0 — research hold | implementation-strategy and performance notes for the Lean standard library, and the accumulated text-processing benchmarks from `mepuka/lean4-nlp`, written up as an authored design input | notes landed under `docs/research/`; the P1 census generator's representation decisions cite them |
| P1 — inventory | census generator over `index.bs`: one row per abstract operation, internal slot, IDL member, and stated requirement, anchored by span digest; every row classified | every row has one disposition; the census join gate is green; missing rows fail cutover |
| P2 — breadth scaffold | empty modules for every category, central contracts and counterexample registers, generated assurance schema | no semantic declarations; scaffold build and declaration scan green |
| P3 — queue-with-sizes and queuing strategies | the first representative: total, kernel-reducible operations with their invariants | breaker battery green; laws proved; axiom receipts recorded |
| P4 — readable default path | `ReadableStream` state machine, default controller, default reader | representative contract closed; counterexamples registered |
| P5 — writable | `WritableStream`, its controller and writer, the erroring state and in-flight bookkeeping | representative contract closed |
| P6 — transform | `TransformStream`, its controller, backpressure coupling | representative contract closed |
| P7 — piping | the piping requirements as a specification; the reference `ReadableStreamPipeTo` as a realizer; relational semantics of shutdown | realizability theorem stated and proved under a named mask |
| P8 — configuration and WPT replay | promise-job queue in the configuration, masks as declared projections, bounded runner, WPT replay harness against the three local host profiles | harness green at exact pins; host-profile refusal rows recorded |
| P9 — byte streams | `ReadableByteStreamController`, BYOB reader and request, ArrayBuffer detachment as a foreign boundary | separate calculus with explicit embedding rows |
| P10 — logic | `wlp`, totality, the `wp` decomposition theorem, EffHOL modality instance | decomposition theorem proved for the chosen semantics |
| P11 — targets | closed combinator alphabet, typed TypeScript IR, lowering, render, host harness | typing and simulation proofs; deterministic bytes; exact coverage |
| P12 — bridges | Node legacy streams calculus, Effect Channel embedding (cross-repository) | each bridge names its loss and its mask |
| S1 — SHA-256 proof lane | the three-layer `Spec`/`Impl`/`Fast` SHA-256 with the `Impl = Spec` refinement and the pointwise `Fast = Impl` bridge, a `Digest`/`Hex` API, root split so consumers never pay for kernel known-answer tests, a typed audit line, streaming, and SHA-224, in stages S1.0–S1.7 per `docs/SHA256-DAG.md` | every edge of `SHA256-PG-IMPL-EQ-SPEC` closed; `Gates` consumes `Sha256.sha256` and regenerates `generated/vendor-manifest.tsv` byte-identically; `leanchecker --fresh`, dual-host, and lean4lean receipts recorded |

S1 is independent of P1 through P12 and may run beside any of them. Its
staging, built-ins ledger, do-not-use list, stop conditions, report shape,
budgets, and rulings follow foldlab's fips202 library specification
(`.staging/fips202-library/SPEC.md`, decision 45), adapted to 32-bit words
and to this repository's stricter semantic ceiling. Until S1 closes, the
vendor seal's digests are executable evidence cross-checked against a second
implementation at pin time, and `docs/PROVENANCE.md` says so.

## Broad-before-deep representatives

Before deep work, freeze one representative contract in each group:

1. data: queue-with-sizes with `EnqueueValueWithSize` and `DequeueValue`;
2. readable: one default-controller enqueue/pull/close lifecycle;
3. writable: one write/close with backpressure;
4. transform: one transform with backpressure propagation;
5. piping: one pipe with error propagation and shutdown;
6. configuration: one promise-settlement ordering case from WPT;
7. logic: one `wlp` judgment over a stream program;
8. target: one generated combinator checked by the TypeScript compiler;
9. bridge: one Node legacy stream related in both directions.

## Dependency policy

Lean core and Std are the default substrate. A third-party Lean dependency is
added only after an exact-pin acceptance probe shows that it builds on the
pinned Lean version, has acceptable licensing and transitive cost, supplies a
materially deeper public abstraction, and does not force the library's
representation to narrow accidentally. Borrowed API ideas are credited even
when their implementation is not imported.

## Current phase

P0 is complete. The package is an independent Lean 4.33.1 package with no
dependencies. The six routers exist. The specification source, its reference
implementation, and the WPT `streams/` directory are vendored at exact
commits and sealed by a Lean-checked manifest. The four Lean gate executables
and the elaboration-time axiom gate are green. Every pin has a digest recorded
in `docs/PROVENANCE.md`, cross-checked between the in-tree SHA-256 and a
second implementation.

R0 is complete: all three documents are landed under `docs/research/` with
their decision-bearing findings in `docs/research/README.md`.

**P1 merged into `main` 2026-09-02** (`72b1bfd`), and **P1.1 and P2 landed
2026-09-02**, all reviewed and re-gated by the coordinator. The census
stands at 450 rows (248 `op`, 133 `idl`, 62 `slot`, 7 `requirement`),
denominator 410; the coverage block reads `denominator 410;
owned-with-green 0/410; green 0, partial 0, absent 410; census 450 rows, 40
excluded`. P2 placed 52 declaration-free breadth stubs under
`Whatwg/Streams/`, one per area and named sub-area of the architecture
table, every one reachable from the root and audited (78 modules). Lane S1
landed the same day (`a8f08d0`): every digest the repository pins is
computed by the proved SHA-256. The RS-D1 algebra package is planned in
`docs/ALGEBRA-PACKAGE-PLAN.md` and held until the operator's incoming
lean4-effect4 work lands.

**Landed 2026-09-02:** S1.5–S1.7 (merge `a1383bc`: streaming `Context`
with the buffered-update law, SHA-224 proved end to end, lean4lean stopped
at its own toolchain gate) and the P3 breaker (merge of `p3/queue-breaker`:
72 frozen ascriptions, 99 theorems red, 44 green witnesses, `DATA-PG-QUEUE`).
`P3-R1` is ruled in `docs/DATA-DAG.md`: an exact size carrier with binary64
rounding as a foreign boundary. Main is deliberately red on the two declared
battery modules until the P3 builder lands; the trust self-test is the
deciding gate meanwhile and CI builds the production targets.

**The algebra dependency is settled by the operator on the Mac:**
`mepuka/lean4-effects` v0.1.0 (commit `5611c3a`) is the standalone
`Effects.Algebra` package, already required by lean4-effect4 at that
commit; its README names WHATWG Streams as the first web-standard
reification built against it. RS-D1 and `docs/ALGEBRA-PACKAGE-PLAN.md` are
therefore superseded. This repository takes `[[require]] effects` when the
first Stratum S packet (P4) opens; P3 is Stratum V data and needs nothing
from it.

**P3 landed 2026-09-02:** the builder proved all 99 frozen theorems with zero battery edits (447 declarations from the two fenced modules, 375 axiom-free, 2 at `[propext, Quot.sound]`), the coordinator allocated the ruled `P3-R1` instance to `Whatwg/Streams/Data/DyadicSize.lean`, the known-red set is empty again, and every gate is green. The first breaker-then-builder packet of the streams calculi is closed; `DATA-PG-QUEUE` has every applicable edge closed. The coverage numerator packet landed 2026-09-02: the block reads `denominator 410; owned-with-green 12/410; green 12, partial 6, absent 392; census 450 rows, 40 excluded`, printed from the Lean emit and refused on any disagreement. **Reorganization (operator, 2026-09-02):** `lean4-hash` finished at `0168306`. This repository becomes the single `whatwg` package, one library per standard, per `docs/WHATWG-PACKAGE-PLAN.md`; hash step 6 is its slice W3 and the effects require its slice W4. P4 and foldlab step 7 wait for W5.

**Operator direction 2026-09-02: the SHA-256 lane and foldlab's accepted
SHA3-512 library are extracted into one shared hash package that this
repository depends on.** `docs/HASH-PACKAGE-PLAN.md` owns the steps; it
runs after the S1.5–S1.7 seat lands (step 0) and lands here as the first
`[[require]]` (step 6), with byte-identical regeneration of both generated
projections as the cutover proof.

P1 was opened by the operator on the R0 evidence, delegated to
one seat in the worktree branch `p1/census` while lane S1's builder holds
the main tree. The census generator's representation decisions are fixed
by that evidence: `ByteArray` and `Nat` offsets, never `String` positions;
fuel-bounded scanning; rows keyed on the `<div algorithm` opener prefix (248
openers, 19 with attributes); span digests through the in-tree SHA-256;
`decide +kernel` for any kernel check; `Std.HashMap` allowed, `Std.TreeMap`
and `Lean.Json` not. Exit gate unchanged: every row has one disposition, the
census join gate is green in both directions, and a byte-for-byte drift gate
regenerates the census into a clean tree. Lane S1 runs beside P1.

## Near-term proof burden

| Order | Owner | Assurance route | Required work before advancing |
| ---: | --- | --- | --- |
| 0 | R0 research | authored design input | land `docs/research/` notes; decide the `index.bs` parsing representation and the byte-span digest strategy from measured data |
| 1 | P1 census generator | generated projection with drift gate | one row per algorithm, slot, IDL member, requirement; anchors occur exactly once; span digests computed by the in-tree SHA-256 |
| 2 | P2 scaffold | none (no declarations) | every category module exists and is reached by the default build |
| 3 | P3 queue-with-sizes | proof graph `DATA-PG-QUEUE` | breaker packet frozen red; builder closes construction, laws, counterexamples, trust |
| S1 | SHA-256 | proof graph `SHA256-PG-IMPL-EQ-SPEC` | **S1.1–S1.4 landed 2026-09-02 (`a8f08d0`)**: `Impl = Spec` and `Fast = Impl` proved at the semantic ceiling, manifest regenerated through the proved library. Open: S1.5 streaming, S1.6 SHA-224, S1.7 dual-host and lean4lean; the trust edge stays open until S1.7 |
