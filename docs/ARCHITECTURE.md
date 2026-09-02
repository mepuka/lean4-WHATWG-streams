# Architecture

## Dependency direction

```text
first-order data (queue-with-sizes, chunks, strategies)
  -> per-class state machines (readable, writable, transform)
  -> piping requirements and realizers
  -> configuration, step relation, runs, observation masks
  -> logic (wlp, totality, EffHOL modality)
  -> combinator alphabet and typed targets
  -> host conformance harnesses
```

Nothing in `WhatwgStreams/` depends on `Gates/`, `WhatwgStreamsTest/`, or
`harness/`. `Gates/` depends on nothing in `WhatwgStreams/`. The test tree
imports both.

## Planned source tree

| Area | Public responsibility |
| --- | --- |
| `WhatwgStreams/Data` | queue-with-sizes, chunk universe, size functions, high-water marks, desired size |
| `WhatwgStreams/Strategy` | the IDL class surface that reads the strategy slots; the two strategy records, their size functions, and the extraction operations live in `WhatwgStreams/Data/Strategy.lean` under `DATA-PG-QUEUE` (ownership repaired at the P3 landing, 2026-09-02) |
| `WhatwgStreams/Readable` | `ReadableStream` state, default controller, default reader, generic reader mixin, tee, async iteration |
| `WhatwgStreams/Readable/Byte` | byte controller, BYOB reader and request, pull-into descriptors (P9) |
| `WhatwgStreams/Writable` | `WritableStream` state, default controller, default writer, backpressure |
| `WhatwgStreams/Transform` | `TransformStream`, its controller, backpressure coupling |
| `WhatwgStreams/Piping` | the piping requirements as a specification; the reference `pipeTo` algorithm as a realizer; `pipeThrough` |
| `WhatwgStreams/Boundary` | foreign-boundary profiles: underlying source, sink, and transformer answers; abort signals; ArrayBuffer detachment |
| `WhatwgStreams/Semantics` | configuration with the promise-job queue, labeled step relation, runs, frontiers, observation masks, equivalence |
| `WhatwgStreams/Logic` | `wlp`, totality, the `wp` decomposition, the EffHOL modality instance |
| `WhatwgStreams/Alphabet` | the closed combinator alphabet as first-order data |
| `WhatwgStreams/Target/TypeScript` | typed target IR, lowering, rendering, decoding, simulation |
| `WhatwgStreams/Bridge` | Node legacy streams calculus and Effect Channel embedding (P12) |
| `WhatwgStreams/Meta` | declaration introspection and deterministic emitters |
| `WhatwgStreams/Audit` | per-packet axiom receipts and closure snapshots |
| `Sha256` | the S1 proven SHA-256: `Spec`, `Impl`, bridge (separate library at the semantic ceiling; `Gates` consumes `Impl`) |

Tests mirror these areas under `WhatwgStreamsTest/`. Durable attacks live
under `WhatwgStreamsTest/Counterexamples/`, while their stable registry and
contracts live under `test/`.

## Public API principles

- Internal slots are fields of first-order state records; the XOR invariants
  the specification states in prose become constructors, not checked
  booleans.
- Abstract operations are total functions of state and decision, or
  relations where the specification leaves a choice.
- Every theorem names its observation mask.
- Host objects, promises, and closures never appear in state. A promise is a
  first-order record with a settlement status and the job-queue position of
  its reactions.
- Runtimes eliminate stream programs but never become canonical program
  data.
- Metaprogramming emits first-order declarations and digests, never stores
  raw `Lean.Expr` as semantic content.

## Observation faces

The library keeps four faces distinct:

1. structural syntax for induction and construction;
2. first-order checked state and combinator data for identity, sharing, and
   generation;
3. relational step and big-step meaning over explicit decisions;
4. executable bounded runners and host harnesses for decidable evidence.

Theorems relate these faces explicitly. No bounded runner is promoted into
the denotation merely because it executes, and no WPT pass is promoted into a
theorem.
