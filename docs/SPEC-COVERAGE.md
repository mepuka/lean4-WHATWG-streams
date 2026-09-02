# Specification coverage

This document owns the definition, vocabulary, and reporting format of the
specification coverage metric. Numbers live in generated and emitted facts,
never here. Read this before quoting, changing, or extending coverage.

## What the metric measures

Coverage is the share of pinned specification *rows* that have a Lean
witness. A row is an abstract operation, an internal slot, an IDL member, or
a stated requirement of `index.bs` at the pin, anchored to its text by span
digest. It is not an implementation checklist and not a conformance claim.

Three artefacts carry it once P1 lands:

| Artefact | Role | Owner |
| --- | --- | --- |
| `generated/spec-algorithm-census.tsv` | the denominator: one row per specification row, anchored to the pinned bytes with a span digest | the P1 census generator under `Gates/` |
| `WhatwgStreamsTest/Audit/SpecCoverage.lean` | the numerator: the frozen row list with disposition, coverage state, witnesses, receipts, and exact witness statements | authored, test-side |
| a Lean census gate | byte drift of the census and the join between census and Lean rows | CI step |

The pinned source is `vendor/whatwg-streams-b9ba9f49/index.bs`; the
generator refuses any other bytes.

## Vocabulary

**Row kinds** (`kind` column, fixed): `op` (an abstract operation or
algorithm block), `slot` (an internal slot), `idl` (an IDL attribute,
method, or constructor), `requirement` (a stated requirement, as in piping),
`rule` (a cross-cutting rule the text states in prose). A row id is
`<kind>.<kebab-name>` and is stable for the life of the census.

**Disposition** is the `SPEC-MANIFEST.md` vocabulary and answers who owns the
row's carrier. `evidenceOnly`, `refused`, and `targetOnly` rows are outside
the denominator and may carry no witness. Every other disposition counts.
`owned` and `requirement` rows must carry at least one witness before they
leave `absent`.

**Coverage state** answers what has been proved about the row today:

| State | Meaning | Rule |
| --- | --- | --- |
| `absent` | no witness | the only state allowed with an empty witness list |
| `partial` | at least one witness, but some step or clause of the row has no theorem | must list what is missing in the row's comment |
| `green` | every step or clause of the row is a named theorem over the Lean model, with an axiom receipt inside `propext`/`Quot.sound`, under a named observation mask | never declared to make a number move |

The green criterion is step-by-step against the algorithm text. A finite
probe, a compile, a WPT pass, or a theorem about the Lean model's own
invariants does not turn a step green. When in doubt the state is `partial`.

**Witness**: a Lean `theorem` (never a `def`, never a Prop-typed def) whose
exact statement is frozen in the module's `StatementSnapshot` section by
`#check (@name : proposition)` ascription, and whose kernel receipt is
`none`, `propext`, `Quot.sound`, or `propext,Quot.sound`.

## The report format

The only sanctioned way to state coverage is the block printed by the
coverage report gate, which runs the Lean emit and prints:

```text
WHATWG Streams (b9ba9f49) coverage: denominator <D>; owned-with-green <O>/<D>;
green <G>, partial <P>, absent <A>; census <total> rows, <E> excluded
partial: <ids>
```

Quote that block verbatim, with the commit it was produced at. Do not compute
a percentage by hand, do not round, and do not describe a row as covered in
prose unless it is `green` in the module. A handoff, plan row, or pull
request that mentions coverage links the gate run and pastes the block. It
never restates numbers from memory or from an earlier session.

## How the number moves

**Adding a witness** happens in the coverage module only: add the theorem
name and its receipt to the row's witnesses; add the exact statement as a
`#check (@…` ascription and append the name to the snapshot list in the same
order; change the row's state only if the green criterion is met; keep the
totals true; run the census gate.

**Adding or re-pinning a census row** happens in the generator only. A row is
`kind|id|anchor|offset-start|offset-end|expected-span-sha256|summary`, where
the anchor occurs exactly once in `index.bs`. A digest that drifts because
upstream changed is a deliberate re-pin: the whole pin moves together, never
one row.

## Path to full coverage

Coverage rises by building models, not by relabelling rows. The families and
the phase that closes each: queue-with-sizes and strategies (P3); readable
default path (P4); writable (P5); transform (P6); piping requirements (P7);
promise-job configuration and mask M2 rows (P8); byte streams (P9).

Take exact row counts from the census, never from this document.
