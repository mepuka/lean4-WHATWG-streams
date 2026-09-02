# lean4-WHATWG-streams

A Lean 4 reification of the WHATWG Streams Standard: the specification's
algorithms and internal state as first-order Lean data with proved laws, a
relational semantics over explicit decisions, an EffHOL-style logic layer
above it, and, later, a checked lowering of a closed combinator alphabet to
TypeScript.

The semantic authority is the specification source, `index.bs`, at one pinned
commit. The specification's own reference implementation is second-tier
evidence. Web Platform Tests are the host conformance corpus, replayed against
named host profiles. No host defines the model.

Current state: **P0 bootstrap complete, pre-release.** The package builds, the
Lean-implemented gates run, the pinned sources are sealed, and no semantic
declaration exists yet. Nothing here claims that any stream behaviour has been
modelled or proved.

## Build and gates

The toolchain is pinned by `lean-toolchain` to exactly
`leanprover/lean4:v4.33.1`, with no Lake dependencies. Consumers of the
`Sha256` library take that exact pin, not a floor (ruling R-9 in
docs/SHA256-DAG.md); every proof receipt in this repository is stated
against that kernel. Everything below runs from any directory inside the
checkout.

```text
lake build                       # libraries, the elaboration-time axiom gate, the gate executables
lake exe sha256 --self-test      # the in-tree SHA-256 against the FIPS 180-4 vectors
lake exe vendorseal              # vendor/ against generated/vendor-manifest.tsv, both directions
lake exe citations               # no line-numbered citation into a protected authored document
lake exe trustselftest           # planted partial/unsafe/choice/sorry/native_decide/malformed/unreachable are each rejected
```

Every gate is Lean. Shell files, where they exist, only orchestrate.

## Where to start

- [`AGENTS.md`](AGENTS.md) routes all work in this repository.
- [`PLAN.md`](PLAN.md) owns the phases, their exit gates, and the current phase.
- [`SPEC-MANIFEST.md`](SPEC-MANIFEST.md) owns the authority pins and the
  section-by-section dispositions of the specification.
- [`docs/DESIGN-BASIS.md`](docs/DESIGN-BASIS.md) records the adopted
  architecture and the role of each primary source, including EffHOL.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) owns module boundaries.
- [`docs/PROVENANCE.md`](docs/PROVENANCE.md) records every pin with its
  digest, fetch command, and cross-check.
- [`docs/SHA256-DAG.md`](docs/SHA256-DAG.md) is the proof plan for the SHA-256
  the gates depend on.
- [`docs/REIFICATION-STRATEGY.md`](docs/REIFICATION-STRATEGY.md) is the
  draft cross-standard design: three strata of one effects algebra, the
  specification dependency graph as a handler tower, two realizers per
  signature. A living document under refinement.
- [`docs/research/README.md`](docs/research/README.md) indexes the research
  passes and the findings decisions rest on.

## Process

This repository follows the breaker/builder discipline developed in
[lean4-effect4](https://github.com/mepuka/lean4-effect4): a contract packet
and red battery are frozen by a separate process before any implementation,
every declaration-changing counterexample receives a stable ID, every
semantic owner closes a ten-edge proof graph, and no claim uses the words
"sound", "equivalent", "preserves", or "complete" without naming the exact
judgment, observation mask, theorem, assumptions, and remaining host boundary.

## Licensing of vendored material

`vendor/whatwg-streams-b9ba9f49/` carries the WHATWG Streams Standard source
(CC-BY 4.0, with BSD-3-Clause for portions incorporated into source code) and
its reference implementation (dual CC0 / MIT). `vendor/wpt-480fdfcd/` carries
the Web Platform Tests `streams/` directory (BSD-3-Clause). Each tree keeps
its upstream license file. Nothing under `vendor/` is edited.
