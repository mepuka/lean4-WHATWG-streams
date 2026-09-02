# Agent routing and continuity

This repository uses six authored instruction files. They separate
repository-wide law from source, test, tooling, host, and generated-output
work without repeating the same rule in several directories.

## Instruction hierarchy

| File | Applies to | Additional authority |
| --- | --- | --- |
| `AGENTS.md` | the whole repository | development order, authority order, representation rules, claims, gates, handoffs |
| `Whatwg/AGENTS.md` | Lean library declarations and proofs | source ownership, spec anchors, assurance routes, proof-graph obligations, the semantic ceiling |
| `WhatwgTest/AGENTS.md` | Lean tests and proof receipts | attacks, counterexample witnesses, known-red declaration, coverage witnesses, audit admissions |
| `Gates/AGENTS.md` | Lean-implemented gates | totality, the implementation ceiling, the PASS/FAIL reporting rule, projection writes |
| `harness/AGENTS.md` | host evidence | exact host profiles, WPT replay, refusal rows |
| `generated/AGENTS.md` | deterministic machine projections | regeneration and drift rules |

The root file applies everywhere. The nearest boundary file adds rules for its
own work but does not restate or weaken the root. A conflict is an ownership
error: stop and repair the routers instead of choosing whichever wording is
more convenient.

These six files are written and reviewed by people. No generator may create,
replace, or edit an `AGENTS.md` file. `Gates/` has its own router because it
is a distinct trust boundary: tooling that reads files and spawns processes
under a wider axiom ceiling. Add another boundary router only when a
directory gains a distinct owner, trust boundary, or toolchain that these six
cannot route accurately.

## Authored facts and generated facts

Instructions and semantic decisions remain authored. Machine projections
make those decisions inspectable and detect drift; they do not decide policy.

| Authored input | Machine projection |
| --- | --- |
| the vendored pinned bytes | `generated/vendor-manifest.tsv` |
| the pinned `index.bs` and authored row anchors | the specification algorithm census (P1) |
| public Lean declarations and theorem statements | declaration and signature snapshot |
| `SPEC-MANIFEST.md` dispositions | disposition snapshot |
| contracts and declared proof obligations | graph obligations and leaf-receipt ledger |
| theorem names, axiom receipts, counterexample rows, leaf receipts | per-declaration assurance snapshot |
| harness runs | host-profile conformance and refusal coverage |

The projections live under `generated/`. Their generator, canonical inputs,
and exact regeneration command are recorded before the output becomes a
gate. The gate regenerates into a clean tree and compares bytes. A drift
failure is repaired in the authored input or generator, never by editing the
projection.

## Public declaration records

Every planned public declaration is covered by one lightweight authored record
before implementation. The record names its intended stable Lean name and
module, unique owner and role, the specification anchor it models with that
anchor's span digest, its disposition from `SPEC-MANIFEST.md`, its
relationship to any canonical owner, and its assurance route. That
relationship is the duplication check: `canonical`, `view`, `adapter`,
`separate-calculus`, `derived`, or `helper`, with the related public
declaration named whenever the record is not canonical.

Routine constructors, projections, and theorems may inherit from their public
type when the generated declaration snapshot still emits and joins their
individual records. Inheritance expands the named type or contract row's
owner, disposition, duplicate-prevention relationship, and assurance route
across those declarations deterministically. It does not permit an exported
declaration to disappear from the census. A source stub with no exported
declarations needs neither a declaration record nor a proof graph.

## Existing-type annotation

Every public type has one disposition row before implementation starts. The
authored row records:

1. its stable public Lean name and owning module;
2. whether it is the canonical carrier, a view, an adapter, a separate
   calculus, a derived expansion, a foreign boundary, or target-only data;
3. the specification section, algorithm, or slot it models, with the span
   digest of that text at the pin;
4. the contract that first fixes its role;
5. the disposition from `SPEC-MANIFEST.md`;
6. any type it replaces, views, embeds into, or is intentionally separate
   from; and
7. its assurance route: either its own proof-graph identifier, or a local
   leaf-receipt identifier marked `standalone` or linked to the shared parent
   graph edge to which those receipts contribute.

The generated declaration snapshot must join every exported type to exactly
one such row. An unannotated exported type, two canonical owners for one
semantic role, or two rows claiming the same specification anchor is a gate
failure.

An additional representation is permitted only when its role is distinct and
named: raw versus checked input, syntax versus denotation, a host view. Its
row names the canonical owner and the conversion, embedding, erasure, or
refusal theorem that relates the two. Renaming an existing carrier or copying
its constructors does not establish a new role and is rejected as duplication.

## Assurance threshold

A public type or declaration does not receive a proof graph merely because it
is public. Use the lightest route that accounts for its actual claims. Attach
one graph to the smallest stable semantic or cutover owner; its public helper
operations and theorems contribute receipts to that graph rather than each
receiving another graph.

A `leaf-receipt` route is allowed only when all of the following hold:

1. the declaration is a nonrecursive finite alphabet or passive value record;
2. construction has no checked invariant beyond the field or constructor
   types;
3. it owns no admission, refusal, diagnostic, judgment, denotation,
   interpreter, transition law, reification, refinement, generation, or
   semantic bridge;
4. it states no nontrivial composition law, recursive invariant, protocol
   transition law, or external semantic equivalence; and
5. it does not independently own a profile-admission or cutover claim.

Such a leaf closes with local receipts for the public facts it actually
claims: exact declaration and recursor signatures, constructor census and
`Nodup` where finite, encode/decode inverse or injectivity where exposed,
declared separation or embedding lemmas, and axiom output for exported
theorems. A standalone leaf records that it has no parent. A leaf that
contributes evidence to a graph-bearing family links its receipts to one
named edge of that graph. The leaf does not get an empty ten-edge graph
filled with `not-applicable` rows.

A `graph` route is required as soon as the declaration or its owning type does
any one of the following:

- admits, rejects, refuses, or classifies stream states, decisions, or
  failures;
- defines a typing or operational judgment, denotation, observation mask,
  transition system, interpreter, or runner;
- owns a semantic reification, refinement, lowering, or generation relation,
  or claims a relation to generated code;
- carries nontrivial composition, recursion, backpressure coupling, resource
  invariants, or protocol-state invariants;
- claims conformance or semantic equivalence across a Lean, host, or
  external-library boundary; or
- independently owns a profile-admission or cutover claim that is not wholly
  accounted for by a named parent graph.

Escalation is monotone. Before a leaf acquires the first graph-bearing claim,
change its authored assurance route, name the new obligations and applicable
counterexamples, and freeze the breaker packet for that change. Every former
leaf receipt, counterexample, and evidence link remains required and is
mapped to a named graph edge. A receipt may disappear only through an
explicit supersession ruling that names its replacement and explains the
change. Constructor count, a short proof, or automatic `deriving` never
decides the route.

## The ten edges

Every proof graph carries the same ten edges, each `required-open`,
`required-closed`, or `not-applicable` with a stated reason: identity,
construction, semantics, laws, representation, counterexamples, bridges,
targets, trust, coverage. `docs/SHA256-DAG.md` is the first instance.

## Packages cloned from this skeleton (ruled 2026-09-02)

Lake resolves module names globally across a workspace. A package created
from this repository's P0 skeleton must therefore rename its tooling tree
and executable roots and executable names with its own prefix before any
consumer can `[[require]]` it: `Gates.*` becomes `<Name>Gates.*`, `bin.*`
becomes `<name>bin.*`, and `sha256`, `vendorseal`, `citations`,
`trustselftest` become `<name>_…`. Library roots (`Whatwg`, `Hash`,
`Effects`) are already unique by construction. The first collision cost one
seat-run: `lean4-hash` at `92cb0cf` could not be required by this repository
until its S6 rename.
