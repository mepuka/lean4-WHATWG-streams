# WhatwgStreams Lean-test routing

This boundary contains executable Lean attacks, examples, conformance
checks, and proof receipts. The repository root rules remain in force;
`docs/AGENT-ROUTING.md` defines the shared type-assurance and counterexample
route.

## Breaker ownership

A breaker freezes a contract and its red battery before the corresponding
implementation. A builder may repair test elaboration without changing the
attacked statement, witness, or acceptance condition, but does not weaken or
delete a breaker-owned test.

Every counterexample that can alter a declaration or cutover decision receives
a stable ID in `test/counterexamples/REGISTER.md`. Put the executable Lean
witness under `WhatwgStreamsTest/Counterexamples/<Area>/` and link it from
the registry and owning contract. Keep the witness after the implementation
rejects it so the repair remains testable.

A frozen red battery is declared in `test/fixtures/trust-gate/known-red.txt`
for the duration of its red phase, and removed the moment the builder turns it
green. The trust self-test checks that declaration in both directions.

## Evidence classes

Tests distinguish theorem evidence, finite executable probes, model checks,
and host observations. A passing example does not become a general law. A
compile-time rejection records the exact rejected declaration or term rather
than relying on an error-message substring unless the diagnostic text itself
is the contract.

Axiom reports cover every exported theorem named by a graph trust edge or leaf
receipt set and record the actual dependencies. Conformance tests name both
observations being compared, the observation mask, and any loss admitted by
the bridge. Creating a test does not by itself force a proof graph: passive
finite alphabets and value records remain on the leaf-receipt route unless
they acquire a semantic or cutover-bearing claim.

## Spec coverage witnesses

`WhatwgStreamsTest/Audit/SpecCoverage.lean`, once P1 lands it, is the
numerator of the specification coverage metric: one frozen row per census
algorithm, its disposition, coverage state, witnesses with axiom receipts, and
every witness statement frozen by `#check (@name : proposition)` ascription. A
witness is a `theorem` whose receipt stays inside the ceiling (`propext`,
`Quot.sound`, `Classical.choice`, ruling R-11); a row is `green` only when
every step of its algorithm is a named theorem or an assertion discharged by
typing.
`docs/SPEC-COVERAGE.md` owns the rules.

## Audit implementation

`WhatwgStreamsTest/Audit/AxiomGate.lean` is the one module admitted to the
implementation ceiling in this tree, by exact name, because `MetaM` reaches
`Classical.choice`. Another audit module is admitted only by adding its exact
name to the gate's list, where a stale entry fails the build.

Before handoff, run the narrow file directly and the default Lake build. Link
the exact command and result to the affected proof-graph edge or leaf receipt;
do not mark the whole type closed from one green test.
