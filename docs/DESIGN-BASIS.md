# Design basis

This repository adopts a spec-authoritative first-order reification with a
relational semantics over explicit decisions, an EffHOL-style logic layer
above that semantics, and separately gated host evidence. The cited
literature motivates the interfaces; it does not prove that the Lean model is
the WHATWG Streams Standard or any host.

Status: adopted at P0, 2026-09-01. Every `DB-*` decision below is a ruling
about representation and claim scope. No semantic claim is established by
this document.

## DB-01 — the specification text is the semantic owner

The WHATWG Streams Standard, at the commit pinned in `SPEC-MANIFEST.md`, is
written as explicit algorithms over named internal slots, with one section
(piping) written as requirements. That form is the reason this target was
chosen over Node's legacy streams, whose behaviour is defined only by an
implementation. Each Lean declaration models one named algorithm, slot, IDL
member, or requirement, anchored by the span digest of its text.

Transcription fidelity is an irreducible human-trust step, as it was for
fips202's FIPS transcription. It is mitigated by the algorithm census, by
per-step theorem witnesses, by the reference implementation as a second
reading, and by WPT replay. It is stated, never claimed away.

## DB-02 — state is first-order; hosts are decisions

Internal slots become fields of first-order records. Where the specification
states an invariant in prose ("exactly one of these is set"), the model uses
constructors that make the other shapes unconstructible. Host-supplied
bodies, the underlying source, sink, and transformer methods, are not
modelled as computations. Each invocation is a decision on the tape whose
answer kinds mirror the specification's own case analysis: a returned value,
a synchronous throw, or a promise that later settles with a value or reason.
`AbortSignal` and ArrayBuffer detachment are foreign boundaries with
profiles. Transferable streams are refused.

## DB-03 — meaning is relational over decisions; promise jobs are state

Full execution meaning is a family of judgments over configurations,
decision tapes, observable events, and terminal outcomes. With no tape
fixed, the meaning of a stream program is a relation. Fixing a complete
compatible tape yields one replay path.

The decision kinds are consumer calls, foreign-boundary answers with their
settlement timing, and abort signals. ECMAScript's promise-job queue is
FIFO and deterministic, so it is state inside the configuration, not a
decision kind. This is a ruling, tested at P8 against WPT's settlement-order
cases under mask M2; if a host exhibits an ordering the FIFO model cannot
produce, that is a host-profile refusal row, not a model repair.

Divergence is witnessed by an infinite run or by compatible finite prefixes,
never by running out of fuel. Fuel exhaustion and unanswered decisions are
live frontiers, distinct from errored, closed, aborted, cancelled, and
refused. The event-and-continuation organization follows Interaction Trees
and the visible-choice organization follows Choice Trees, as in lean4-effect4;
neither is adopted as a carrier.

## DB-04 — two pre-registered observation masks

Every theorem names one mask:

- **M1** — the sequence of chunks delivered to a consumer and the terminal
  outcome (closed, errored with reason, cancelled with reason, aborted with
  reason).
- **M2** — M1 plus the full order of promise settlements observable by the
  consumer, including `ready`, `closed`, `desiredSize` reads, and read
  results.

Equivalence, refinement, and conformance claims are made under a named mask
and nowhere else. A disagreement between two models or between a model and
a host is a theorem or a refusal only relative to a mask. WPT ordering cases
count toward M2 only.

## DB-05 — piping is a specification realized by an algorithm

The standard specifies `ReadableStreamPipeTo` by requirements on error and
close propagation, shutdown, and backpressure, and states that
implementations may satisfy them however they like. The model states those
requirements as a specification φ over runs, and the reference
implementation's algorithm as one candidate realizer. The flagship theorem
of P7 is that the realizer's runs satisfy φ under mask M1. This is the
EffHOL organization applied where the standard already has that shape.

## DB-06 — EffHOL contributes the logic layer, not the carrier

[EffHOL](https://arxiv.org/abs/2506.09458) (Cohen, Grunfeld, Kirst, Miquey,
LICS 2025) parameterizes effectful realizability by a monad and a program
modality, and separates kinds, types, programs, logical indices, expressions,
and specifications. This repository follows that organization: the stream
semantics precede the logic, and `wlp`, totality, and realizability live in
`Whatwg/Streams/Logic`, never in the state machines.

The angle modality `<x <- p> φ` is classified as a weakest liberal
precondition, `wlp`, not a total `wp`, because the paper permits
`<x <- p> false` to be derivable for some `p`. The total-correctness layer
owes the decomposition

```text
wp p post <-> wlp p post /\ total p
```

for the chosen semantics before any judgment is called `wp`. That is a P10
obligation. EffHOL's constructive soundness theorem is evidence about EffHOL,
not a proof of this repository's instance.

## DB-07 — fixed fuel is an approximation, not a denotation

A bounded runner reports completion, an observable terminal result, or a
live frontier. There is no general fixed-fuel bind law; composition and
coherence are proved at the big-step face. Finite approximations satisfy
monotonicity, compatibility, and coherence laws: a completing observation
cannot later become an unrelated failure, and a live leaf may be refined by
more execution without first being reclassified as an error.

## DB-08 — hosts are profiles

The reference implementation, Node's `node:stream/web`, and Bun are host
profiles. A harness result names its host, version, platform, WPT commit,
observation mask, and command. A host that disagrees with the specification
yields a host-profile refusal row. Browser engines enter only through
published WPT results cited by run identifier.

## DB-09 — every gate is Lean

Every decision about whether the tree is green is made by a Lean program
under the pinned toolchain and audited by the same axiom gate as the proofs:
SHA-256, the vendor seal, the citation gate, and the trust self-test. Shell
files only orchestrate. The axiom gate forbids `Lean.ofReduceBool`, which
excludes `native_decide` and `bv_decide` from every proof in this repository.

## DB-10 — the SHA-256 the gates depend on has its own proof graph

Digests decide what bytes this repository trusts. The in-tree SHA-256 is
executable evidence cross-checked against a second implementation until
`docs/SHA256-DAG.md` closes its `Impl = Spec` refinement under the fips202
discipline. No document may call it verified before then.

## Primary sources

- WHATWG, [Streams Standard](https://streams.spec.whatwg.org/), source at
  commit `b9ba9f49d95b4280be0dc2372377a006c3a91c18`.
- WHATWG, Streams reference implementation, same commit.
- web-platform-tests, `streams/` at commit
  `480fdfcd85d043c23875665f464c35c0043dff52`.
- Liron Cohen, Ariel Grunfeld, Dominik Kirst, and Étienne Miquey,
  [*Syntactic Effectful Realizability in Higher-Order Logic*](https://arxiv.org/abs/2506.09458),
  arXiv v1, 2025-06-11, LICS 2025.
- Li-yao Xia et al.,
  [*Interaction Trees: Representing Recursive and Impure Programs in Coq*](https://arxiv.org/abs/1906.00046).
- Nicolas Chappe et al.,
  [*Choice Trees: Representing Nondeterministic, Recursive, and Impure Programs in Coq*](https://arxiv.org/abs/2211.06863).
- NIST, [FIPS 180-4, *Secure Hash Standard*](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.180-4.pdf), August 2015.
- Lean, [source at `v4.33.1`](https://github.com/leanprover/lean4/tree/v4.33.1).
- `mepuka/lean4-effect4` at `e9075e192bb3065e3900ccabe7c0c2a6df1ddffc` and
  `mepuka/foldlab` `formal/fips202` at `8d36195970b83a1439ec705b9a504617554b8062`,
  as process precedents.
