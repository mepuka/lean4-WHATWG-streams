/-!
# Piping.PipeTo.lean

Owner: the reference `ReadableStreamPipeTo` algorithm as one candidate
realizer of the piping requirements, with its shutdown, abort and
finalization steps.

Spec anchors: `rs-abstract-ops`.

Opens in P7.

The requirements it realizes are owned by
`WhatwgStreams/Piping/Requirements.lean`; realizability is a claim about the
pair, under a named observation mask.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/
