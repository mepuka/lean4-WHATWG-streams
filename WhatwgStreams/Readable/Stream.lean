/-!
# Readable.Stream.lean

Owner: the `ReadableStream` state as a first-order record: the readable,
closed and errored cases as constructors, the disturbed and locked flags,
and the stream-level abstract operations over them.

Spec anchors: `rs-class`, `rs-internal-slots`, `rs-abstract-ops`.

Opens in P4.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/
