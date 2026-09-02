/-!
# Writable.Stream.lean

Owner: the `WritableStream` state as a first-order record: the writable,
erroring, errored and closed cases, the in-flight write and close
bookkeeping, and the stream-level abstract operations.

Spec anchors: `ws-class`, `ws-internal-slots`, `ws-abstract-ops`.

Opens in P5.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/
