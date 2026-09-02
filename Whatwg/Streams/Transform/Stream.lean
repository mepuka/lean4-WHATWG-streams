/-!
# Transform.Stream.lean

Owner: the `TransformStream` state as a first-order record: the readable and
writable halves it owns, the backpressure change signal, and the
stream-level abstract operations.

Spec anchors: `ts-class`, `ts-internal-slots`, `ts-abstract-ops`.

Opens in P6.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/
