/-!
# Readable.Tee.lean

Owner: the tee algorithms: the two-branch split of one readable stream, its
shared cancel bookkeeping, and the byte-stream variant that reads into the
branches separately.

Spec anchors: `rs-abstract-ops`, `rbs-controller-abstract-ops`.

Opens in P4 for the default tee; the byte tee waits for P9.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/
