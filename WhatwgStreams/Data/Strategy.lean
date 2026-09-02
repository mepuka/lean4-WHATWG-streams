/-!
# Data.Strategy.lean

Owner: queuing-strategy data at the data layer: a size function as
first-order data, a high-water mark, and the desired size read off a queue
against that mark.

Spec anchors: `queuing-strategies`, `queue-with-sizes`.

Opens in P3.

This is the carrier. The specification-facing classes and the abstract
operations that build one live under `WhatwgStreams/Strategy`, which the
architecture table keeps as its own area.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.
-/
