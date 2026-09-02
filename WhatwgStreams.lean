import WhatwgStreams.Data.Queue
import WhatwgStreams.Data.Chunk
import WhatwgStreams.Data.Strategy
import WhatwgStreams.Data.DyadicSize
import WhatwgStreams.Strategy.CountQueuing
import WhatwgStreams.Strategy.ByteLengthQueuing
import WhatwgStreams.Strategy.Ops
import WhatwgStreams.Readable.Stream
import WhatwgStreams.Readable.DefaultController
import WhatwgStreams.Readable.DefaultReader
import WhatwgStreams.Readable.GenericReader
import WhatwgStreams.Readable.Tee
import WhatwgStreams.Readable.AsyncIteration
import WhatwgStreams.Readable.Byte.Controller
import WhatwgStreams.Readable.Byte.ByobReader
import WhatwgStreams.Readable.Byte.ByobRequest
import WhatwgStreams.Readable.Byte.PullInto
import WhatwgStreams.Writable.Stream
import WhatwgStreams.Writable.DefaultController
import WhatwgStreams.Writable.DefaultWriter
import WhatwgStreams.Writable.Backpressure
import WhatwgStreams.Transform.Stream
import WhatwgStreams.Transform.DefaultController
import WhatwgStreams.Transform.Backpressure
import WhatwgStreams.Piping.Requirements
import WhatwgStreams.Piping.PipeTo
import WhatwgStreams.Piping.PipeThrough
import WhatwgStreams.Boundary.UnderlyingSource
import WhatwgStreams.Boundary.UnderlyingSink
import WhatwgStreams.Boundary.Transformer
import WhatwgStreams.Boundary.AbortSignal
import WhatwgStreams.Boundary.ArrayBuffer
import WhatwgStreams.Semantics.Configuration
import WhatwgStreams.Semantics.Step
import WhatwgStreams.Semantics.Runs
import WhatwgStreams.Semantics.Frontier
import WhatwgStreams.Semantics.Mask
import WhatwgStreams.Semantics.Equivalence
import WhatwgStreams.Logic.Wlp
import WhatwgStreams.Logic.Totality
import WhatwgStreams.Logic.Modality
import WhatwgStreams.Alphabet.Combinators
import WhatwgStreams.Target.TypeScript.Ir
import WhatwgStreams.Target.TypeScript.Lower
import WhatwgStreams.Target.TypeScript.Render
import WhatwgStreams.Target.TypeScript.Decode
import WhatwgStreams.Target.TypeScript.Simulation
import WhatwgStreams.Bridge.NodeStreams
import WhatwgStreams.Bridge.EffectChannel
import WhatwgStreams.Meta.Introspection
import WhatwgStreams.Meta.Emit
import WhatwgStreams.Audit.Receipts
import WhatwgStreams.Audit.Closure

/-!
# WhatwgStreams

Production root of the WHATWG Streams reification library. Every library
module is imported from here; a module not reachable from this root is not
part of the production build and is rejected by the module-closure gate.

The imports above are the P2 breadth scaffold: one module per area and named
sub-area of the planned source tree in `docs/ARCHITECTURE.md`, in that
table's order. Every one of them is a module docstring and nothing else.
P2 declares no semantic object anywhere in this tree; a declaration arrives
only behind a frozen contract packet and its counterexample register.
-/
