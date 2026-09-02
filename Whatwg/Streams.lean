import Whatwg.Streams.Data.Queue
import Whatwg.Streams.Data.Chunk
import Whatwg.Streams.Data.Strategy
import Whatwg.Streams.Data.DyadicSize
import Whatwg.Streams.Strategy.CountQueuing
import Whatwg.Streams.Strategy.ByteLengthQueuing
import Whatwg.Streams.Strategy.Ops
import Whatwg.Streams.Readable.Stream
import Whatwg.Streams.Readable.DefaultController
import Whatwg.Streams.Readable.DefaultReader
import Whatwg.Streams.Readable.GenericReader
import Whatwg.Streams.Readable.Tee
import Whatwg.Streams.Readable.AsyncIteration
import Whatwg.Streams.Readable.Byte.Controller
import Whatwg.Streams.Readable.Byte.ByobReader
import Whatwg.Streams.Readable.Byte.ByobRequest
import Whatwg.Streams.Readable.Byte.PullInto
import Whatwg.Streams.Writable.Stream
import Whatwg.Streams.Writable.DefaultController
import Whatwg.Streams.Writable.DefaultWriter
import Whatwg.Streams.Writable.Backpressure
import Whatwg.Streams.Transform.Stream
import Whatwg.Streams.Transform.DefaultController
import Whatwg.Streams.Transform.Backpressure
import Whatwg.Streams.Piping.Requirements
import Whatwg.Streams.Piping.PipeTo
import Whatwg.Streams.Piping.PipeThrough
import Whatwg.Streams.Boundary.UnderlyingSource
import Whatwg.Streams.Boundary.UnderlyingSink
import Whatwg.Streams.Boundary.Transformer
import Whatwg.Streams.Boundary.AbortSignal
import Whatwg.Streams.Boundary.ArrayBuffer
import Whatwg.Streams.Semantics.Configuration
import Whatwg.Streams.Semantics.Step
import Whatwg.Streams.Semantics.Runs
import Whatwg.Streams.Semantics.Frontier
import Whatwg.Streams.Semantics.Mask
import Whatwg.Streams.Semantics.Equivalence
import Whatwg.Streams.Logic.Wlp
import Whatwg.Streams.Logic.Totality
import Whatwg.Streams.Logic.Modality
import Whatwg.Streams.Alphabet.Combinators
import Whatwg.Streams.Target.TypeScript.Ir
import Whatwg.Streams.Target.TypeScript.Lower
import Whatwg.Streams.Target.TypeScript.Render
import Whatwg.Streams.Target.TypeScript.Decode
import Whatwg.Streams.Target.TypeScript.Simulation
import Whatwg.Streams.Bridge.NodeStreams
import Whatwg.Streams.Bridge.EffectChannel
import Whatwg.Streams.Meta.Introspection
import Whatwg.Streams.Meta.Emit
import Whatwg.Streams.Audit.Receipts
import Whatwg.Streams.Audit.Closure

/-!
# Whatwg

Production root of the WHATWG Streams reification library. Every library
module is imported from here; a module not reachable from this root is not
part of the production build and is rejected by the module-closure gate.

The imports above are the P2 breadth scaffold: one module per area and named
sub-area of the planned source tree in `docs/ARCHITECTURE.md`, in that
table's order. Every one of them is a module docstring and nothing else.
P2 declares no semantic object anywhere in this tree; a declaration arrives
only behind a frozen contract packet and its counterexample register.
-/
