import Gates
import WhatwgTest.Streams.Counterexamples.Data.Queue
import WhatwgTest.Streams.Data.QueueContract
import WhatwgTest.Streams.Data.QueueAxiomReport
import WhatwgTest.Html.DecideBenchmark
import WhatwgTest.Html.Lattice
import WhatwgTest.Html.Builders
import WhatwgTest.Html.Breakers
import WhatwgTest.Audit.SpecCoverage
import WhatwgTest.Audit.AxiomGate

/-!
# Whatwg test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate. The gate command below runs last and inspects the whole
compiled environment.
-/

#whatwg_streams_axiom_gate
