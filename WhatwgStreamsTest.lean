import Gates
import Sha256.Verified
import WhatwgStreamsTest.Counterexamples.Sha.Mutants
import WhatwgStreamsTest.Counterexamples.Data.Queue
import WhatwgStreamsTest.Data.QueueContract
import WhatwgStreamsTest.Data.QueueAxiomReport
import WhatwgStreamsTest.Audit.SpecCoverage
import WhatwgStreamsTest.Audit.AxiomGate

/-!
# WhatwgStreams test battery

The default Lake build imports every admitted contract, attack, and kernel
dependency report through this root. A test file not reachable here is not a
passing gate. The gate command below runs last and inspects the whole
compiled environment.
-/

#whatwg_streams_axiom_gate
