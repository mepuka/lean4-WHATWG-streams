/-!
# WhatwgStreams

Production root of the WHATWG Streams reification library. Every library
module is imported from here; a module not reachable from this root is not
part of the production build and is rejected by the module-closure gate.

Phase P0 declares nothing. Breadth stubs arrive in P2 and semantic
declarations arrive only behind a frozen contract packet.
-/
