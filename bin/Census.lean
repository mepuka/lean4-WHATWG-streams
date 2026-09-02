import Gates.Census
import WhatwgStreamsTest.Audit.SpecCoverage

/-- Entry point only; the audited logic is Gates.Census.cli. The coverage
emit is the test-side numerator's, which `Gates/` may not import. -/
def main (args : List String) : IO UInt32 :=
  Gates.Census.cli WhatwgStreamsTest.Audit.SpecCoverage.emit args
