import Gates.TrustSelfTest

/-- Entry point only; the audited logic is Gates.TrustSelfTest.cli. -/
def main (args : List String) : IO UInt32 := Gates.TrustSelfTest.cli args
