import Gates.Sha256

/-- Entry point only; the audited logic is Gates.Sha256.cli. -/
def main (args : List String) : IO UInt32 := Gates.Sha256.cli args
