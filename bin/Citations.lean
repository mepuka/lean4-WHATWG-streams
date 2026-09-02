import Gates.Citations

/-- Entry point only; the audited logic is Gates.Citations.cli. -/
def main (args : List String) : IO UInt32 := Gates.Citations.cli args
