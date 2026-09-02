import Gates.Census

/-- Entry point only; the audited logic is Gates.Census.cli. -/
def main (args : List String) : IO UInt32 := Gates.Census.cli args
