import Gates.VendorSeal

/-- Entry point only; the audited logic is Gates.VendorSeal.cli. -/
def main (args : List String) : IO UInt32 := Gates.VendorSeal.cli args
