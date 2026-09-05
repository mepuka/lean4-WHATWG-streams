import Gates.TyxmlSchemaEmit

/-- Entry point only; the audited logic is Gates.TyxmlSchemaEmit.cli, which
runs the projection check of Gates.TyxmlSchema first. -/
def main (args : List String) : IO UInt32 := Gates.TyxmlSchemaEmit.cli args
