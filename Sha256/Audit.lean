import Lean
import Lean.Util.CollectAxioms

/-!
# `Sha256` axiom audit

`#sha256_axiom_audit` walks the compiled environment, keeps every declaration
whose owning module lies under the `Sha256` namespace and is not this module,
collects the axioms each one reaches, and emits exactly one line stating what
was scanned and against which ceiling. It replaces the `#print axioms` lines
that would otherwise put one info line per declaration into every consumer's
build log (`docs/SHA256-DAG.md` §3.3).

The ceiling is the repository's semantic ceiling, `propext` and `Quot.sound`
(§3.1). It is stricter than foldlab's `formal/fips202` audit, which tolerates
`Classical.choice`. Ruling R-3 may later admit `Classical.choice` for the
exact string-facing declarations of `Sha256.Digest` and `Sha256.Hex`;
`admittedStringDeclarations` is that list and is empty until a receipt
justifies an entry.

This audit is the library's own typed verdict. It is not the repository's
trust boundary: `WhatwgStreamsTest/Audit/AxiomGate.lean` is, and it audits
every declaration of this tree, including the private and compiler-generated
ones that `Name.isInternal` filters out here.

Shape adapted from foldlab `.staging/fips202-library/SPEC.md` §6 item S0.4 and
from the repository's own `WhatwgStreamsTest/Audit/AxiomGate.lean`.
-/

open Lean

namespace Sha256.Audit

/-- The semantic ceiling of `docs/SHA256-DAG.md` §3.1. -/
private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound]

/-- Exact declarations admitted to `Classical.choice` under ruling R-3, each
recorded on the proof graph's trust edge with its receipt. Empty at S1.0: no
declaration exists yet, so nothing has been measured, so nothing is admitted.
An entry is added only after the S1.3 seat reports the receipt that requires
it. -/
private def admittedStringDeclarations : List Name := []

/-- The audit must be shown to have scanned something before its verdict
means anything. Stages S1.1 to S1.6 landed 422 declarations across twelve
modules; this floor is a coarse tripwire well below that, so that an audit
which silently stopped seeing the tree fails here rather than passing
vacuously. The *exact* count is pinned separately by `#guard_msgs` in
`Sha256.Verified`, which is what catches a single declaration appearing or
disappearing. -/
private def minimumDeclarations : Nat := 380

/-- Every module under this prefix is audited. -/
private def treePrefix : Name := `Sha256

/-- This module is excluded from its own audit: it is the audit
implementation, it runs in `MetaM`, and it therefore reaches
`Classical.choice`. `WhatwgStreamsTest/Audit/AxiomGate.lean` names it exactly
in `auditImplementationModules` for that reason. -/
private def auditModule : Name := `Sha256.Audit

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

/-- Lean compiles a safe definition into an auxiliary unsafe recursor. The
companion of a safe definition is not an authored `unsafe` declaration and is
not audit material. Same test as `WhatwgStreamsTest/Audit/AxiomGate.lean`. -/
private def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | _ => false

private def isAuditedModule (moduleName : Name) : Bool :=
  treePrefix.isPrefixOf moduleName && moduleName != auditModule

/-- Render a name list as a plain `String`. The audit line is pinned by
`#guard_msgs`, and `MessageData` formatting of a `List` inserts breakable
separators whose rendering depends on the surrounding width. A `String` has
no break points, so the pinned line is stable. -/
private def renderNames (names : List Name) : String :=
  "[" ++ String.intercalate ", " (names.map toString) ++ "]"

open Lean Elab Command in
/-- Audit every `Sha256.*` declaration against the semantic ceiling and emit
one verdict line. Throws, listing every offender, if any declaration reaches
an axiom outside the ceiling and is not in `admittedStringDeclarations`. -/
elab "#sha256_axiom_audit" : command => do
  let environment ← getEnv
  let mut declarations : Array Name := #[]
  let mut modules : Array Name := #[]
  for (name, _) in environment.constants.toList do
    if name.isInternal then continue
    if isGeneratedSafeRecursor environment name then continue
    let some moduleName := moduleOf? environment name | continue
    if !isAuditedModule moduleName then continue
    declarations := declarations.push name
    if !modules.contains moduleName then
      modules := modules.push moduleName

  if declarations.size < minimumDeclarations then
    throwError "sha256 axiom audit: scanned only {declarations.size} declarations; at least {minimumDeclarations} were expected, so the audit has not been shown to cover the tree"

  let mut offenders : Array (Name × Name) := #[]
  for declaration in declarations do
    let admitted := admittedStringDeclarations.contains declaration
    let bound := if admitted then allowedAxioms ++ [``Classical.choice] else allowedAxioms
    for axiomName in ← collectAxioms declaration do
      if !bound.contains axiomName then
        offenders := offenders.push (declaration, axiomName)

  unless offenders.isEmpty do
    let mut report := s!"sha256 axiom audit: {offenders.size} offender(s) outside the ceiling {renderNames allowedAxioms}"
    for (declaration, axiomName) in offenders do
      report := report ++ s!"\n  {declaration} reaches {axiomName}"
    throwError "{report}"

  logInfo s!"sha256 axiom audit: {declarations.size} declarations across {modules.size} modules; ceiling {renderNames allowedAxioms}; {admittedStringDeclarations.length} admitted string declarations; 0 offenders"

end Sha256.Audit
