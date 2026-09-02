import Lean
import Gates
import WhatwgStreamsTest.Audit.SpecCoverageRows

/-!
# Specification-coverage numerator

`docs/SPEC-COVERAGE.md` owns the metric; this module is its numerator side.
The frozen row list is `WhatwgStreamsTest/Audit/SpecCoverageRows.lean`, which
`lake exe census --write` generates alongside
`generated/spec-algorithm-census.tsv` so that a table of several hundred rows (450 at P1.1) is never
transcribed by hand. Both projections are covered by the census gate's
byte-for-byte drift check, so neither can be edited without failing
`lake exe census`.

What is authored here is the freeze and the checks. `expectedRowTotal` and
`expectedDenominator` are literals: a census that grows or shrinks fails this
build until someone updates them deliberately. The elaboration-time gate below
then checks, in both directions, that

- the frozen rows and the census projection carry the same ids in the same
  order and the same number of them;
- the header of the census projection agrees with the row count;
- every disposition recorded in `census/overrides.tsv` reached its row, and
  every row that file names exists;
- the denominator recomputed from the frozen dispositions matches the frozen
  `denominator`, using the exclusion rule of `docs/SPEC-COVERAGE.md`; and
- every row is `absent` with an empty witness list, which is what P1 claims.

The last check is what lets `lake exe census --report` print the coverage
block from the census alone: with no witness anywhere, `green` and `partial`
are zero by construction rather than by assertion. The first witness to land
must move the report onto a Lean emit.

Reading files at elaboration puts this module in `MetaM`, which reaches
`Classical.choice`, so its exact name is listed in
`WhatwgStreamsTest/Audit/AxiomGate.lean`'s `auditImplementationModules`. The
section-to-disposition join itself is not recomputed here: it needs the pinned
`index.bs`, and `lake exe census` is the gate that owns it.
-/

open Lean

namespace WhatwgStreamsTest.Audit.SpecCoverage

open Gates.Census

/-- Census rows frozen for this commit. A change here is deliberate. -/
def expectedRowTotal : Nat := 450

/-- Rows inside the coverage denominator, that is, rows whose disposition is
not `evidenceOnly`, `refused` or `targetOnly`. -/
def expectedDenominator : Nat := 410

/-- The frozen numerator rows. -/
def rows : Array CoverageRow := SpecCoverageRows.rows

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "WhatwgStreams.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "spec coverage gate: could not locate the project root"
  throw <| IO.userError "spec coverage gate: project-root search exceeded 64 parents"

/-- The `kind|id` pairs of the census projection, in file order, with the row
count its header records. -/
def parseCensus (text : String) : Except String (Array String × Nat) := Id.run do
  match Gates.Common.lines text with
  | [] => return .error "the census projection is empty"
  | header :: dataLines =>
    let expectedHeader := censusHeader dataLines.length
    if header != expectedHeader then
      return .error "the census projection header does not record its own row count and generator identity"
    let mut ids : Array String := #[]
    let mut lineNumber := 1
    for line in dataLines do
      lineNumber := lineNumber + 1
      match splitRow line with
      | .error message => return .error s!"census line {lineNumber}: {message}"
      | .ok fields =>
        if fields.size != 7 then
          return .error s!"census line {lineNumber}: expected seven fields, found {fields.size}"
        let kindText := fields.getD 0 ""
        let rowId := fields.getD 1 ""
        match Kind.ofString? kindText with
        | none => return .error s!"census line {lineNumber}: unknown kind {kindText}"
        | some kind =>
          if !rowId.startsWith (kind.name ++ ".") then
            return .error s!"census line {lineNumber}: row id {rowId} does not carry its own kind"
          ids := ids.push rowId
    return .ok (ids, dataLines.length)

open Elab Command in
elab "#spec_coverage_gate" : command => do
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "spec coverage gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let censusPath := projectRoot / censusRelativePath
  unless ← liftIO censusPath.pathExists do
    throwError "spec coverage gate: missing {censusRelativePath}; run `{regenerateCommand}`"
  let overridesPath := projectRoot / overridesRelativePath
  unless ← liftIO overridesPath.pathExists do
    throwError "spec coverage gate: missing {overridesRelativePath}"
  let censusText ← liftIO <| IO.FS.readFile censusPath
  let overridesText ← liftIO <| IO.FS.readFile overridesPath

  let (censusIds, headerCount) ←
    match parseCensus censusText with
    | .ok pair => pure pair
    | .error message => throwError "spec coverage gate: {message}"
  let overrides ←
    match parseOverrides overridesText with
    | .ok parsed => pure parsed
    | .error message => throwError "spec coverage gate: {message}"

  -- Counts, frozen against the authored literals in this file.
  if rows.size != expectedRowTotal then
    throwError "spec coverage gate: the frozen row list holds {rows.size} rows; expectedRowTotal is {expectedRowTotal}"
  if SpecCoverageRows.rowTotal != expectedRowTotal then
    throwError "spec coverage gate: the generated rowTotal is {SpecCoverageRows.rowTotal}; expectedRowTotal is {expectedRowTotal}"
  if censusIds.size != expectedRowTotal then
    throwError "spec coverage gate: {censusRelativePath} holds {censusIds.size} rows; expectedRowTotal is {expectedRowTotal}"
  if headerCount != expectedRowTotal then
    throwError "spec coverage gate: the census header records {headerCount} rows; expectedRowTotal is {expectedRowTotal}"

  -- Ids, in both directions and in order. Both files are sorted by kind then
  -- id, so equality of the sequences is equality of the sets plus the order.
  for i in [0:expectedRowTotal] do
    let frozen := (rows.getD i default).id
    let projected := censusIds.getD i ""
    if frozen != projected then
      throwError "spec coverage gate: row {i} is {frozen} in the frozen list and {projected} in {censusRelativePath}"
  for id in censusIds do
    unless rows.any (fun r => r.id == id) do
      throwError "spec coverage gate: {censusRelativePath} carries {id}, which the frozen list does not"
  for row in rows do
    unless censusIds.contains row.id do
      throwError "spec coverage gate: the frozen list carries {row.id}, which {censusRelativePath} does not"

  -- Row ids are unique.
  for i in [1:rows.size] do
    if (rows.getD i default).id == (rows.getD (i - 1) default).id then
      throwError "spec coverage gate: duplicate frozen row id {(rows.getD i default).id}"

  -- Every authored override reached its row, and named a row that exists.
  for entry in overrides do
    match rows.find? (fun r => r.id == entry.rowId) with
    | none =>
      throwError "spec coverage gate: {overridesRelativePath} names {entry.rowId}, which is not a census row"
    | some row =>
      if row.disposition != entry.disposition then
        throwError "spec coverage gate: {entry.rowId} carries {row.disposition.name} but {overridesRelativePath} dispositions it {entry.disposition.name}"

  -- The denominator, recomputed from the frozen dispositions.
  let denominator := rows.foldl (fun acc r => if r.disposition.excluded then acc else acc + 1) 0
  if denominator != expectedDenominator then
    throwError "spec coverage gate: the frozen dispositions give a denominator of {denominator}; expectedDenominator is {expectedDenominator}"
  if SpecCoverageRows.denominator != expectedDenominator then
    throwError "spec coverage gate: the generated denominator is {SpecCoverageRows.denominator}; expectedDenominator is {expectedDenominator}"

  -- P1 claims no witness anywhere. `docs/SPEC-COVERAGE.md` allows an empty
  -- witness list only with `absent`, so the two checks are one claim.
  for row in rows do
    if row.state != CoverageState.absent then
      throwError "spec coverage gate: {row.id} is {row.state.name}, but P1 states every row is absent"
    unless row.witnesses.isEmpty do
      throwError "spec coverage gate: {row.id} is absent yet carries witnesses {row.witnesses}"

  let excluded := expectedRowTotal - expectedDenominator
  logInfo
    m!"WhatwgStreams spec coverage gate: {expectedRowTotal} frozen rows agree with {censusRelativePath} in both directions; denominator {expectedDenominator}, {excluded} excluded; {overrides.size} authored override(s) applied; every row is absent with no witness"

end WhatwgStreamsTest.Audit.SpecCoverage

open WhatwgStreamsTest.Audit.SpecCoverage in
#spec_coverage_gate
