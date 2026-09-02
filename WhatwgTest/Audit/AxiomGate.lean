import Lean
import Lean.Util.CollectAxioms
import Whatwg
import Gates

/-!
# Whatwg axiom allowlist gate

This command tokenizes every authored source under `Whatwg/Streams/`,
`WhatwgTest/Streams/`, and `Gates/` and inspects every declaration compiled
from them, including definitions, instances, generated declarations, and
private helpers. The build fails on an authored `unsafe` or `partial`
declaration modifier, on any declaration that reaches a forbidden axiom, and
on any declaration that reaches an axiom outside its tree's ceiling.

Two ceilings exist:

- the semantic ceiling, Lean's standard base `propext`, `Quot.sound`, and
  `Classical.choice` (operator ruling R-11, 2026-09-02; before it the
  semantic trees excluded `Classical.choice`); and
- the implementation ceiling, which additionally admits `Classical.choice`,
  for the `Gates/` tooling tree and for exact-module audit implementation
  such as this file, because `MetaM` and Lean's `String` traversals reach
  `Classical.choice` through library proofs.

`sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, and `Lean.trustCompiler`
are forbidden everywhere. The gate is exhaustive over the compiled namespace
rather than a hand-written theorem list; per-packet axiom reports remain the
human-readable receipts.

This gate is ported from lean4-effect4's `Effect4Test/Audit/AxiomGate.lean`
with the tree names, ceilings, and messages changed for this repository.
-/

open Lean

namespace WhatwgTest.Audit

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def implementationAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

/-- Exact modules whose declarations are audit implementation. `MetaM`
reaches `Classical.choice`, so these modules are bound by
`implementationAxioms`. The list is explicit rather than a namespace prefix
so that a file dropped into the audit tree cannot silently acquire the wider
ceiling. Each entry is checked for staleness below. -/
private def auditImplementationModules : List Name :=
  [ `WhatwgTest.Audit.AxiomGate,
    `WhatwgTest.Audit.SpecCoverage ]

/-- Exact public declarations admitted to the implementation ceiling outside
an implementation module. Empty at P0; a later target renderer names its
output-text crossings here, with its proof-graph edge recording why. -/
private def implementationDeclarations : List Name := []

/-- Private declarations admitted the same way, identified by exact owning
module and original spelling, never by Lean's private-name counter. -/
private def implementationPrivateDeclarations : List (Name × Name) := []

/-- The `Gates/` tree is tooling: it is audited for totality and forbidden
axioms, and admitted to the implementation ceiling as a whole. It contains
no semantic declaration; `Gates/AGENTS.md` owns that rule. -/
private def toolingTreePrefix : Name := `Gates

private def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- `native_decide` and `bv_decide` mint a per-declaration auxiliary axiom
whose name carries a `_native` component. Such an axiom is forbidden by
shape, whatever declaration it hangs off. -/
private def isNativeAuxiliaryAxiom (axiomName : Name) : Bool :=
  axiomName.anyS fun component => component == "_native"

private def moduleOf? (environment : Environment) (declaration : Name) : Option Name := do
  let index ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[index.toNat]?

private def resolveImplementationDeclarations
    (environment : Environment) (declarations : Array Name) : Except String (List Name) := do
  let mut resolved := implementationDeclarations
  for (owner, originalName) in implementationPrivateDeclarations do
    let privateCandidates := declarations.toList.filter fun declaration =>
      moduleOf? environment declaration == some owner &&
        privateToUserName? declaration == some originalName
    match privateCandidates with
    | [declaration] => resolved := resolved ++ [declaration]
    | _ => throw s!"Whatwg axiom gate: private implementation exemption {owner}/{originalName} matched {privateCandidates.length} declarations; expected exactly one"
  return resolved

/-- The two semantic trees. The SHA-256 lane that used to be a third one is
the required `hash` package since step 6 of `docs/HASH-PACKAGE-PLAN.md`; its
own gate audits it there, and nothing under a dependency is inspected here. -/
private def semanticTreePrefixes : List Name :=
  [`Whatwg, `WhatwgTest]

private def belongsToAuditedTree (moduleName : Name) : Bool :=
  semanticTreePrefixes.any (·.isPrefixOf moduleName) ||
    toolingTreePrefix.isPrefixOf moduleName

private def isGeneratedSafeRecursor (environment : Environment) (name : Name) : Bool :=
  match Lean.Compiler.isUnsafeRecName? name with
  | none => false
  | some sourceName =>
      match environment.find? sourceName with
      | some (.defnInfo sourceInfo) => sourceInfo.safety == .safe
      | none => false
      | _ => false

/-
`Parser.testParseFile` cannot replay an already-compiled source against the
final project environment: syntax introduced by a later-imported test module
can turn an earlier ordinary identifier into a keyword. Tokenization is the
right level for this source check. Lean's own tokenizer skips comments and
handles ordinary, character, interpolated, and raw string literals, while the
compiled-environment pass below independently confirms declaration safety.
-/
private def forbiddenTrustToken?
    (environment : Environment)
    (source : System.FilePath) : IO (Option String) := do
  let input ← IO.FS.readFile source
  let inputContext := Parser.mkInputContext input source.toString
  let parserContext : Parser.ParserModuleContext :=
    { env := environment, options := {} }
  let tokenTable := Parser.Module.updateTokens (Parser.getTokenTable environment)
  let mut state := Parser.mkParserState input
  let mut projectionEnd : Option String.Pos.Raw := none
  while !inputContext.atEnd state.pos do
    let skipped := Parser.whitespace.run inputContext parserContext tokenTable state
    if let some error := skipped.errorMsg then
      throw <| IO.userError
        s!"Whatwg source trust gate: tokenization failed in {source}: {error}"
    state := skipped
    if inputContext.atEnd state.pos then
      return none
    -- Documentation comments are syntax nodes rather than whitespace. Consume
    -- them with Lean's own parsers so their prose never becomes audit tokens.
    let docComment := Parser.Command.docComment.fn.run
      inputContext parserContext tokenTable state
    if docComment.errorMsg.isNone then
      state := docComment.popSyntax
      projectionEnd := none
      continue
    let moduleDoc := Parser.Command.moduleDoc.fn.run
      inputContext parserContext tokenTable state
    if moduleDoc.errorMsg.isNone then
      state := moduleDoc.popSyntax
      projectionEnd := none
      continue
    -- Lean parses the index in `h.2.trans` and `h |>.2.trans` with
    -- `fieldIdxFn`: the ordinary number tokenizer mistakes `2.trans` for a
    -- decimal. Use the same parser only immediately after a projection dot;
    -- ordinary numerals and every tokenization error retain their usual path.
    let tokenParser :=
      if projectionEnd == some state.pos && (inputContext.get state.pos).isDigit then
        Parser.fieldIdxFn
      else
        Parser.tokenFn []
    let next := tokenParser.run inputContext parserContext tokenTable state
    if let some error := next.errorMsg then
      let position := inputContext.fileMap.toPosition state.pos
      throw <| IO.userError
        s!"Whatwg source trust gate: tokenization failed in {source}:{position.line}:{position.column + 1}: {error}"
    let token := next.stxStack.back
    if token.isToken "unsafe" then
      return some "unsafe"
    if token.isToken "partial" then
      return some "partial"
    projectionEnd :=
      if token.isToken "." || token.isToken "|>." then token.getTailPos? else none
    state := next.popSyntax
  return none

private def auditSourceTrustModifiers
    (environment : Environment)
    (sources : Array System.FilePath) : IO Unit := do
  for source in sources do
    if let some modifier ← forbiddenTrustToken? environment source then
      throw <| IO.userError
        s!"Whatwg source trust gate: {source} contains an authored `{modifier}` declaration modifier"

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Whatwg.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "Whatwg axiom gate: could not locate the project root"
  throw <| IO.userError "Whatwg axiom gate: project-root search exceeded 64 parents"

private def leanFilesBelow (directory : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← directory.walkDir
  return entries.filter fun path => path.extension == some "lean"

private def auditedSources (projectRoot : System.FilePath) : IO (Array System.FilePath) := do
  let production ← leanFilesBelow (projectRoot / "Whatwg")
  let tests ← leanFilesBelow (projectRoot / "WhatwgTest")
  let tooling ← leanFilesBelow (projectRoot / "Gates")
  return production ++ tests ++ tooling
    |>.push (projectRoot / "Whatwg.lean")
    |>.push (projectRoot / "Gates.lean")
    |>.push (projectRoot / "WhatwgTest.lean")

open Lean Elab Command in
elab "#whatwg_streams_axiom_gate" : command => do
  let environment ← getEnv
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "Whatwg axiom gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let sources ← liftIO <| auditedSources projectRoot
  let importedPaths := environment.header.moduleNames.map fun moduleName =>
    (Lean.modToFilePath projectRoot moduleName "lean").normalize
  for source in sources do
    if source.normalize != sourceFile.normalize && !importedPaths.contains source.normalize then
      throwError
        "Whatwg module-closure gate: {source} is not reachable from the WhatwgTest audit root"

  liftIO <| auditSourceTrustModifiers environment sources

  let mut declarations : Array Name := #[]
  for (name, info) in environment.constants.toList do
    if let some moduleName := moduleOf? environment name then
      if belongsToAuditedTree moduleName then
        if !isGeneratedSafeRecursor environment name then
          if info.isUnsafe then
            throwError "Whatwg trust gate: declaration {name} is unsafe"
          if info.isPartial then
            throwError "Whatwg trust gate: declaration {name} is partial"
        declarations := declarations.push name

  let exactImplementationDeclarations ←
    match resolveImplementationDeclarations environment declarations with
    | .ok resolved => pure resolved
    | .error message => throwError "{message}"

  let mut toolingCount : Nat := 0
  for declaration in declarations do
    let axioms ← collectAxioms declaration
    let moduleName := moduleOf? environment declaration
    let inTooling := moduleName.any toolingTreePrefix.isPrefixOf
    if inTooling then toolingCount := toolingCount + 1
    let bound :=
      if inTooling || moduleName.any auditImplementationModules.contains ||
          exactImplementationDeclarations.contains declaration then
        implementationAxioms
      else
        allowedAxioms
    for axiomName in axioms do
      if isNativeAuxiliaryAxiom axiomName then
        throwError
          "Whatwg axiom gate: declaration {declaration} reaches forbidden axiom {axiomName} (native_decide auxiliary)"
      if forbiddenAxioms.contains axiomName then
        throwError
          "Whatwg axiom gate: declaration {declaration} reaches forbidden axiom {axiomName}"
      if !bound.contains axiomName then
        throwError
          "Whatwg axiom gate: declaration {declaration} reaches unexpected axiom {axiomName}; allowed axioms are {bound}"

  -- An exemption must not outlive its reason. A named implementation module
  -- that no longer reaches `Classical.choice` widens the trust boundary for
  -- nothing, so it fails the gate.
  for exempted in auditImplementationModules do
    let mut used := false
    for declaration in declarations do
      if moduleOf? environment declaration == some exempted then
        if (← collectAxioms declaration).contains ``Classical.choice then
          used := true
    if !used then
      throwError
        "Whatwg axiom gate: stale implementation exemption for {exempted}; no declaration in it reaches Classical.choice, so remove it from auditImplementationModules"

  for exempted in exactImplementationDeclarations do
    if !(declarations.contains exempted) then
      throwError
        "Whatwg axiom gate: exact implementation exemption names missing declaration {exempted}"
    if !(← collectAxioms exempted).contains ``Classical.choice then
      throwError
        "Whatwg axiom gate: stale exact implementation exemption for {exempted}; it no longer reaches Classical.choice"

  logInfo
    m!"Whatwg module and axiom gate: checked {sources.size} modules and {declarations.size} declarations ({toolingCount} in the Gates tooling tree); semantic/test ceiling is {allowedAxioms}; implementation ceiling ({auditImplementationModules.length} audit module(s), {exactImplementationDeclarations.length} exact declaration(s), plus the Gates tree) additionally allows Classical.choice"

end WhatwgTest.Audit
