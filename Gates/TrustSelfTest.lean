import Gates.Common

/-!
# Gates.TrustSelfTest

Exercises the elaboration-time trust gate in `WhatwgStreamsTest/Audit/AxiomGate.lean`
by planting declarations it must reject and confirming it rejects them for
the stated reason.

The gate runs in the root aggregator `WhatwgStreamsTest.lean`, which Lake
builds last. Any earlier module that fails to build prevents the gate from
running at all, so a red tree would make the planted checks meaningless. The
breaker/builder discipline deliberately keeps frozen batteries red before
their builder lands. This self-test therefore:

1. copies the Lean sources into a throwaway directory;
2. builds once and requires the set of failing modules to equal the declared
   set in `test/fixtures/trust-gate/known-red.txt`, in both directions;
3. excises the declared red modules from the copy; and
4. runs the planted-declaration checks against a genuinely green tree.

Run `lake exe trustselftest` from anywhere inside the checkout. It invokes
`lake build` in the throwaway copy through the same toolchain.
-/

namespace Gates.TrustSelfTest

open Gates.Common

structure Context where
  root : System.FilePath
  probe : System.FilePath

def copiedFiles : List String :=
  ["lakefile.toml", "lake-manifest.json", "lean-toolchain",
   "WhatwgStreams.lean", "Gates.lean", "WhatwgStreamsTest.lean"]

def copiedTrees : List String :=
  ["WhatwgStreams", "WhatwgStreamsTest", "Gates", "bin"]

def fixture (root : System.FilePath) (name : String) : System.FilePath :=
  root / "test" / "fixtures" / "trust-gate" / name

def auditSource (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgStreamsTest" / "Audit" / "AxiomGate.lean"

def productionRoot (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgStreams.lean"

def testRoot (probe : System.FilePath) : System.FilePath :=
  probe / "WhatwgStreamsTest.lean"

def copyTree (source destination : System.FilePath) : IO Unit := do
  for file in ← regularFilesBelow source do
    let relative ← relativeTo source file
    let target := destination / relative
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile target (← IO.FS.readBinFile file)

def makeProbe (root : System.FilePath) : IO System.FilePath := do
  let base : System.FilePath ←
    match ← IO.getEnv "TMPDIR" with
    | some dir => pure dir
    | none =>
      match ← IO.getEnv "TEMP" with
      | some dir => pure dir
      | none => pure "/tmp"
  let probe := base / s!"whatwg-streams-trust-{← IO.monoNanosNow}"
  IO.FS.createDirAll probe
  for file in copiedFiles do
    IO.FS.writeBinFile (probe / file) (← IO.FS.readBinFile (root / file))
  for tree in copiedTrees do
    copyTree (root / tree) (probe / tree)
  return probe

def lakeCommand : String :=
  if System.Platform.isWindows then "lake.exe" else "lake"

/-- Run `lake build` in the probe; return success and the combined output. -/
def build (probe : System.FilePath) : IO (Bool × String) := do
  let output ← IO.Process.output
    { cmd := lakeCommand, args := #["build"], cwd := some probe }
  return (output.exitCode == 0, output.stdout ++ output.stderr)

/-- Lake reports failing targets as `- <Module>` lines after its summary
marker. `job computation` is Lake's own pseudo-target, listed whenever any
target fails; it is never a module and is dropped. -/
def failingTargets (output : String) : List String := Id.run do
  let mut collecting := false
  let mut targets : List String := []
  for line in lines output do
    if line.startsWith "Some required targets logged failures:" then
      collecting := true
    else if collecting && line.startsWith "- " then
      let target := dropChars line 2
      if target != "job computation" then
        targets := targets ++ [target]
    else if collecting then
      collecting := false
  return targets.eraseDups.mergeSort (· < ·)

def knownRed (root : System.FilePath) : IO (List String) := do
  let path := fixture root "known-red.txt"
  unless ← path.pathExists do return []
  return (listFileEntries (← IO.FS.readFile path)).eraseDups.mergeSort (· < ·)

def moduleFile (probe : System.FilePath) (moduleName : String) : System.FilePath :=
  probe / (String.intercalate "/" (moduleName.splitOn ".") ++ ".lean")

def excise (probe : System.FilePath) (modules : List String) : IO Unit := do
  for moduleName in modules do
    let path := moduleFile probe moduleName
    unless ← path.pathExists do
      throw <| IO.userError s!"declared red module has no source file: {moduleName}"
    IO.FS.removeFile path
    IO.println s!"NOTE excised declared red module from the probe copy: {moduleName}"
  let root := testRoot probe
  let kept := (lines (← IO.FS.readFile root)).filter fun line =>
    !(modules.any fun m => line == s!"import {m}")
  IO.FS.writeFile root (String.intercalate "\n" kept ++ "\n")

def tail (output : String) (count : Nat) : String :=
  String.intercalate "\n" ((lines output).reverse.take count).reverse

/-- Append a fixture to a file, run the block, and restore the file. -/
def withPlanted (target : System.FilePath) (fixturePath : System.FilePath)
    (body : IO Bool) : IO Bool := do
  let original ← IO.FS.readBinFile target
  let planted ← IO.FS.readFile fixturePath
  IO.FS.writeFile target (String.fromUTF8! original ++ "\n" ++ planted)
  try
    body
  finally
    IO.FS.writeBinFile target original

def expectAcceptance (probe : System.FilePath) (label : String) : IO Bool := do
  let (ok, output) ← build probe
  if ok then
    IO.println s!"PASS trust gate accepted {label}"
    return true
  IO.eprintln s!"FAIL trust gate unexpectedly rejected {label}"
  IO.eprintln (tail output 60)
  return false

def expectRejection (probe : System.FilePath) (label : String)
    (expectedFragment : Option String) : IO Bool := do
  let (ok, output) ← build probe
  if ok then
    IO.eprintln s!"FAIL trust gate unexpectedly accepted {label}"
    return false
  match expectedFragment with
  | some fragment =>
    if (output.splitOn fragment).length > 1 then
      IO.println s!"PASS planted {label} rejected with the expected diagnostic"
      return true
    IO.eprintln s!"FAIL trust gate rejected {label} for an unexpected reason; expected: {fragment}"
    IO.eprintln (tail output 60)
    return false
  | none =>
    IO.println s!"PASS planted {label} rejected"
    return true

structure Plant where
  label : String
  fixtureName : String
  /-- Which probe file receives the fixture. -/
  target : System.FilePath → System.FilePath
  expected : Option String

def acceptancePlants : List Plant :=
  [{ label := "comments, strings, and numeric projections", fixtureName := "benign.lean.txt",
     target := auditSource, expected := none }]

def rejectionPlants : List Plant :=
  [{ label := "partial declaration", fixtureName := "partial.lean.txt", target := auditSource,
     expected := some "contains an authored `partial` declaration modifier" },
   { label := "unsafe declaration", fixtureName := "unsafe.lean.txt", target := auditSource,
     expected := some "contains an authored `unsafe` declaration modifier" },
   { label := "unadmitted Classical.choice in the production tree",
     fixtureName := "unadmitted-choice.lean.txt", target := productionRoot,
     expected := some "reaches unexpected axiom Classical.choice" },
   { label := "sorry in the production tree", fixtureName := "sorry.lean.txt",
     target := productionRoot, expected := some "reaches forbidden axiom sorryAx" },
   { label := "native_decide in the production tree", fixtureName := "native-decide.lean.txt",
     target := productionRoot, expected := some "(native_decide auxiliary)" },
   { label := "malformed string literal", fixtureName := "malformed-string.lean.txt",
     target := productionRoot, expected := none },
   { label := "malformed raw string literal", fixtureName := "malformed-raw-string.lean.txt",
     target := productionRoot, expected := none },
   { label := "malformed decimal literal", fixtureName := "malformed-decimal.lean.txt",
     target := productionRoot, expected := none },
   { label := "unterminated comment", fixtureName := "malformed-comment.lean.txt",
     target := productionRoot, expected := none }]

def run (root : System.FilePath) (probe : System.FilePath) : IO Bool := do
  -- 0. The declared red set must be exactly the failing set.
  let declared ← knownRed root
  let (_, output) ← build probe
  let observed := (failingTargets output).filter fun target =>
    !(declared.length > 0 && target == "WhatwgStreamsTest")
  if observed != declared then
    IO.eprintln "FAIL the declared red set does not match the modules that actually fail"
    IO.eprintln "--- failing but not declared in test/fixtures/trust-gate/known-red.txt ---"
    for target in observed do
      unless declared.contains target do IO.eprintln s!"  {target}"
    IO.eprintln "--- declared red but actually green; remove the stale entry ---"
    for target in declared do
      unless observed.contains target do IO.eprintln s!"  {target}"
    IO.eprintln (tail output 60)
    return false
  IO.println s!"PASS declared red set matches the observed red set ({declared.length} module(s))"
  -- 1. Excise the declared red modules.
  excise probe declared
  -- 2. Green control.
  let mut allOk ← expectAcceptance probe "the unmodified source tree"
  for plant in acceptancePlants do
    let ok ← withPlanted (plant.target probe) (fixture root plant.fixtureName)
      (expectAcceptance probe plant.label)
    allOk := allOk && ok
  -- 3. Planted rejections.
  for plant in rejectionPlants do
    let ok ← withPlanted (plant.target probe) (fixture root plant.fixtureName)
      (expectRejection probe plant.label plant.expected)
    allOk := allOk && ok
  -- 4. Module closure: a source file not reachable from the test root.
  let unreachable := probe / "WhatwgStreamsTest" / "Planted" / "Unreachable.lean"
  IO.FS.createDirAll (probe / "WhatwgStreamsTest" / "Planted")
  IO.FS.writeFile unreachable (← IO.FS.readFile (fixture root "unreachable.lean.txt"))
  let ok ← try
      expectRejection probe "unreachable test module"
        (some "is not reachable from the WhatwgStreamsTest audit root")
    finally
      IO.FS.removeDirAll (probe / "WhatwgStreamsTest" / "Planted")
  allOk := allOk && ok
  -- 5. Final green control after every restoration.
  let ok ← expectAcceptance probe "the restored source tree"
  allOk := allOk && ok
  return allOk

/-- Command-line entry, invoked by `bin/TrustSelfTest.lean`. -/
def cli (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: lake exe trustselftest"
    return 2
  let root ← Gates.Common.projectRoot
  let probe ← makeProbe root
  IO.println s!"NOTE probe copy at {probe}"
  let ok ← try
      run root probe
    finally
      IO.FS.removeDirAll probe
  if ok then
    IO.println "PASS trust self-test: every planted declaration was rejected for its stated reason and every control was accepted"
    return 0
  IO.eprintln "FAIL trust self-test"
  return 1

end Gates.TrustSelfTest
