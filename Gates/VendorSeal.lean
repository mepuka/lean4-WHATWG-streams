import Gates.Common
import Gates.Sha256
import Sha256

/-!
# Gates.VendorSeal

The vendor seal. Everything under `vendor/` is pinned third-party bytes:
the WHATWG Streams specification source and reference implementation at one
commit, and the Web Platform Tests `streams/` directory at one commit. The
seal is the projection `generated/vendor-manifest.tsv`, one row per file:

```text
<relative path>\t<sha256>\t<byte count>
```

`lake exe vendorseal` checks the working tree against the manifest in both
directions: every manifested file must exist with the recorded digest and
size, and every file under `vendor/` must be manifested. It also refuses any
path that cannot exist on a Windows host, because a pinned tree that fails to
check out on one supported host is not a pin.

`lake exe vendorseal --write` regenerates the manifest. The manifest is a
generated projection: repair the vendored bytes or this generator, never the
manifest by hand. A re-pin moves a whole tree together.
-/

namespace Gates.VendorSeal

open Gates.Common

structure Row where
  path : String
  digest : String
  size : Nat
  deriving Repr, BEq, Inhabited

def manifestPath (root : System.FilePath) : System.FilePath :=
  root / "generated" / "vendor-manifest.tsv"

def vendorDirectory (root : System.FilePath) : System.FilePath :=
  root / "vendor"

/-- Observe every regular file under `vendor/`, sorted by relative path. -/
def observe (root : System.FilePath) : IO (Array Row) := do
  let vendor := vendorDirectory root
  unless ← vendor.isDir do
    throw <| IO.userError s!"vendor seal: {vendor} is not a directory"
  let files ← regularFilesBelow vendor
  let mut rows : Array Row := #[]
  for file in files do
    let relative ← relativeTo root file
    let bytes ← IO.FS.readBinFile file
    -- Stage S1.4: every digest this repository pins is computed by the proved
    -- library, not by tooling arithmetic. Meaning: `Sha256.Bridge.sha256_bridge`.
    rows := rows.push
      { path := relative, digest := (_root_.Sha256.sha256 bytes).toHex, size := bytes.size }
  return rows.qsort fun a b => a.path < b.path

def render (rows : Array Row) : String :=
  String.join (rows.toList.map fun row => s!"{row.path}\t{row.digest}\t{row.size}\n")

def parseRow (line : String) (lineNumber : Nat) : Except String Row :=
  match line.splitOn "\t" with
  | [path, digest, size] =>
    match size.toNat? with
    | some size =>
      if digest.length != 64 || !digest.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
        .error s!"manifest line {lineNumber}: malformed digest"
      else if !path.startsWith "vendor/" then
        .error s!"manifest line {lineNumber}: path is outside vendor/: {path}"
      else
        .ok { path, digest, size }
    | none => .error s!"manifest line {lineNumber}: malformed size"
  | _ => .error s!"manifest line {lineNumber}: expected three tab-separated fields"

def parse (text : String) : Except String (Array Row) := do
  let mut rows : Array Row := #[]
  let mut lineNumber := 0
  for line in lines text do
    lineNumber := lineNumber + 1
    rows := rows.push (← parseRow line lineNumber)
  return rows

/-- Top-level vendored tree of a relative path, such as
`vendor/whatwg-streams-b9ba9f49`. -/
def treeOf (path : String) : String :=
  match path.splitOn "/" with
  | "vendor" :: tree :: _ => s!"vendor/{tree}"
  | _ => path

def summarize (rows : Array Row) : String := Id.run do
  let mut trees : Array (String × Nat × Nat) := #[]
  for row in rows do
    let tree := treeOf row.path
    match trees.findIdx? (fun entry => entry.1 == tree) with
    | some index =>
      trees := trees.modify index fun (name, files, bytes) => (name, files + 1, bytes + row.size)
    | none => trees := trees.push (tree, 1, row.size)
  let total := rows.foldl (fun acc row => acc + row.size) 0
  let mut out := s!"vendor seal: {rows.size} files, {total} bytes, {trees.size} pinned trees\n"
  for (name, files, bytes) in trees do
    out := out ++ s!"  {name}: {files} files, {bytes} bytes\n"
  return out

def write (root : System.FilePath) : IO UInt32 := do
  let rows ← observe root
  let mut problems : List String := []
  for row in rows do
    for problem in windowsPathProblems row.path do
      problems := problems ++ [s!"{row.path}: {problem}"]
  unless problems.isEmpty do
    IO.eprintln "FAIL vendor seal: refusing to write a manifest containing paths invalid on Windows"
    for problem in problems do IO.eprintln s!"  {problem}"
    return 1
  IO.FS.createDirAll (root / "generated")
  IO.FS.writeFile (manifestPath root) (render rows)
  IO.print (summarize rows)
  IO.println s!"WROTE {← relativeTo root (manifestPath root)}"
  return 0

def check (root : System.FilePath) : IO UInt32 := do
  let manifest := manifestPath root
  unless ← manifest.pathExists do
    IO.eprintln s!"FAIL vendor seal: missing manifest {manifest}; run `lake exe vendorseal --write`"
    return 1
  let expected ← match parse (← IO.FS.readFile manifest) with
    | .ok rows => pure rows
    | .error message =>
      IO.eprintln s!"FAIL vendor seal: {message}"
      return 1
  let observed ← observe root
  let mut failures : Array String := #[]
  -- Manifest order is itself part of the projection.
  let sortedExpected := expected.qsort fun a b => a.path < b.path
  if sortedExpected != expected then
    failures := failures.push "manifest rows are not sorted by path"
  for i in [1:expected.size] do
    if expected[i - 1]!.path == expected[i]!.path then
      failures := failures.push s!"duplicate manifest row for {expected[i]!.path}"
  for row in expected do
    match observed.find? (fun o => o.path == row.path) with
    | none => failures := failures.push s!"manifested file is missing: {row.path}"
    | some actual =>
      if actual.digest != row.digest then
        failures := failures.push
          s!"digest drift: {row.path} expected {row.digest} observed {actual.digest}"
      if actual.size != row.size then
        failures := failures.push s!"size drift: {row.path} expected {row.size} observed {actual.size}"
  for row in observed do
    if (expected.find? fun e => e.path == row.path).isNone then
      failures := failures.push s!"unmanifested file under vendor/: {row.path}"
    for problem in windowsPathProblems row.path do
      failures := failures.push s!"path invalid on Windows: {row.path}: {problem}"
  if failures.isEmpty then
    IO.print (summarize expected)
    IO.println "PASS vendor seal: manifest and vendor/ agree in both directions; every path is valid on Windows"
    return 0
  IO.eprintln s!"FAIL vendor seal: {failures.size} problem(s)"
  for failure in failures do IO.eprintln s!"  {failure}"
  return 1

def usage : String :=
  "usage: lake exe vendorseal          check vendor/ against generated/vendor-manifest.tsv\n" ++
  "       lake exe vendorseal --write  regenerate the manifest from vendor/"

/-- Command-line entry, invoked by `bin/VendorSeal.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] => check root
  | ["--write"] => write root
  | _ =>
    IO.eprintln usage
    return 2

end Gates.VendorSeal
