import Gates.Common

/-!
# Gates.Citations

The internal-citation gate: no line-numbered citation into a mutable authored
document of this repository.

A line citation into a pinned vendored source is stable: the bytes are
identified by digest and never edited here. A line citation into one of this
repository's own authored rulings is not stable. Those documents are edited
continuously, so a name plus a line number silently retargets whenever a
section above it grows or shrinks, and the citing sentence keeps asserting a
claim the target no longer makes.

The gate scans every authored text file outside `vendor/`, `.lake/`, and
`.git/` and rejects a token that names a protected document together with a
line number, in either the full-path or the basename spelling followed by a
colon and a digit. Cite a section heading, an obligation ID, a proof-graph
node, or a short quoted phrase instead.

What a pass means: no such token exists in the scanned tree. What a pass does
not mean: that any other citation resolves, or that a target still says what
the citing sentence claims. This is a lexical scan, not a resolver.
-/

namespace Gates.Citations

open Gates.Common

/-- Authored documents that may not be cited by line number. Basenames are
matched as well as full paths. -/
def protectedDocuments : List String :=
  ["AGENTS.md", "PLAN.md", "SPEC-MANIFEST.md", "COORDINATION.md",
   "docs/ARCHITECTURE.md", "docs/AGENT-ROUTING.md", "docs/DESIGN-BASIS.md",
   "docs/SPEC-COVERAGE.md", "docs/PROVENANCE.md"]

/-- Every spelling a citation might use for a protected document. -/
def protectedSpellings : List String :=
  protectedDocuments.foldl (fun acc doc =>
    let base := (doc.splitOn "/").getLastD doc
    acc ++ [doc, "./" ++ doc, base]) [] |>.eraseDups

def scannedExtensions : List String :=
  ["md", "lean", "txt", "toml", "tsv", "yml", "yaml", "json", "sh", "ps1", "ts", "js"]

/-- Skipped tree roots, relative to the repository root. -/
def skippedPrefixes : List String :=
  ["vendor/", ".lake/", ".git/"]

private def isPathChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '.' || c == '/'

private def matchesAt (chars needle : Array Char) (start : Nat) : Bool := Id.run do
  for j in [0:needle.size] do
    if chars[start + j]! != needle[j]! then
      return false
  return true

/-- Does `line` contain `spelling`, at a token boundary, immediately followed
by `:` and a digit? -/
def containsLineCitation (line spelling : String) : Bool := Id.run do
  let chars := line.toList.toArray
  let needle := (spelling ++ ":").toList.toArray
  if needle.size == 0 || chars.size < needle.size + 1 then
    return false
  for start in [0:chars.size - needle.size] do
    if matchesAt chars needle start then
      let boundaryOk := start == 0 || !isPathChar chars[start - 1]!
      if boundaryOk && chars[start + needle.size]!.isDigit then
        return true
  return false

structure Violation where
  file : String
  line : Nat
  text : String

def scanFile (root : System.FilePath) (file : System.FilePath) : IO (List Violation) := do
  let relative ← relativeTo root file
  let content ← IO.FS.readFile file
  let mut violations : List Violation := []
  let mut lineNumber := 0
  for line in lines content do
    lineNumber := lineNumber + 1
    if protectedSpellings.any (containsLineCitation line ·) then
      violations := violations ++ [{ file := relative, line := lineNumber, text := trimmed line }]
  return violations

def scanned (root : System.FilePath) : IO (Array System.FilePath) := do
  let files ← regularFilesBelow root
  let mut selected : Array System.FilePath := #[]
  for file in files do
    let relative ← relativeTo root file
    if skippedPrefixes.any (relative.startsWith ·) then continue
    match file.extension with
    | some ext => if scannedExtensions.contains ext then selected := selected.push file
    | none => pure ()
  return selected.qsort fun a b => a.toString < b.toString

def check (root : System.FilePath) : IO UInt32 := do
  let files ← scanned root
  let mut violations : List Violation := []
  for file in files do
    violations := violations ++ (← scanFile root file)
  if violations.isEmpty then
    IO.println s!"PASS internal citations: {files.size} files scanned; no line-numbered citation into a protected authored document"
    return 0
  IO.eprintln s!"FAIL internal citations: {violations.length} line-numbered citation(s) into protected authored documents"
  for v in violations do
    IO.eprintln s!"  {v.file} line {v.line}: {v.text}"
  return 1

/-- Command-line entry, invoked by `bin/Citations.lean`. -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | [] => check (← Gates.Common.projectRoot)
  | ["--root", directory] => check directory
  | _ =>
    IO.eprintln "usage: lake exe citations [--root <dir>]"
    return 2

end Gates.Citations
