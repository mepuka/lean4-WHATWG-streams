/-!
# Gates.Common

Shared helpers for the Lean-implemented repository gates: project-root
discovery, path spelling, file walking, small string utilities, and the
Windows path-validity rule.

Every gate resolves the repository root by searching upward for
`Whatwg.Streams.lean`, so it can be run from any working directory inside the
checkout, and it never trusts an environment variable for that location.

String utilities here operate on `List Char` rather than the slice API so
that the gates read the same on every toolchain minor and never depend on
byte-position arithmetic.
-/

namespace Gates.Common

/-- Search upward from `directory` for the repository root, identified by the
production root module `Whatwg.Streams.lean`. -/
def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Whatwg.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "gate: could not locate the repository root (no Whatwg.Streams.lean above the working directory)"
  throw <| IO.userError "gate: repository-root search exceeded 64 parents"

/-- The repository root for the current working directory. -/
def projectRoot : IO System.FilePath := do
  findProjectRoot (← IO.currentDir)

/-- Host-independent spelling: forward slashes only. -/
def forwardSlashes (path : String) : String :=
  path.map fun c => if c == '\\' then '/' else c

/-- The string with its first `n` characters removed. -/
def dropChars (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

/-- The string with its last `n` characters removed. -/
def dropLastChars (s : String) (n : Nat) : String :=
  String.ofList (s.toList.reverse.drop n |>.reverse)

/-- ASCII and Unicode whitespace removed from both ends. -/
def trimmed (s : String) : String :=
  String.ofList
    (s.toList.dropWhile Char.isWhitespace |>.reverse.dropWhile Char.isWhitespace |>.reverse)

/-- `path` spelled relative to `root`, with forward slashes. Throws when
`path` is not under `root`. -/
def relativeTo (root path : System.FilePath) : IO String := do
  let rootText := forwardSlashes root.toString
  let pathText := forwardSlashes path.toString
  let prefixText := if rootText.endsWith "/" then rootText else rootText ++ "/"
  if pathText.startsWith prefixText then
    return dropChars pathText prefixText.length
  throw <| IO.userError s!"gate: {pathText} is not under {rootText}"

/-- Every regular file below `directory`, in the host's directory order.
Callers sort the result before relying on order. -/
def regularFilesBelow (directory : System.FilePath) : IO (Array System.FilePath) := do
  let entries ← directory.walkDir
  let mut files : Array System.FilePath := #[]
  for entry in entries do
    if !(← entry.isDir) then
      files := files.push entry
  return files

/-- Lines of a text file with the line terminator removed; a trailing
newline does not produce an empty final line. -/
def lines (text : String) : List String :=
  let raw := (text.splitOn "\n").map fun line =>
    if line.endsWith "\r" then dropLastChars line 1 else line
  match raw.reverse with
  | "" :: rest => rest.reverse
  | _ => raw

/-- Lines of a fixture-style list file: comments start with `#`, blank lines
are ignored, surrounding whitespace is trimmed. -/
def listFileEntries (text : String) : List String :=
  (lines text).filterMap fun line =>
    let t := trimmed line
    if t.isEmpty || t.startsWith "#" then none else some t

/-- Windows reserved device names, compared case-insensitively against the
stem of each path segment. -/
private def reservedSegmentStems : List String :=
  ["CON", "PRN", "AUX", "NUL",
   "COM1", "COM2", "COM3", "COM4", "COM5", "COM6", "COM7", "COM8", "COM9",
   "LPT1", "LPT2", "LPT3", "LPT4", "LPT5", "LPT6", "LPT7", "LPT8", "LPT9"]

private def windowsForbiddenChars : List Char := ['<', '>', ':', '"', '|', '?', '*']

/-- Why one path segment cannot exist on a Windows host, if it cannot. This
is the rule the vendor seal enforces so that a checkout succeeds on every
host the repository claims to support. -/
def windowsSegmentProblem? (segment : String) : Option String :=
  let chars := segment.toList
  if segment.isEmpty then some "empty path segment"
  else if segment == "." || segment == ".." then some "relative segment"
  else if chars.any (fun c => c.toNat < 0x20) then some "control character"
  else if chars.any windowsForbiddenChars.contains then
    some "character not allowed on Windows (one of < > : \" | ? *)"
  else if segment.endsWith " " || segment.endsWith "." then
    some "trailing space or dot is stripped by Windows"
  else
    let stem := (segment.splitOn ".").headD segment
    if reservedSegmentStems.contains stem.toUpper then
      some s!"reserved device name {stem.toUpper}"
    else if chars.length > 200 then some "segment longer than 200 characters"
    else none

/-- Every problem with a forward-slash relative path, as `segment: reason`. -/
def windowsPathProblems (relativePath : String) : List String :=
  (relativePath.splitOn "/").filterMap fun segment =>
    (windowsSegmentProblem? segment).map fun reason => s!"{segment}: {reason}"

end Gates.Common
