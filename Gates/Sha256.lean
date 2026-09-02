import Sha256
import Gates.Common

/-!
# Gates.Sha256

The command-line face of the proved SHA-256 library. Since stage S1.4 of
`docs/SHA256-DAG.md` this module holds no hash arithmetic of its own: every
digest is `Sha256.sha256` and every hexadecimal spelling is
`Sha256.Hex.encode`, both from the `Sha256/` tree, which is audited at the
repository's semantic ceiling and whose meaning is
`Sha256.Bridge.sha256_bridge`.

The P0 implementation this replaced was written in the `Id.run do` / `xs[i]!`
style that `docs/SHA256-DAG.md` §3.3 forbids for theorem-bearing code, which is
exactly why it carried no theorem. Its seven self-test vectors were typed from
memory and had no pinned provenance. Both are gone.

**The self-test no longer contains a literal.** It reads
`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp` — NIST CAVP, CAVS 11.0, generated
2011-03-15, sealed by `generated/vendor-manifest.tsv` — at run time and
reproduces every record in it. It therefore cannot drift from the pin: if the
vendored bytes change, the seal fails; if the implementation changes, this
fails.

Each record's `Len` field, not the length of its `Msg` text, is the authority
for how many message bytes there are. The `Len = 0` record writes `Msg = 00`,
one byte of hex text standing for a zero-length message
(`test/contracts/sha256.contract.md`, E5); reading `Msg` and ignoring `Len`
would hash the single byte `0x00` and produce a different digest.

Run `lake exe sha256 --self-test` or `lake exe sha256 <file>`.
-/

namespace Gates.Sha256

/-- Hexadecimal SHA-256 of a byte array, through the proved library. -/
def hexDigest (message : ByteArray) : String := (_root_.Sha256.sha256 message).toHex

/-- Hexadecimal SHA-256 of the UTF-8 encoding of a string. -/
def hexDigestOfString (text : String) : String := hexDigest text.toUTF8

/-- Hexadecimal SHA-256 of a file's bytes. -/
def hexDigestOfFile (path : System.FilePath) : IO String := do
  return hexDigest (← IO.FS.readBinFile path)

/-- One `Len` / `Msg` / `MD` record of a CAVP response file. -/
structure Record where
  len : Nat
  msg : ByteArray
  md : String
  deriving Inhabited

def vectorsPath (root : System.FilePath) : System.FilePath :=
  root / "vendor" / "nist-cavp-sha256" / "SHA256ShortMsg.rsp"

/-- The five contract witnesses, by `Len` in bits: W1, W2, E1, E2, E3
(`test/contracts/sha256.contract.md`). The self-test refuses to pass if the
pinned file has stopped containing any of them. -/
def requiredLens : List Nat := [0, 24, 440, 448, 512]

/-- The field value after an `n`-character `key = ` prefix, with any carriage
return removed so the parser reads the same on a host whose checkout converted
line endings. The vendored file is LF-only and sealed; this is defence in depth,
not a repair. `String.drop` and `String.trim` return a `String.Slice` under
v4.33.1 and are deprecated, so the character list is the stable route. -/
private def fieldAfter (line : String) (n : Nat) : String :=
  String.ofList ((line.toList.drop n).filter fun c => c != '\r')

/-- Parse a CAVP `.rsp` file. `Len` is the authority for the message length;
surplus hex text in `Msg` is dropped, which is what makes the `Len = 0`
placeholder record read as the empty message. -/
def parseRecords (text : String) : Except String (Array Record) := do
  let mut out : Array Record := #[]
  let mut len : Option Nat := none
  let mut msgHex : Option String := none
  let mut lineNumber : Nat := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    if line.startsWith "Len = " then
      match (fieldAfter line 6).toNat? with
      | some value => len := some value
      | none => throw s!"line {lineNumber}: malformed Len field"
    else if line.startsWith "Msg = " then
      msgHex := some (fieldAfter line 6)
    else if line.startsWith "MD = " then
      match len, msgHex with
      | some bitLength, some hex =>
        if bitLength % 8 != 0 then
          throw s!"line {lineNumber}: Len {bitLength} is not a whole number of bytes"
        match _root_.Sha256.Hex.decode? hex with
        | some bytes =>
          if bytes.size * 8 < bitLength then
            throw s!"line {lineNumber}: Msg is shorter than its Len"
          out := out.push
            { len := bitLength, msg := bytes.extract 0 (bitLength / 8),
              md := fieldAfter line 5 }
          len := none
          msgHex := none
        | none => throw s!"line {lineNumber}: malformed Msg hexadecimal"
      | _, _ => throw s!"line {lineNumber}: MD without a preceding Len and Msg"
  return out

/-- Reproduce every pinned CAVP record. Returns `true` when all match. -/
def selfTest : IO Bool := do
  let root ← Gates.Common.projectRoot
  let path := vectorsPath root
  let relative ← Gates.Common.relativeTo root path
  unless ← path.pathExists do
    IO.eprintln s!"FAIL sha256 self-test: missing pinned vectors {relative}"
    return false
  let records ←
    match parseRecords (← IO.FS.readFile path) with
    | .ok records => pure records
    | .error message =>
      IO.eprintln s!"FAIL sha256 self-test: {message}"
      return false
  let mut failures : Array String := #[]
  for record in records do
    let actual := hexDigest record.msg
    if actual != record.md then
      failures := failures.push
        s!"Len = {record.len}: expected {record.md}, computed {actual}"
  for required in requiredLens do
    if (records.find? fun record => record.len == required).isNone then
      failures := failures.push s!"the pinned file has no record with Len = {required}"
  if failures.isEmpty then
    IO.println s!"PASS sha256 self-test: {records.size} CAVP records from {relative} reproduced, including Len = 0, 24, 440, 448 and 512"
    return true
  IO.eprintln s!"FAIL sha256 self-test: {failures.size} problem(s)"
  for failure in failures do IO.eprintln s!"  {failure}"
  return false

def usage : String :=
  "usage: lake exe sha256 --self-test\n       lake exe sha256 <file>..."

/-- Command-line entry, invoked by `bin/Sha256.lean`. -/
def cli (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] =>
    if ← selfTest then return 0 else return 1
  | [] =>
    IO.eprintln usage
    return 2
  | paths =>
    if paths.any (fun p => p.startsWith "--") then
      IO.eprintln usage
      return 2
    for path in paths do
      IO.println s!"{← hexDigestOfFile path}  {path}"
    return 0

end Gates.Sha256
