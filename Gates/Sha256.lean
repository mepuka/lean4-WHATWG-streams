import Hash
import Gates.Common

/-!
# Gates.Sha256

The digest face of the gates. Since step 6 of `docs/HASH-PACKAGE-PLAN.md`
this module holds no hash arithmetic and no self-test: every digest is
`Hash.Sha256.sha256` and every hexadecimal spelling is `Hash.Sha256.Hex.encode`,
from the required `hash` package, whose meaning is
`Hash.Sha256.Bridge.sha256_bridge` and whose known-answer tests, axiom audit,
and CAVP self-test run in that package. The vendor seal and the census
compute SHA-256 only.
-/

namespace Gates.Sha256

/-- Hexadecimal SHA-256 of a byte array, through the proved library. -/
def hexDigest (message : ByteArray) : String := (Hash.Sha256.sha256 message).toHex

/-- Hexadecimal SHA-256 of the UTF-8 encoding of a string. -/
def hexDigestOfString (text : String) : String := hexDigest text.toUTF8

/-- Hexadecimal SHA-256 of a file's bytes. -/
def hexDigestOfFile (path : System.FilePath) : IO String := do
  return hexDigest (← IO.FS.readBinFile path)

end Gates.Sha256
