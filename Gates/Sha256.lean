/-!
# Gates.Sha256

SHA-256 (FIPS 180-4) over byte arrays, implemented in Lean so that every
digest the repository pins or checks is produced by code under the repository
trust gate rather than by a host utility.

This is tooling. It is total, uses no `partial` or `unsafe`, and reaches no
axiom beyond the implementation ceiling. It carries no theorem: the self-test
below is finite executable evidence against the FIPS 180-4 example vectors,
not a correctness proof.

Run `lake exe sha256 --self-test` or `lake exe sha256 <file>`.
-/

namespace Gates.Sha256

private def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def initialState : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] private def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
@[inline] private def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
@[inline] private def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
@[inline] private def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- Big-endian 32-bit word at a byte offset. -/
private def wordAt (bytes : ByteArray) (offset : Nat) : UInt32 :=
  (bytes[offset]!.toUInt32 <<< 24) ||| (bytes[offset + 1]!.toUInt32 <<< 16) |||
    (bytes[offset + 2]!.toUInt32 <<< 8) ||| bytes[offset + 3]!.toUInt32

/-- FIPS 180-4 §5.1.1 padding: one `0x80` byte, zeros to 56 mod 64, then the
message bit length as a 64-bit big-endian integer. -/
def pad (message : ByteArray) : ByteArray := Id.run do
  let bitLength : UInt64 := message.size.toUInt64 * 8
  let zeroCount := (120 - ((message.size + 1) % 64)) % 64
  let mut out := message.push 0x80
  for _ in [0:zeroCount] do
    out := out.push 0
  for i in [0:8] do
    out := out.push (bitLength >>> (8 * (7 - i)).toUInt64).toUInt8
  return out

/-- One compression round over the 64-byte block starting at `offset`. -/
private def compress (state : Array UInt32) (bytes : ByteArray) (offset : Nat) : Array UInt32 :=
  Id.run do
    let mut schedule : Array UInt32 := Array.mkEmpty 64
    for i in [0:16] do
      schedule := schedule.push (wordAt bytes (offset + 4 * i))
    for i in [16:64] do
      schedule := schedule.push
        (schedule[i - 16]! + smallSigma0 schedule[i - 15]! +
          schedule[i - 7]! + smallSigma1 schedule[i - 2]!)
    let mut a := state[0]!
    let mut b := state[1]!
    let mut c := state[2]!
    let mut d := state[3]!
    let mut e := state[4]!
    let mut f := state[5]!
    let mut g := state[6]!
    let mut h := state[7]!
    for i in [0:64] do
      let choose := (e &&& f) ^^^ ((~~~ e) &&& g)
      let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t1 := h + bigSigma1 e + choose + roundConstants[i]! + schedule[i]!
      let t2 := bigSigma0 a + majority
      h := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
             state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

/-- The 32-byte SHA-256 digest of a byte array. -/
def digest (message : ByteArray) : ByteArray := Id.run do
  let padded := pad message
  let mut state := initialState
  for block in [0:padded.size / 64] do
    state := compress state padded (block * 64)
  let mut out := ByteArray.empty
  for word in state do
    for i in [0:4] do
      out := out.push (word >>> (8 * (3 - i)).toUInt32).toUInt8
  return out

private def hexDigits : Array Char := "0123456789abcdef".toList.toArray

/-- Lowercase hexadecimal spelling of a byte array. -/
def hex (bytes : ByteArray) : String := Id.run do
  let mut out := ""
  for i in [0:bytes.size] do
    let byte := bytes[i]!
    out := out.push hexDigits[(byte >>> 4).toNat]!
    out := out.push hexDigits[(byte &&& 0xf).toNat]!
  return out

/-- Hexadecimal SHA-256 of a byte array. -/
def hexDigest (message : ByteArray) : String := hex (digest message)

/-- Hexadecimal SHA-256 of the UTF-8 encoding of a string. -/
def hexDigestOfString (text : String) : String := hexDigest text.toUTF8

/-- Hexadecimal SHA-256 of a file's bytes. -/
def hexDigestOfFile (path : System.FilePath) : IO String := do
  return hexDigest (← IO.FS.readBinFile path)

/-- FIPS 180-4 example vectors (Appendix B of the SHA-256 examples document)
plus the one-million-`a` vector. -/
def selfTestVectors : List (String × ByteArray × String) := [
  ("empty message", "".toUTF8,
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("\"abc\"", "abc".toUTF8,
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
  ("two-block message", "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8,
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
  ("55 bytes, padding boundary", (String.ofList (List.replicate 55 'a')).toUTF8,
    "9f4390f8d30c2dd92ec9f095b65e2b9ae9b0a925a5258e241c9f1e910f734318"),
  ("56 bytes, padding boundary", (String.ofList (List.replicate 56 'a')).toUTF8,
    "b35439a4ac6f0948b6d6f9e3c6af0f5f590ce20f1bde7090ef7970686ec6738a"),
  ("64 bytes, one full block", (String.ofList (List.replicate 64 'a')).toUTF8,
    "ffe054fe7ae0cb6dc65c3af9b61d5209f439851db43d0ba5997337df154668eb"),
  ("one million \"a\"", ByteArray.mk (Array.replicate 1000000 0x61),
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0")]

/-- Run the self-test and report each vector. Returns `true` when all match. -/
def selfTest : IO Bool := do
  let mut ok := true
  for (label, message, expected) in selfTestVectors do
    let actual := hexDigest message
    if actual == expected then
      IO.println s!"PASS sha256 {label}"
    else
      IO.eprintln s!"FAIL sha256 {label}: expected {expected}, computed {actual}"
      ok := false
  return ok

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
