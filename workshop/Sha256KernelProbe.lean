/-!
# Scratch measurement: kernel and interpreter cost of the `Impl` shape

**This file is not part of any library.** It is outside every `lean_lib` glob
in `lakefile.toml`, it is imported by nothing, and it states nothing that any
other file may rely on. It exists to produce two numbers for stage S1.0.4 of
`docs/SHA256-DAG.md`:

1. what one `decide +kernel` SHA-256 compression over `BitVec 32` costs the
   kernel, which is what ruling R-4 needs in order to size the S1.1 kernel
   known-answer test; and
2. what the `Impl`-shaped definitions cost the interpreter on real input,
   which is what §2's prediction is about.

**Nothing here is a known-answer test.** The literal in `kernelProbe` below
was produced by `#eval` of the definitions in this same file, so it tests the
kernel against the interpreter and nothing else. A digest that disagreed with
FIPS 180-4 would still make it pass. The real known-answer tests arrive at
S1.1, on `Sha256.Impl`, with literals transcribed from
`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp`.

The definitions mirror the shape `docs/SHA256-DAG.md` §4 A1.S1 prescribes for
`Sha256.Impl`, because the shape is what is being measured: `BitVec 32` words,
`Vector` state and schedule, `Nat.fold` for every bounded loop, proof-carrying
indexing, no `Id.run do`, no `xs[i]!`, no `partial`, no `unsafe`, no `IO`
inside a definition. `IO` appears only in the `#eval` wrappers at the end.

The constants are transcribed from the pinned FIPS 180-4 PDF
(`vendor/nist-fips-180-4/NIST.FIPS.180-4.pdf`, sha256
`0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82`), §4.2.2
and §5.3.3, read from page images (physical pages 16 and 20, printed 11 and
15). They are transcribed again, independently, by the S1.1 seat into
`Sha256/Spec.lean`; this copy carries no authority.
-/

namespace Sha256KernelProbe

abbrev W := BitVec 32

/-- FIPS 180-4 §4.1.2 (4.2). -/
def Ch (x y z : W) : W := (x &&& y) ^^^ (~~~x &&& z)

/-- FIPS 180-4 §4.1.2 (4.3). -/
def Maj (x y z : W) : W := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 §4.1.2 (4.4). -/
def BigSigma0 (x : W) : W := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- FIPS 180-4 §4.1.2 (4.5). -/
def BigSigma1 (x : W) : W := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- FIPS 180-4 §4.1.2 (4.6). -/
def smallSigma0 (x : W) : W := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- FIPS 180-4 §4.1.2 (4.7). -/
def smallSigma1 (x : W) : W := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- FIPS 180-4 §4.2.2. -/
def K : Vector W 64 :=
  #v[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- FIPS 180-4 §5.3.3. -/
def H0 : Vector W 8 :=
  #v[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- FIPS 180-4 §6.2.2 step 1: `Wt = Mt` for `0 ≤ t ≤ 15`, and
`σ1(W t-2) + W t-7 + σ0(W t-15) + W t-16` for `16 ≤ t ≤ 63`. -/
def schedule (m : Vector W 16) : Vector W 64 :=
  Nat.fold 48
    (fun i _ acc =>
      let t := i + 16
      have h2 : t - 2 < 64 := by omega
      have h7 : t - 7 < 64 := by omega
      have h15 : t - 15 < 64 := by omega
      have h16 : t - 16 < 64 := by omega
      acc.set t
        (smallSigma1 acc[t - 2] + acc[t - 7] + smallSigma0 acc[t - 15] + acc[t - 16])
        (by omega))
    (Vector.ofFn (fun i : Fin 64 => if h : i.val < 16 then m[i.val] else 0))

/-- FIPS 180-4 §6.2.2 steps 2–4, on one block. The working state is carried as
`⟨a, b, c, d, e, f, g, h⟩`. -/
def compress (H : Vector W 8) (m : Vector W 16) : Vector W 8 :=
  let sched := schedule m
  let final :=
    Nat.fold 64
      (fun t ht st =>
        let a := st[0]
        let b := st[1]
        let c := st[2]
        let d := st[3]
        let e := st[4]
        let f := st[5]
        let g := st[6]
        let h := st[7]
        let T1 := h + BigSigma1 e + Ch e f g + K[t] + sched[t]
        let T2 := BigSigma0 a + Maj a b c
        #v[T1 + T2, a, b, c, d + T1, e, f, g])
      H
  Vector.ofFn (fun i : Fin 8 =>
    have hi : i.1 < 8 := i.2
    H[i.1] + final[i.1])

/-! ## The kernel probe

One compression of the all-zero block from the FIPS 180-4 initial hash value.
The all-zero block is not a padded message, so this value is not a digest of
anything; it is a fixed point of the round function's data flow chosen because
it needs no padding code to state. -/

def zeroBlock : Vector W 16 := Vector.replicate 16 0

-- `#eval compress H0 zeroBlock` produced the literal below.

/-- The measurement. The right-hand side is the value `#eval` of the
definitions above prints; it is not read from FIPS 180-4 and not read from a
vector file, so this theorem checks the kernel against the interpreter and
nothing more. Its cost, not its truth, is the point. -/
theorem kernelProbe :
    compress H0 zeroBlock =
      #v[0xda5698be, 0x17b9b469, 0x62335799, 0x779fbeca,
         0x8ce5d491, 0xc0d26243, 0xbafef9ea, 0x1837a9d8] := by
  decide +kernel

/-! ## The interpreter probe

`Impl`-shaped byte handling, so that `#eval` on a real file measures what
`Sha256.Impl` will cost. No `IO` and no partiality inside any definition. -/

def wordOfBytes (b0 b1 b2 b3 : UInt8) : W :=
  (b0.toUInt32.toBitVec <<< 24) ||| (b1.toUInt32.toBitVec <<< 16) |||
    (b2.toUInt32.toBitVec <<< 8) ||| b3.toUInt32.toBitVec

def wordsOfBlock (block : List UInt8) : Vector W 16 :=
  Vector.ofFn (fun i : Fin 16 =>
    wordOfBytes (block.getD (4 * i.1) 0) (block.getD (4 * i.1 + 1) 0)
      (block.getD (4 * i.1 + 2) 0) (block.getD (4 * i.1 + 3) 0))

/-- Big-endian 8-byte encoding of the bit length, FIPS 180-4 §5.1.1. -/
def lengthBytes (bitLength : Nat) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat (bitLength >>> (8 * (7 - i))))

/-- FIPS 180-4 §5.1.1 at byte granularity: `0x80`, then zeros to 56 mod 64,
then the 8-byte big-endian bit length. -/
def padBytes (msg : List UInt8) : List UInt8 :=
  let n := msg.length
  let zeros := (119 - (n % 64)) % 64
  msg ++ (0x80 :: List.replicate zeros 0) ++ lengthBytes (8 * n)

-- `h` is used by `decreasing_by`, which the unused-variable linter does not see.
set_option linter.unusedVariables false in
def blocks (P : List UInt8) : List (List UInt8) :=
  if h : P.isEmpty then [] else P.take 64 :: blocks (P.drop 64)
termination_by P.length
decreasing_by
  simp only [List.isEmpty_iff] at h
  have : 0 < P.length := List.length_pos_iff.mpr h
  simp only [List.length_drop]
  omega

def hash (msg : List UInt8) : Vector W 8 :=
  (blocks (padBytes msg)).foldl (fun H block => compress H (wordsOfBlock block)) H0

def bytesOfWord (w : W) : List UInt8 :=
  [UInt8.ofNat (w >>> 24).toNat, UInt8.ofNat (w >>> 16).toNat,
   UInt8.ofNat (w >>> 8).toNat, UInt8.ofNat w.toNat]

def sha256 (msg : List UInt8) : List UInt8 :=
  (List.range 8).flatMap (fun i => bytesOfWord ((hash msg).getD i 0))

def hexOfByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits.getD (b.toNat / 16) '?', digits.getD (b.toNat % 16) '?']

def hex (bs : List UInt8) : String := String.join (bs.map hexOfByte)

/-! ## Wrappers. `IO` lives here and nowhere else in this file. -/

/-- Digest of the empty message; a cheap check that `padBytes`/`blocks`/`hash`
are wired up before the file probe is timed. Expected (CAVP `Len = 0`):
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. -/
def emptyDigest : String := hex (sha256 [])

def digestOfFile (path : System.FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile path
  return hex (sha256 bytes.data.toList)

def digestOfPrefix (path : System.FilePath) (n : Nat) : IO String := do
  let bytes ← IO.FS.readBinFile path
  return hex (sha256 (bytes.data.toList.take n))

end Sha256KernelProbe
