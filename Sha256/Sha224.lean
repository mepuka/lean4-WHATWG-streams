import Sha256.Api

/-!
# `Sha256.Sha224` — SHA-224 from FIPS 180-4 §6.3

`docs/SHA256-DAG.md` §4 A1.S6. FIPS 180-4 §6.3, read from the vendored PDF
`vendor/nist-fips-180-4/NIST.FIPS.180-4.pdf` (sealed by
`generated/vendor-manifest.tsv`), printed pages 23–24: "SHA-224 … is defined in
the exact same manner as SHA-256 (Section 6.2), with the following two
exceptions: 1. The initial hash value, H(0), shall be set as specified in Sec.
5.3.2; and 2. The 224-bit message digest is obtained by truncating the final
hash value, H(N), to its left-most 224 bits", spelled there as
`H₀ ‖ H₁ ‖ H₂ ‖ H₃ ‖ H₄ ‖ H₅ ‖ H₆` — the first seven words.

So the whole of SHA-224 is: the same `compress`, `schedule`, `pad`, `parse`
and output map, run from a different initial value and cut to 28 bytes. That
is why this module adds no arithmetic. It generalises `hash` to `hashWith`,
which takes the initial value as an argument, proves the existing `hash` is
`hashWith Spec.H0`, and carries every layer's SHA-256 theorem across to the
generalised form.

The eight §5.3.2 words below were transcribed from page images of the vendored
PDF, printed page 14 for `H₀`–`H₆` and printed page 15 for `H₇`, never from
memory (`docs/SHA256-DAG.md` §3.4). `Bridge.sha224IV_eq` pins that they are the
same eight words as the S1.2 negative's `Bridge.sha224IV`.

Known-answer vectors come from `vendor/nist-cavp-sha224/SHA224ShortMsg.rsp`
(NIST CAVP, CAVS 11.0, generated 2011-03-15), pinned at S1.6 out of the git
object of the prior-art clone and sealed. The `Impl`-level guards are in
`Sha256.Kats`; this file ends with the same five witnesses restated on the
public API.
-/

namespace Sha256

/-! ## §5.3.2 and §6.2.2 at the specification layer -/

namespace Spec

/-- FIPS 180-4 §5.3.2: the SHA-224 initial hash value, the eight 32-bit words
of printed pages 14–15 of the vendored standard. -/
def H0_224 : Vector Word 8 :=
  #v[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
     0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

/-- FIPS 180-4 §6.2.2 with the initial hash value supplied. `hash` is this at
`H0`; SHA-224 is this at `H0_224`. -/
def hashWith (iv : Vector Word 8) (M : List Bool) : Vector Word 8 :=
  (parse (pad M)).foldl compress iv

theorem hash_eq_hashWith (M : List Bool) : hash M = hashWith H0 M := rfl

/-- FIPS 180-4 §6.3: SHA-224 is SHA-256 from the §5.3.2 initial value,
truncated to the left-most 224 bits. -/
def sha224 (M : List Bool) : List Bool := (bitsOfWords (hashWith H0_224 M)).take 224

/-- SHA-224 on byte-aligned messages, the only domain this lane claims. -/
def sha224_bytes (msg : List UInt8) : List UInt8 := bytesOfBits (sha224 (bitsOfBytes msg))

theorem length_sha224 (M : List Bool) : (sha224 M).length = 224 := by
  rw [sha224, List.length_take, length_bitsOfWords]
  omega

end Spec

/-! ## The byte-level reference -/

namespace Impl

/-- FIPS 180-4 §6.2 with the initial hash value supplied. -/
def hashWith (iv : St) (msg : List UInt8) : St :=
  ((blocks (padBytes msg)).map wordsOfBlock).foldl compress iv

theorem hash_eq_hashWith (msg : List UInt8) : hash msg = hashWith Spec.H0 msg := rfl

/-- FIPS 180-4 §3.1: the untruncated 32 output bytes of a final hash value. -/
def hashBytes (H : St) : List UInt8 := (List.finRange 8).flatMap fun i => bytesOfWord H[i]

theorem length_hashBytes (H : St) : (hashBytes H).length = 32 := by
  rw [hashBytes, Spec.length_flatMap_const _ _ 4 fun _ => length_bytesOfWord _]
  simp

theorem sha256_eq_hashBytes (msg : List UInt8) : sha256 msg = hashBytes (hash msg) := rfl

/-- The 28-byte SHA-224 digest: the left-most 28 of the 32 output bytes of the
run from the §5.3.2 initial value.

Meaning: `Sha256.Bridge.sha224_bridge`, which proves this equals
`Sha256.Spec.sha224_bytes`. -/
def sha224 (msg : List UInt8) : List UInt8 := (hashBytes (hashWith Spec.H0_224 msg)).take 28

theorem length_sha224 (msg : List UInt8) : (sha224 msg).length = 28 := by
  rw [sha224, List.length_take, length_hashBytes]
  omega

end Impl

/-! ## The bridge -/

namespace Bridge

/-- The S1.2 negative's constant and the §5.3.2 constant are the same eight
words. `Bridge.sha224IV` stays as the name `Bridge.sha256_ne_sha224_iv` is
stated on; `Spec.H0_224` is the constant SHA-224 is defined from. -/
theorem sha224IV_eq : sha224IV = Spec.H0_224 := rfl

/-- The byte-level reference computes the FIPS 180-4 function from any initial
hash value, not only `H0`. `hash_bridge` is this at `Spec.H0`. -/
theorem hashWith_bridge (iv : Impl.St) (msg : List UInt8) :
    Impl.hashWith iv msg = Spec.hashWith iv (Spec.bitsOfBytes msg) := by
  rw [Impl.hashWith, Spec.hashWith, ← padBytes_bridge,
    blocks_bridge _ (Impl.length_padBytes msg)]
  rfl

/-- The SHA-224 apex: the byte-level reference computes the FIPS 180-4 §6.3
function on every byte string. -/
theorem sha224_bridge (msg : List UInt8) : Impl.sha224 msg = Spec.sha224_bytes msg := by
  rw [Impl.sha224, Impl.hashBytes, Spec.sha224_bytes, Spec.sha224, ← hashWith_bridge,
    ← output_bridge, show (224 : Nat) = 8 * 28 from rfl, ← bitsOfBytes_take,
    Spec.bytesOfBits_bitsOfBytes]

/-- The final form of the discriminating negative (`docs/SHA256-DAG.md` §4
A1.S6): running the identical algorithm from the §5.3.2 initial value gives a
different untruncated digest on the empty message, so the initial value is
load-bearing. Injectivity of `compress` is not claimed and is not needed. -/
theorem sha256_ne_hashWith_sha224IV :
    Impl.sha256 [] ≠ (List.finRange 8).flatMap
      (fun i => Impl.bytesOfWord (Impl.hashWith Spec.H0_224 [])[i]) := by
  decide +kernel

end Bridge

/-! ## The native layer -/

namespace Fast

/-- FIPS 180-4 §5.3.2 at native width; `H0_224_eq` pins that these are
`Spec.H0_224`. -/
def H0_224 : St :=
  #v[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
     0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

theorem H0_224_eq : abs H0_224 = Spec.H0_224 := by
  apply Vector.ext
  intro i hi
  rw [abs, Vector.getElem_map]
  match i, hi with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl

/-- `hashAll` with the initial hash value supplied, over already-padded bytes. -/
def hashWith (iv : St) (P : ByteArray) : St := hashFrom P iv (P.size / 64) 0

theorem hashAll_eq_hashWith (P : ByteArray) : hashAll P = hashWith H0 P := rfl

theorem hashWith_abs (iv : St) (P : ByteArray) :
    abs (hashWith iv P)
      = ((Impl.blocks P.data.toList).map Impl.wordsOfBlock).foldl Impl.compress (abs iv) := by
  have hsize : P.data.toList.length = P.size := Array.length_toList
  rw [hashWith, hashFrom_abs P (P.size / 64) iv 0 (by omega), List.drop_zero,
    show 64 * (P.size / 64) = 64 * (P.data.toList.length / 64) from by rw [hsize],
    blocks_take_multiple]

/-- The 28 left-most output bytes of a final hash value. -/
def squeeze224 (H : St) : ByteArray :=
  (((List.finRange 8).flatMap fun i => bytesOfWord H[i]).take 28).toByteArray

private theorem flatMap_abs (H : St) :
    ((List.finRange 8).flatMap fun i => bytesOfWord H[i])
      = (List.finRange 8).flatMap fun i => Impl.bytesOfWord (abs H)[i] :=
  List.toList_data_toByteArray.symm.trans (squeeze_eq H)

def sha224 (msg : ByteArray) : ByteArray := squeeze224 (hashWith H0_224 (padBytes msg))

theorem sha224_eq_impl (msg : ByteArray) :
    (sha224 msg).data.toList = Impl.sha224 msg.data.toList := by
  rw [sha224, squeeze224, List.toList_data_toByteArray, flatMap_abs, Impl.sha224,
    Impl.hashBytes, hashWith_abs, padBytes_eq, H0_224_eq, Impl.hashWith]

theorem size_sha224 (msg : ByteArray) : (sha224 msg).size = 28 := by
  rw [sha224, squeeze224, List.size_toByteArray, List.length_take,
    Spec.length_flatMap_const _ _ 4 fun _ => rfl]
  simp

end Fast

/-! ## The public API -/

/-- The two algorithms this library computes. -/
inductive Algorithm where
  /-- FIPS 180-4 §6.2. -/
  | sha256
  /-- FIPS 180-4 §6.3. -/
  | sha224
  deriving DecidableEq, Repr

/-- The digest length in bytes. -/
def Algorithm.outputBytes : Algorithm → Nat
  | .sha256 => 32
  | .sha224 => 28

/-- SHA-224 of a byte string.

**Meaning**: `sha224_spec`. The digest is `Sha256.Spec.sha224_bytes` of the
input bytes, that is, the function FIPS 180-4 §6.3 defines.

**Trust base**: as `Sha256.sha256` — the FIPS 180-4 transcription in
`Sha256.Spec`, whose fidelity to the published standard is a named human step,
and the Lean v4.33.1 kernel. No security property of any kind is claimed. -/
def sha224 (msg : ByteArray) : Digest 28 := ⟨Fast.sha224 msg, Fast.size_sha224 msg⟩

/-- SHA-224 of the UTF-8 encoding of a string. -/
def sha224String (s : String) : Digest 28 := sha224 s.toUTF8

/-- Either algorithm, with the digest length carried by the type. -/
def digest (alg : Algorithm) (msg : ByteArray) : Digest alg.outputBytes :=
  match alg with
  | .sha256 => sha256 msg
  | .sha224 => sha224 msg

theorem digest_sha256 (msg : ByteArray) : digest .sha256 msg = sha256 msg := rfl

theorem digest_sha224 (msg : ByteArray) : digest .sha224 msg = sha224 msg := rfl

theorem sha224_impl (msg : ByteArray) :
    (sha224 msg).toList = Impl.sha224 msg.data.toList :=
  Fast.sha224_eq_impl msg

theorem sha224_spec (msg : ByteArray) :
    (sha224 msg).toList = Spec.sha224_bytes msg.data.toList := by
  rw [sha224_impl, Bridge.sha224_bridge]

/-! ## The five CAVP SHA-224 witnesses, restated on the API

Produced mechanically from the vendored, sealed
`vendor/nist-cavp-sha224/SHA224ShortMsg.rsp` by reading each record's `Len`,
`Msg` and `MD` fields and splitting the hex into byte literals; never retyped.
The `Len` values are the same five the SHA-256 witnesses use — `0`, `24`, `440`,
`448`, `512` — because the SHA-224 file contains a record at each of them. The
messages differ from the SHA-256 file's; the two files are independent vector
sets. `Sha256.Kats` runs the same five on `Impl.sha224`. -/

/-! CAVP `Len = 0` (the file's `Msg = 00` placeholder is one byte of hex text
for a zero-length message). -/
#guard (sha224 (List.toByteArray [])).toList ==
  [0xd1, 0x4a, 0x02, 0x8c, 0x2a, 0x3a, 0x2b, 0xc9, 0x47, 0x61, 0x02, 0xbb, 0x28, 0x82, 0x34, 0xc4,
   0x15, 0xa2, 0xb0, 0x1f, 0x82, 0x8e, 0xa6, 0x2a, 0xc5, 0xb3, 0xe4, 0x2f]

/-! CAVP `Len = 24`. -/
#guard (sha224 (List.toByteArray [0x51, 0xca, 0x3d])).toList ==
  [0x2c, 0x89, 0x59, 0x02, 0x35, 0x15, 0x47, 0x6e, 0x38, 0x38, 0x8a, 0xbb, 0x43, 0x59, 0x9a, 0x29,
   0x87, 0x6b, 0x4b, 0x33, 0xd5, 0x6a, 0xdc, 0x06, 0x03, 0x2d, 0xe3, 0xa2]

/-! CAVP `Len = 440`, 55 bytes: the last length whose padding fits one block. -/
#guard (sha224 (List.toByteArray
  [0x44, 0x5e, 0x86, 0x98, 0xee, 0xb8, 0xac, 0xcb, 0xaa, 0xc4, 0xff, 0xa7, 0xd9, 0x34, 0xff, 0xfd,
   0x16, 0x01, 0x4a, 0x43, 0x0e, 0xf7, 0x0f, 0x3a, 0x91, 0x74, 0xc6, 0xcf, 0xe9, 0x6d, 0x1e, 0x3f,
   0x6a, 0xb1, 0x37, 0x7f, 0x4a, 0x72, 0x12, 0xdb, 0xb3, 0x01, 0x46, 0xdd, 0x17, 0xd9, 0xf4, 0x70,
   0xc4, 0xdf, 0xfc, 0x45, 0xb8, 0xe8, 0x71])).toList ==
  [0x4c, 0x7a, 0xe0, 0x28, 0xc0, 0xfe, 0x61, 0xf2, 0xa9, 0xca, 0xda, 0x61, 0xfa, 0xe3, 0x06, 0x85,
   0xb7, 0x7f, 0x04, 0xc6, 0x44, 0x25, 0x76, 0xe9, 0x12, 0xaf, 0x9f, 0xa6]

/-! CAVP `Len = 448`, 56 bytes: the padding spills into a second block. -/
#guard (sha224 (List.toByteArray
  [0x52, 0x83, 0x9f, 0x2f, 0x08, 0x53, 0xa3, 0x0d, 0xf1, 0x4e, 0xc8, 0x97, 0xa1, 0x91, 0x4c, 0x68,
   0x5c, 0x1a, 0xc2, 0x14, 0x70, 0xd0, 0x06, 0x54, 0xc8, 0xc3, 0x76, 0x63, 0xbf, 0xb6, 0x5f, 0xa7,
   0x32, 0xdb, 0xb6, 0x94, 0xd9, 0xdd, 0x09, 0xce, 0xd7, 0x23, 0xb4, 0x8d, 0x8f, 0x54, 0x58, 0x46,
   0xba, 0x16, 0x89, 0x88, 0xb6, 0x1c, 0xc7, 0x24])).toList ==
  [0x2f, 0x75, 0x5a, 0x57, 0x67, 0x4b, 0x49, 0xd5, 0xc2, 0x5c, 0xb3, 0x73, 0x48, 0xf3, 0x5b, 0x6f,
   0xd2, 0xde, 0x25, 0x52, 0xc7, 0x49, 0xf2, 0x64, 0x5b, 0xa6, 0x3d, 0x20]

/-! CAVP `Len = 512`, 64 bytes: the padding is a whole extra block. -/
#guard (sha224 (List.toByteArray
  [0xa3, 0x31, 0x0b, 0xa0, 0x64, 0xbe, 0x2e, 0x14, 0xad, 0x32, 0x27, 0x6e, 0x18, 0xcd, 0x03, 0x10,
   0xc9, 0x33, 0xa6, 0xe6, 0x50, 0xc3, 0xc7, 0x54, 0xd0, 0x24, 0x3c, 0x6c, 0x61, 0x20, 0x78, 0x65,
   0xb4, 0xb6, 0x52, 0x48, 0xf6, 0x6a, 0x08, 0xed, 0xf6, 0xe0, 0x83, 0x26, 0x89, 0xa9, 0xdc, 0x3a,
   0x2e, 0x5d, 0x20, 0x95, 0xee, 0xea, 0x50, 0xbd, 0x86, 0x2b, 0xac, 0x88, 0xc8, 0xbd, 0x31, 0x8d])).toList ==
  [0xb2, 0xa5, 0x58, 0x6d, 0x9c, 0xbf, 0x0b, 0xaa, 0x99, 0x91, 0x57, 0xb4, 0xaf, 0x06, 0xd8, 0x8a,
   0xe0, 0x8d, 0x7c, 0x9f, 0xaa, 0xb4, 0xbc, 0x1a, 0x96, 0x82, 0x9d, 0x65]

end Sha256
