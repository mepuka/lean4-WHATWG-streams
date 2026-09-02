import Sha256.Hex

/-!
# `Sha256.Digest` — a byte string whose length is carried by its type

Shape copied from foldlab `formal/fips202`'s A1.S1 `Digest`, rewritten here
rather than imported because zero Lake dependencies is part of this artifact's
trust statement.

As in `Sha256.Hex`, the hexadecimal facts are stated on the `List Char` form.
A theorem mentioning `String.length` or `String.toList` inherits
`Classical.choice` from its own statement under v4.33.1, which the ceiling of
`docs/SHA256-DAG.md` §3.1 forbids for this tree; §4 A1.S3's measured note
directs the `List Char` restatement.
-/

namespace Sha256

/-- A byte string whose length is carried by its type. -/
structure Digest (n : Nat) where
  bytes : ByteArray
  size_eq : bytes.size = n

namespace Digest

def toByteArray {n : Nat} (d : Digest n) : ByteArray := d.bytes

def toList {n : Nat} (d : Digest n) : List UInt8 := d.bytes.data.toList

/-- Lowercase hexadecimal spelling, two characters per byte (R-5). -/
def toHex {n : Nat} (d : Digest n) : String := Hex.encode d.bytes

/-- The proved form of `toHex`: the characters themselves. -/
def toHexChars {n : Nat} (d : Digest n) : List Char := Hex.encodeChars d.bytes

/-- Parse a digest of the required length from hexadecimal characters. -/
def ofHexChars? (n : Nat) (cs : List Char) : Option (Digest n) :=
  match Hex.decodeChars? cs with
  | some bs => if h : bs.size = n then some ⟨bs, h⟩ else none
  | none => none

/-- Parse a digest of the required length from a hexadecimal string. -/
def ofHex? (n : Nat) (s : String) : Option (Digest n) :=
  match Hex.decode? s with
  | some bs => if h : bs.size = n then some ⟨bs, h⟩ else none
  | none => none

theorem ext {n : Nat} {a b : Digest n} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  subst h
  rfl

theorem size_toByteArray {n : Nat} (d : Digest n) : d.toByteArray.size = n := d.size_eq

theorem length_toList {n : Nat} (d : Digest n) : d.toList.length = n := by
  rw [toList, Array.length_toList]
  exact d.size_eq

/-- The frozen `length_toHex` of `docs/SHA256-DAG.md` §4 A1.S3, on the
`List Char` form. -/
theorem length_toHexChars {n : Nat} (d : Digest n) : d.toHexChars.length = 2 * n := by
  rw [toHexChars, Hex.length_encodeChars, d.size_eq]

/-- The frozen `ofHex?_toHex` of §4 A1.S3, on the `List Char` form. -/
theorem ofHexChars?_toHexChars {n : Nat} (d : Digest n) :
    ofHexChars? n d.toHexChars = some d := by
  rw [ofHexChars?, toHexChars, Hex.decodeChars?_encodeChars]
  show (if h : d.bytes.size = n then some ⟨d.bytes, h⟩ else none) = some d
  rw [dif_pos d.size_eq]

instance instDecidableEq {n : Nat} : DecidableEq (Digest n) := fun a b =>
  if h : a.bytes.data.toList = b.bytes.data.toList then
    isTrue (ext (Hex.byteArray_eq_of_data h))
  else
    isFalse fun hab => h (by rw [hab])

instance instBEq {n : Nat} : BEq (Digest n) := instBEqOfDecidableEq

end Digest

end Sha256
