import Sha256.Spec

/-!
# `Sha256.Hex` — lowercase hexadecimal

Shape copied from foldlab `formal/fips202`'s A1.S1 `Hex`, rewritten here rather
than imported because zero Lake dependencies is part of this artifact's trust
statement.

Lowercase only, in both directions (ruling R-5): the vendor manifest and every
pin in this repository are lowercase, and a case-insensitive decoder would
accept a spelling no gate ever produces.

## Why the theorems are stated on `List Char`

`docs/SHA256-DAG.md` §4 A1.S3 records the coordinator's measurement that
`String.length` and `String.toList` reach `Classical.choice` under v4.33.1, and
directs this stage to make `encode` a `List Char` producer wrapped by
`String.ofList` and to state the length theorem on the `List Char` form,
"because a theorem whose statement mentions `String.length` inherits
`Classical.choice` from the statement itself".

That is what is done here, and it is confirmed by measurement:
`String.ofList` and `String.toUTF8` are axiom-free, while `String.toList`,
`String.length`, `String.toList_ofList` and `String.length_ofList` all report
`[propext, Classical.choice, Quot.sound]`. So `encodeChars`, `decodeChars?` and
their three theorems are the proved content, and `encode` and `decode?` are
`String`-typed wrappers over them. `decode?` reaches its characters through
`String.toUTF8`, which is axiom-free, rather than through `String.toList`, so
the R-3 exact-declaration list stays **empty**.

The cost is real and is stated rather than hidden: no theorem relates
`decode? (encode bs)` to `bs` at the `String` layer, because every route between
`String.ofList` and `String.toUTF8` in v4.33.1 core leaves the ceiling.
`decodeChars?_encodeChars` carries the whole round trip one layer down.
-/

namespace Sha256.Hex

/-- The sixteen lowercase hexadecimal digits, in value order. -/
private def digitTable : List Char :=
  ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']

/-- The lowercase hexadecimal digit of a value, read modulo 16. -/
def digit (n : Nat) : Char := digitTable.getD (n % 16) '0'

/-- The value of a lowercase hexadecimal digit. Uppercase is rejected (R-5). -/
def digitValue? (c : Char) : Option Nat :=
  let i := digitTable.idxOf c
  if i < 16 then some i else none

theorem digitValue?_digit (n : Nat) : digitValue? (digit n) = some (n % 16) := by
  have hall : ∀ m : Fin 16, digitValue? (digit m.val) = some m.val := by decide
  have h := hall ⟨n % 16, Nat.mod_lt _ (by decide)⟩
  rw [show digit (n % 16) = digit n from by
    simp only [digit]; congr 1; omega] at h
  exact h

theorem toLower_digit (n : Nat) : (digit n).toLower = digit n := by
  have hall : ∀ m : Fin 16, (digit m.val).toLower = digit m.val := by decide
  have h := hall ⟨n % 16, Nat.mod_lt _ (by decide)⟩
  rwa [show digit (n % 16) = digit n from by simp only [digit]; congr 1; omega] at h

/-! ## Encoding -/

/-- Two lowercase digits per byte, high nibble first, no separators. -/
def encodeCharsOfList (l : List UInt8) : List Char :=
  l.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)]

/-- The proved encoder. `encode` is this wrapped in `String.ofList`. -/
def encodeChars (bs : ByteArray) : List Char := encodeCharsOfList bs.data.toList

/-- Lowercase hexadecimal spelling of a byte array, two characters per byte,
no separators. -/
def encode (bs : ByteArray) : String := String.ofList (encodeChars bs)

/-! ## Decoding -/

private def decodeAux : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest =>
      match digitValue? a, digitValue? b, decodeAux rest with
      | some x, some y, some t => some (UInt8.ofNat (16 * x + y) :: t)
      | _, _, _ => none

/-- The proved decoder: `none` on an odd length or on any character that is not
a lowercase hexadecimal digit. -/
def decodeChars? (cs : List Char) : Option ByteArray := (decodeAux cs).map List.toByteArray

/-- The characters of a byte array read as ASCII. Used only to give `decode?` a
`String` face without `String.toList`, which is outside the axiom ceiling. -/
private def asciiChars (bs : ByteArray) : List Char :=
  bs.data.toList.map fun b => Char.ofNat b.toNat

/-- Lowercase hexadecimal decoding of a string, through its UTF-8 bytes. On the
lowercase ASCII this module produces, these are the string's own characters. -/
def decode? (s : String) : Option ByteArray := decodeChars? (asciiChars s.toUTF8)

/-! ## Facts -/

/-- Two `ByteArray`s with the same bytes are the same `ByteArray`, by structure
eta on `ByteArray` and `Array`. -/
theorem byteArray_eq_of_data {x y : ByteArray} (h : x.data.toList = y.data.toList) : x = y := by
  have hx : x = ⟨⟨x.data.toList⟩⟩ := rfl
  have hy : y = ⟨⟨y.data.toList⟩⟩ := rfl
  rw [hx, hy, h]

theorem toByteArray_data_toList (bs : ByteArray) : bs.data.toList.toByteArray = bs :=
  byteArray_eq_of_data List.toList_data_toByteArray

theorem length_encodeCharsOfList (l : List UInt8) :
    (encodeCharsOfList l).length = 2 * l.length :=
  Spec.length_flatMap_const l _ 2 fun _ => rfl

/-- The frozen `length_encode` of `docs/SHA256-DAG.md` §4 A1.S3, stated on the
`List Char` form as §4's own measured note directs. -/
theorem length_encodeChars (bs : ByteArray) : (encodeChars bs).length = 2 * bs.size := by
  rw [encodeChars, length_encodeCharsOfList, Array.length_toList]
  rfl

theorem decodeAux_encodeCharsOfList (l : List UInt8) : decodeAux (encodeCharsOfList l) = some l := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      have hlt : b.toNat < 256 := Nat.lt_of_lt_of_le b.toNat_lt (by decide)
      have hd1 : digitValue? (digit (b.toNat / 16)) = some (b.toNat / 16) := by
        rw [digitValue?_digit, Nat.mod_eq_of_lt (by omega)]
      have hd2 : digitValue? (digit (b.toNat % 16)) = some (b.toNat % 16) := by
        rw [digitValue?_digit]
        congr 1
        omega
      have hb : UInt8.ofNat (16 * (b.toNat / 16) + b.toNat % 16) = b := by
        rw [show 16 * (b.toNat / 16) + b.toNat % 16 = b.toNat by omega, UInt8.ofNat_toNat]
      have hstep : encodeCharsOfList (b :: t)
          = digit (b.toNat / 16) :: digit (b.toNat % 16) :: encodeCharsOfList t := rfl
      rw [hstep]
      simp only [decodeAux, hd1, hd2, ih, hb]

/-- The frozen `decode?_encode` of §4 A1.S3, stated on the `List Char` form. -/
theorem decodeChars?_encodeChars (bs : ByteArray) : decodeChars? (encodeChars bs) = some bs := by
  rw [decodeChars?, encodeChars, decodeAux_encodeCharsOfList, Option.map_some,
    toByteArray_data_toList]

/-- The frozen `encode_lower` of §4 A1.S3, stated on the `List Char` form:
every character produced is already lowercase (R-5). -/
theorem encodeChars_lower (bs : ByteArray) : ∀ c ∈ encodeChars bs, c.toLower = c := by
  intro c hc
  rw [encodeChars, encodeCharsOfList, List.mem_flatMap] at hc
  obtain ⟨b, _, hcb⟩ := hc
  rcases List.mem_cons.mp hcb with h | h
  · rw [h]; exact toLower_digit _
  · rcases List.mem_cons.mp h with h' | h'
    · rw [h']; exact toLower_digit _
    · exact absurd h' (List.not_mem_nil)

end Sha256.Hex
