import Whatwg.Infra.Text.String

/-!
# Text.Scalar

Owner: the bridge between the scalar value of section `code-points` of
`vendor/whatwg-infra-3f984adc/infra.bs` and Lean's `Char`, and through it the
bridge between a scalar value string of section `strings` and Lean's
`String`.

A scalar value is "a code point that is not a surrogate" (`ScalarValue`,
ruling INFRA-R2), and a `Char` is a `UInt32` with `Char.valid`, which says
the value is below U+D800 or strictly between U+DFFF and U+110000. Those are
the same set, so the two directions `ScalarValue.toChar` and
`ScalarValue.ofChar` are each other's inverses; the two round-trip theorems
are the `ScalarValue ≃ Char` bridge named by `docs/INFRA-PROOF-PLAN.md`
section 3.

Over strings, `JsString.ofString` is the UTF-16 view of a Lean string, and
`JsString.toString?` recovers a Lean string exactly from a scalar value string,
"a string whose code points are all scalar values", and is `none` otherwise
(INFRA-R3), since a Lean `String` cannot hold a lone surrogate (INFRA-R1).
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace CodePoint

/-- Every `Char` is at most U+10FFFF, from `Char.valid`. -/
theorem char_toNat_le (c : Char) : c.toNat ≤ 0x10FFFF := by
  have h := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at h
  show c.val.toNat ≤ 0x10FFFF
  omega

/-- The code point of a `Char`, section `code-points`: a `Char` is a scalar
value, hence "a Unicode code point … in the range U+0000 to U+10FFFF". -/
def ofChar (c : Char) : CodePoint := ⟨c.toNat, char_toNat_le c⟩

/-- The code point of a `Char` is "not a surrogate", from `Char.valid`. -/
theorem ofChar_isSurrogate (c : Char) : (ofChar c).isSurrogate = false := by
  have h := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at h
  unfold ofChar
  simp only [isSurrogate, isLeadingSurrogate, isTrailingSurrogate, inRange,
    Bool.or_eq_false_iff, decide_eq_false_iff_not]
  show ¬(0xD800 ≤ c.val.toNat ∧ c.val.toNat ≤ 0xDBFF) ∧
    ¬(0xDC00 ≤ c.val.toNat ∧ c.val.toNat ≤ 0xDFFF)
  omega

end CodePoint

namespace ScalarValue

/-- A scalar value's number satisfies `Nat.isValidChar`: being "not a
surrogate" and at most U+10FFFF is exactly `Char`'s validity condition. -/
theorem isValidChar (s : ScalarValue) : Nat.isValidChar s.val.val := by
  have h := s.property
  have hle := s.val.isLe
  simp only [CodePoint.isSurrogate, CodePoint.isLeadingSurrogate,
    CodePoint.isTrailingSurrogate, CodePoint.inRange, Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at h
  unfold Nat.isValidChar
  omega

/-- The `Char` of a scalar value, section `code-points`: "a code point that is
not a surrogate" is exactly what `Char.valid` admits. -/
def toChar (s : ScalarValue) : Char := Char.ofNatAux s.val.val (isValidChar s)

/-- The scalar value of a `Char`, section `code-points`: its code point is
"not a surrogate" by `Char.valid`. -/
def ofChar (c : Char) : ScalarValue := ⟨CodePoint.ofChar c, CodePoint.ofChar_isSurrogate c⟩

/-- `Char.ofNatAux` returns the number it was given. -/
theorem toNat_ofNatAux (n : Nat) (h : n.isValidChar) : (Char.ofNatAux n h).toNat = n := by
  simp [Char.ofNatAux, Char.toNat]

/-- `ofChar` is a left inverse of `toChar`: the bridge is injective from
scalar values into `Char`. -/
theorem ofChar_toChar (s : ScalarValue) : ofChar (toChar s) = s :=
  Subtype.ext (CodePoint.ext (toNat_ofNatAux s.val.val (isValidChar s)))

/-- `toChar` is a left inverse of `ofChar`: the bridge is injective from
`Char` into scalar values. With `ofChar_toChar` this is `ScalarValue ≃ Char`. -/
theorem toChar_ofChar (c : Char) : toChar (ofChar c) = c :=
  Char.ext (UInt32.toNat.inj (toNat_ofNatAux c.toNat (isValidChar (ofChar c))))

end ScalarValue

namespace JsString

/-- The string of a Lean `String`, section `strings`: each `Char` is a scalar
value, so the string is the code units of its code points, "converting"
astral scalar values to surrogate pairs under `unitsOfCodePoint`. This is the
UTF-16 view of the Lean string. -/
def ofString (t : String) : JsString := ofCodePoints (t.toList.map CodePoint.ofChar)

/-- The Lean `String` of a scalar value string, section `strings`: defined
exactly when the string is "a string whose code points are all scalar values"
(`isScalarValueString`), and `none` otherwise (INFRA-R3), since a Lean
`String` holds scalar values only. Under the guard every code point is valid
for `Char.ofNat`, so its fallback to U+0000 is never taken. -/
def toString? (s : JsString) : Option String :=
  if isScalarValueString s then
    some (String.ofList ((codePoints s).map fun c => Char.ofNat c.val))
  else none

end JsString

end Whatwg.Infra
