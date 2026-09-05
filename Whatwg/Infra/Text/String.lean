import Whatwg.Infra.Text.CodePoint

/-!
# Text.String

Owner: the string carrier of section `strings` of
`vendor/whatwg-infra-3f984adc/infra.bs`, its two lengths, its code point
view, the three restricted string kinds, and `convert`.

A string "is a sequence of 16-bit unsigned integers, also known as code
units", "also known as a JavaScript string". The carrier is `List UInt16`
and deliberately not Lean's `String` (ruling INFRA-R1,
`docs/INFRA-PROOF-PLAN.md` section 3): Lean's `String` is UTF-8 over scalar
values, so it cannot hold the lone surrogate of the text's own example and its
`length` counts what the text calls code point length. The type is named
`JsString` after the text's synonym so that Lean's `String` stays available
for prose and rendering.

The code point view transcribes the rule the text cites from ECMA-262 §6.1.4
and restates in its own note: "this conversion process converts surrogate
pairs into their corresponding scalar value and maps any remaining surrogates
to their corresponding code point, leaving them effectively as-is".
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- A code unit, section `strings`: a "16-bit unsigned integer". -/
abbrev CodeUnit := UInt16

/-- A string, section `strings`: "a sequence of 16-bit unsigned integers,
also known as code units … also known as a JavaScript string". -/
abbrev JsString := List CodeUnit

namespace CodeUnit

/-- Whether a code unit is in the leading-surrogate range 0xD800 to 0xDBFF. -/
def isLeadingSurrogate (u : CodeUnit) : Bool := decide (0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF)

/-- Whether a code unit is in the trailing-surrogate range 0xDC00 to 0xDFFF. -/
def isTrailingSurrogate (u : CodeUnit) : Bool := decide (0xDC00 ≤ u.toNat ∧ u.toNat ≤ 0xDFFF)

end CodeUnit

namespace JsString

/-- A string's length, section `strings`: "the number of code units it
contains". -/
def length (s : JsString) : Nat := List.length s

/-- The scalar value a leading and a trailing surrogate encode, ECMA-262
§6.1.4 as cited by section `strings`: `(lead − 0xD800) × 0x400 + (trail −
0xDC00) + 0x10000`. The bound is forced by the two ranges. -/
def pairValue (lead trail : CodeUnit) (hl : 0xD800 ≤ lead.toNat ∧ lead.toNat ≤ 0xDBFF)
    (ht : 0xDC00 ≤ trail.toNat ∧ trail.toNat ≤ 0xDFFF) : CodePoint :=
  ⟨(lead.toNat - 0xD800) * 0x400 + (trail.toNat - 0xDC00) + 0x10000, by omega⟩

/-- A string "interpreted as containing code points", section `strings`:
surrogate pairs become their scalar value and any remaining surrogate stays a
code point. Every code unit is consumed exactly once, so this is total. -/
def codePoints : JsString → List CodePoint
  | [] => []
  | u :: rest =>
    if hl : 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF then
      match rest with
      | v :: rest' =>
        if ht : 0xDC00 ≤ v.toNat ∧ v.toNat ≤ 0xDFFF then
          pairValue u v hl ht :: codePoints rest'
        else
          CodePoint.ofUnit u :: codePoints (v :: rest')
      | [] => [CodePoint.ofUnit u]
    else
      CodePoint.ofUnit u :: codePoints rest

/-- The code units of one code point: itself below U+10000, and otherwise the
surrogate pair of ECMA-262 §6.1.4. -/
def unitsOfCodePoint (c : CodePoint) : List CodeUnit :=
  if c.val < 0x10000 then [UInt16.ofNat c.val]
  else
    let v := c.val - 0x10000
    [UInt16.ofNat (0xD800 + v / 0x400), UInt16.ofNat (0xDC00 + v % 0x400)]

/-- The string whose code points are the given list, section `strings` read
in the other direction; the inverse of `codePoints` on strings, and of
`codePoints` on code point lists with no adjacent leading-then-trailing pair. -/
def ofCodePoints (cs : List CodePoint) : JsString := cs.flatMap unitsOfCodePoint

/-- A string's code point length, section `strings`: "the number of code
points it contains". -/
def codePointLength (s : JsString) : Nat := (codePoints s).length

/-- An ASCII string, section `strings`: "a string whose code points are all
ASCII code points". -/
def isAsciiString (s : JsString) : Bool := (codePoints s).all CodePoint.isAscii

/-- An isomorphic string, section `strings`: "a string whose code points are
all in the range U+0000 NULL to U+00FF (ÿ), inclusive". -/
def isIsomorphicString (s : JsString) : Bool := (codePoints s).all (·.inRange 0x00 0xFF)

/-- A scalar value string, section `strings`: "a string whose code points are
all scalar values". -/
def isScalarValueString (s : JsString) : Bool := (codePoints s).all CodePoint.isScalarValue

/-- `convert` a string into a scalar value string, section `strings`:
"replace any surrogates with U+FFFD (�)". The replaced surrogates are the lone
ones, since `codePoints` has already paired the pairs. -/
def convert (s : JsString) : JsString :=
  ofCodePoints ((codePoints s).map fun c =>
    if c.isSurrogate then replacementCharacter.val else c)

/-- Two strings are identical, section `strings`: "if it consists of the same
sequence of code units". List equality is that relation. -/
def identical (a b : JsString) : Bool := decide (a = b)

/-- The string of a Lean literal, for examples and constants: every `Char` is
a scalar value, so each becomes its code units under `unitsOfCodePoint`. The
`none` branch is unreachable because `Char.toNat` is below U+110000; it is
written out so the definition is total without a proof about `Char`. -/
def ofLiteral (t : String) : JsString :=
  t.toList.flatMap fun c =>
    match CodePoint.ofNat? c.toNat with
    | some cp => unitsOfCodePoint cp
    | none => []

end JsString

end Whatwg.Infra
