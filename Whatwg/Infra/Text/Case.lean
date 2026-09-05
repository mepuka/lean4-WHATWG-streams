import Whatwg.Infra.Text.String

/-!
# Text.Case

Owner: the ASCII case operations of section `strings` of
`vendor/whatwg-infra-3f984adc/infra.bs`: "ASCII lowercase", "ASCII
uppercase", and the "ASCII case-insensitive" match.

The text replaces ASCII upper alphas and ASCII lower alphas, which are
classes of code points (section `code-points`), so each operation is stated
on the code point view of the string and returns the string of the replaced
code points. The corresponding code point of an ASCII alpha in the other
case is the one 0x20 away, the distance between U+0041 (A) and U+0061 (a).
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace JsString

/-- The distance between an ASCII upper alpha and "their corresponding code
point in ASCII lower alpha": U+0061 (a) − U+0041 (A). -/
def asciiCaseDistance : Nat := 0x20

/-- One step of "ASCII lowercase", section `strings`: an ASCII upper alpha is
replaced "with their corresponding code point in ASCII lower alpha"; any
other code point is kept. The replacement stays in range because an ASCII
upper alpha is at most U+005A (Z). -/
def lowerCodePoint (c : CodePoint) : CodePoint :=
  if h : c.isAsciiUpperAlpha = true then
    ⟨c.val + asciiCaseDistance, by
      simp only [CodePoint.isAsciiUpperAlpha, CodePoint.inRange, decide_eq_true_eq] at h
      simp only [asciiCaseDistance]
      omega⟩
  else c

/-- One step of "ASCII uppercase", section `strings`: an ASCII lower alpha is
replaced "with their corresponding code point in ASCII upper alpha"; any
other code point is kept. The replacement stays in range because it is
smaller than the code point replaced. -/
def upperCodePoint (c : CodePoint) : CodePoint :=
  if c.isAsciiLowerAlpha then
    ⟨c.val - asciiCaseDistance, Nat.le_trans (Nat.sub_le _ _) c.isLe⟩
  else c

/-- "To ASCII lowercase a string, replace all ASCII upper alphas in the
string with their corresponding code point in ASCII lower alpha", section
`strings`. -/
def asciiLowercase (s : JsString) : JsString :=
  ofCodePoints ((codePoints s).map lowerCodePoint)

/-- "To ASCII uppercase a string, replace all ASCII lower alphas in the
string with their corresponding code point in ASCII upper alpha", section
`strings`. -/
def asciiUppercase (s : JsString) : JsString :=
  ofCodePoints ((codePoints s).map upperCodePoint)

/-- "A string `A` is an ASCII case-insensitive match for a string `B`, if the
ASCII lowercase of `A` is the ASCII lowercase of `B`", section `strings`;
"is" being `identical`. -/
def isAsciiCaseInsensitiveMatch (a b : JsString) : Bool :=
  identical (asciiLowercase a) (asciiLowercase b)

end JsString

end Whatwg.Infra
