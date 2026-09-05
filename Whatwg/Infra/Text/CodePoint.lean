/-!
# Text.CodePoint

Owner: the code point carrier and every classification predicate of section
`code-points` of `vendor/whatwg-infra-3f984adc/infra.bs`: surrogates, scalar
values, noncharacters, and the ASCII and control classes.

A code point "is a Unicode code point … in the range U+0000 to U+10FFFF,
inclusive". The carrier is a bounded natural number and deliberately not
Lean's `Char` (ruling INFRA-R2, `docs/INFRA-PROOF-PLAN.md` section 3): `Char`
excludes the surrogate range, and the Infra text needs surrogates as code
points, for instance in its example string 0xD83D 0xDCA9 0xD800. A scalar
value, "a code point that is not a surrogate", is the subtype, and it is that
subtype which is in bijection with `Char`; the bridge lives in
`Whatwg.Infra.Text.Scalar`.

Every predicate here is `Bool`-valued and transcribes one sentence of the
pinned text, quoted in its docstring.
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- A code point, section `code-points`: "a Unicode code point … in the range
U+0000 to U+10FFFF, inclusive". -/
structure CodePoint where
  /-- The code point's value: "its underlying number". -/
  val : Nat
  /-- The upper bound of the range; the lower bound is `Nat`'s. -/
  isLe : val ≤ 0x10FFFF

namespace CodePoint

/-- The largest code point value, U+10FFFF. -/
def maxVal : Nat := 0x10FFFF

theorem ext {a b : CodePoint} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq CodePoint := fun a b =>
  if h : a.val = b.val then isTrue (ext h)
  else isFalse (fun e => h (congrArg CodePoint.val e))

instance : LT CodePoint := ⟨fun a b => a.val < b.val⟩
instance : LE CodePoint := ⟨fun a b => a.val ≤ b.val⟩
instance (a b : CodePoint) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : CodePoint) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.val ≤ b.val))

instance : Repr CodePoint :=
  ⟨fun c _ => "U+" ++ String.ofList (Nat.toDigits 16 c.val |>.map Char.toUpper)⟩

/-- The code point of a value known to be in range. -/
def ofNat (n : Nat) (h : n ≤ 0x10FFFF) : CodePoint := ⟨n, h⟩

/-- The code point of a value, or `none` above U+10FFFF. -/
def ofNat? (n : Nat) : Option CodePoint :=
  if h : n ≤ 0x10FFFF then some ⟨n, h⟩ else none

/-- The code point of a 16-bit code unit; every code unit is in range. -/
def ofUnit (u : UInt16) : CodePoint :=
  ⟨u.toNat, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le u.toNat_lt (by decide))⟩

/-- Whether the value lies in an inclusive range; the shape every class below
is stated in. -/
@[inline] def inRange (c : CodePoint) (lo hi : Nat) : Bool :=
  decide (lo ≤ c.val ∧ c.val ≤ hi)

/-- A leading surrogate: "a code point that is in the range U+D800 to U+DBFF,
inclusive". -/
def isLeadingSurrogate (c : CodePoint) : Bool := c.inRange 0xD800 0xDBFF

/-- A trailing surrogate: "a code point that is in the range U+DC00 to U+DFFF,
inclusive". -/
def isTrailingSurrogate (c : CodePoint) : Bool := c.inRange 0xDC00 0xDFFF

/-- A surrogate: "a leading surrogate or a trailing surrogate". -/
def isSurrogate (c : CodePoint) : Bool := c.isLeadingSurrogate || c.isTrailingSurrogate

/-- A scalar value: "a code point that is not a surrogate". -/
def isScalarValue (c : CodePoint) : Bool := !c.isSurrogate

/-- A noncharacter: "a code point that is in the range U+FDD0 to U+FDEF,
inclusive, or U+FFFE, U+FFFF, U+1FFFE, U+1FFFF, …, U+10FFFE, or U+10FFFF".
The 32 listed values outside the range are exactly the code points whose low
16 bits are 0xFFFE or 0xFFFF, which is how the second disjunct is written. -/
def isNoncharacter (c : CodePoint) : Bool :=
  c.inRange 0xFDD0 0xFDEF || decide (c.val % 0x10000 = 0xFFFE) || decide (c.val % 0x10000 = 0xFFFF)

/-- An ASCII code point: "a code point in the range U+0000 NULL to U+007F
DELETE, inclusive". -/
def isAscii (c : CodePoint) : Bool := c.inRange 0x00 0x7F

/-- An ASCII tab or newline: "U+0009 TAB, U+000A LF, or U+000D CR". -/
def isAsciiTabOrNewline (c : CodePoint) : Bool :=
  decide (c.val = 0x09) || decide (c.val = 0x0A) || decide (c.val = 0x0D)

/-- ASCII whitespace: "U+0009 TAB, U+000A LF, U+000C FF, U+000D CR, or U+0020
SPACE". -/
def isAsciiWhitespace (c : CodePoint) : Bool :=
  decide (c.val = 0x09) || decide (c.val = 0x0A) || decide (c.val = 0x0C) ||
    decide (c.val = 0x0D) || decide (c.val = 0x20)

/-- A C0 control: "a code point in the range U+0000 NULL to U+001F INFORMATION
SEPARATOR ONE, inclusive". -/
def isC0Control (c : CodePoint) : Bool := c.inRange 0x00 0x1F

/-- A C0 control or space: "a C0 control or U+0020 SPACE". -/
def isC0ControlOrSpace (c : CodePoint) : Bool := c.isC0Control || decide (c.val = 0x20)

/-- A control: "a C0 control or a code point in the range U+007F DELETE to
U+009F APPLICATION PROGRAM COMMAND, inclusive". -/
def isControl (c : CodePoint) : Bool := c.isC0Control || c.inRange 0x7F 0x9F

/-- An ASCII digit: "a code point in the range U+0030 (0) to U+0039 (9),
inclusive". -/
def isAsciiDigit (c : CodePoint) : Bool := c.inRange 0x30 0x39

/-- An ASCII upper hex digit: "an ASCII digit or a code point in the range
U+0041 (A) to U+0046 (F), inclusive". -/
def isAsciiUpperHexDigit (c : CodePoint) : Bool := c.isAsciiDigit || c.inRange 0x41 0x46

/-- An ASCII lower hex digit: "an ASCII digit or a code point in the range
U+0061 (a) to U+0066 (f), inclusive". -/
def isAsciiLowerHexDigit (c : CodePoint) : Bool := c.isAsciiDigit || c.inRange 0x61 0x66

/-- An ASCII hex digit: "an ASCII upper hex digit or ASCII lower hex digit". -/
def isAsciiHexDigit (c : CodePoint) : Bool := c.isAsciiUpperHexDigit || c.isAsciiLowerHexDigit

/-- An ASCII upper alpha: "a code point in the range U+0041 (A) to U+005A (Z),
inclusive". -/
def isAsciiUpperAlpha (c : CodePoint) : Bool := c.inRange 0x41 0x5A

/-- An ASCII lower alpha: "a code point in the range U+0061 (a) to U+007A (z),
inclusive". -/
def isAsciiLowerAlpha (c : CodePoint) : Bool := c.inRange 0x61 0x7A

/-- An ASCII alpha: "an ASCII upper alpha or ASCII lower alpha". -/
def isAsciiAlpha (c : CodePoint) : Bool := c.isAsciiUpperAlpha || c.isAsciiLowerAlpha

/-- An ASCII alphanumeric: "an ASCII digit or ASCII alpha". -/
def isAsciiAlphanumeric (c : CodePoint) : Bool := c.isAsciiDigit || c.isAsciiAlpha

end CodePoint

/-- A scalar value, section `code-points`: "a code point that is not a
surrogate". This is the subtype in bijection with Lean's `Char`. -/
abbrev ScalarValue := { c : CodePoint // c.isSurrogate = false }

/-- U+FFFD REPLACEMENT CHARACTER, the scalar value that `convert` substitutes
for a surrogate (section `strings`). -/
def replacementCharacter : ScalarValue := ⟨⟨0xFFFD, by decide⟩, by decide⟩

end Whatwg.Infra
