import Whatwg.Infra.Bytes.Byte
import Whatwg.Infra.Text.String

/-!
# Text.Codec

Owner: the four byte-to-string and string-to-byte conversions of
`vendor/whatwg-infra-3f984adc/infra.bs` that need no encoding: "isomorphic
decode" (the last algorithm of section `byte-sequences`), and "isomorphic
encode", "ASCII encode", and "ASCII decode" (section `strings`).

Isomorphic decode is total: every byte value is a code point. The three
others are stated by the text only on isomorphic strings, ASCII strings, and
byte sequences of ASCII bytes; under ruling INFRA-R3
(`docs/INFRA-PROOF-PLAN.md`) that restriction is a hypothesis argument, and
the encoders use it to obtain each byte from a code point value known to be
below 0x100. Each restricted conversion also has an `Option`-returning form
that decides its hypothesis at run time, and isomorphic encode has an
unchecked total form that reduces every code point value modulo 0x100, for
callers that already know the string is isomorphic.
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- "To isomorphic decode a byte sequence `input`, return a string whose code
point length is equal to `input`'s length and whose code points have the
same values as the values of `input`'s bytes, in the same order", section
`byte-sequences`. A byte value is below 0x100, so it is a code point. -/
def isomorphicDecode (input : ByteSequence) : JsString :=
  JsString.ofCodePoints (input.map fun b =>
    ⟨b.value, Nat.le_of_lt_succ (Nat.lt_of_lt_of_le b.toNat_lt (by decide))⟩)

namespace JsString

/-- "To isomorphic encode an isomorphic string `input`: return a byte
sequence whose length is equal to `input`'s code point length and whose
bytes have the same values as the values of `input`'s code points, in the
same order", section `strings`. The hypothesis is the text's restriction to
isomorphic strings; it bounds every code point value below 0x100, which is
what makes the byte of that value exist. -/
def isomorphicEncode (input : JsString) (h : input.isIsomorphicString = true) : ByteSequence :=
  (codePoints input).pmap
    (fun c (hc : c.inRange 0x00 0xFF = true) =>
      UInt8.ofNatLT c.val (Nat.lt_succ_of_le (of_decide_eq_true hc).2))
    (List.all_eq_true.mp h)

/-- `isomorphicEncode` with its hypothesis decided at run time: `none` when
the string is not an isomorphic string. -/
def isomorphicEncode? (input : JsString) : Option ByteSequence :=
  if h : input.isIsomorphicString = true then some (isomorphicEncode input h) else none

/-- The total map underlying `isomorphicEncode`, with no hypothesis: each
code point value is taken modulo 0x100 by `UInt8.ofNat`. Precondition: the
string is an isomorphic string, in which case no reduction occurs and this
is the text's "isomorphic encode"; on any other string the result is not one
the text defines. -/
def isomorphicEncodeUnchecked (input : JsString) : ByteSequence :=
  (codePoints input).map fun c => UInt8.ofNat c.val

/-- An ASCII string is an isomorphic string: every ASCII code point, "in the
range U+0000 NULL to U+007F DELETE", is "in the range U+0000 NULL to U+00FF
(ÿ)". This is the fact "ASCII encode" relies on when it returns the
isomorphic encoding of an ASCII string. -/
theorem isIsomorphicString_of_isAsciiString (s : JsString) (h : s.isAsciiString = true) :
    s.isIsomorphicString = true :=
  List.all_eq_true.mpr fun c hc =>
    have ha : c.inRange 0x00 0x7F = true := List.all_eq_true.mp h c hc
    decide_eq_true ⟨(of_decide_eq_true ha).1, Nat.le_trans (of_decide_eq_true ha).2 (by decide)⟩

/-- "To ASCII encode an ASCII string `input`: return the isomorphic encoding
of `input`", section `strings`. The hypothesis is the text's restriction to
ASCII strings, from which the isomorphic string hypothesis follows. -/
def asciiEncode (input : JsString) (h : input.isAsciiString = true) : ByteSequence :=
  isomorphicEncode input (isIsomorphicString_of_isAsciiString input h)

/-- `asciiEncode` with its hypothesis decided at run time: `none` when the
string is not an ASCII string. -/
def asciiEncode? (input : JsString) : Option ByteSequence :=
  if h : input.isAsciiString = true then some (asciiEncode input h) else none

end JsString

/-- "To ASCII decode a byte sequence `input`, run these steps: Assert: all
bytes in `input` are ASCII bytes. Return the isomorphic decoding of
`input`", section `strings`. The assertion is the hypothesis; the text notes
it "ensures that isomorphic decode and UTF-8 decode return the same string
for this input". -/
def asciiDecode (input : ByteSequence) (_h : input.all Byte.isAscii = true) : JsString :=
  isomorphicDecode input

/-- `asciiDecode` with its assertion decided at run time: `none` when some
byte is not an ASCII byte. -/
def asciiDecode? (input : ByteSequence) : Option JsString :=
  if h : input.all Byte.isAscii = true then some (asciiDecode input h) else none

end Whatwg.Infra
