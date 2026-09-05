/-!
# Primitive.Integer

Owner: the boolean and the nine fixed-width integer types of sections
`booleans` and `numbers` of `vendor/whatwg-infra-3f984adc/infra.bs`.

A boolean "is either true or false"; each N-bit integer "is an integer in the
range" the text states, inclusive. The carriers are Lean core's own
fixed-width types, `UInt8/16/32/64` and `Int8/16/32/64`, and `BitVec 128` for
the 128-bit unsigned integer, which core has no `UInt128` for (ruling
INFRA-R11, `docs/INFRA-PROOF-PLAN.md` section 3). Each type carries one range
theorem stating the sentence it transcribes over the carrier's `toNat` or
`toInt` view; that theorem is the row's witness that the carrier is exactly
the stated range and not a superset.

The text's note that "numbers are complicated" and defers general guidance
is not transcribed: no arithmetic is defined here.
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- A boolean, section `booleans`: "either true or false". -/
abbrev Boolean := Bool

/-- An 8-bit unsigned integer, section `numbers`: "an integer in the range 0
to 255 (0 to 2^8 − 1), inclusive". -/
abbrev Unsigned8 := UInt8

/-- The range of section `numbers` for an 8-bit unsigned integer: "0 to 255
… inclusive". -/
theorem Unsigned8.inRange (x : Unsigned8) : 0 ≤ x.toNat ∧ x.toNat ≤ 255 := by
  have := x.toNat_lt; omega

/-- A 16-bit unsigned integer, section `numbers`: "an integer in the range 0
to 65535 (0 to 2^16 − 1), inclusive". -/
abbrev Unsigned16 := UInt16

/-- The range of section `numbers` for a 16-bit unsigned integer: "0 to
65535 … inclusive". -/
theorem Unsigned16.inRange (x : Unsigned16) : 0 ≤ x.toNat ∧ x.toNat ≤ 65535 := by
  have := x.toNat_lt; omega

/-- A 32-bit unsigned integer, section `numbers`: "an integer in the range 0
to 4294967295 (0 to 2^32 − 1), inclusive". -/
abbrev Unsigned32 := UInt32

/-- The range of section `numbers` for a 32-bit unsigned integer: "0 to
4294967295 … inclusive". -/
theorem Unsigned32.inRange (x : Unsigned32) : 0 ≤ x.toNat ∧ x.toNat ≤ 4294967295 := by
  have := x.toNat_lt; omega

/-- A 64-bit unsigned integer, section `numbers`: "an integer in the range 0
to 18446744073709551615 (0 to 2^64 − 1), inclusive". -/
abbrev Unsigned64 := UInt64

/-- The range of section `numbers` for a 64-bit unsigned integer: "0 to
18446744073709551615 … inclusive". -/
theorem Unsigned64.inRange (x : Unsigned64) :
    0 ≤ x.toNat ∧ x.toNat ≤ 18446744073709551615 := by
  have := x.toNat_lt; omega

/-- A 128-bit unsigned integer, section `numbers`: "an integer in the range 0
to 340282366920938463463374607431768211455 (0 to 2^128 − 1), inclusive". The
text's example is that "an IPv6 address is a 128-bit unsigned integer". Lean
core has no `UInt128`, so the carrier is `BitVec 128` (ruling INFRA-R11). -/
abbrev Unsigned128 := BitVec 128

/-- The range of section `numbers` for a 128-bit unsigned integer: "0 to
340282366920938463463374607431768211455 … inclusive". -/
theorem Unsigned128.inRange (x : Unsigned128) :
    0 ≤ x.toNat ∧ x.toNat ≤ 340282366920938463463374607431768211455 := by
  have := x.isLt; omega

/-- An 8-bit signed integer, section `numbers`: "an integer in the range −128
to 127 (−2^7 to 2^7 − 1), inclusive". -/
abbrev Signed8 := Int8

/-- The range of section `numbers` for an 8-bit signed integer: "−128 to 127
… inclusive". -/
theorem Signed8.inRange (x : Signed8) : -128 ≤ x.toInt ∧ x.toInt ≤ 127 := by
  have := x.le_toInt; have := x.toInt_lt; omega

/-- A 16-bit signed integer, section `numbers`: "an integer in the range
−32768 to 32767 (−2^15 to 2^15 − 1), inclusive". -/
abbrev Signed16 := Int16

/-- The range of section `numbers` for a 16-bit signed integer: "−32768 to
32767 … inclusive". -/
theorem Signed16.inRange (x : Signed16) : -32768 ≤ x.toInt ∧ x.toInt ≤ 32767 := by
  have := x.le_toInt; have := x.toInt_lt; omega

/-- A 32-bit signed integer, section `numbers`: "an integer in the range
−2147483648 to 2147483647 (−2^31 to 2^31 − 1), inclusive". -/
abbrev Signed32 := Int32

/-- The range of section `numbers` for a 32-bit signed integer: "−2147483648
to 2147483647 … inclusive". -/
theorem Signed32.inRange (x : Signed32) :
    -2147483648 ≤ x.toInt ∧ x.toInt ≤ 2147483647 := by
  have := x.le_toInt; have := x.toInt_lt; omega

/-- A 64-bit signed integer, section `numbers`: "an integer in the range
−9223372036854775808 to 9223372036854775807 (−2^63 to 2^63 − 1), inclusive". -/
abbrev Signed64 := Int64

/-- The range of section `numbers` for a 64-bit signed integer:
"−9223372036854775808 to 9223372036854775807 … inclusive". -/
theorem Signed64.inRange (x : Signed64) :
    -9223372036854775808 ≤ x.toInt ∧ x.toInt ≤ 9223372036854775807 := by
  have := x.le_toInt; have := x.toInt_lt; omega

end Whatwg.Infra
