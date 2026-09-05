/-!
# Bytes.Byte

Owner: the byte and byte-sequence carriers of the Infra Standard, sections
`bytes` and `byte-sequences` of `vendor/whatwg-infra-3f984adc/infra.bs`.

A byte "is a sequence of eight bits" whose value "is its underlying number";
an ASCII byte "is a byte in the range 0x00 (NUL) to 0x7F (DEL), inclusive"; a
byte sequence "is a sequence of bytes". The carriers are `UInt8` and
`List UInt8` at the proof face (ruling INFRA-R1 family, `docs/INFRA-PROOF-PLAN.md`
section 3); an `Array` or `ByteArray` realizer is a representation-edge
concern and is not defined here. The operations over byte sequences live in
`Whatwg.Infra.Bytes.Sequence`.
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- A byte, section `bytes`: "a sequence of eight bits … in the range 0x00 to
0xFF, inclusive". -/
abbrev Byte := UInt8

namespace Byte

/-- A byte's value, section `bytes`: "its underlying number". -/
def value (b : Byte) : Nat := b.toNat

/-- An ASCII byte, section `bytes`: "a byte in the range 0x00 (NUL) to 0x7F
(DEL), inclusive". -/
def isAscii (b : Byte) : Bool := b ≤ 0x7F

end Byte

/-- A byte sequence, section `byte-sequences`: "a sequence of bytes". -/
abbrev ByteSequence := List Byte

end Whatwg.Infra
