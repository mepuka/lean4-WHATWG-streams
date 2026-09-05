import Whatwg.Infra.Bytes.Byte

/-!
# Bytes.Sequence

Owner: the operations over byte sequences of section `byte-sequences` of
`vendor/whatwg-infra-3f984adc/infra.bs`: a byte sequence's length,
byte-lowercase, byte-uppercase, byte-case-insensitive match, prefix and its
synonym "starts with", and byte less than. `isomorphic decode` of the same
section is a text operation and is owned by the text modules, not here.

The carrier is `ByteSequence := List Byte` from `Whatwg.Infra.Bytes.Byte`
(ruling INFRA-R1 family, `docs/INFRA-PROOF-PLAN.md` section 3). The two
numbered-step algorithms of the section, prefix and byte less than, are
transcribed step for step as total functions: their `While true` loop and
"smallest index" search become fuel-bounded recursion whose fuel is a length
the data already carries, with the fuel invariant stated in each docstring.
A structural companion of prefix via `List.isPrefixOf` is given as well and
is marked as such; the step transcription is the primary definition.

Every predicate here is `Bool`-valued and transcribes one sentence or one
numbered algorithm of the pinned text, quoted in its docstring.
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace ByteSequence

/-- Section `byte-sequences`, "length": "A byte sequence's length is the number
of bytes it contains". -/
def length (s : ByteSequence) : Nat := List.length s

/-- Section `byte-sequences`, "byte-lowercase": "To byte-lowercase a byte
sequence, increase each byte it contains, in the range 0x41 (A) to 0x5A (Z),
inclusive, by 0x20". -/
def byteLowercase (s : ByteSequence) : ByteSequence :=
  s.map fun b => if 0x41 ≤ b ∧ b ≤ 0x5A then b + 0x20 else b

/-- Section `byte-sequences`, "byte-uppercase": "To byte-uppercase a byte
sequence, subtract each byte it contains, in the range 0x61 (a) to 0x7A (z),
inclusive, by 0x20". -/
def byteUppercase (s : ByteSequence) : ByteSequence :=
  s.map fun b => if 0x61 ≤ b ∧ b ≤ 0x7A then b - 0x20 else b

/-- Section `byte-sequences`, "byte-case-insensitive": "A byte sequence A is a
byte-case-insensitive match for a byte sequence B, if the byte-lowercase of A
is the byte-lowercase of B". -/
def isByteCaseInsensitiveMatch (a b : ByteSequence) : Bool :=
  a.byteLowercase == b.byteLowercase

/-- The loop body of section `byte-sequences`, "prefix", from step 2 with the
index `i` of step 1 threaded through: "While true: If i is greater than or
equal to potentialPrefix's length, then return true. If i is greater than or
equal to input's length, then return false. Let potentialPrefixByte be the ith
byte of potentialPrefix. Let inputByte be the ith byte of input. Return false
if potentialPrefixByte is not inputByte. Set i to i + 1."

The loop is fuel-bounded: `isPrefix` starts it with fuel
`potentialPrefix.length` at `i = 0`, and each iteration increases `i` by one
and spends one fuel, so `fuel + i = potentialPrefix.length` throughout. Fuel
`0` therefore means `i` has reached `potentialPrefix`'s length, which is the
first step's `return true`; the two agree, and no iteration is ever cut short
by exhausted fuel. -/
def isPrefixLoop (potentialPrefix input : ByteSequence) : Nat → Nat → Bool
  | _, 0 => true
  | i, fuel + 1 =>
    if hp : i < potentialPrefix.length then
      if hi : i < input.length then
        if potentialPrefix[i] != input[i] then false
        else isPrefixLoop potentialPrefix input (i + 1) fuel
      else false
    else true

/-- Section `byte-sequences`, "prefix": "A byte sequence potentialPrefix is a
prefix of a byte sequence input if the following steps return true: Let i be
0. While true: …" (the loop is `isPrefixLoop`). This step transcription is the
primary definition; `isPrefixStructural` is its structural companion. -/
def isPrefix (potentialPrefix input : ByteSequence) : Bool :=
  isPrefixLoop potentialPrefix input 0 potentialPrefix.length

/-- Structural companion of `isPrefix`, section `byte-sequences`, "prefix",
stated through `List.isPrefixOf` rather than the numbered steps. It is not the
primary definition; `isPrefix` is. -/
def isPrefixStructural (potentialPrefix input : ByteSequence) : Bool :=
  List.isPrefixOf potentialPrefix input

/-- Section `byte-sequences`, "starts with": "'input starts with
potentialPrefix' can be used as a synonym for 'potentialPrefix is a prefix of
input'". -/
def startsWith (input potentialPrefix : ByteSequence) : Bool :=
  potentialPrefix.isPrefix input

/-- The search of section `byte-sequences`, "byte less than", step 3: "Let n
be the smallest index such that the nth byte of a is different from the nth
byte of b", scanning indices upward from `i`.

The scan is fuel-bounded: `isByteLessThan` starts it with fuel `a.length` at
`i = 0`, and each step increases `i` by one and spends one fuel, so
`fuel + i = a.length` throughout; a differing index, when one exists, lies
below `a.length` and is found before the fuel runs out. `none` is returned
when an index runs past either sequence, which the spec's parenthetical
"(There has to be such an index, since neither byte sequence is a prefix of
the other.)" rules out at the only call site. -/
def firstDifferingIndex (a b : ByteSequence) : Nat → Nat → Option Nat
  | _, 0 => none
  | i, fuel + 1 =>
    if ha : i < a.length then
      if hb : i < b.length then
        if a[i] == b[i] then firstDifferingIndex a b (i + 1) fuel
        else some i
      else none
    else none

/-- Section `byte-sequences`, "byte less than": "A byte sequence a is byte less
than a byte sequence b if the following steps return true: If b is a prefix of
a, then return false. If a is a prefix of b, then return true. Let n be the
smallest index such that the nth byte of a is different from the nth byte of
b. (There has to be such an index, since neither byte sequence is a prefix of
the other.) If the nth byte of a is less than the nth byte of b, then return
true. Return false."

Step 3 is `firstDifferingIndex`. The `none` branch and the missing-byte
branch of the final match are unreachable by the spec's parenthetical, since
steps 1 and 2 have already returned when either sequence is a prefix of the
other; they return false so the function is total. -/
def isByteLessThan (a b : ByteSequence) : Bool :=
  if b.isPrefix a then false
  else if a.isPrefix b then true
  else
    match firstDifferingIndex a b 0 a.length with
    | some n =>
      match a[n]?, b[n]? with
      | some x, some y => decide (x < y)
      | _, _ => false
    | none => false

/-! ### Examples

Drawn from the section's own example byte sequences: 0x48 0x49, "can also be
represented as `HI`", and the header `Content-Type`. -/

example : byteLowercase [0x48, 0x49] = [0x68, 0x69] := by decide

example : byteUppercase [0x68, 0x69] = [0x48, 0x49] := by decide

example : ([0x48, 0x49] : ByteSequence).length = 2 := by decide

example :
    isByteCaseInsensitiveMatch
      [0x43, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x54, 0x79, 0x70, 0x65]
      [0x63, 0x6F, 0x6E, 0x74, 0x65, 0x6E, 0x74, 0x2D, 0x74, 0x79, 0x70, 0x65] = true := by
  decide

example : isPrefix [0x48] [0x48, 0x49] = true := by decide

example : isPrefix [0x48, 0x49] [0x48] = false := by decide

example : isPrefixStructural [0x48] [0x48, 0x49] = isPrefix [0x48] [0x48, 0x49] := by decide

example : startsWith [0x48, 0x49] [0x48] = true := by decide

example : isByteLessThan [0x48] [0x48, 0x49] = true := by decide

example : isByteLessThan [0x48, 0x49] [0x48] = false := by decide

example : isByteLessThan [0x48, 0x49] [0x48, 0x4A] = true := by decide

example : isByteLessThan [0x48, 0x49] [0x48, 0x49] = false := by decide

end ByteSequence

end Whatwg.Infra
