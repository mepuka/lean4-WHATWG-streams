import Whatwg.Infra.Text.String

/-!
# Text.Substring

Owner: the six substring definitions of section `strings` of
`vendor/whatwg-infra-3f984adc/infra.bs`: the code unit substring "from
`start` with length `length`", "from `start` to `end`", and "from `start` to
the end of a string", and the code point substring in the same three forms.

The text guards the two primitive forms with `Assert:` steps on the indices.
Under ruling INFRA-R3 (`docs/INFRA-PROOF-PLAN.md`) an asserted index
precondition is a hypothesis argument, so each primitive takes
`start + length ≤ length-of-string` as an explicit proof and stays total
without clamping; "`start` and `length` are nonnegative" is discharged by
their type. An `Option`-returning variant of each primitive decides the
precondition at run time for callers that do not carry the proof. The
derived forms are transcribed as the text states them, as calls to the
primitive with the arithmetic the text gives, so the proof obligation they
pass down is the text's own.
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace JsString

/-- The loop shared by both primitive substrings, section `strings`: "Let
`result` be the empty string. For each `i` of the range from `start` to
`start` + `length`, exclusive: append the `i`th [element] of `string` to
`result`. Return `result`." Structural on the count of elements still to
append; the hypothesis keeps every index in bounds. -/
def appendRange {α : Type} (xs : List α) (i : Nat) :
    (count : Nat) → (h : i + count ≤ List.length xs) → List α
  | 0, _ => []
  | count + 1, h => xs[i]'(by omega) :: appendRange xs (i + 1) count (by omega)

/-- "The code unit substring from `start` with length `length` within a
string `string`", section `strings`: "Assert: `start` and `length` are
nonnegative. Assert: `start` + `length` is less than or equal to `string`'s
length. Let `result` be the empty string. For each `i` of the range from
`start` to `start` + `length`, exclusive: append the `i`th code unit of
`string` to `result`. Return `result`." The second assertion is the
hypothesis `h`; the first is the type `Nat`. -/
def codeUnitSubstring (s : JsString) (start length : Nat) (h : start + length ≤ s.length) :
    JsString :=
  appendRange s start length h

/-- `codeUnitSubstring` with its precondition decided at run time: `none`
exactly when the text's assertion would fail. -/
def codeUnitSubstring? (s : JsString) (start length : Nat) : Option JsString :=
  if h : start + length ≤ s.length then some (codeUnitSubstring s start length h) else none

/-- "The code unit substring from `start` to `end` within a string `string`
is the code unit substring from `start` with length `end` − `start` within
`string`", section `strings` (`code unit substring by positions`). The
hypothesis is the primitive's assertion for that length; with `start ≤ end`
the natural subtraction is the text's. -/
def codeUnitSubstringByPositions (s : JsString) (start «end» : Nat)
    (h : start + («end» - start) ≤ s.length) : JsString :=
  codeUnitSubstring s start («end» - start) h

/-- `codeUnitSubstringByPositions` with the precondition decided at run
time, together with `start ≤ end` so that the subtraction is the text's. -/
def codeUnitSubstringByPositions? (s : JsString) (start «end» : Nat) : Option JsString :=
  if h : start ≤ «end» ∧ start + («end» - start) ≤ s.length then
    some (codeUnitSubstringByPositions s start «end» h.2)
  else none

/-- "The code unit substring from `start` to the end of a string `string` is
the code unit substring from `start` to `string`'s length within `string`",
section `strings` (`code unit substring to the end of the string`). The
hypothesis is the one the by-positions form needs at `end` = length, which
reduces to `start ≤ length`. -/
def codeUnitSubstringToEnd (s : JsString) (start : Nat) (h : start ≤ s.length) : JsString :=
  codeUnitSubstringByPositions s start s.length (by omega)

/-- `codeUnitSubstringToEnd` with its precondition decided at run time. -/
def codeUnitSubstringToEnd? (s : JsString) (start : Nat) : Option JsString :=
  if h : start ≤ s.length then some (codeUnitSubstringToEnd s start h) else none

/-- "The code point substring within a string `string` from `start` with
length `length`", section `strings`: "Assert: `start` and `length` are
nonnegative. Assert: `start` + `length` is less than or equal to `string`'s
code point length. Let `result` be the empty string. For each `i` of the
range from `start` to `start` + `length`, exclusive: append the `i`th code
point of `string` to `result`. Return `result`." The code points are those
of `codePoints`, and the result is the string of the appended code points. -/
def codePointSubstring (s : JsString) (start length : Nat)
    (h : start + length ≤ s.codePointLength) : JsString :=
  ofCodePoints (appendRange (codePoints s) start length h)

/-- `codePointSubstring` with its precondition decided at run time. -/
def codePointSubstring? (s : JsString) (start length : Nat) : Option JsString :=
  if h : start + length ≤ s.codePointLength then some (codePointSubstring s start length h)
  else none

/-- "The code point substring from `start` to `end` within a string `string`
is the code point substring within `string` from `start` with length `end` −
`start`", section `strings` (`code point substring by positions`). -/
def codePointSubstringByPositions (s : JsString) (start «end» : Nat)
    (h : start + («end» - start) ≤ s.codePointLength) : JsString :=
  codePointSubstring s start («end» - start) h

/-- `codePointSubstringByPositions` with the precondition decided at run
time, together with `start ≤ end` so that the subtraction is the text's. -/
def codePointSubstringByPositions? (s : JsString) (start «end» : Nat) : Option JsString :=
  if h : start ≤ «end» ∧ start + («end» - start) ≤ s.codePointLength then
    some (codePointSubstringByPositions s start «end» h.2)
  else none

/-- "The code point substring from `start` to the end of a string `string`
is the code point substring from `start` to `string`'s code point length
within `string`", section `strings` (`code point substring to the end of the
string`). -/
def codePointSubstringToEnd (s : JsString) (start : Nat) (h : start ≤ s.codePointLength) :
    JsString :=
  codePointSubstringByPositions s start s.codePointLength (by omega)

/-- `codePointSubstringToEnd` with its precondition decided at run time. -/
def codePointSubstringToEnd? (s : JsString) (start : Nat) : Option JsString :=
  if h : start ≤ s.codePointLength then some (codePointSubstringToEnd s start h) else none

/-- The example of section `strings` (`example-code-unit-substring`): "The
code unit substring from 1 with length 3 within "Hello world" is "ell"." -/
example :
    codeUnitSubstring (ofLiteral "Hello world") 1 3 (by decide) = ofLiteral "ell" := by decide

/-- The same example's second sentence: "This can also be expressed as the
code unit substring from 1 to 4." -/
example :
    codeUnitSubstringByPositions (ofLiteral "Hello world") 1 4 (by decide) = ofLiteral "ell" := by
  decide

/-- The note of section `strings`: "the code unit substring from 0 to 0
within the empty string is the empty string, even though there is no code
unit at index 0 within the empty string". -/
example : codeUnitSubstringByPositions [] 0 0 (by decide) = [] := by decide

/-- The example of section `strings` (`example-code-unit-vs-point-substring`):
"the code point substring from 0 with length 1 within "👽" is "👽"". -/
example : codePointSubstring (ofLiteral "👽") 0 1 (by decide) = ofLiteral "👽" := by decide

/-- The same example's contrast: "the code unit substring from 0 with length
1 within "👽" is the string containing the single surrogate". U+1F47D is the
pair 0xD83D 0xDC7D, so that surrogate is 0xD83D; the text prints it as
U+D83B, which does not match its own pairing rule and is read as a slip. -/
example : codeUnitSubstring (ofLiteral "👽") 0 1 (by decide) = [0xD83D] := by decide

end JsString

end Whatwg.Infra
