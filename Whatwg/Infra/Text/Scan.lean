import Whatwg.Infra.Text.Whitespace

/-!
# Text.Scan

Owner: the position-variable algorithms of section `strings` of
`vendor/whatwg-infra-3f984adc/infra.bs`: collect a sequence of code points,
skip ASCII whitespace, strictly split, split on ASCII whitespace, split on
commas, and concatenate.

The text's "position variable … tracking the position of the calling
algorithm within input" is modelled explicitly as a `Nat` index into the
code point view of the input. `collect` returns both the collected code
points and the updated position, exactly as the note says it "updates the
position variable in the calling algorithm", and each split threads that
position through its loop the same way.

The split loops are "while position is not past the end of input". Every
iteration advances the position by at least one, so the remaining length
`input.length - position` at loop entry bounds the iteration count; that
remaining length is the fuel each loop recurses on, which keeps every loop
total without a separate termination argument.
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace JsString

/-- U+002C (,), the delimiter of "split on commas". -/
def comma : CodePoint := ⟨0x2C, by decide⟩

/-- Collect a sequence of code points meeting a condition from `input`
given a position variable, section `strings`: "While position doesn't point
past the end of input and the code point at position within input meets the
condition condition: append that code point to the end of result; advance
position by 1. Return result." The returned pair is the result and the
updated position: "in addition to returning the collected code points, this
algorithm updates the position variable in the calling algorithm". -/
def collect (cond : CodePoint → Bool) (input : List CodePoint) (position : Nat) :
    List CodePoint × Nat :=
  let result := (input.drop position).takeWhile cond
  (result, position + result.length)

/-- Skip ASCII whitespace within `input` given a position variable, section
`strings`: "collect a sequence of code points that are ASCII whitespace from
input given position. The collected code points are not used, but position
is still updated." Returns the updated position. -/
def skipAsciiWhitespace (input : List CodePoint) (position : Nat) : Nat :=
  (collect CodePoint.isAsciiWhitespace input position).2

/-- The loop of strictly split, section `strings`: "While position is not
past the end of input: Assert: the code point at position within input is
delimiter. Advance position by 1. Let token be the result of collecting a
sequence of code points that are not equal to delimiter from input, given
position. Append token to tokens." The assertion holds because the previous
collect stopped only at a code point equal to `delimiter`; it is discharged
by that invariant, not checked. Fuel: the remaining length at entry. -/
def strictlySplitLoop (delimiter : CodePoint) (input : List CodePoint) :
    Nat → Nat → List (List CodePoint)
  | 0, _ => []
  | fuel + 1, position =>
    if position < input.length then
      let position := position + 1
      let (token, position) := collect (· != delimiter) input position
      token :: strictlySplitLoop delimiter input fuel position
    else []

/-- Strictly split a string `input` on a particular delimiter code point
`delimiter`, section `strings`: "Let position be a position variable for
input, initially pointing at the start of input. Let tokens be a list of
strings, initially empty. Let token be the result of collecting a sequence
of code points that are not equal to delimiter from input, given position.
Append token to tokens." Then the loop of `strictlySplitLoop`, and "Return
tokens." -/
def strictlySplit (input : JsString) (delimiter : CodePoint) : List JsString :=
  let cps := codePoints input
  let (token, position) := collect (· != delimiter) cps 0
  (token :: strictlySplitLoop delimiter cps (cps.length - position) position).map ofCodePoints

/-- The loop of split on ASCII whitespace, section `strings`: "While
position is not past the end of input: Let token be the result of collecting
a sequence of code points that are not ASCII whitespace from input, given
position. Append token to tokens. Skip ASCII whitespace within input given
position." Fuel: the remaining length at entry. -/
def splitOnAsciiWhitespaceLoop (input : List CodePoint) : Nat → Nat → List (List CodePoint)
  | 0, _ => []
  | fuel + 1, position =>
    if position < input.length then
      let (token, position) := collect (!·.isAsciiWhitespace) input position
      let position := skipAsciiWhitespace input position
      token :: splitOnAsciiWhitespaceLoop input fuel position
    else []

/-- Split a string `input` on ASCII whitespace, section `strings`: "Let
position be a position variable for input, initially pointing at the start
of input. Let tokens be a list of strings, initially empty. Skip ASCII
whitespace within input given position." Then the loop of
`splitOnAsciiWhitespaceLoop`, and "Return tokens." -/
def splitOnAsciiWhitespace (input : JsString) : List JsString :=
  let cps := codePoints input
  let position := skipAsciiWhitespace cps 0
  (splitOnAsciiWhitespaceLoop cps (cps.length - position) position).map ofCodePoints

/-- The loop of split on commas, section `strings`: "While position is not
past the end of input: Let token be the result of collecting a sequence of
code points that are not U+002C (,) from input, given position. Strip
leading and trailing ASCII whitespace from token. Append token to tokens. If
position is not past the end of input: Assert: the code point at position
within input is U+002C (,). Advance position by 1." The note "token might be
the empty string" is why an empty token is appended unconditionally. The
assertion holds because collect stopped only at a comma. Fuel: the
remaining length at entry. -/
def splitOnCommasLoop (input : List CodePoint) : Nat → Nat → List (List CodePoint)
  | 0, _ => []
  | fuel + 1, position =>
    if position < input.length then
      let (token, position) := collect (· != comma) input position
      let token := CodePoints.stripLeadingAndTrailingAsciiWhitespace token
      let position := if position < input.length then position + 1 else position
      token :: splitOnCommasLoop input fuel position
    else []

/-- Split a string `input` on commas, section `strings`: "Let position be a
position variable for input, initially pointing at the start of input. Let
tokens be a list of strings, initially empty." Then the loop of
`splitOnCommasLoop`, and "Return tokens." -/
def splitOnCommas (input : JsString) : List JsString :=
  let cps := codePoints input
  (splitOnCommasLoop cps cps.length 0).map ofCodePoints

/-- Concatenate a list of strings `list`, using an optional separator string
`separator`, section `strings`: "If list is empty, then return the empty
string. If separator is not given, then set separator to the empty string.
Return a string whose contents are list's items, in order, separated from
each other by separator." -/
def concatenate (list : List JsString) (separator : Option JsString := none) : JsString :=
  match list with
  | [] => []
  | _ => List.intercalate (separator.getD []) list

/-! Witnesses derived from the text's steps and notes. The set-serialization
example of section `strings` is "the concatenation of set using U+0020
SPACE". -/

example : collect CodePoint.isAsciiDigit (codePoints (ofLiteral "12ab")) 0 =
    (codePoints (ofLiteral "12"), 2) := by decide

example : collect CodePoint.isAsciiDigit (codePoints (ofLiteral "12ab")) 2 = ([], 2) := by decide

example : collect CodePoint.isAsciiDigit (codePoints (ofLiteral "12ab")) 7 = ([], 7) := by decide

example : skipAsciiWhitespace (codePoints (ofLiteral " \t x")) 0 = 3 := by decide

example : strictlySplit (ofLiteral "a,,b") comma = [ofLiteral "a", ofLiteral "", ofLiteral "b"] := by
  decide

example : strictlySplit (ofLiteral "") comma = [ofLiteral ""] := by decide

example : strictlySplit (ofLiteral "a, b,") comma = [ofLiteral "a", ofLiteral " b", ofLiteral ""] := by
  decide

example : splitOnAsciiWhitespace (ofLiteral "  a \t b\n ") = [ofLiteral "a", ofLiteral "b"] := by
  decide

example : splitOnAsciiWhitespace (ofLiteral " \t ") = [] := by decide

example : splitOnCommas (ofLiteral " a , ,b,") =
    [ofLiteral "a", ofLiteral "", ofLiteral "b", ofLiteral ""] := by decide

example : splitOnCommas (ofLiteral "") = [] := by decide

example : concatenate [ofLiteral "a", ofLiteral "b", ofLiteral "c"] (some (ofLiteral " ")) =
    ofLiteral "a b c" := by decide

example : concatenate [ofLiteral "a", ofLiteral "b"] = ofLiteral "ab" := by decide

example : concatenate [] (some (ofLiteral " ")) = ofLiteral "" := by decide

end JsString

end Whatwg.Infra
