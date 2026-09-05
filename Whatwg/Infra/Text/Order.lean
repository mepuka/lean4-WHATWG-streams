import Whatwg.Infra.Text.String

/-!
# Text.Order

Owner: the code unit prefix, suffix, and ordering relations of section
`strings` of `vendor/whatwg-infra-3f984adc/infra.bs`: "code unit prefix" with
its synonym "starts with", "code unit suffix" with its synonym "ends with",
and "code unit less than".

Each relation is stated in the text as a numbered `While true` loop over an
index and is transcribed here as a loop function on that index, bounded by
the distance the index still has to travel, so the transcription is total
and step-for-step faithful. The text's index arithmetic is over integers;
where a step compares an index with 0 the equivalent comparison on natural
numbers is written and the docstring says so.
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace JsString

/-- The loop of "code unit prefix", section `strings`, entered at index `i`:
"While true: If `i` is greater than or equal to `potentialPrefix`'s length,
then return true. If `i` is greater than or equal to `input`'s length, then
return false. Let `potentialPrefixCodeUnit` be the `i`th code unit of
`potentialPrefix`. Let `inputCodeUnit` be the `i`th code unit of `input`.
Return false if `potentialPrefixCodeUnit` is not `inputCodeUnit`. Set `i` to
`i` + 1." Bounded by the code units of `potentialPrefix` not yet visited. -/
def codeUnitPrefixLoop (potentialPrefix input : JsString) (i : Nat) : Bool :=
  if hp : potentialPrefix.length ≤ i then true
  else if hi : input.length ≤ i then false
  else
    let potentialPrefixCodeUnit := potentialPrefix[i]'(Nat.lt_of_not_le hp)
    let inputCodeUnit := input[i]'(Nat.lt_of_not_le hi)
    if potentialPrefixCodeUnit ≠ inputCodeUnit then false
    else codeUnitPrefixLoop potentialPrefix input (i + 1)
termination_by potentialPrefix.length - i
decreasing_by simp only [JsString.length] at *; omega

/-- A string `potentialPrefix` "is a code unit prefix of a string `input` if
the following steps return true", section `strings`: "Let `i` be 0", then
the loop `codeUnitPrefixLoop`. -/
def isCodeUnitPrefixOf (potentialPrefix input : JsString) : Bool :=
  codeUnitPrefixLoop potentialPrefix input 0

/-- "`input` starts with `potentialPrefix`", section `strings`: "a synonym
for `potentialPrefix` is a code unit prefix of `input`", used "when it is
clear from context that code units are in play". -/
def startsWith (input potentialPrefix : JsString) : Bool :=
  isCodeUnitPrefixOf potentialPrefix input

/-- The loop of "code unit suffix", section `strings`, entered at index `i`
(the text starts it at 1, hence the hypothesis): "While true: Let
`potentialSuffixIndex` be `potentialSuffix`'s length − `i`. Let `inputIndex`
be `input`'s length − `i`. If `potentialSuffixIndex` is less than 0, then
return true. If `inputIndex` is less than 0, then return false. Let
`potentialSuffixCodeUnit` be the `potentialSuffixIndex`th code unit of
`potentialSuffix`. Let `inputCodeUnit` be the `inputIndex`th code unit of
`input`. Return false if `potentialSuffixCodeUnit` is not `inputCodeUnit`.
Set `i` to `i` + 1." The text's subtractions are over integers; "less than
0" for a length minus `i` is "the length is less than `i`", which is the test
written here, and the two indices are then formed by natural subtraction
once the tests have established that they are not negative. Bounded by the
code units of `potentialSuffix` not yet visited. -/
def codeUnitSuffixLoop (potentialSuffix input : JsString) (i : Nat) (hi : 1 ≤ i) : Bool :=
  if hs : potentialSuffix.length < i then true
  else if hn : input.length < i then false
  else
    let potentialSuffixIndex := potentialSuffix.length - i
    let inputIndex := input.length - i
    let potentialSuffixCodeUnit :=
      potentialSuffix[potentialSuffixIndex]'(by simp only [JsString.length] at *; omega)
    let inputCodeUnit := input[inputIndex]'(by simp only [JsString.length] at *; omega)
    if potentialSuffixCodeUnit ≠ inputCodeUnit then false
    else codeUnitSuffixLoop potentialSuffix input (i + 1) (Nat.le_succ_of_le hi)
termination_by potentialSuffix.length + 1 - i
decreasing_by simp only [JsString.length] at *; omega

/-- A string `potentialSuffix` "is a code unit suffix of a string `input` if
the following steps return true", section `strings`: "Let `i` be 1", then
the loop `codeUnitSuffixLoop`. -/
def isCodeUnitSuffixOf (potentialSuffix input : JsString) : Bool :=
  codeUnitSuffixLoop potentialSuffix input 1 (Nat.le_refl 1)

/-- "`input` ends with `potentialSuffix`", section `strings`: "a synonym for
`potentialSuffix` is a code unit suffix of `input`", used "when it is clear
from context that code units are in play". -/
def endsWith (input potentialSuffix : JsString) : Bool :=
  isCodeUnitSuffixOf potentialSuffix input

/-- Step 3 of "code unit less than", section `strings`, searched from index
`n` upward: "the smallest index such that the `n`th code unit of `a` is
different from the `n`th code unit of `b`". The search stops with `none`
when either string runs out, which the text rules out for the call it makes
("There has to be such an index, since neither string is a prefix of the
other"). The index returned carries the two bounds that make it a valid
index of both strings. Bounded by the code units of `a` not yet visited. -/
def firstDifferingIndex (a b : JsString) (n : Nat) :
    Option { n : Nat // n < List.length a ∧ n < List.length b } :=
  if ha : a.length ≤ n then none
  else if hb : b.length ≤ n then none
  else if a[n]'(Nat.lt_of_not_le ha) ≠ b[n]'(Nat.lt_of_not_le hb) then
    some ⟨n, Nat.lt_of_not_le ha, Nat.lt_of_not_le hb⟩
  else firstDifferingIndex a b (n + 1)
termination_by a.length - n
decreasing_by simp only [JsString.length] at *; omega

/-- A string `a` "is code unit less than a string `b` if the following steps
return true", section `strings`: "If `b` is a code unit prefix of `a`, then
return false. If `a` is a code unit prefix of `b`, then return true. Let `n`
be the smallest index such that the `n`th code unit of `a` is different from
the `n`th code unit of `b`. If the `n`th code unit of `a` is less than the
`n`th code unit of `b`, then return true. Return false." The `none` arm of
the index search is unreachable after the two prefix tests and returns the
final step's false. -/
def isCodeUnitLessThan (a b : JsString) : Bool :=
  if isCodeUnitPrefixOf b a then false
  else if isCodeUnitPrefixOf a b then true
  else
    match firstDifferingIndex a b 0 with
    | some ⟨n, hn⟩ => decide (a[n]'hn.1 < b[n]'hn.2)
    | none => false

/-- The example of section `strings` (`example-code-unit-less-than`): "the
tilde is composed of a single code unit 0xFF5E, while the smiley is composed
of two code units 0xD83D and 0XDE00, so the smiley is code unit less than
the tilde". -/
example : isCodeUnitLessThan [0xD83D, 0xDE00] [0xFF5E] = true := by decide

/-- The converse of the same example: the tilde is not code unit less than
the smiley. -/
example : isCodeUnitLessThan [0xFF5E] [0xD83D, 0xDE00] = false := by decide

end JsString

end Whatwg.Infra
