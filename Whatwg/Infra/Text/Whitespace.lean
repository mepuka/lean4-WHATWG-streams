import Whatwg.Infra.Text.String

/-!
# Text.Whitespace

Owner: the four newline and ASCII whitespace rewrites of section `strings`
of `vendor/whatwg-infra-3f984adc/infra.bs`: strip newlines, normalize
newlines, strip leading and trailing ASCII whitespace, and strip and collapse
ASCII whitespace.

Each operation is stated by the text on code points, so each is defined on
the code point view: `codePoints s`, the transform on `List CodePoint` (held
in `namespace CodePoints`), then `ofCodePoints`. The `JsString` operations
are those compositions.

Normalize newlines follows ruling INFRA-R4 (`docs/INFRA-PROOF-PLAN.md`
section 3): a single left-to-right non-overlapping pass replacing CR LF by
LF, followed by replacing every remaining CR by LF. On CR CR LF this yields
LF LF, of length 2, the discriminating case against an iterate-to-fixed-point
reading, which would yield a single LF.
-/

set_option autoImplicit false

namespace Whatwg.Infra

namespace CodePoints

/-- U+000A LF, the code point every newline rewrite produces. -/
def lf : CodePoint := ⟨0x0A, by decide⟩

/-- U+0020 SPACE, the code point a collapsed whitespace run becomes. -/
def space : CodePoint := ⟨0x20, by decide⟩

/-- Whether a code point is U+000A LF or U+000D CR, the two code points
"strip newlines" removes (section `strings`). -/
def isNewline (c : CodePoint) : Bool := decide (c.val = 0x0A) || decide (c.val = 0x0D)

/-- Strip newlines on the code point view, section `strings`: "remove any
U+000A LF and U+000D CR code points from the string". -/
def stripNewlines (cs : List CodePoint) : List CodePoint := cs.filter (!isNewline ·)

/-- The first step of normalize newlines, section `strings`: "replace every
U+000D CR U+000A LF code point pair with a single U+000A LF code point". One
left-to-right non-overlapping pass (ruling INFRA-R4): a CR followed by LF
becomes LF and both are consumed; any other code point is kept. -/
def replaceCrLfPairs : List CodePoint → List CodePoint
  | [] => []
  | c :: rest =>
    if c.val = 0x0D then
      match rest with
      | d :: rest' =>
        if d.val = 0x0A then lf :: replaceCrLfPairs rest'
        else c :: replaceCrLfPairs (d :: rest')
      | [] => [c]
    else c :: replaceCrLfPairs rest

/-- The second step of normalize newlines, section `strings`: "then replace
every remaining U+000D CR code point with a U+000A LF code point". -/
def replaceCr (cs : List CodePoint) : List CodePoint :=
  cs.map fun c => if c.val = 0x0D then lf else c

/-- Normalize newlines on the code point view, section `strings`: "replace
every U+000D CR U+000A LF code point pair with a single U+000A LF code point,
and then replace every remaining U+000D CR code point with a U+000A LF code
point". The two steps are sequenced, not iterated (ruling INFRA-R4), so on
CR CR LF the result is LF LF, of length 2. -/
def normalizeNewlines (cs : List CodePoint) : List CodePoint :=
  replaceCr (replaceCrLfPairs cs)

/-- Strip leading and trailing ASCII whitespace on the code point view,
section `strings`: "remove all ASCII whitespace that are at the start or the
end of the string". -/
def stripLeadingAndTrailingAsciiWhitespace (cs : List CodePoint) : List CodePoint :=
  ((cs.dropWhile CodePoint.isAsciiWhitespace).reverse.dropWhile CodePoint.isAsciiWhitespace).reverse

/-- The first step of strip and collapse ASCII whitespace, section
`strings`: "replace any sequence of one or more consecutive code points that
are ASCII whitespace in the string with a single U+0020 SPACE code point".
The flag records whether the previous code point was ASCII whitespace, so
the first code point of a run emits the SPACE and the rest of the run emits
nothing. -/
def collapseAsciiWhitespace : Bool → List CodePoint → List CodePoint
  | _, [] => []
  | inRun, c :: rest =>
    if c.isAsciiWhitespace then
      if inRun then collapseAsciiWhitespace true rest
      else space :: collapseAsciiWhitespace true rest
    else c :: collapseAsciiWhitespace false rest

/-- Strip and collapse ASCII whitespace on the code point view, section
`strings`: "replace any sequence of one or more consecutive code points that
are ASCII whitespace in the string with a single U+0020 SPACE code point, and
then remove any leading and trailing ASCII whitespace from that string". -/
def stripAndCollapseAsciiWhitespace (cs : List CodePoint) : List CodePoint :=
  stripLeadingAndTrailingAsciiWhitespace (collapseAsciiWhitespace false cs)

end CodePoints

namespace JsString

/-- Strip newlines from a string, section `strings`: "remove any U+000A LF
and U+000D CR code points from the string". -/
def stripNewlines (s : JsString) : JsString :=
  ofCodePoints (CodePoints.stripNewlines (codePoints s))

/-- Normalize newlines in a string, section `strings`: "replace every U+000D
CR U+000A LF code point pair with a single U+000A LF code point, and then
replace every remaining U+000D CR code point with a U+000A LF code point".
A single left-to-right pass then a map (ruling INFRA-R4): on CR CR LF the
result is LF LF, of length 2, not the single LF an iterate-to-fixed-point
reading would give. -/
def normalizeNewlines (s : JsString) : JsString :=
  ofCodePoints (CodePoints.normalizeNewlines (codePoints s))

/-- Strip leading and trailing ASCII whitespace from a string, section
`strings`: "remove all ASCII whitespace that are at the start or the end of
the string". -/
def stripLeadingAndTrailingAsciiWhitespace (s : JsString) : JsString :=
  ofCodePoints (CodePoints.stripLeadingAndTrailingAsciiWhitespace (codePoints s))

/-- Strip and collapse ASCII whitespace in a string, section `strings`:
"replace any sequence of one or more consecutive code points that are ASCII
whitespace in the string with a single U+0020 SPACE code point, and then
remove any leading and trailing ASCII whitespace from that string". -/
def stripAndCollapseAsciiWhitespace (s : JsString) : JsString :=
  ofCodePoints (CodePoints.stripAndCollapseAsciiWhitespace (codePoints s))

/-! Witnesses derived from the text's sentences. The CR CR LF case is the
INFRA-R4 discriminator. -/

example : stripNewlines (ofLiteral "a\nb\r\nc") = ofLiteral "abc" := by decide

example : normalizeNewlines (ofLiteral "a\r\nb\rc\n") = ofLiteral "a\nb\nc\n" := by decide

example : normalizeNewlines (ofLiteral "\r\r\n") = ofLiteral "\n\n" := by decide

example : (normalizeNewlines (ofLiteral "\r\r\n")).length = 2 := by decide

example : stripLeadingAndTrailingAsciiWhitespace (ofLiteral " \t a b \n") = ofLiteral "a b" := by
  decide

example : stripAndCollapseAsciiWhitespace (ofLiteral "  a \t\n b\x0c c  ") = ofLiteral "a b c" := by
  decide

example : stripAndCollapseAsciiWhitespace (ofLiteral " \t ") = ofLiteral "" := by decide

end JsString

end Whatwg.Infra
