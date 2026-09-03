import Whatwg.Html.Print.Render
import WhatwgTest.Html.Builders

/-!
# WhatwgTest.Html.Print

Probes for slice H4: the escaper, the serializer, and the decoder that
inverts the serializer on the sublanguage `Whatwg.Html.Print.wf` names. Each
`example` is a closed evaluation, so the file failing to elaborate is the
gate; the quantified statements live in `Whatwg.Html.Print.Escape` and
`Whatwg.Html.Print.Render`.

Control characters are written `Char.ofNat n` rather than as literals, so
that no source file of this repository carries one.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits
every declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Print

open Whatwg.Html
open Whatwg.Html.Print
open Whatwg.Html.Schema (Tag ContentSet Attr)

/-! ## The escaper -/

/-- The four named references of `add_unsafe_char`. -/
example : escapeString "a<b>c&d\"e" = "a&lt;b&gt;c&amp;d&quot;e" := by decide

/-- A control character becomes a decimal numeric reference. -/
example : escapeString (String.ofList ['a', Char.ofNat 1, 'b']) = "a&#1;b" := by decide

/-- `127` is a control character by TyXML's `is_control`; `9`, `10` and `13`
are not, and pass through. -/
example : escapeString (String.ofList [Char.ofNat 127, Char.ofNat 9, Char.ofNat 10])
    = String.ofList (['&', '#', '1', '2', '7', ';'] ++ [Char.ofNat 9, Char.ofNat 10]) := by decide

/-- `encode_unsafe_char_and_at` additionally escapes `@`. -/
example : escapeAndAtString "a@b" = "a&#64;b" := by decide

/-- The escaper's output decodes back, at a point. -/
example : unescape (escape "a<b&c".toList) = "a<b&c".toList := by decide

/-! ## The serializer -/

/-- An element with an attribute and a nested child. -/
example : render (.element "div" [("class", "card")] [.element "p" [] [.text "Hi & bye"]])
    = "<div class=\"card\"><p>Hi &amp; bye</p></div>" := by decide

/-- A void element closes as `xh_print_closedtag` closes it. -/
example : render (.element "br" [] []) = "<br />" := by decide

/-- A void element with an attribute. -/
example : render (.element "br" [("class", "spacer")] []) = "<br class=\"spacer\" />" := by decide

/-- A non-void element with no children gets a closing tag instead. -/
example : render (.element "span" [] []) = "<span></span>" := by decide

/-- An attribute value is escaped and double-quoted. -/
example : render (.element "input" [("value", "a\"b")] []) = "<input value=\"a&quot;b\" />" := by
  decide

/-- A control character inside a text run. -/
example : render (.text (String.ofList ['a', Char.ofNat 1, 'b'])) = "a&#1;b" := by decide

/-- An entity reference is written unescaped, as TyXML writes it. -/
example : render (.entity "nbsp") = "&nbsp;" := by decide

/-- A comment's text is escaped with the same escaper as a text run. -/
example : render (.comment "a < b") = "<!--a &lt; b-->" := by decide

/-- The void names come from the schema, not from a retyped list. -/
example : isVoidName "img" = true := by decide

/-- And no other name is void. -/
example : isVoidName "p" = false := by decide

/-! ## A whole document, from the typed builders -/

/-- The document of `WhatwgTest.Html.Builders`, shortened by one metadata
child. Those probes are anonymous `example`s, so the construction is repeated
here rather than referenced; the import above is what pins the two to the
same combinators. -/
def document : Element .html .html_content_fun :=
  E.html
    (E.head (E.title (E.txt "Slice H4"))
      [E.el (E.«meta» [A.a_charset "utf-8"])])
    (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A & B", E.el (E.br)])])

set_option maxRecDepth 4000 in
/-- Rendered end to end through erasure. The `maxRecDepth` bump is the
elaborator's stack, not a heartbeat budget: `decide` reduces a 130-byte
`String` equality here. -/
example : document.render
    = "<html><head><title>Slice H4</title><meta charset=\"utf-8\" /></head>"
      ++ "<body><h1>Content models</h1><p>A &amp; B<br /></p></body></html>" := by decide

set_option maxRecDepth 4000 in
/-- With the doctype line `html_f.ml`'s `Info.doctype` composes. -/
example : document.renderDoc
    = "<!DOCTYPE html>\n"
      ++ "<html><head><title>Slice H4</title><meta charset=\"utf-8\" /></head>"
      ++ "<body><h1>Content models</h1><p>A &amp; B<br /></p></body></html>" := by decide

/-- A child renders through the raw node it carries. -/
example : (Child.of (set := ContentSet.flow5) (E.p [E.txt "x"])).render = "<p>x</p>" := by decide

/-! ## The decoder -/

/-- The document is in the sublanguage the decoder inverts. -/
example : wf document.toRaw = true := by decide

/-- And it decodes back from its own rendering. -/
example : decodeNode? (weight document.toRaw) (renderChars document.toRaw)
    = some (document.toRaw, []) := decodeNode?_render (by decide)

/-- A tree with an entity node is outside that sublanguage: `&amp;` is
already the escaping of a text `&`. -/
example : wf (.element "p" [] [.entity "amp"]) = false := by decide

/-- So is a tree with two adjacent text runs. -/
example : wf (.element "p" [] [.text "a", .text "b"]) = false := by decide

/-- And so is an empty text run. -/
example : wf (.text "") = false := by decide

end WhatwgTest.Html.Print
