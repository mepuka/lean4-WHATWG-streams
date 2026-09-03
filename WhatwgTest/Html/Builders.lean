import Whatwg.Html.Node.Combinators
import Whatwg.Html.Node.Erasure

/-!
# WhatwgTest.Html.Builders

Positive probes for slice H3.3–H3.4: constructions that must elaborate. Every
`example` below is a construction whose `by decide` obligations — one child
admission per child, one attribute admission per element — were all
discharged, so the file failing to elaborate is the gate. A construction is
evidence about the sealed TyXML 4.6.0 projection at one point; the quantified
statements are the theorems in `Whatwg.Html.Node.Erasure` and
`Whatwg.Html.Content`.

`WhatwgTest/Html/Breakers.lean` holds the mirror image: the constructions that
must be rejected, each with the obligation that rejects it.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Builders

open Whatwg.Html
open Whatwg.Html.Schema (Tag ContentSet Attr)

/-! ## A whole document

TyXML's `html : ?a -> [< head] elt wrap -> [< body] elt wrap -> [> html] elt`,
with the required `title` heading the metadata of `head`. -/

/-- A minimal document: `html`, `head` with its `title` and a `meta`, `body`
with a heading and a paragraph. -/
example : Element .html .html_content_fun :=
  E.html
    (E.head (E.title (E.txt "Slice H3"))
      [E.el (E.«meta» [A.a_charset "utf-8"]),
       E.el (E.link "stylesheet" "/site.css")])
    (E.body
      [E.el (E.h1 [E.txt "Content models"]),
       E.el (E.p [E.txt "A paragraph of ", E.el (E.em [E.txt "phrasing"]), E.txt " content."])])

/-! ## Void elements

The fifteen void tags take no children argument at all, so a void element is
built from attributes alone. -/

/-- `img` carries TyXML's two required labelled arguments. -/
example : Element .img .notag := E.img "/logo.png" "The logo"

/-- `br` with an attribute from `br_attrib`. -/
example : Element .br .notag := E.br [A.a_class "spacer"]

/-- `input` with two attributes from `input_attrib`. -/
example : Element .input .notag := E.input [A.a_input_type "text", A.a_name "q"]

/-- `hr` with no attributes at all. -/
example : Element .hr .notag := E.hr

/-! ## A deep phrasing chain

Each step re-checks the child against the parent's own content set, which is
`phrasing` at every level here. -/

/-- `p → span → strong → em → txt`. -/
example : Element .p .phrasing :=
  E.p [E.el (E.span [E.el (E.strong [E.el (E.em [E.txt "deep"])])])]

/-! ## Transparency (ruling HP-4)

The transparent combinators are polymorphic in their content parameter. In a
child position `Child.of` assigns that parameter `childSet set t`, which is
TyXML's payload for `t` in `set`. -/

/-- `childSet` at the two contexts the probes below use. -/
example : childSet .phrasing .a = ContentSet.phrasing_without_interactive := rfl

/-- The same link in a flow context resolves to the flow payload instead. -/
example : childSet .flow5 .a = ContentSet.flow5_without_interactive := rfl

/-- `p → a → span → txt`: the link's children are checked against
`phrasing_without_interactive`, which names `Span`. -/
example : Element .p .phrasing :=
  E.p [E.el (E.a [E.el (E.span [E.txt "link text"])])]

/-- `div → a → p`: the same link in a flow context is checked against
`flow5_without_interactive`, which names `P`. The identical `a` term is
rejected under `p` (see `WhatwgTest/Html/Breakers.lean`). -/
example : Element .div .flow5 :=
  E.div [E.el (E.a [E.el (E.p [E.txt "block link"])] [A.a_href "/target"])]

/-- `del` and `ins` are transparent in the same way, and their payload in a
flow context is the unrestricted `flow5`. -/
example : Element .div .flow5 :=
  E.div [E.el (E.del [E.el (E.div [])]), E.el (E.ins [E.el (E.p [])])]

/-- `canvas`, `map`, `object_`, `audio` and `video` complete the eight. -/
example : Element .div .flow5 :=
  E.div
    [E.el (E.canvas [E.el (E.p [])]),
     E.el (E.map [E.el (E.div [])] [A.a_name "m"]),
     E.el (E.object_ [E.el (E.p [])] [E.param []]),
     E.el (E.audio [E.el (E.p [])] (src := some "/a.ogg") (srcs := [E.source []])),
     E.el (E.video [E.el (E.p [])])]

/-! ## Lists and tables -/

/-- `ul` admits `li` and nothing else. -/
example : Element .ul .ul_content_fun :=
  E.ul [E.el (E.li [E.txt "one"]), E.el (E.li [E.txt "two"]), E.el (E.li [E.txt "three"])]

/-- `table` admits `tr`, and takes TyXML's four optional labelled arguments. -/
example : Element .table .table_content_fun :=
  E.table
    [E.el (E.tr [E.el (E.td [E.txt "cell"]), E.el (E.th [E.txt "head"])])]
    (caption := some (E.caption [E.txt "A table"]))

/-- `tablex` is the second `Table` constructor: same tag, `tbody` children. -/
example : Element .table .tablex_content_fun :=
  E.tablex [E.el (E.tbody [E.el (E.tr [E.el (E.td [E.txt "cell"])])])]

/-! ## Other labelled forms -/

/-- `details` takes its required `summary` first. -/
example : Element .details .flow5 :=
  E.details (E.summary [E.txt "More"]) [E.el (E.p [E.txt "Detail."])]

/-- `select` admits `optgroup` and `option`; `option` is `unary`. -/
example : Element .select .select_content_fun :=
  E.select
    [E.el (E.option (E.txt "One")),
     E.el (E.optgroup "Group" [E.el (E.option (E.txt "Two"))])]

/-- `figure` places its optional caption first. -/
example : Element .figure .flow5 :=
  E.figure [E.el (E.p [E.txt "body"])] (figcaption := some (E.figcaption [E.txt "cap"]))

/-- `picture` takes its required `img` first. -/
example : Element .picture .picture_content_fun :=
  E.picture (E.img "/p.png" "p") [E.el (E.source [])]

/-- `bdo` carries its required direction. -/
example : Element .bdo .phrasing := E.bdo "rtl" [E.txt "טקסט"]

/-- `svg` takes neither children nor an attribute obligation (ruling HP-9). -/
example : Element .svg .notag := E.svg

/-! ## Erasure probes

Each is `rfl`: `Element.toRaw` is the markup name, the attribute markup names
and the already-erased children. -/

/-- A text child under a `div`. -/
example : (E.div [E.txt "hi"]).toRaw = RawNode.element "div" [] [RawNode.text "hi"] := rfl

/-- A void element with an attribute, whose markup name comes from
`attributeCtors`. -/
example : (E.br [A.a_class "spacer"]).toRaw
    = RawNode.element "br" [("class", "spacer")] [] := rfl

/-- `img`'s two required labelled arguments lead its attribute list. -/
example : (E.img "/logo.png" "The logo").toRaw
    = RawNode.element "img" [("src", "/logo.png"), ("alt", "The logo")] [] := rfl

/-- `tablex` erases to the markup name `table`, which it shares with
`table`. -/
example : (E.tablex).toRaw = RawNode.element "table" [] [] := rfl

/-- One nested step, through `Child.of`. -/
example : (E.div [E.el (E.p [E.txt "x"])]).toRaw
    = RawNode.element "div" [] [RawNode.element "p" [] [RawNode.text "x"]] := rfl

/-- An entity child. -/
example : (E.p [E.entity "nbsp"]).toRaw
    = RawNode.element "p" [] [RawNode.entity "nbsp"] := rfl

/-- The raw-tree measures on a small document. -/
example : (E.div [E.el (E.p [E.txt "x"]), E.el (E.br)]).toRaw.size = 4 := rfl

/-- The same document is three levels deep. -/
example : (E.div [E.el (E.p [E.txt "x"]), E.el (E.br)]).toRaw.depth = 3 := rfl

end WhatwgTest.Html.Builders
