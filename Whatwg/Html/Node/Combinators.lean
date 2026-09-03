import Whatwg.Html.Node.Typed

/-!
# Whatwg.Html.Node.Combinators

One combinator per element constructor of `Html_sigs.T` (111 of them, in
`html_sigs.mli` order), the two text constructors, and one helper per
attribute constructor (216 of them). Slice H3.4 of
`docs/HTML-PACKAGE-PLAN.md`.

PRODUCED FROM `Whatwg.Html.Schema.elements` and
`Whatwg.Html.Schema.attributeCtors` at H3 by a hand-run script, then edited by
hand for the labelled forms of `html_sigs.mli`. It is NOT drift-checked:
`lake exe tyxmlschema` owns `Whatwg/Html/Schema/**` and says nothing about
this file. A schema change therefore has to be reflected here by hand, and
the shape check that catches an omission is that the tests in
`WhatwgTest/Html/Builders.lean` stop elaborating.

## Shape

Names are TyXML's OCaml value names (`object_`, `output_elt`, `tablex`), with
`section` and `meta` in guillemets because they collide with Lean tokens.
They live in `Whatwg.Html.E` and `Whatwg.Html.A` rather than in
`Whatwg.Html`, because a dozen of them are single letters (`a`, `b`, `i`,
`p`, `q`, `s`, `u`) that would otherwise shadow ordinary variable names at
every use site of the library.

Argument order departs from the sketch in the slice brief: children come
first and `attrs` second with a default of `[]`. OCaml's `?a:` is a labelled
optional argument, which Lean has no direct analogue for; putting the
attributes last keeps `div [txt "x"]` working positionally, and
`div [txt "x"] [A.a_class "lead"]` and `div (attrs := [A.a_id "x"]) []` both
read the way TyXML's `div ~a:[...] [...]` does. Required labelled arguments
of `html_sigs.mli` (`img ~src ~alt`, `link ~rel ~href`, `area ~alt`,
`bdo ~dir`, `optgroup ~label`, `command ~label`, `picture ~img`,
`details summary`, `html head body`, `head title`) are explicit leading
arguments; optional labelled arguments (`figure ?figcaption`,
`table ?caption ?columns ?thead ?tfoot`, `fieldset ?legend`,
`object_ ?params`, `audio/video ?src ?srcs`) are optional arguments after the
children.

## What was simplified

- `figure ?figcaption` is `` `Top `` only: TyXML's `` `Bottom `` placement is
  not expressible through a single `Option`.
- `datalist ?children` and `menu ?children` are dropped. Both are `nullary`
  rows in the projection whose TyXML signature carries an optional variant of
  two child shapes (`` `Options ``/`` `Phras ``, `` `Lis ``/`` `Flows ``);
  modelling that needs a sum whose two arms carry different content sets, and
  the element's own content set in the projection is `notag`, so a faithful
  version would have to sit outside the `Element t inner` shape. The two
  combinators here take attributes and no children.
- `svg` takes neither children nor an attribute obligation (ruling HP-9).
- Attribute values are `String`; TyXML's typed value constructors are a later
  slice. The two prefixed constructors, `a_user_data` (`data-`) and `a_aria`
  (`aria-`), therefore lose their name suffix, because `Attr × String` has no
  room for it.
- `noscript` is not polymorphic in `inner`. Its element row is not
  transparent and TyXML's own `val noscript` is not polymorphic either, but
  `ContentSet.transparentPayload` does assign it a payload, so a `noscript`
  can be placed only where that payload is its own content set
  `flow5_without_noscript` — in a phrasing context the payload is
  `phrasing_without_noscript` and `Child.of` will reject it. That is TyXML's
  signature reproduced, and the mismatch between the two notions of
  transparency is the theorem `transparent_eq_isTransparent_or_four` of
  `Whatwg.Html.Content.Transparent`.
-/

namespace Whatwg.Html.E

open Whatwg.Html.Schema (Tag ContentSet Attr AttrSet)

/-! ## Text constructors (ruling HP-5)

`txt` and `entity` are `Child.text` and `Child.entity` under TyXML's names;
both are admitted exactly where the content set names `PCDATA`. -/

/-- TyXML `val txt : string wrap -> [> txt] elt`. -/
def txt {set : ContentSet} (s : String)
    (h : Content.Admits set .pcdata := by decide) : Child set :=
  Child.text s h

/-- TyXML `val entity : string -> [> txt] elt`. -/
def entity {set : ContentSet} (name : String)
    (h : Content.Admits set .pcdata := by decide) : Child set :=
  Child.entity name h

/-- Place a typed element in a child position: `Child.of` under a short name,
for use inside a children list. -/
def el {set : ContentSet} {t : Tag} (e : Element t (childSet set t))
    (h : Content.Admits set t := by decide) : Child set :=
  Child.of e h

/-! ## Element constructors, in `html_sigs.mli` order -/

/-- TyXML `val html : ?a:html_attrib attrib list -> [< head] elt wrap ->
[< body] elt wrap -> [> html] elt`. The two required children are positional,
as in `html_sigs.mli`; their content sets are the ones `childSet` assigns
them under `html_content_fun`. -/
def html (head : Element .head .metadata_without_title) (body : Element .body .flow5)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .html_attrib attrs := by decide) :
    Element .html .html_content_fun :=
  ⟨attrs, [head.toRaw, body.toRaw]⟩
/-- TyXML `val head : ?a:head_attrib attrib list -> [< title] elt wrap ->
(head_content_fun elt) list_wrap -> [> head] elt`: the required `title` comes
first and the remaining metadata follows. -/
def head (title : Element .title .title_content_fun)
    (children : List (Child .metadata_without_title) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .head_attrib attrs := by decide) :
    Element .head .metadata_without_title :=
  ⟨attrs, title.toRaw :: children.map Child.raw⟩
/-- TyXML `val base : ([< base_attrib], [> base]) nullary`: no children. -/
def base
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .base_attrib attrs := by decide) :
    Element .base .notag :=
  ⟨attrs, []⟩

/-- TyXML `val title : (title_attrib, [< title_content_fun], [> title]) unary`: exactly one
child, checked against `title_content_fun`. -/
def title (child : Child .title_content_fun)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .title_attrib attrs := by decide) :
    Element .title .title_content_fun :=
  ⟨attrs, [child.raw]⟩

/-- TyXML `val body : ([< body_attrib], [< body_content_fun], [> body]) star`: its children
are checked against `flow5`. -/
def body (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .body_attrib attrs := by decide) :
    Element .body .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val svg : ?a:[< svg_attrib] Svg.attrib list ->
[< svg_content] Svg.elt list_wrap -> [> svg] elt`. SVG is a W3C standard and
is not modelled in this package (ruling HP-9), so this combinator takes no
children and no attribute obligation: the `svg` element row is the only one
of the 111 with neither a content set nor an attribute set. Its `inner` index
is `notag`, which is what `childSet` assigns `Svg` in every context. -/
def svg (attrs : List (Attr × String) := []) : Element .svg .notag :=
  ⟨attrs, []⟩
/-- TyXML `val footer : ([< footer_attrib], [< footer_content_fun], [> footer]) star`: its children
are checked against `flow5_without_header_footer`. -/
def footer (children : List (Child .flow5_without_header_footer) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .footer_attrib attrs := by decide) :
    Element .footer .flow5_without_header_footer :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val header : ([< header_attrib], [< header_content_fun], [> header]) star`: its children
are checked against `flow5_without_header_footer`. -/
def header (children : List (Child .flow5_without_header_footer) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .header_attrib attrs := by decide) :
    Element .header .flow5_without_header_footer :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val section : ([< section_attrib], [< section_content_fun], [> section]) star`: its children
are checked against `flow5`. -/
def «section» (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .section_attrib attrs := by decide) :
    Element .«section» .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val nav : ([< nav_attrib], [< nav_content_fun], [> nav]) star`: its children
are checked against `flow5`. -/
def nav (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .nav_attrib attrs := by decide) :
    Element .nav .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val h1 : ([< h1_attrib], [< h1_content_fun], [> h1]) star`: its children
are checked against `phrasing`. -/
def h1 (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .h1_attrib attrs := by decide) :
    Element .h1 .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val h2 : ([< h2_attrib], [< h2_content_fun], [> h2]) star`: its children
are checked against `phrasing`. -/
def h2 (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .h2_attrib attrs := by decide) :
    Element .h2 .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val h3 : ([< h3_attrib], [< h3_content_fun], [> h3]) star`: its children
are checked against `phrasing`. -/
def h3 (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .h3_attrib attrs := by decide) :
    Element .h3 .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val h4 : ([< h4_attrib], [< h4_content_fun], [> h4]) star`: its children
are checked against `phrasing`. -/
def h4 (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .h4_attrib attrs := by decide) :
    Element .h4 .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val h5 : ([< h5_attrib], [< h5_content_fun], [> h5]) star`: its children
are checked against `phrasing`. -/
def h5 (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .h5_attrib attrs := by decide) :
    Element .h5 .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val h6 : ([< h6_attrib], [< h6_content_fun], [> h6]) star`: its children
are checked against `phrasing`. -/
def h6 (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .h6_attrib attrs := by decide) :
    Element .h6 .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val hgroup : ([< hgroup_attrib], [< hgroup_content_fun], [> hgroup]) star`: its children
are checked against `hgroup_content_fun`. -/
def hgroup (children : List (Child .hgroup_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .hgroup_attrib attrs := by decide) :
    Element .hgroup .hgroup_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val address : ([< address_attrib], [< address_content_fun], [> address]) star`: its children
are checked against `flow5_without_sectioning_heading_header_footer_address`. -/
def address (children : List (Child .flow5_without_sectioning_heading_header_footer_address) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .address_attrib attrs := by decide) :
    Element .address .flow5_without_sectioning_heading_header_footer_address :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val article : ([< article_attrib], [< article_content_fun], [> article]) star`: its children
are checked against `flow5`. -/
def article (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .article_attrib attrs := by decide) :
    Element .article .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val aside : ([< aside_attrib], [< aside_content_fun], [> aside]) star`: its children
are checked against `flow5`. -/
def aside (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .aside_attrib attrs := by decide) :
    Element .aside .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val main : ([< main_attrib], [< main_content_fun], [> main]) star`: its children
are checked against `flow5`. -/
def main (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .main_attrib attrs := by decide) :
    Element .main .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val p : ([< p_attrib], [< p_content_fun], [> p]) star`: its children
are checked against `phrasing`. -/
def p (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .p_attrib attrs := by decide) :
    Element .p .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val pre : ([< pre_attrib], [< pre_content_fun], [> pre]) star`: its children
are checked against `phrasing`. -/
def pre (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .pre_attrib attrs := by decide) :
    Element .pre .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val blockquote : ([< blockquote_attrib], [< blockquote_content_fun], [> blockquote]) star`: its children
are checked against `flow5`. -/
def blockquote (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .blockquote_attrib attrs := by decide) :
    Element .blockquote .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val dialog : ([< dialog_attrib], [< dialog_content_fun], [> dialog]) star`: its children
are checked against `flow5`. -/
def dialog (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .dialog_attrib attrs := by decide) :
    Element .dialog .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val div : ([< div_attrib], [< div_content_fun], [> div]) star`: its children
are checked against `flow5`. -/
def div (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .div_attrib attrs := by decide) :
    Element .div .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val dl : ([< dl_attrib], [< dl_content_fun], [> dl]) star`: its children
are checked against `dl_content_fun`. -/
def dl (children : List (Child .dl_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .dl_attrib attrs := by decide) :
    Element .dl .dl_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val ol : ([< ol_attrib], [< ol_content_fun], [> ol]) star`: its children
are checked against `ol_content_fun`. -/
def ol (children : List (Child .ol_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .ol_attrib attrs := by decide) :
    Element .ol .ol_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val ul : ([< ul_attrib], [< ul_content_fun], [> ul]) star`: its children
are checked against `ul_content_fun`. -/
def ul (children : List (Child .ul_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .ul_attrib attrs := by decide) :
    Element .ul .ul_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val dd : ([< dd_attrib], [< dd_content_fun], [> dd]) star`: its children
are checked against `flow5`. -/
def dd (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .dd_attrib attrs := by decide) :
    Element .dd .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val dt : ([< dt_attrib], [< dt_content_fun], [> dt]) star`: its children
are checked against `flow5_without_sectioning_heading_header_footer`. -/
def dt (children : List (Child .flow5_without_sectioning_heading_header_footer) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .dt_attrib attrs := by decide) :
    Element .dt .flow5_without_sectioning_heading_header_footer :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val li : ([< li_attrib], [< li_content_fun], [> li]) star`: its children
are checked against `flow5`. -/
def li (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .li_attrib attrs := by decide) :
    Element .li .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val figcaption : ([< figcaption_attrib], [< figcaption_content_fun], [> figcaption]) star`: its children
are checked against `flow5`. -/
def figcaption (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .figcaption_attrib attrs := by decide) :
    Element .figcaption .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val figure : ?figcaption:[`Top of ... | `Bottom of ...] -> ... star`.
Simplified at this pin: the optional caption is a single `Option` placed
before the flow children, so `` `Bottom `` is not expressible. -/
def figure (children : List (Child .flow5) := [])
    (figcaption : Option (Element .figcaption .flow5) := none)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .figure_attrib attrs := by decide) :
    Element .figure .flow5 :=
  ⟨attrs, figcaption.toList.map Element.toRaw ++ children.map Child.raw⟩
/-- TyXML `val hr : ([< hr_attrib], [> hr]) nullary`: no children. -/
def hr
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .hr_attrib attrs := by decide) :
    Element .hr .notag :=
  ⟨attrs, []⟩

/-- TyXML `val b : ([< b_attrib], [< b_content_fun], [> b]) star`: its children
are checked against `phrasing`. -/
def b (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .b_attrib attrs := by decide) :
    Element .b .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val i : ([< i_attrib], [< i_content_fun], [> i]) star`: its children
are checked against `phrasing`. -/
def i (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .i_attrib attrs := by decide) :
    Element .i .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val u : ([< u_attrib], [< u_content_fun], [> u]) star`: its children
are checked against `phrasing`. -/
def u (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .u_attrib attrs := by decide) :
    Element .u .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val small : ([< small_attrib], [< small_content_fun], [> small]) star`: its children
are checked against `phrasing`. -/
def small (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .small_attrib attrs := by decide) :
    Element .small .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val sub : ([< sub_attrib], [< sub_content_fun], [> sub]) star`: its children
are checked against `phrasing`. -/
def sub (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .sub_attrib attrs := by decide) :
    Element .sub .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val sup : ([< sup_attrib], [< sup_content_fun], [> sup]) star`: its children
are checked against `phrasing`. -/
def sup (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .sup_attrib attrs := by decide) :
    Element .sup .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val mark : ([< mark_attrib], [< mark_content_fun], [> mark]) star`: its children
are checked against `phrasing`. -/
def mark (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .mark_attrib attrs := by decide) :
    Element .mark .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val wbr : ([< wbr_attrib], [> wbr]) nullary`: no children. -/
def wbr
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .wbr_attrib attrs := by decide) :
    Element .wbr .notag :=
  ⟨attrs, []⟩

/-- TyXML `val bdo : dir:[< `Ltr | `Rtl] wrap -> ... star`: the required
direction is carried as the `dir` attribute, whose value is a plain `String`
at this pin. -/
def bdo (dir : String) (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .bdo_attrib attrs := by decide) :
    Element .bdo .phrasing :=
  ⟨(Attr.dir, dir) :: attrs, children.map Child.raw⟩
/-- TyXML `val abbr : ([< abbr_attrib], [< abbr_content_fun], [> abbr]) star`: its children
are checked against `phrasing`. -/
def abbr (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .abbr_attrib attrs := by decide) :
    Element .abbr .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val br : ([< br_attrib], [> br]) nullary`: no children. -/
def br
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .br_attrib attrs := by decide) :
    Element .br .notag :=
  ⟨attrs, []⟩

/-- TyXML `val cite : ([< cite_attrib], [< cite_content_fun], [> cite]) star`: its children
are checked against `phrasing`. -/
def cite (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .cite_attrib attrs := by decide) :
    Element .cite .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val code : ([< code_attrib], [< code_content_fun], [> code]) star`: its children
are checked against `phrasing`. -/
def code (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .code_attrib attrs := by decide) :
    Element .code .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val dfn : ([< dfn_attrib], [< dfn_content_fun], [> dfn]) star`: its children
are checked against `phrasing_without_dfn`. -/
def dfn (children : List (Child .phrasing_without_dfn) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .dfn_attrib attrs := by decide) :
    Element .dfn .phrasing_without_dfn :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val em : ([< em_attrib], [< em_content_fun], [> em]) star`: its children
are checked against `phrasing`. -/
def em (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .em_attrib attrs := by decide) :
    Element .em .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val kbd : ([< kbd_attrib], [< kbd_content_fun], [> kbd]) star`: its children
are checked against `phrasing`. -/
def kbd (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .kbd_attrib attrs := by decide) :
    Element .kbd .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val q : ([< q_attrib], [< q_content_fun], [> q]) star`: its children
are checked against `phrasing`. -/
def q (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .q_attrib attrs := by decide) :
    Element .q .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val samp : ([< samp_attrib], [< samp_content_fun], [> samp]) star`: its children
are checked against `phrasing`. -/
def samp (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .samp_attrib attrs := by decide) :
    Element .samp .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val span : ([< span_attrib], [< span_content_fun], [> span]) star`: its children
are checked against `phrasing`. -/
def span (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .span_attrib attrs := by decide) :
    Element .span .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val strong : ([< strong_attrib], [< strong_content_fun], [> strong]) star`: its children
are checked against `phrasing`. -/
def strong (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .strong_attrib attrs := by decide) :
    Element .strong .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val time : ([< time_attrib], [< time_content_fun], [> time]) star`: its children
are checked against `phrasing_without_time`. -/
def time (children : List (Child .phrasing_without_time) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .time_attrib attrs := by decide) :
    Element .time .phrasing_without_time :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val var : ([< var_attrib], [< var_content_fun], [> var]) star`: its children
are checked against `phrasing`. -/
def var (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .var_attrib attrs := by decide) :
    Element .var .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val a : ([< a_attrib], 'a, [> 'a a]) star`: transparent, so its
children are checked against the payload the enclosing content set assigns
it, which unification takes from `childSet` at the child position. -/
def a {inner : ContentSet} (children : List (Child inner) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .a_attrib attrs := by decide) :
    Element .a inner :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val del : ([< del_attrib], 'a, [> 'a del]) star`: transparent, so its
children are checked against the payload the enclosing content set assigns
it, which unification takes from `childSet` at the child position. -/
def del {inner : ContentSet} (children : List (Child inner) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .del_attrib attrs := by decide) :
    Element .del inner :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val ins : ([< ins_attrib], 'a, [> 'a ins]) star`: transparent, so its
children are checked against the payload the enclosing content set assigns
it, which unification takes from `childSet` at the child position. -/
def ins {inner : ContentSet} (children : List (Child inner) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .ins_attrib attrs := by decide) :
    Element .ins inner :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val img : src:Xml.uri wrap -> alt:text wrap ->
([< img_attrib], [> img]) nullary`: both labelled arguments are required and
become attributes. -/
def img (src : String) (alt : String)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .img_attrib attrs := by decide) :
    Element .img .notag :=
  ⟨(Attr.src, src) :: (Attr.alt, alt) :: attrs, []⟩
/-- TyXML `val picture : img:([< img] elt wrap) -> ... star`: the required
`img` is the first positional argument and heads the children. -/
def picture (img : Element .img .notag) (children : List (Child .picture_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .picture_attrib attrs := by decide) :
    Element .picture .picture_content_fun :=
  ⟨attrs, img.toRaw :: children.map Child.raw⟩
/-- TyXML `val iframe : ([< iframe_attrib], [< iframe_content_fun], [> iframe]) star`: its children
are checked against `iframe_content_fun`. -/
def iframe (children : List (Child .iframe_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .iframe_attrib attrs := by decide) :
    Element .iframe .iframe_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val object_ : ?params:([< param] elt) list_wrap ->
([< object__attrib], 'a, [> `Object of 'a]) star`: transparent, with an
optional leading list of `param` children. -/
def object_ {inner : ContentSet} (children : List (Child inner) := [])
    (params : List (Element .param .notag) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .object__attrib attrs := by decide) :
    Element .object inner :=
  ⟨attrs, params.map Element.toRaw ++ children.map Child.raw⟩
/-- TyXML `val param : ([< param_attrib], [> param]) nullary`: no children. -/
def param
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .param_attrib attrs := by decide) :
    Element .param .notag :=
  ⟨attrs, []⟩

/-- TyXML `val embed : ([< embed_attrib], [> embed]) nullary`: no children. -/
def embed
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .embed_attrib attrs := by decide) :
    Element .embed .notag :=
  ⟨attrs, []⟩

/-- TyXML `val audio : ?src:Xml.uri wrap -> ?srcs:([< source] elt) list_wrap ->
([< audio_attrib], 'a, [> 'a audio]) star`: transparent, with an optional
`src` attribute and an optional leading list of `source` children. -/
def audio {inner : ContentSet} (children : List (Child inner) := [])
    (src : Option String := none)
    (srcs : List (Element .source .notag) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .audio_attrib attrs := by decide) :
    Element .audio inner :=
  ⟨src.toList.map (fun u => (Attr.src, u)) ++ attrs,
   srcs.map Element.toRaw ++ children.map Child.raw⟩
/-- TyXML `val video : ?src:Xml.uri wrap -> ?srcs:([< source] elt) list_wrap ->
([< video_attrib], 'a, [> 'a video]) star`: transparent, shaped exactly like
`audio`. -/
def video {inner : ContentSet} (children : List (Child inner) := [])
    (src : Option String := none)
    (srcs : List (Element .source .notag) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .video_attrib attrs := by decide) :
    Element .video inner :=
  ⟨src.toList.map (fun u => (Attr.src, u)) ++ attrs,
   srcs.map Element.toRaw ++ children.map Child.raw⟩
/-- TyXML `val canvas : ([< canvas_attrib], 'a, [> 'a canvas]) star`: transparent, so its
children are checked against the payload the enclosing content set assigns
it, which unification takes from `childSet` at the child position. -/
def canvas {inner : ContentSet} (children : List (Child inner) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .canvas_attrib attrs := by decide) :
    Element .canvas inner :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val source : ([< source_attrib], [> source]) nullary`: no children. -/
def source
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .source_attrib attrs := by decide) :
    Element .source .notag :=
  ⟨attrs, []⟩

/-- TyXML `val area : alt:text wrap -> ([< area_attrib_inline], [> area]) nullary`:
the required `alt` becomes an attribute. -/
def area (alt : String)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .area_attrib_inline attrs := by decide) :
    Element .area .notag :=
  ⟨(Attr.alt, alt) :: attrs, []⟩
/-- TyXML `val map : ([< map_attrib], 'a, [> 'a map]) star`: transparent, so its
children are checked against the payload the enclosing content set assigns
it, which unification takes from `childSet` at the child position. -/
def map {inner : ContentSet} (children : List (Child inner) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .map_attrib attrs := by decide) :
    Element .map inner :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val caption : ([< caption_attrib], [< caption_content_fun], [> caption]) star`: its children
are checked against `flow5_without_table`. -/
def caption (children : List (Child .flow5_without_table) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .caption_attrib attrs := by decide) :
    Element .caption .flow5_without_table :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val table : ?caption -> ?columns -> ?thead -> ?tfoot -> ... star`:
the four labelled arguments become optional trailing arguments and are
spliced ahead of the row children in `html_sigs.mli` order. -/
def table (children : List (Child .table_content_fun) := [])
    (caption : Option (Element .caption .flow5_without_table) := none)
    (columns : List (Element .colgroup .colgroup_content_fun) := [])
    (thead : Option (Element .thead .thead_content_fun) := none)
    (tfoot : Option (Element .tfoot .tfoot_content_fun) := none)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .table_attrib attrs := by decide) :
    Element .table .table_content_fun :=
  ⟨attrs, caption.toList.map Element.toRaw ++ columns.map Element.toRaw
    ++ thead.toList.map Element.toRaw ++ tfoot.toList.map Element.toRaw
    ++ children.map Child.raw⟩
/-- TyXML `val tablex : ?caption -> ?columns -> ?thead -> ?tfoot -> ... star`.
The second `Table` constructor: same markup name and tag as `table`, a wider
attribute set and the `tablex_content_fun` content set. -/
def tablex (children : List (Child .tablex_content_fun) := [])
    (caption : Option (Element .caption .flow5_without_table) := none)
    (columns : List (Element .colgroup .colgroup_content_fun) := [])
    (thead : Option (Element .thead .thead_content_fun) := none)
    (tfoot : Option (Element .tfoot .tfoot_content_fun) := none)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .tablex_attrib attrs := by decide) :
    Element .table .tablex_content_fun :=
  ⟨attrs, caption.toList.map Element.toRaw ++ columns.map Element.toRaw
    ++ thead.toList.map Element.toRaw ++ tfoot.toList.map Element.toRaw
    ++ children.map Child.raw⟩
/-- TyXML `val colgroup : ([< colgroup_attrib], [< colgroup_content_fun], [> colgroup]) star`: its children
are checked against `colgroup_content_fun`. -/
def colgroup (children : List (Child .colgroup_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .colgroup_attrib attrs := by decide) :
    Element .colgroup .colgroup_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val col : ([< col_attrib], [> col]) nullary`: no children. -/
def col
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .col_attrib attrs := by decide) :
    Element .col .notag :=
  ⟨attrs, []⟩

/-- TyXML `val thead : ([< thead_attrib], [< thead_content_fun], [> thead]) star`: its children
are checked against `thead_content_fun`. -/
def thead (children : List (Child .thead_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .thead_attrib attrs := by decide) :
    Element .thead .thead_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val tbody : ([< tbody_attrib], [< tbody_content_fun], [> tbody]) star`: its children
are checked against `tbody_content_fun`. -/
def tbody (children : List (Child .tbody_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .tbody_attrib attrs := by decide) :
    Element .tbody .tbody_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val tfoot : ([< tfoot_attrib], [< tfoot_content_fun], [> tfoot]) star`: its children
are checked against `tfoot_content_fun`. -/
def tfoot (children : List (Child .tfoot_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .tfoot_attrib attrs := by decide) :
    Element .tfoot .tfoot_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val td : ([< td_attrib], [< td_content_fun], [> td]) star`: its children
are checked against `flow5`. -/
def td (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .td_attrib attrs := by decide) :
    Element .td .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val th : ([< th_attrib], [< th_content_fun], [> th]) star`: its children
are checked against `flow5`. -/
def th (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .th_attrib attrs := by decide) :
    Element .th .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val tr : ([< tr_attrib], [< tr_content_fun], [> tr]) star`: its children
are checked against `tr_content_fun`. -/
def tr (children : List (Child .tr_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .tr_attrib attrs := by decide) :
    Element .tr .tr_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val form : ([< form_attrib], [< form_content_fun], [> form]) star`: its children
are checked against `flow5_without_form`. -/
def form (children : List (Child .flow5_without_form) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .form_attrib attrs := by decide) :
    Element .form .flow5_without_form :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val fieldset : ?legend:[< legend] elt wrap -> ... star`: the
optional legend heads the children. -/
def fieldset (children : List (Child .flow5) := [])
    (legend : Option (Element .legend .phrasing) := none)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .fieldset_attrib attrs := by decide) :
    Element .fieldset .flow5 :=
  ⟨attrs, legend.toList.map Element.toRaw ++ children.map Child.raw⟩
/-- TyXML `val legend : ([< legend_attrib], [< legend_content_fun], [> legend]) star`: its children
are checked against `phrasing`. -/
def legend (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .legend_attrib attrs := by decide) :
    Element .legend .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val label : ([< label_attrib], [< label_content_fun], [> label]) star`: its children
are checked against `phrasing_without_label`. -/
def label (children : List (Child .phrasing_without_label) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .label_attrib attrs := by decide) :
    Element .label .phrasing_without_label :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val input : ([< input_attrib], [> input]) nullary`: no children. -/
def input
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .input_attrib attrs := by decide) :
    Element .input .notag :=
  ⟨attrs, []⟩

/-- TyXML `val button : ([< button_attrib], [< button_content_fun], [> button]) star`: its children
are checked against `phrasing_without_interactive`. -/
def button (children : List (Child .phrasing_without_interactive) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .button_attrib attrs := by decide) :
    Element .button .phrasing_without_interactive :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val select : ([< select_attrib], [< select_content_fun], [> select]) star`: its children
are checked against `select_content_fun`. -/
def select (children : List (Child .select_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .select_attrib attrs := by decide) :
    Element .select .select_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val datalist : ([< datalist_attrib], [> datalist]) nullary`: no children. -/
def datalist
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .datalist_attrib attrs := by decide) :
    Element .datalist .notag :=
  ⟨attrs, []⟩

/-- TyXML `val optgroup : label:text wrap -> ... star`: the required label
becomes the `label` attribute. -/
def optgroup (label : String) (children : List (Child .optgroup_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .optgroup_attrib attrs := by decide) :
    Element .optgroup .optgroup_content_fun :=
  ⟨(Attr.label, label) :: attrs, children.map Child.raw⟩
/-- TyXML `val option : (option_attrib, [< option_content_fun], [> option]) unary`: exactly one
child, checked against `option_content_fun`. -/
def option (child : Child .option_content_fun)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .option_attrib attrs := by decide) :
    Element .option .option_content_fun :=
  ⟨attrs, [child.raw]⟩

/-- TyXML `val textarea : (textarea_attrib, [< textarea_content_fun], [> textarea]) unary`: exactly one
child, checked against `textarea_content`. -/
def textarea (child : Child .textarea_content)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .textarea_attrib attrs := by decide) :
    Element .textarea .textarea_content :=
  ⟨attrs, [child.raw]⟩

/-- TyXML `val keygen : ([< keygen_attrib], [> keygen]) nullary`: no children. -/
def keygen
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .keygen_attrib attrs := by decide) :
    Element .keygen .notag :=
  ⟨attrs, []⟩

/-- TyXML `val progress : ([< progress_attrib], [< progress_content_fun], [> progress]) star`: its children
are checked against `phrasing_without_progress`. -/
def progress (children : List (Child .phrasing_without_progress) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .progress_attrib attrs := by decide) :
    Element .progress .phrasing_without_progress :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val meter : ([< meter_attrib], [< meter_content_fun], [> meter]) star`: its children
are checked against `phrasing_without_meter`. -/
def meter (children : List (Child .phrasing_without_meter) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .meter_attrib attrs := by decide) :
    Element .meter .phrasing_without_meter :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val output_elt : ([< output_elt_attrib], [< output_elt_content_fun], [> output_elt]) star`: its children
are checked against `phrasing`. -/
def output_elt (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .output_elt_attrib attrs := by decide) :
    Element .output .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val details : [< summary] elt wrap -> ... star`: the required
summary is the first positional argument and heads the children. -/
def details (summary : Element .summary .phrasing) (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .details_attrib attrs := by decide) :
    Element .details .flow5 :=
  ⟨attrs, summary.toRaw :: children.map Child.raw⟩
/-- TyXML `val summary : ([< summary_attrib], [< summary_content_fun], [> summary]) star`: its children
are checked against `phrasing`. -/
def summary (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .summary_attrib attrs := by decide) :
    Element .summary .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val command : label:text wrap -> ([< command_attrib], [> command]) nullary`:
the required label becomes the `label` attribute. -/
def command (label : String)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .command_attrib attrs := by decide) :
    Element .command .notag :=
  ⟨(Attr.label, label) :: attrs, []⟩
/-- TyXML `val menu : ([< menu_attrib], [> menu]) nullary`: no children. -/
def menu
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .menu_attrib attrs := by decide) :
    Element .menu .notag :=
  ⟨attrs, []⟩

/-- TyXML `val script : (script_attrib, [< script_content_fun], [> script]) unary`: exactly one
child, checked against `script_content_fun`. -/
def script (child : Child .script_content_fun)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .script_attrib attrs := by decide) :
    Element .script .script_content_fun :=
  ⟨attrs, [child.raw]⟩

/-- TyXML `val noscript : ([< noscript_attrib], [< noscript_content_fun], [> noscript]) star`: its children
are checked against `flow5_without_noscript`. -/
def noscript (children : List (Child .flow5_without_noscript) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .noscript_attrib attrs := by decide) :
    Element .noscript .flow5_without_noscript :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val template : ([< template_attrib], [< template_content_fun], [> template]) star`: its children
are checked against `flow5`. -/
def template (children : List (Child .flow5) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .template_attrib attrs := by decide) :
    Element .template .flow5 :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val meta : ([< meta_attrib], [> meta]) nullary`: no children. -/
def «meta»
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .meta_attrib attrs := by decide) :
    Element .«meta» .notag :=
  ⟨attrs, []⟩

/-- TyXML `val style : ([< style_attrib], [< style_content_fun], [> style]) star`: its children
are checked against `style_content_fun`. -/
def style (children : List (Child .style_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .style_attrib attrs := by decide) :
    Element .style .style_content_fun :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val link : rel:linktypes wrap -> href:Xml.uri wrap ->
([< link_attrib], [> link]) nullary`: both labelled arguments are required
and become attributes. -/
def link (rel : String) (href : String)
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .link_attrib attrs := by decide) :
    Element .link .notag :=
  ⟨(Attr.rel, rel) :: (Attr.href, href) :: attrs, []⟩
/-- TyXML `val rt : ([< rt_attrib], [< rt_content_fun], [> rt]) star`: its children
are checked against `phrasing`. -/
def rt (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .rt_attrib attrs := by decide) :
    Element .rt .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val rp : ([< rp_attrib], [< rp_content_fun], [> rp]) star`: its children
are checked against `phrasing`. -/
def rp (children : List (Child .phrasing) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .rp_attrib attrs := by decide) :
    Element .rp .phrasing :=
  ⟨attrs, children.map Child.raw⟩

/-- TyXML `val ruby : ([< ruby_attrib], [< ruby_content_fun], [> ruby]) star`: its children
are checked against `ruby_content_fun`. -/
def ruby (children : List (Child .ruby_content_fun) := [])
    (attrs : List (Attr × String) := [])
    (_ha : AttrsAdmitted .ruby_attrib attrs := by decide) :
    Element .ruby .ruby_content_fun :=
  ⟨attrs, children.map Child.raw⟩
end Whatwg.Html.E

namespace Whatwg.Html.A

open Whatwg.Html.Schema (Attr)

/-! ## Attribute constructors

One helper per row of `Whatwg.Html.Schema.attributeCtors`, named as TyXML
names it and returning the tag/value pair a combinator's `attrs` argument
takes. Every value is a `String` at this pin; TyXML's typed value arguments
(`nmtokens wrap`, `[< `Text | `Password ] wrap`, `Xml.event_handler`) are a
later slice, and the `valueType` column each docstring quotes is what they
will become. -/

/-- TyXML `a_class : nmtokens wrap`, markup `class`. -/
def a_class (value : String) : Attr × String := (.«class», value)

/-- TyXML `a_user_data : nmtoken -> text wrap`, markup `data-`. The TyXML constructor takes a name suffix as well; `Attr × String` has no room for it at this pin, so only the value is carried. -/
def a_user_data (value : String) : Attr × String := (.user_data, value)

/-- TyXML `a_id : text wrap`, markup `id`. -/
def a_id (value : String) : Attr × String := (.id, value)

/-- TyXML `a_title : text wrap`, markup `title`. -/
def a_title (value : String) : Attr × String := (.title, value)

/-- TyXML `a_xml_lang : languagecode wrap`, markup `xml:lang`. -/
def a_xml_lang (value : String) : Attr × String := (.xml_lang, value)

/-- TyXML `a_lang : languagecode wrap`, markup `lang`. -/
def a_lang (value : String) : Attr × String := (.lang, value)

/-- TyXML `a_onabort : Xml.event_handler`, markup `onabort`. -/
def a_onabort (value : String) : Attr × String := (.onAbort, value)

/-- TyXML `a_onafterprint : Xml.event_handler`, markup `onafterprint`. -/
def a_onafterprint (value : String) : Attr × String := (.onAfterPrint, value)

/-- TyXML `a_onbeforeprint : Xml.event_handler`, markup `onbeforeprint`. -/
def a_onbeforeprint (value : String) : Attr × String := (.onBeforePrint, value)

/-- TyXML `a_onbeforeunload : Xml.event_handler`, markup `onbeforeunload`. -/
def a_onbeforeunload (value : String) : Attr × String := (.onBeforeUnload, value)

/-- TyXML `a_onblur : Xml.event_handler`, markup `onblur`. -/
def a_onblur (value : String) : Attr × String := (.onBlur, value)

/-- TyXML `a_oncanplay : Xml.event_handler`, markup `oncanplay`. -/
def a_oncanplay (value : String) : Attr × String := (.onCanPlay, value)

/-- TyXML `a_oncanplaythrough : Xml.event_handler`, markup `oncanplaythrough`. -/
def a_oncanplaythrough (value : String) : Attr × String := (.onCanPlayThrough, value)

/-- TyXML `a_onchange : Xml.event_handler`, markup `onchange`. -/
def a_onchange (value : String) : Attr × String := (.onChange, value)

/-- TyXML `a_onclose : Xml.event_handler`, markup `onclose`. -/
def a_onclose (value : String) : Attr × String := (.onClose, value)

/-- TyXML `a_ondurationchange : Xml.event_handler`, markup `ondurationchange`. -/
def a_ondurationchange (value : String) : Attr × String := (.onDurationChange, value)

/-- TyXML `a_onemptied : Xml.event_handler`, markup `onemptied`. -/
def a_onemptied (value : String) : Attr × String := (.onEmptied, value)

/-- TyXML `a_onended : Xml.event_handler`, markup `onended`. -/
def a_onended (value : String) : Attr × String := (.onEnded, value)

/-- TyXML `a_onerror : Xml.event_handler`, markup `onerror`. -/
def a_onerror (value : String) : Attr × String := (.onError, value)

/-- TyXML `a_onfocus : Xml.event_handler`, markup `onfocus`. -/
def a_onfocus (value : String) : Attr × String := (.onFocus, value)

/-- TyXML `a_onformchange : Xml.event_handler`, markup `onformchange`. -/
def a_onformchange (value : String) : Attr × String := (.onFormChange, value)

/-- TyXML `a_onforminput : Xml.event_handler`, markup `onforminput`. -/
def a_onforminput (value : String) : Attr × String := (.onFormInput, value)

/-- TyXML `a_onhashchange : Xml.event_handler`, markup `onhashchange`. -/
def a_onhashchange (value : String) : Attr × String := (.onHashChange, value)

/-- TyXML `a_oninput : Xml.event_handler`, markup `oninput`. -/
def a_oninput (value : String) : Attr × String := (.onInput, value)

/-- TyXML `a_oninvalid : Xml.event_handler`, markup `oninvalid`. -/
def a_oninvalid (value : String) : Attr × String := (.onInvalid, value)

/-- TyXML `a_onmousewheel : Xml.event_handler`, markup `onmousewheel`. -/
def a_onmousewheel (value : String) : Attr × String := (.onMouseWheel, value)

/-- TyXML `a_onoffline : Xml.event_handler`, markup `onoffline`. -/
def a_onoffline (value : String) : Attr × String := (.onOffLine, value)

/-- TyXML `a_ononline : Xml.event_handler`, markup `ononline`. -/
def a_ononline (value : String) : Attr × String := (.onOnLine, value)

/-- TyXML `a_onpause : Xml.event_handler`, markup `onpause`. -/
def a_onpause (value : String) : Attr × String := (.onPause, value)

/-- TyXML `a_onplay : Xml.event_handler`, markup `onplay`. -/
def a_onplay (value : String) : Attr × String := (.onPlay, value)

/-- TyXML `a_onplaying : Xml.event_handler`, markup `onplaying`. -/
def a_onplaying (value : String) : Attr × String := (.onPlaying, value)

/-- TyXML `a_onpagehide : Xml.event_handler`, markup `onpagehide`. -/
def a_onpagehide (value : String) : Attr × String := (.onPageHide, value)

/-- TyXML `a_onpageshow : Xml.event_handler`, markup `onpageshow`. -/
def a_onpageshow (value : String) : Attr × String := (.onPageShow, value)

/-- TyXML `a_onpopstate : Xml.event_handler`, markup `onpopstate`. -/
def a_onpopstate (value : String) : Attr × String := (.onPopState, value)

/-- TyXML `a_onprogress : Xml.event_handler`, markup `onprogress`. -/
def a_onprogress (value : String) : Attr × String := (.onProgress, value)

/-- TyXML `a_onratechange : Xml.event_handler`, markup `onratechange`. -/
def a_onratechange (value : String) : Attr × String := (.onRateChange, value)

/-- TyXML `a_onreadystatechange : Xml.event_handler`, markup `onreadystatechange`. -/
def a_onreadystatechange (value : String) : Attr × String := (.onReadyStateChange, value)

/-- TyXML `a_onredo : Xml.event_handler`, markup `onredo`. -/
def a_onredo (value : String) : Attr × String := (.onRedo, value)

/-- TyXML `a_onresize : Xml.event_handler`, markup `onresize`. -/
def a_onresize (value : String) : Attr × String := (.onResize, value)

/-- TyXML `a_onscroll : Xml.event_handler`, markup `onscroll`. -/
def a_onscroll (value : String) : Attr × String := (.onScroll, value)

/-- TyXML `a_onseeked : Xml.event_handler`, markup `onseeked`. -/
def a_onseeked (value : String) : Attr × String := (.onSeeked, value)

/-- TyXML `a_onseeking : Xml.event_handler`, markup `onseeking`. -/
def a_onseeking (value : String) : Attr × String := (.onSeeking, value)

/-- TyXML `a_onselect : Xml.event_handler`, markup `onselect`. -/
def a_onselect (value : String) : Attr × String := (.onSelect, value)

/-- TyXML `a_onshow : Xml.event_handler`, markup `onshow`. -/
def a_onshow (value : String) : Attr × String := (.onShow, value)

/-- TyXML `a_onstalled : Xml.event_handler`, markup `onstalled`. -/
def a_onstalled (value : String) : Attr × String := (.onStalled, value)

/-- TyXML `a_onstorage : Xml.event_handler`, markup `onstorage`. -/
def a_onstorage (value : String) : Attr × String := (.onStorage, value)

/-- TyXML `a_onsubmit : Xml.event_handler`, markup `onsubmit`. -/
def a_onsubmit (value : String) : Attr × String := (.onSubmit, value)

/-- TyXML `a_onsuspend : Xml.event_handler`, markup `onsuspend`. -/
def a_onsuspend (value : String) : Attr × String := (.onSuspend, value)

/-- TyXML `a_ontimeupdate : Xml.event_handler`, markup `ontimeupdate`. -/
def a_ontimeupdate (value : String) : Attr × String := (.onTimeUpdate, value)

/-- TyXML `a_onundo : Xml.event_handler`, markup `onundo`. -/
def a_onundo (value : String) : Attr × String := (.onUndo, value)

/-- TyXML `a_onunload : Xml.event_handler`, markup `onunload`. -/
def a_onunload (value : String) : Attr × String := (.onUnload, value)

/-- TyXML `a_onvolumechange : Xml.event_handler`, markup `onvolumechange`. -/
def a_onvolumechange (value : String) : Attr × String := (.onVolumeChange, value)

/-- TyXML `a_onwaiting : Xml.event_handler`, markup `onwaiting`. -/
def a_onwaiting (value : String) : Attr × String := (.onWaiting, value)

/-- TyXML `a_onload : Xml.event_handler`, markup `onload`. -/
def a_onload (value : String) : Attr × String := (.onLoad, value)

/-- TyXML `a_onloadeddata : Xml.event_handler`, markup `onloadeddata`. -/
def a_onloadeddata (value : String) : Attr × String := (.onLoadedData, value)

/-- TyXML `a_onloadedmetadata : Xml.event_handler`, markup `onloadedmetadata`. -/
def a_onloadedmetadata (value : String) : Attr × String := (.onLoadedMetaData, value)

/-- TyXML `a_onloadstart : Xml.event_handler`, markup `onloadstart`. -/
def a_onloadstart (value : String) : Attr × String := (.onLoadStart, value)

/-- TyXML `a_onmessage : Xml.event_handler`, markup `onmessage`. -/
def a_onmessage (value : String) : Attr × String := (.onMessage, value)

/-- TyXML `a_onclick : Xml.mouse_event_handler`, markup `onclick`. -/
def a_onclick (value : String) : Attr × String := (.onClick, value)

/-- TyXML `a_oncontextmenu : Xml.mouse_event_handler`, markup `oncontextmenu`. -/
def a_oncontextmenu (value : String) : Attr × String := (.onContextMenu, value)

/-- TyXML `a_ondblclick : Xml.mouse_event_handler`, markup `ondblclick`. -/
def a_ondblclick (value : String) : Attr × String := (.onDblClick, value)

/-- TyXML `a_ondrag : Xml.mouse_event_handler`, markup `ondrag`. -/
def a_ondrag (value : String) : Attr × String := (.onDrag, value)

/-- TyXML `a_ondragend : Xml.mouse_event_handler`, markup `ondragend`. -/
def a_ondragend (value : String) : Attr × String := (.onDragEnd, value)

/-- TyXML `a_ondragenter : Xml.mouse_event_handler`, markup `ondragenter`. -/
def a_ondragenter (value : String) : Attr × String := (.onDragEnter, value)

/-- TyXML `a_ondragleave : Xml.mouse_event_handler`, markup `ondragleave`. -/
def a_ondragleave (value : String) : Attr × String := (.onDragLeave, value)

/-- TyXML `a_ondragover : Xml.mouse_event_handler`, markup `ondragover`. -/
def a_ondragover (value : String) : Attr × String := (.onDragOver, value)

/-- TyXML `a_ondragstart : Xml.mouse_event_handler`, markup `ondragstart`. -/
def a_ondragstart (value : String) : Attr × String := (.onDragStart, value)

/-- TyXML `a_ondrop : Xml.mouse_event_handler`, markup `ondrop`. -/
def a_ondrop (value : String) : Attr × String := (.onDrop, value)

/-- TyXML `a_onmousedown : Xml.mouse_event_handler`, markup `onmousedown`. -/
def a_onmousedown (value : String) : Attr × String := (.onMouseDown, value)

/-- TyXML `a_onmouseup : Xml.mouse_event_handler`, markup `onmouseup`. -/
def a_onmouseup (value : String) : Attr × String := (.onMouseUp, value)

/-- TyXML `a_onmouseover : Xml.mouse_event_handler`, markup `onmouseover`. -/
def a_onmouseover (value : String) : Attr × String := (.onMouseOver, value)

/-- TyXML `a_onmousemove : Xml.mouse_event_handler`, markup `onmousemove`. -/
def a_onmousemove (value : String) : Attr × String := (.onMouseMove, value)

/-- TyXML `a_onmouseout : Xml.mouse_event_handler`, markup `onmouseout`. -/
def a_onmouseout (value : String) : Attr × String := (.onMouseOut, value)

/-- TyXML `a_ontouchstart : Xml.touch_event_handler`, markup `ontouchstart`. -/
def a_ontouchstart (value : String) : Attr × String := (.onTouchStart, value)

/-- TyXML `a_ontouchend : Xml.touch_event_handler`, markup `ontouchend`. -/
def a_ontouchend (value : String) : Attr × String := (.onTouchEnd, value)

/-- TyXML `a_ontouchmove : Xml.touch_event_handler`, markup `ontouchmove`. -/
def a_ontouchmove (value : String) : Attr × String := (.onTouchMove, value)

/-- TyXML `a_ontouchcancel : Xml.touch_event_handler`, markup `ontouchcancel`. -/
def a_ontouchcancel (value : String) : Attr × String := (.onTouchCancel, value)

/-- TyXML `a_onkeypress : Xml.keyboard_event_handler`, markup `onkeypress`. -/
def a_onkeypress (value : String) : Attr × String := (.onKeyPress, value)

/-- TyXML `a_onkeydown : Xml.keyboard_event_handler`, markup `onkeydown`. -/
def a_onkeydown (value : String) : Attr × String := (.onKeyDown, value)

/-- TyXML `a_onkeyup : Xml.keyboard_event_handler`, markup `onkeyup`. -/
def a_onkeyup (value : String) : Attr × String := (.onKeyUp, value)

/-- TyXML `a_allowfullscreen : unit`, markup `allowfullscreen`. -/
def a_allowfullscreen (value : String) : Attr × String := (.allowfullscreen, value)

/-- TyXML `a_allowpaymentrequest : unit`, markup `allowpaymentrequest`. -/
def a_allowpaymentrequest (value : String) : Attr × String := (.allowpaymentrequest, value)

/-- TyXML `a_autocomplete : autocomplete_option wrap`, markup `autocomplete`. -/
def a_autocomplete (value : String) : Attr × String := (.autocomplete, value)

/-- TyXML `a_async : unit`, markup `async`. -/
def a_async (value : String) : Attr × String := (.async, value)

/-- TyXML `a_autofocus : unit`, markup `autofocus`. -/
def a_autofocus (value : String) : Attr × String := (.autofocus, value)

/-- TyXML `a_autoplay : unit`, markup `autoplay`. -/
def a_autoplay (value : String) : Attr × String := (.autoplay, value)

/-- TyXML `a_muted : unit`, markup `muted`. -/
def a_muted (value : String) : Attr × String := (.muted, value)

/-- TyXML `a_crossorigin : [< `Anonymous | `Use_credentials ] wrap`, markup `crossorigin`. -/
def a_crossorigin (value : String) : Attr × String := (.crossorigin, value)

/-- TyXML `a_integrity : string wrap`, markup `integrity`. -/
def a_integrity (value : String) : Attr × String := (.integrity, value)

/-- TyXML `a_mediagroup : string wrap`, markup `mediagroup`. -/
def a_mediagroup (value : String) : Attr × String := (.mediagroup, value)

/-- TyXML `a_challenge : text wrap`, markup `challenge`. -/
def a_challenge (value : String) : Attr × String := (.challenge, value)

/-- TyXML `a_contenteditable : bool wrap`, markup `contenteditable`. -/
def a_contenteditable (value : String) : Attr × String := (.contenteditable, value)

/-- TyXML `a_contextmenu : idref wrap`, markup `contextmenu`. -/
def a_contextmenu (value : String) : Attr × String := (.contextmenu, value)

/-- TyXML `a_controls : unit`, markup `controls`. -/
def a_controls (value : String) : Attr × String := (.controls, value)

/-- TyXML `a_dir : [< `Rtl | `Ltr ] wrap`, markup `dir`. -/
def a_dir (value : String) : Attr × String := (.dir, value)

/-- TyXML `a_draggable : bool wrap`, markup `draggable`. -/
def a_draggable (value : String) : Attr × String := (.draggable, value)

/-- TyXML `a_form : idref wrap`, markup `form`. -/
def a_form (value : String) : Attr × String := (.form, value)

/-- TyXML `a_formaction : Xml.uri wrap`, markup `formaction`. -/
def a_formaction (value : String) : Attr × String := (.formaction, value)

/-- TyXML `a_formenctype : contenttype wrap`, markup `formenctype`. -/
def a_formenctype (value : String) : Attr × String := (.formenctype, value)

/-- TyXML `a_formnovalidate : unit`, markup `formnovalidate`. -/
def a_formnovalidate (value : String) : Attr × String := (.formnovalidate, value)

/-- TyXML `a_formtarget : text wrap`, markup `formtarget`. -/
def a_formtarget (value : String) : Attr × String := (.formtarget, value)

/-- TyXML `a_hidden : unit`, markup `hidden`. -/
def a_hidden (value : String) : Attr × String := (.hidden, value)

/-- TyXML `a_high : float_number wrap`, markup `high`. -/
def a_high (value : String) : Attr × String := (.high, value)

/-- TyXML `a_icon : Xml.uri wrap`, markup `icon`. -/
def a_icon (value : String) : Attr × String := (.icon, value)

/-- TyXML `a_ismap : unit`, markup `ismap`. -/
def a_ismap (value : String) : Attr × String := (.ismap, value)

/-- TyXML `a_keytype : text wrap`, markup `keytype`. -/
def a_keytype (value : String) : Attr × String := (.keytype, value)

/-- TyXML `a_list : idref wrap`, markup `list`. -/
def a_list (value : String) : Attr × String := (.list, value)

/-- TyXML `a_loop : unit`, markup `loop`. -/
def a_loop (value : String) : Attr × String := (.loop, value)

/-- TyXML `a_low : float_number wrap`, markup `low`. -/
def a_low (value : String) : Attr × String := (.high, value)

/-- TyXML `a_max : float_number wrap`, markup `max`. -/
def a_max (value : String) : Attr × String := (.max, value)

/-- TyXML `a_input_max : number_or_datetime wrap`, markup `max`. -/
def a_input_max (value : String) : Attr × String := (.input_Max, value)

/-- TyXML `a_min : float_number wrap`, markup `min`. -/
def a_min (value : String) : Attr × String := (.min, value)

/-- TyXML `a_input_min : number_or_datetime wrap`, markup `min`. -/
def a_input_min (value : String) : Attr × String := (.input_Min, value)

/-- TyXML `a_inputmode : [< `None | `Text | `Decimal | `Numeric | `Tel | `Search | `Email | `Url ] wrap`, markup `inputmode`. -/
def a_inputmode (value : String) : Attr × String := (.inputmode, value)

/-- TyXML `a_novalidate : unit`, markup `novalidate`. -/
def a_novalidate (value : String) : Attr × String := (.novalidate, value)

/-- TyXML `a_open : unit`, markup `open`. -/
def a_open (value : String) : Attr × String := (.«open», value)

/-- TyXML `a_optimum : float_number wrap`, markup `optimum`. -/
def a_optimum (value : String) : Attr × String := (.optimum, value)

/-- TyXML `a_pattern : text wrap`, markup `pattern`. -/
def a_pattern (value : String) : Attr × String := (.pattern, value)

/-- TyXML `a_placeholder : text wrap`, markup `placeholder`. -/
def a_placeholder (value : String) : Attr × String := (.placeholder, value)

/-- TyXML `a_poster : Xml.uri wrap`, markup `poster`. -/
def a_poster (value : String) : Attr × String := (.poster, value)

/-- TyXML `a_preload : [< `None | `Metadata | `Audio ] wrap`, markup `preload`. -/
def a_preload (value : String) : Attr × String := (.preload, value)

/-- TyXML `a_pubdate : unit`, markup `pubdate`. -/
def a_pubdate (value : String) : Attr × String := (.pubdate, value)

/-- TyXML `a_radiogroup : text wrap`, markup `radiogroup`. -/
def a_radiogroup (value : String) : Attr × String := (.radiogroup, value)

/-- TyXML `a_referrerpolicy : referrerpolicy wrap`, markup `referrerpolicy`. -/
def a_referrerpolicy (value : String) : Attr × String := (.referrerpolicy, value)

/-- TyXML `a_required : unit`, markup `required`. -/
def a_required (value : String) : Attr × String := (.required, value)

/-- TyXML `a_reversed : unit`, markup `reserved`. -/
def a_reversed (value : String) : Attr × String := (.reversed, value)

/-- TyXML `a_sandbox : [< sandbox_token ] list wrap`, markup `sandbox`. -/
def a_sandbox (value : String) : Attr × String := (.sandbox, value)

/-- TyXML `a_spellcheck : bool wrap`, markup `spellcheck`. -/
def a_spellcheck (value : String) : Attr × String := (.spellcheck, value)

/-- TyXML `a_scoped : unit`, markup `scoped`. -/
def a_scoped (value : String) : Attr × String := (.«scoped», value)

/-- TyXML `a_seamless : unit`, markup `seamless`. -/
def a_seamless (value : String) : Attr × String := (.seamless, value)

/-- TyXML `a_sizes : (number * number) list option wrap`, markup `sizes`. -/
def a_sizes (value : String) : Attr × String := (.sizes, value)

/-- TyXML `a_span : number wrap`, markup `span`. -/
def a_span (value : String) : Attr × String := (.span, value)

/-- TyXML `a_srclang : nmtoken wrap`, markup `xml:lang`. -/
def a_srclang (value : String) : Attr × String := (.xml_lang, value)

/-- TyXML `a_srcset : image_candidate list wrap`, markup `srcset`. -/
def a_srcset (value : String) : Attr × String := (.srcset, value)

/-- TyXML `a_img_sizes : text list wrap`, markup `sizes`. -/
def a_img_sizes (value : String) : Attr × String := (.img_sizes, value)

/-- TyXML `a_start : number wrap`, markup `start`. -/
def a_start (value : String) : Attr × String := (.start, value)

/-- TyXML `a_step : float_number option wrap`, markup `step`. -/
def a_step (value : String) : Attr × String := (.step, value)

/-- TyXML `a_translate : [< `Yes | `No ] wrap`, markup `translate`. -/
def a_translate (value : String) : Attr × String := (.translate, value)

/-- TyXML `a_wrap : [< `Soft | `Hard ] wrap`, markup `wrap`. -/
def a_wrap (value : String) : Attr × String := (.wrap, value)

/-- TyXML `a_version : cdata wrap`, markup `version`. -/
def a_version (value : String) : Attr × String := (.version, value)

/-- TyXML `a_xmlns : [< `W3_org_1999_xhtml ] wrap`, markup `xmlns`. -/
def a_xmlns (value : String) : Attr × String := (.xmlns, value)

/-- TyXML `a_manifest : Xml.uri wrap`, markup `manifest`. -/
def a_manifest (value : String) : Attr × String := (.manifest, value)

/-- TyXML `a_cite : Xml.uri wrap`, markup `cite`. -/
def a_cite (value : String) : Attr × String := (.cite, value)

/-- TyXML `a_xml_space : [< `Default | `Preserve ] wrap`, markup `xml:space`. -/
def a_xml_space (value : String) : Attr × String := (.xml_space, value)

/-- TyXML `a_accesskey : character wrap`, markup `accesskey`. -/
def a_accesskey (value : String) : Attr × String := (.accesskey, value)

/-- TyXML `a_charset : charset wrap`, markup `charset`. -/
def a_charset (value : String) : Attr × String := (.charset, value)

/-- TyXML `a_accept_charset : charsets wrap`, markup `accept-charset`. -/
def a_accept_charset (value : String) : Attr × String := (.accept_charset, value)

/-- TyXML `a_accept : contenttypes wrap`, markup `accept`. -/
def a_accept (value : String) : Attr × String := (.accept, value)

/-- TyXML `a_href : Xml.uri wrap`, markup `href`. -/
def a_href (value : String) : Attr × String := (.href, value)

/-- TyXML `a_hreflang : languagecode wrap`, markup `hreflang`. -/
def a_hreflang (value : String) : Attr × String := (.hreflang, value)

/-- TyXML `a_download : string option wrap`, markup `download`. -/
def a_download (value : String) : Attr × String := (.download, value)

/-- TyXML `a_rel : linktypes wrap`, markup `rel`. -/
def a_rel (value : String) : Attr × String := (.rel, value)

/-- TyXML `a_tabindex : number wrap`, markup `tabindex`. -/
def a_tabindex (value : String) : Attr × String := (.tabindex, value)

/-- TyXML `a_mime_type : contenttype wrap`, markup `type`. -/
def a_mime_type (value : String) : Attr × String := (.mime_type, value)

/-- TyXML `a_datetime : cdata wrap`, markup `datetime`. -/
def a_datetime (value : String) : Attr × String := (.datetime, value)

/-- TyXML `a_action : Xml.uri wrap`, markup `action`. -/
def a_action (value : String) : Attr × String := (.action, value)

/-- TyXML `a_checked : unit`, markup `checked`. -/
def a_checked (value : String) : Attr × String := (.checked, value)

/-- TyXML `a_cols : number wrap`, markup `cols`. -/
def a_cols (value : String) : Attr × String := (.cols, value)

/-- TyXML `a_enctype : contenttype wrap`, markup `enctype`. -/
def a_enctype (value : String) : Attr × String := (.enctype, value)

/-- TyXML `a_label_for : idref wrap`, markup `for`. -/
def a_label_for (value : String) : Attr × String := (.label_for, value)

/-- TyXML `a_for : idref wrap`, markup `for`. -/
def a_for (value : String) : Attr × String := (.label_for, value)

/-- TyXML `a_output_for : idrefs wrap`, markup `for`. -/
def a_output_for (value : String) : Attr × String := (.output_for, value)

/-- TyXML `a_for_list : idrefs wrap`, markup `for`. -/
def a_for_list (value : String) : Attr × String := (.output_for, value)

/-- TyXML `a_maxlength : number wrap`, markup `maxlength`. -/
def a_maxlength (value : String) : Attr × String := (.maxlength, value)

/-- TyXML `a_minlength : number wrap`, markup `minlength`. -/
def a_minlength (value : String) : Attr × String := (.minlength, value)

/-- TyXML `a_method : [< `Get | `Post ] wrap`, markup `method`. -/
def a_method (value : String) : Attr × String := (.method, value)

/-- TyXML `a_formmethod : [< `Get | `Post ] wrap`, markup `formmethod`. -/
def a_formmethod (value : String) : Attr × String := (.formmethod, value)

/-- TyXML `a_multiple : unit`, markup `multiple`. -/
def a_multiple (value : String) : Attr × String := (.multiple, value)

/-- TyXML `a_name : text wrap`, markup `name`. -/
def a_name (value : String) : Attr × String := (.name, value)

/-- TyXML `a_rows : number wrap`, markup `rows`. -/
def a_rows (value : String) : Attr × String := (.rows, value)

/-- TyXML `a_selected : unit`, markup `selected`. -/
def a_selected (value : String) : Attr × String := (.selected, value)

/-- TyXML `a_size : number wrap`, markup `size`. -/
def a_size (value : String) : Attr × String := (.size, value)

/-- TyXML `a_src : Xml.uri wrap`, markup `src`. -/
def a_src (value : String) : Attr × String := (.src, value)

/-- TyXML `a_input_type : [< `Url | `Tel | `Text | `Time | `Search | `Password | `Checkbox | `Range | `Radio | `Submit | `Reset | `Number | `Hidden | `Month | `Week | `File | `Email | `Image | `Datetime_local | `Datetime | `Date | `Color | `Button ] wrap`, markup `type`. -/
def a_input_type (value : String) : Attr × String := (.input_Type, value)

/-- TyXML `a_text_value : text wrap`, markup `value`. -/
def a_text_value (value : String) : Attr × String := (.text_Value, value)

/-- TyXML `a_int_value : number wrap`, markup `value`. -/
def a_int_value (value : String) : Attr × String := (.int_Value, value)

/-- TyXML `a_value : cdata wrap`, markup `value`. -/
def a_value (value : String) : Attr × String := (.value, value)

/-- TyXML `a_float_value : float_number wrap`, markup `value`. -/
def a_float_value (value : String) : Attr × String := (.float_Value, value)

/-- TyXML `a_disabled : unit`, markup `disabled`. -/
def a_disabled (value : String) : Attr × String := (.disabled, value)

/-- TyXML `a_readonly : unit`, markup `readonly`. -/
def a_readonly (value : String) : Attr × String := (.readOnly, value)

/-- TyXML `a_button_type : [< `Button | `Submit | `Reset ] wrap`, markup `type`. -/
def a_button_type (value : String) : Attr × String := (.button_Type, value)

/-- TyXML `a_script_type : Html_types.script_type wrap`, markup `type`. -/
def a_script_type (value : String) : Attr × String := (.script_type, value)

/-- TyXML `a_command_type : [< `Command | `Checkbox | `Radio ] wrap`, markup `type`. -/
def a_command_type (value : String) : Attr × String := (.command_Type, value)

/-- TyXML `a_menu_type : [< `Context | `Toolbar ] wrap`, markup `type`. -/
def a_menu_type (value : String) : Attr × String := (.menu_Type, value)

/-- TyXML `a_label : text wrap`, markup `label`. -/
def a_label (value : String) : Attr × String := (.label, value)

/-- TyXML `a_align : [< `Left | `Right | `Justify | `Char ] wrap`, markup `align`. -/
def a_align (value : String) : Attr × String := (.align, value)

/-- TyXML `a_axis : cdata wrap`, markup `axis`. -/
def a_axis (value : String) : Attr × String := (.axis, value)

/-- TyXML `a_colspan : number wrap`, markup `colspan`. -/
def a_colspan (value : String) : Attr × String := (.colspan, value)

/-- TyXML `a_headers : idrefs wrap`, markup `headers`. -/
def a_headers (value : String) : Attr × String := (.headers, value)

/-- TyXML `a_rowspan : number wrap`, markup `rowspan`. -/
def a_rowspan (value : String) : Attr × String := (.rowspan, value)

/-- TyXML `a_scope : [< `Row | `Col | `Rowgroup | `Colgroup ] wrap`, markup `scope`. -/
def a_scope (value : String) : Attr × String := (.scope, value)

/-- TyXML `a_summary : text wrap`, markup `summary`. -/
def a_summary (value : String) : Attr × String := (.summary, value)

/-- TyXML `a_border : pixels wrap`, markup `border`. -/
def a_border (value : String) : Attr × String := (.border, value)

/-- TyXML `a_rules : [< `None | `Groups | `Rows | `Cols | `All ] wrap`, markup `rules`. -/
def a_rules (value : String) : Attr × String := (.rules, value)

/-- TyXML `a_char : character wrap`, markup `char`. -/
def a_char (value : String) : Attr × String := (.char, value)

/-- TyXML `a_alt : text wrap`, markup `alt`. -/
def a_alt (value : String) : Attr × String := (.alt, value)

/-- TyXML `a_height : number wrap`, markup `height`. -/
def a_height (value : String) : Attr × String := (.height, value)

/-- TyXML `a_width : number wrap`, markup `width`. -/
def a_width (value : String) : Attr × String := (.width, value)

/-- TyXML `a_shape : shape wrap`, markup `shape`. -/
def a_shape (value : String) : Attr × String := (.shape, value)

/-- TyXML `a_coords : numbers wrap`, markup `coords`. -/
def a_coords (value : String) : Attr × String := (.coords, value)

/-- TyXML `a_usemap : idref wrap`, markup `usemap`. -/
def a_usemap (value : String) : Attr × String := (.usemap, value)

/-- TyXML `a_data : Xml.uri wrap`, markup `data`. -/
def a_data (value : String) : Attr × String := (.«data», value)

/-- TyXML `a_codetype : contenttype wrap`, markup `codetype`. -/
def a_codetype (value : String) : Attr × String := (.codetype, value)

/-- TyXML `a_frameborder : [< `Zero | `One ] wrap`, markup `frameborder`. -/
def a_frameborder (value : String) : Attr × String := (.frameborder, value)

/-- TyXML `a_marginheight : pixels wrap`, markup `marginheight`. -/
def a_marginheight (value : String) : Attr × String := (.marginheight, value)

/-- TyXML `a_marginwidth : pixels wrap`, markup `marginwidth`. -/
def a_marginwidth (value : String) : Attr × String := (.marginwidth, value)

/-- TyXML `a_scrolling : [< `Yes | `No | `Auto ] wrap`, markup `scrolling`. -/
def a_scrolling (value : String) : Attr × String := (.scrolling, value)

/-- TyXML `a_target : frametarget wrap`, markup `target`. -/
def a_target (value : String) : Attr × String := (.target, value)

/-- TyXML `a_content : text wrap`, markup `content`. -/
def a_content (value : String) : Attr × String := (.content, value)

/-- TyXML `a_http_equiv : text wrap`, markup `http-equiv`. -/
def a_http_equiv (value : String) : Attr × String := (.http_equiv, value)

/-- TyXML `a_defer : unit`, markup `defer`. -/
def a_defer (value : String) : Attr × String := (.defer, value)

/-- TyXML `a_media : mediadesc wrap`, markup `media`. -/
def a_media (value : String) : Attr × String := (.media, value)

/-- TyXML `a_style : string wrap`, markup `style`. -/
def a_style (value : String) : Attr × String := (.style_Attr, value)

/-- TyXML `a_property : string wrap`, markup `property`. -/
def a_property (value : String) : Attr × String := (.property, value)

/-- TyXML `a_role : string list wrap`, markup `role`. -/
def a_role (value : String) : Attr × String := (.role, value)

/-- TyXML `a_aria : string -> string list wrap`, markup `aria-`. The TyXML constructor takes a name suffix as well; `Attr × String` has no room for it at this pin, so only the value is carried. -/
def a_aria (value : String) : Attr × String := (.aria, value)
end Whatwg.Html.A
