import Whatwg.Html.Content.Lattice
import Whatwg.Html.Content.Transparent
import Whatwg.Html.Content.Admission
import Whatwg.Html.Node.Raw

/-!
# Whatwg.Html.Node.Typed

The tag-indexed tree of slice H3.3 (`docs/HTML-PACKAGE-PLAN.md`, rulings
HP-4, HP-5 and HP-6): an element carries the admission obligations of its
children and of its attributes as propositions decided at construction, never
as checked booleans, and the value it holds is already erased.

## TyXML's scheme, reproduced through unification

TyXML types a constructor as `('a attrib list, 'b, 'c) star`, where `'c` is
the *result* row. For an ordinary element the result row is a bare variant
(`` [> `Div] ``) and `'b` is that element's own content type. For a
transparent element the result row carries the content parameter
(`` a : ('a attrib, 'a, [> 'a a]) star ``), so a link placed in a phrasing
position is unified against `` `A of phrasing_without_interactive `` and its
children are checked against that payload rather than against the link's own
content type. That is ruling HP-4: transparency is resolved at the enclosing
non-transparent parent, not by a flag passed downward.

`Element t inner` is the Lean transcription of that pair: `t` is the result
tag and `inner` is the content set the element's children were checked
against. A non-transparent combinator fixes `inner` to the element's own
content set; a transparent combinator leaves `inner` universally quantified.
`Child.of` demands `Element t (childSet set t)`, so placing a transparent
element in a `Child set` position assigns `inner := childSet set t`, and
`childSet` reads exactly TyXML's payload table through
`Whatwg.Html.Content.resolveChildSet`.

The inference works as designed on this toolchain, with no fallback needed:
Lean's application elaborator propagates the expected type into the result
type of a function application before elaborating its explicit arguments, so
`?inner` is assigned from the `Child set` position *before* the transparent
element's own children are elaborated, and the `by decide` obligation on each
of those children is stated over a fully assigned content set.
`childSet` is an `abbrev` so that unification may unfold it at reducible
transparency; the obligations themselves reduce at default transparency in
either spelling.

## What is checked, and what is not

- Child admission: `Child.of` and `Child.text` discharge
  `Whatwg.Html.Content.Admits set t` by `decide` at the call site, and the
  resulting `Child` stores that proof. So a `Child set` is evidence that its
  tag is a member of `set` in the sealed TyXML 4.6.0 projection. It is not a
  claim about the HTML Standard; departures of the port are the business of
  `Whatwg.Html.Content.Divergence`.
- Attribute admission: every combinator carries an auto-parameter `_ha`
  proving `AttrsAdmitted` for its element's attribute set. The proof is not
  stored, because `Element` is indexed by the tag and the child content set
  only and the attribute set is not a function of the tag (`table` and
  `tablex` share the tag `Table` and take different attribute sets); the
  parameter is therefore spelled with a leading underscore, and a rejection
  names `_ha`.
- Attribute *values* are plain `String` at this pin. TyXML's typed value
  constructors (`` a_input_type : [< `Text | `Password | ...] wrap -> attrib ``)
  are a later slice.
- Comments have no tag in the content model, so `RawNode.comment` has no
  typed constructor here; a comment enters the tree only through the raw
  layer.
-/

namespace Whatwg.Html.Schema

/-- The markup name of a tag as a total function: `Tag.markupName` where the
projection has one, and the OCaml variant name otherwise. Only the five tags
with no element constructor at all (`PCDATA`, `Img_interactive`,
`Audio_interactive`, `Object_interactive`, `Video_interactive`) take the
fallback, and none of them is reachable from a combinator, so the fallback is
a totality device rather than a spelling claim. -/
def Tag.markupText (t : Tag) : String := t.markupName.getD t.variantName

/-- The markup name of an attribute, by constructor dispatch over the
`markup` column of `attributeCtors`. Where several constructors share a tag
the first row of `attributeCtors` wins, matching `Tag.markupName`'s rule for
`table`/`tablex`; the four tags this affects are `Xml_lang` (`a_xml_lang`
before `a_srclang`), `High`, `Label_for` and `Output_for`. The four attribute
tags that no constructor names fall through to the OCaml variant name. -/
def Attr.markupName : Attr → String
  | .«class» => "class"
  | .user_data => "data-"
  | .id => "id"
  | .title => "title"
  | .xml_lang => "xml:lang"
  | .lang => "lang"
  | .onAbort => "onabort"
  | .onAfterPrint => "onafterprint"
  | .onBeforePrint => "onbeforeprint"
  | .onBeforeUnload => "onbeforeunload"
  | .onBlur => "onblur"
  | .onCanPlay => "oncanplay"
  | .onCanPlayThrough => "oncanplaythrough"
  | .onChange => "onchange"
  | .onClose => "onclose"
  | .onDurationChange => "ondurationchange"
  | .onEmptied => "onemptied"
  | .onEnded => "onended"
  | .onError => "onerror"
  | .onFocus => "onfocus"
  | .onFormChange => "onformchange"
  | .onFormInput => "onforminput"
  | .onHashChange => "onhashchange"
  | .onInput => "oninput"
  | .onInvalid => "oninvalid"
  | .onMouseWheel => "onmousewheel"
  | .onOffLine => "onoffline"
  | .onOnLine => "ononline"
  | .onPause => "onpause"
  | .onPlay => "onplay"
  | .onPlaying => "onplaying"
  | .onPageHide => "onpagehide"
  | .onPageShow => "onpageshow"
  | .onPopState => "onpopstate"
  | .onProgress => "onprogress"
  | .onRateChange => "onratechange"
  | .onReadyStateChange => "onreadystatechange"
  | .onRedo => "onredo"
  | .onResize => "onresize"
  | .onScroll => "onscroll"
  | .onSeeked => "onseeked"
  | .onSeeking => "onseeking"
  | .onSelect => "onselect"
  | .onShow => "onshow"
  | .onStalled => "onstalled"
  | .onStorage => "onstorage"
  | .onSubmit => "onsubmit"
  | .onSuspend => "onsuspend"
  | .onTimeUpdate => "ontimeupdate"
  | .onUndo => "onundo"
  | .onUnload => "onunload"
  | .onVolumeChange => "onvolumechange"
  | .onWaiting => "onwaiting"
  | .onLoad => "onload"
  | .onLoadedData => "onloadeddata"
  | .onLoadedMetaData => "onloadedmetadata"
  | .onLoadStart => "onloadstart"
  | .onMessage => "onmessage"
  | .onClick => "onclick"
  | .onContextMenu => "oncontextmenu"
  | .onDblClick => "ondblclick"
  | .onDrag => "ondrag"
  | .onDragEnd => "ondragend"
  | .onDragEnter => "ondragenter"
  | .onDragLeave => "ondragleave"
  | .onDragOver => "ondragover"
  | .onDragStart => "ondragstart"
  | .onDrop => "ondrop"
  | .onMouseDown => "onmousedown"
  | .onMouseUp => "onmouseup"
  | .onMouseOver => "onmouseover"
  | .onMouseMove => "onmousemove"
  | .onMouseOut => "onmouseout"
  | .onTouchStart => "ontouchstart"
  | .onTouchEnd => "ontouchend"
  | .onTouchMove => "ontouchmove"
  | .onTouchCancel => "ontouchcancel"
  | .onKeyPress => "onkeypress"
  | .onKeyDown => "onkeydown"
  | .onKeyUp => "onkeyup"
  | .allowfullscreen => "allowfullscreen"
  | .allowpaymentrequest => "allowpaymentrequest"
  | .autocomplete => "autocomplete"
  | .async => "async"
  | .autofocus => "autofocus"
  | .autoplay => "autoplay"
  | .muted => "muted"
  | .crossorigin => "crossorigin"
  | .integrity => "integrity"
  | .mediagroup => "mediagroup"
  | .challenge => "challenge"
  | .contenteditable => "contenteditable"
  | .contextmenu => "contextmenu"
  | .controls => "controls"
  | .dir => "dir"
  | .draggable => "draggable"
  | .form => "form"
  | .formaction => "formaction"
  | .formenctype => "formenctype"
  | .formnovalidate => "formnovalidate"
  | .formtarget => "formtarget"
  | .hidden => "hidden"
  | .high => "high"
  | .icon => "icon"
  | .ismap => "ismap"
  | .keytype => "keytype"
  | .list => "list"
  | .loop => "loop"
  | .max => "max"
  | .input_Max => "max"
  | .min => "min"
  | .input_Min => "min"
  | .inputmode => "inputmode"
  | .novalidate => "novalidate"
  | .«open» => "open"
  | .optimum => "optimum"
  | .pattern => "pattern"
  | .placeholder => "placeholder"
  | .poster => "poster"
  | .preload => "preload"
  | .pubdate => "pubdate"
  | .radiogroup => "radiogroup"
  | .referrerpolicy => "referrerpolicy"
  | .required => "required"
  | .reversed => "reserved"
  | .sandbox => "sandbox"
  | .spellcheck => "spellcheck"
  | .«scoped» => "scoped"
  | .seamless => "seamless"
  | .sizes => "sizes"
  | .span => "span"
  | .srcset => "srcset"
  | .img_sizes => "sizes"
  | .start => "start"
  | .step => "step"
  | .translate => "translate"
  | .wrap => "wrap"
  | .version => "version"
  | .xmlns => "xmlns"
  | .manifest => "manifest"
  | .cite => "cite"
  | .xml_space => "xml:space"
  | .accesskey => "accesskey"
  | .charset => "charset"
  | .accept_charset => "accept-charset"
  | .accept => "accept"
  | .href => "href"
  | .hreflang => "hreflang"
  | .download => "download"
  | .rel => "rel"
  | .tabindex => "tabindex"
  | .mime_type => "type"
  | .datetime => "datetime"
  | .action => "action"
  | .checked => "checked"
  | .cols => "cols"
  | .enctype => "enctype"
  | .label_for => "for"
  | .output_for => "for"
  | .maxlength => "maxlength"
  | .minlength => "minlength"
  | .method => "method"
  | .formmethod => "formmethod"
  | .multiple => "multiple"
  | .name => "name"
  | .rows => "rows"
  | .selected => "selected"
  | .size => "size"
  | .src => "src"
  | .input_Type => "type"
  | .text_Value => "value"
  | .int_Value => "value"
  | .value => "value"
  | .float_Value => "value"
  | .disabled => "disabled"
  | .readOnly => "readonly"
  | .button_Type => "type"
  | .script_type => "type"
  | .command_Type => "type"
  | .menu_Type => "type"
  | .label => "label"
  | .align => "align"
  | .axis => "axis"
  | .colspan => "colspan"
  | .headers => "headers"
  | .rowspan => "rowspan"
  | .scope => "scope"
  | .summary => "summary"
  | .border => "border"
  | .rules => "rules"
  | .char => "char"
  | .alt => "alt"
  | .height => "height"
  | .width => "width"
  | .shape => "shape"
  | .coords => "coords"
  | .usemap => "usemap"
  | .«data» => "data"
  | .codetype => "codetype"
  | .frameborder => "frameborder"
  | .marginheight => "marginheight"
  | .marginwidth => "marginwidth"
  | .scrolling => "scrolling"
  | .target => "target"
  | .content => "content"
  | .http_equiv => "http-equiv"
  | .defer => "defer"
  | .media => "media"
  | .style_Attr => "style"
  | .property => "property"
  | .role => "role"
  | .aria => "aria-"
  | other => other.variantName

end Whatwg.Html.Schema

namespace Whatwg.Html

open Whatwg.Html.Schema (Tag ContentSet Attr AttrSet)

/-- An element of tag `t` whose children were checked against the content
set `inner` and whose children are already erased to `RawNode`. The two
indices are TyXML's result row: `t` is the variant and `inner` is the payload
that variant carries when the element is transparent. -/
structure Element (t : Tag) (inner : ContentSet) where
  /-- The attributes, as tag/value pairs; admission against the element's
  attribute set was decided by the combinator that built this value. -/
  attrs : List (Attr × String)
  /-- The erased children, each of which was a `Child inner`. -/
  children : List RawNode

/-- Erasure to the untyped tree: the markup name of the tag, the markup names
of the attributes, and the already-erased children. -/
def Element.toRaw {t : Tag} {inner : ContentSet} (e : Element t inner) : RawNode :=
  .element t.markupText (e.attrs.map (fun p => (p.1.markupName, p.2))) e.children

/-- The content set an element of tag `t` placed in the context `set` must
have checked its children against: the transparent payload the context
assigns `t` when there is one, else `t`'s own content set, else the empty set
`notag`. Total, so that it can index a type; `Whatwg.Html.Content`'s
`resolveChildSet_none` says the fallback is taken exactly for the five tags
with no element row (`PCDATA` and the four `*_interactive` variants) and for
`svg`, whose row carries no content set. An `abbrev` so that unification may
unfold it at reducible transparency. -/
abbrev childSet (set : ContentSet) (t : Tag) : ContentSet :=
  (Content.resolveChildSet t set).getD .notag

/-- A child admitted under the content set `set`: its tag, the proof that
`set` names it, and its erased form. Storing the proof rather than discarding
it is what makes a `Child set` evidence, and it is why `Child.of`'s
auto-parameter is not a dead binder. -/
structure Child (set : ContentSet) where
  /-- The tag of the child. -/
  tag : Tag
  /-- The context admits that tag, in the sense of
  `Whatwg.Html.Content.Admits`. -/
  admitted : Content.Admits set tag
  /-- The erased child. -/
  raw : RawNode

/-- Place a typed element in a child position. The element's `inner` index is
`childSet set t`, so a transparent combinator's content parameter is assigned
by this unification and its children are then checked against TyXML's payload
for `t` in `set`. -/
def Child.of {set : ContentSet} {t : Tag} (e : Element t (childSet set t))
    (h : Content.Admits set t := by decide) : Child set :=
  ⟨t, h, e.toRaw⟩

/-- Weakening: a child admitted under a narrower set is admitted under a
wider one. This is where the inclusion theorems of
`Whatwg.Html.Content.Lattice` become usable at a call site: a
`Child .phrasing` is placed in a `Child .flow5` position by
`Child.weaken Content.phrasing_subset_flow5`. Deliberately not a `Coe`:
`SubsetOf` is a proposition, not a class, and the inclusion used should stay
visible in the source (the same reasoning that ruled out `Fact`, HP-6). -/
def Child.weaken {a b : ContentSet} (h : Content.SubsetOf a.contains b.contains)
    (c : Child a) : Child b :=
  ⟨c.tag, h c.tag c.admitted, c.raw⟩

/-- A text run, admitted wherever the content set names `PCDATA` (ruling
HP-5). -/
def Child.text {set : ContentSet} (s : String)
    (h : Content.Admits set .pcdata := by decide) : Child set :=
  ⟨.pcdata, h, .text s⟩

/-- A named entity reference. TyXML's `entity` has the same result tag as
`txt`, so it is admitted exactly where `PCDATA` is. -/
def Child.entity {set : ContentSet} (name : String)
    (h : Content.Admits set .pcdata := by decide) : Child set :=
  ⟨.pcdata, h, .entity name⟩

/-- Every attribute supplied to a combinator is a member of that element's
attribute set. This is the proposition each combinator's `_ha` auto-parameter
discharges by `decide`. -/
abbrev AttrsAdmitted (set : AttrSet) (attrs : List (Attr × String)) : Prop :=
  attrs.all (fun p => set.contains p.1) = true

end Whatwg.Html
