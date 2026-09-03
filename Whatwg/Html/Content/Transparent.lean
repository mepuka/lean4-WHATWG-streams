import Whatwg.Html.Content.Lattice

/-!
# Whatwg.Html.Content.Transparent

Transparent coherence (node L3 of the H3 proof graph in
`docs/HTML-PACKAGE-PLAN.md`, ruling HP-4) and the child-set resolver the
typed tree of the next slice calls at every element node.

TyXML's scheme. A transparent element does not receive a context flag from
its parent; instead the content set that names it carries the set its
children were checked against, as the payload of the polymorphic variant.
`ContentSet.transparentPayload` is that payload table, generated in slice H2:
`flow5, a` yields `flow5_without_interactive`, `phrasing, a` yields
`phrasing_without_interactive`, `flow5, audio` yields `flow5_without_media`.
A violation therefore surfaces at the enclosing non-transparent parent rather
than at the transparent element itself.

Two notions of "transparent" live in the projection and they do not coincide.

- `Tag.isTransparent` below is the element-row notion: the eight constructors
  whose TyXML type takes the content parameter `'a` — `a`, `del`, `ins`,
  `object_`, `audio`, `video`, `canvas`, `map`. `Element.transparent` of the
  generated rows agrees with it (`elements_transparent_eq_isTransparent`).
- `Sets.transparent` is the content-set notion: the twelve tags of TyXML's
  `transparent` row type, which adds `Noscript` and the three variants
  `Audio_interactive`, `Object_interactive` and `Video_interactive` that name
  no element constructor of their own
  (`transparent_eq_isTransparent_or_four`).

Every payload in the table hangs off a `Sets.transparent` member, so the
coherence lemmas below are stated against `Sets.transparent`, not against
`Tag.isTransparent`. `Noscript` is the sharpest case: its element row is not
transparent and fixes its content at `flow5_without_noscript`, while the
payload table gives it `phrasing_without_noscript` in a phrasing context.
`resolveChildSet` prefers the payload for exactly this reason.

What is proved here, and what is not:

- a payload exists only for a member of the set that is a `Sets.transparent`
  tag, and conversely for every such member of every set other than the four
  `transparent*` sets and `metadata_without_title`;
- every payload set is inside `flow5`;
- the payload stays inside the context set itself only for `flow5`,
  `phrasing` and `ruby_content_fun`. For the other seventeen
  payload-carrying sets it does not, and the failure is recorded as a
  theorem, not repaired: a `del` inside a `flow5_without_form` context may
  contain a `form`, because TyXML's payload for `Del` in that row is the
  unrestricted `flow5`. This is a property of the sealed TyXML 4.6.0 port;
  `Whatwg.Html.Content.Divergence` owns its reading against the HTML
  Standard.
-/

namespace Whatwg.Html.Schema

/-- The element-row notion of transparency: the eight element constructors
whose TyXML type takes the content parameter `'a` (ruling HP-4). -/
def Tag.isTransparent : Tag → Bool
  | .a | .del | .ins | .object | .audio | .video | .canvas | .map => true
  | _ => false

end Whatwg.Html.Schema

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-! ## The two notions of transparency -/

/-- `Tag.isTransparent` reproduces the `transparent` field of every element
row, both `table` rows included. -/
theorem elements_transparent_eq_isTransparent :
    ∀ e ∈ elements, Element.transparent e = (Element.tag e).isTransparent := by
  intro e he
  have h := forall_elements_of_all
    (fun e => Element.transparent e == (Element.tag e).isTransparent) (by decide +kernel) e he
  exact eq_of_beq h

/-- Every element-transparent tag is a member of the `transparent` content
set. -/
theorem isTransparent_subset_transparent : SubsetOf Tag.isTransparent Sets.transparent :=
  subsetOf_of_all (by decide +kernel)

/-- The converse fails on exactly four tags: `Sets.transparent` is
`Tag.isTransparent` together with `Noscript`, `Audio_interactive`,
`Object_interactive` and `Video_interactive`. -/
theorem transparent_eq_isTransparent_or_four : ∀ t : Tag,
    Sets.transparent t
      = (t.isTransparent || t == .noscript || t == .audio_interactive
          || t == .object_interactive || t == .video_interactive) :=
  eq_of_all (by decide +kernel)

/-! ## Where payloads exist -/

/-- A payload is assigned only where the set names the tag. -/
theorem transparentPayload_isSome_contains : ∀ (s : ContentSet) (t : Tag),
    (s.transparentPayload t).isSome = true → s.contains t = true := by
  intro s t h
  have hb := forall_contentSet_tag_of_all
    (fun s t => !(ContentSet.transparentPayload s t).isSome || ContentSet.contains s t)
    (by decide +kernel) s t
  rw [h] at hb
  simpa using hb

/-- A payload is assigned only to a member of the `transparent` content
set. -/
theorem transparentPayload_isSome_transparent : ∀ (s : ContentSet) (t : Tag),
    (s.transparentPayload t).isSome = true → Sets.transparent t = true := by
  intro s t h
  have hb := forall_contentSet_tag_of_all
    (fun s t => !(ContentSet.transparentPayload s t).isSome || Sets.transparent t)
    (by decide +kernel) s t
  rw [h] at hb
  simpa using hb

/-- The five content sets that name a `transparent` tag and assign it no
payload: the four `transparent*` row types themselves, whose members are the
bare variants, and `metadata_without_title`, whose `Noscript` case is TyXML's
`` `Noscript of [ `Meta | `Link | `Style ] `` and carries no payload in the
generated table. -/
def payloadFree (s : ContentSet) : Bool :=
  s == .transparent || s == .transparent_without_interactive
    || s == .transparent_without_media || s == .transparent_without_noscript
    || s == .metadata_without_title

/-- Outside those five sets, every `transparent` tag a set names carries a
payload. -/
theorem contains_transparent_payload_isSome : ∀ (s : ContentSet) (t : Tag),
    payloadFree s = false → s.contains t = true → Sets.transparent t = true →
      (s.transparentPayload t).isSome = true := by
  intro s t hf hc ht
  have hb := forall_contentSet_tag_of_all
    (fun s t => payloadFree s || !ContentSet.contains s t || !Sets.transparent t
      || (ContentSet.transparentPayload s t).isSome)
    (by decide +kernel) s t
  rw [hf, hc, ht] at hb
  simpa using hb

/-- No void tag carries a payload in any context: none of the fifteen void
tags is a member of the `transparent` content set. -/
theorem transparentPayload_void : ∀ (s : ContentSet) (t : Tag),
    t.isVoid = true → s.transparentPayload t = none := by
  intro s t hv
  have h := forall_contentSet_tag_of_all
    (fun s t => !t.isVoid || (ContentSet.transparentPayload s t).isNone)
    (by decide +kernel) s t
  rw [hv] at h
  exact Option.isNone_iff_eq_none.mp (by simpa using h)

/-! ## Where payloads lead -/

/-- Every payload set is inside `flow5`: a transparent element never opens a
context wider than flow content. The fourteen sets that occur as payloads at
this pin are `flow5`, `flow5_without_interactive`,
`flow5_without_interactive_header_footer`, `flow5_without_media`,
`flow5_without_noscript`, `phrasing`, `phrasing_without_dfn`,
`phrasing_without_interactive`, `phrasing_without_label`,
`phrasing_without_media`, `phrasing_without_meter`,
`phrasing_without_noscript`, `phrasing_without_progress` and
`phrasing_without_time`. -/
theorem transparentPayload_subset_flow5 (s : ContentSet) (t : Tag) (p : ContentSet)
    (h : s.transparentPayload t = some p) : SubsetOf p.contains Sets.flow5 := by
  apply subsetOf_of_all
  have hb := forall_contentSet_tag_of_all
    (fun s t => Option.all
      (fun q => Tag.all.all (fun v => !ContentSet.contains q v || Sets.flow5 v))
      (ContentSet.transparentPayload s t))
    (by decide +kernel) s t
  rw [h] at hb
  exact hb

/-- In a `flow5` context the payload stays inside `flow5`. -/
theorem flow5_transparentPayload_subset_context (t : Tag) (p : ContentSet)
    (h : ContentSet.transparentPayload .flow5 t = some p) :
    SubsetOf p.contains (ContentSet.contains .flow5) := by
  apply subsetOf_of_all
  have hb := forall_tag_of_all
    (fun t => Option.all
      (fun q => Tag.all.all (fun v => !ContentSet.contains q v || ContentSet.contains .flow5 v))
      (ContentSet.transparentPayload .flow5 t))
    (by decide +kernel) t
  rw [h] at hb
  exact hb

/-- In a `phrasing` context the payload stays inside `phrasing`. -/
theorem phrasing_transparentPayload_subset_context (t : Tag) (p : ContentSet)
    (h : ContentSet.transparentPayload .phrasing t = some p) :
    SubsetOf p.contains (ContentSet.contains .phrasing) := by
  apply subsetOf_of_all
  have hb := forall_tag_of_all
    (fun t => Option.all
      (fun q => Tag.all.all (fun v => !ContentSet.contains q v || ContentSet.contains .phrasing v))
      (ContentSet.transparentPayload .phrasing t))
    (by decide +kernel) t
  rw [h] at hb
  exact hb

/-- In a `ruby_content_fun` context the payload stays inside
`ruby_content_fun`. -/
theorem ruby_transparentPayload_subset_context (t : Tag) (p : ContentSet)
    (h : ContentSet.transparentPayload .ruby_content_fun t = some p) :
    SubsetOf p.contains (ContentSet.contains .ruby_content_fun) := by
  apply subsetOf_of_all
  have hb := forall_tag_of_all
    (fun t => Option.all
      (fun q => Tag.all.all
        (fun v => !ContentSet.contains q v || ContentSet.contains .ruby_content_fun v))
      (ContentSet.transparentPayload .ruby_content_fun t))
    (by decide +kernel) t
  rw [h] at hb
  exact hb

/-- `flow5`, `phrasing` and `ruby_content_fun` are the only three
payload-carrying sets whose payloads stay inside the context. In the other
seventeen the payload is wider than the context, because TyXML fixes the
payload of a transparent variant against the unrestricted base category.
`Del` in a `flow5_without_form` context is the smallest witness: its payload
is `flow5`, which admits `Form`, and the context does not. -/
theorem transparentPayload_escapes_context :
    ContentSet.transparentPayload .flow5_without_form .del = some .flow5
      ∧ ContentSet.contains .flow5 .form = true
      ∧ ContentSet.contains .flow5_without_form .form = false := by
  decide

/-! ## Element rows without a content set -/

/-- `svg` is the only element row with no content set: its children are SVG
elements, which this library does not model yet. -/
theorem element_content_none_svg :
    ∀ e ∈ elements, Element.content e = none → Element.tag e = .svg := by
  intro e he hn
  have h := forall_elements_of_all
    (fun e => (Element.content e).isSome || (Element.tag e == Tag.svg)) (by decide +kernel) e he
  rw [hn] at h
  exact eq_of_beq (by simpa using h)

/-- Every transparent element row has a content set. -/
theorem transparent_element_content_isSome :
    ∀ e ∈ elements, Element.transparent e = true → (Element.content e).isSome = true := by
  intro e he ht
  have h := forall_elements_of_all
    (fun e => !Element.transparent e || (Element.content e).isSome) (by decide +kernel) e he
  rw [ht] at h
  simpa using h

/-- Every non-transparent element row other than `svg` has a content set, so
a non-transparent parent's admission obligation is always a named set. -/
theorem nontransparent_element_content_isSome :
    ∀ e ∈ elements, Element.transparent e = false → Element.tag e ≠ .svg →
      (Element.content e).isSome = true := by
  intro e he ht hs
  have h := forall_elements_of_all
    (fun e => Element.transparent e || (Element.tag e == Tag.svg) || (Element.content e).isSome)
    (by decide +kernel) e he
  rw [ht, beq_eq_false_iff_ne.mpr hs] at h
  simpa using h

/-! ## The child-set resolver -/

/-- The content set the children of a `parent` element must satisfy when that
element sits in the context set `ctx`.

The payload table wins where it has an entry: that is TyXML's transparency,
and it is context-sensitive, so an `a` in a `phrasing` context resolves to
`phrasing_without_interactive` while the same `a` in a `flow5` context
resolves to `flow5_without_interactive`. Where the table has no entry the
element's own content set is used, which covers every non-transparent parent
and also a `transparent` tag appearing in one of the five `payloadFree` sets
of this module. `none` is returned only when the parent has no element row at
all (`PCDATA`, `Img_interactive`, and the three `*_interactive` variants) or
when its row carries no content set (`svg`); `resolveChildSet_none` states
exactly that. -/
def resolveChildSet (parent : Tag) (ctx : ContentSet) : Option ContentSet :=
  match ctx.transparentPayload parent with
  | some payload => some payload
  | none => (Tag.element? parent).bind Element.content

/-- Where the payload table has an entry, the resolver returns it. -/
theorem resolveChildSet_payload (parent : Tag) (ctx : ContentSet) (p : ContentSet)
    (h : ctx.transparentPayload parent = some p) : resolveChildSet parent ctx = some p := by
  simp [resolveChildSet, h]

/-- Where it has none, the resolver returns the element row's own content
set. -/
theorem resolveChildSet_element (parent : Tag) (ctx : ContentSet)
    (h : ctx.transparentPayload parent = none) :
    resolveChildSet parent ctx = (Tag.element? parent).bind Element.content := by
  simp [resolveChildSet, h]

/-- The resolver returns nothing only where the element row supplies
nothing. -/
theorem resolveChildSet_none (parent : Tag) (ctx : ContentSet)
    (h : resolveChildSet parent ctx = none) :
    (Tag.element? parent).bind Element.content = none := by
  unfold resolveChildSet at h
  cases hp : ctx.transparentPayload parent with
  | some p => rw [hp] at h; exact absurd h (by simp)
  | none => rw [hp] at h; exact h

/-- A void parent resolves to the empty content set in every context. This is
the shape node T2 of the proof graph needs: a typed tree can put no child
under a void tag. -/
theorem resolveChildSet_void (parent : Tag) (ctx : ContentSet) (h : parent.isVoid = true) :
    resolveChildSet parent ctx = some .notag := by
  rw [resolveChildSet_element parent ctx (transparentPayload_void ctx parent h)]
  exact void_element_content_notag parent h

end Whatwg.Html.Content
