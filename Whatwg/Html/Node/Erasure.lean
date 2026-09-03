import Whatwg.Html.Node.Combinators

/-!
# Whatwg.Html.Node.Erasure

Erasure from the typed tree to the raw tree (TyXML's `toelt` / `tot` pair,
`html_sigs.mli`), and what can be said about it cheaply at slice H3.3.

`Element.toRaw` itself lives in `Whatwg.Html.Node.Typed`, because `Child.of`
calls it. This module owns the statements: that erasing a child returns the
raw node the child already held, that the raw tag string of an erased element
is the tag's markup name whenever the projection gives it one, that erasure
reads nothing but the two data fields — so the content-set index and the
admission proofs are exactly the part it forgets — and that no typed child
exists under a void tag in any context.

What is *not* claimed here. Injectivity of the serializer and escaping
soundness are the H4 theorems (ruling HP-8); a parse round trip is refused
until a parser exists. Nothing below is a statement about the HTML Standard:
the markup spellings are TyXML 4.6.0's, as sealed under
`vendor/tyxml-d2916535/`.
-/

namespace Whatwg.Html

open Whatwg.Html.Schema

/-! ## Erasure forgets only the indices and the proofs -/

/-- Erasing a child returns the raw node it already carries: `Child.of` put
`Element.toRaw` there and nothing else happens on the way out. -/
theorem Child.of_raw {set : ContentSet} {t : Tag} (e : Element t (childSet set t))
    (h : Content.Admits set t) : (Child.of e h).raw = e.toRaw := rfl

/-- A text child erases to a text node. -/
theorem Child.text_raw {set : ContentSet} (s : String)
    (h : Content.Admits set .pcdata) : (Child.text (set := set) s h).raw = .text s := rfl

/-- An entity child erases to an entity node. -/
theorem Child.entity_raw {set : ContentSet} (name : String)
    (h : Content.Admits set .pcdata) :
    (Child.entity (set := set) name h).raw = .entity name := rfl

/-- Erasure reads only the two data fields, so two elements that agree on
them erase equally however their content-set indices differ. This is the
cheap form of "erasure forgets only proofs": the index `inner` and the
`Child` admission proofs are not observable in the result. -/
theorem Element.toRaw_congr {t : Tag} {inner inner' : ContentSet}
    (e : Element t inner) (e' : Element t inner')
    (hattrs : e.attrs = e'.attrs) (hchildren : e.children = e'.children) :
    e.toRaw = e'.toRaw := by
  simp [Element.toRaw, hattrs, hchildren]

/-! ## The erased shape -/

/-- The erased element is an element node whose name is the tag's markup
text. -/
theorem Element.toRaw_tagName? {t : Tag} {inner : ContentSet} (e : Element t inner) :
    e.toRaw.tagName? = some t.markupText := rfl

/-- The erased element's children are the element's children, unchanged. -/
theorem Element.toRaw_childNodes {t : Tag} {inner : ContentSet} (e : Element t inner) :
    e.toRaw.childNodes = e.children := rfl

/-- Where the projection gives the tag a markup name, that name is what
erasure emits: `Tag.markupText`'s variant-name fallback is never observed at
such a tag. -/
theorem markupText_eq_markupName (t : Tag) (m : String) (h : t.markupName = some m) :
    t.markupText = m := by
  simp [Tag.markupText, h]

/-- A tag has a markup name exactly when it has an element row, so the
fallback in `Tag.markupText` is unreachable from every combinator of
`Whatwg.Html.Node.Combinators`: the five tags that take it (`PCDATA` and the
four `*_interactive` variants) have no constructor. -/
theorem markupName_isSome_eq_elementIndex?_isSome (t : Tag) :
    t.markupName.isSome = (Tag.elementIndex? t).isSome :=
  eq_of_beq <| forall_tag_of_all
    (fun t => (Tag.markupName t).isSome == (Tag.elementIndex? t).isSome) (by decide) t

/-! ## Void tags -/

/-- No typed child can be placed under a void tag, in any context: the child
set a void parent resolves to is `notag`, which admits nothing. This is the
typed-tree form of `Whatwg.Html.Content.resolveChildSet_void`, and it is why
the fifteen void combinators take no children argument at all. -/
theorem no_child_under_void {set : ContentSet} {t : Tag} (hv : t.isVoid = true)
    (c : Child (childSet set t)) : False := by
  have h : childSet set t = ContentSet.notag := by
    simp [childSet, Content.resolveChildSet_void t set hv]
  exact Content.not_admits_notag c.tag (h ▸ c.admitted)

/-- An element with no children erases to an element node with no children.
Every void combinator builds such a value, since none of them takes a
children argument. -/
theorem Element.toRaw_childNodes_nil {t : Tag} {inner : ContentSet} (e : Element t inner)
    (h : e.children = []) : e.toRaw.childNodes = [] := by
  rw [Element.toRaw_childNodes, h]

/-- The four void combinators the builder tests exercise erase with an empty
child list, by evaluation. -/
theorem void_combinators_children_nil :
    (E.br).children = [] ∧ (E.hr).children = [] ∧ (E.input).children = []
      ∧ (E.img "u" "a").children = [] := ⟨rfl, rfl, rfl, rfl⟩

end Whatwg.Html
