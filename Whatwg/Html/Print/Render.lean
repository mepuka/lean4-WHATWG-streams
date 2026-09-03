import Whatwg.Html.Print.Escape
import Whatwg.Html.Node.Erasure

/-!
# Whatwg.Html.Print.Render

The serializer of slice H4 of `docs/HTML-PACKAGE-PLAN.md`: the raw tree of
`Whatwg.Html.Node.Raw` written out as markup, ported from the string printer
of TyXML's `xml_print.ml` — `xh_print_attrs`, `xh_print_closedtag`,
`xh_print_tag` and `xh_print_taglist` in the functor `Make` — with the void
tag list read out of the schema rather than retyped.

Everything is computed at `List Char` and lifted once by `String.ofList`, so
`toList_render` transports every statement below to the `String` surface.

## The exact shapes emitted

| node | output |
| --- | --- |
| element with children | `<name attrs>children</name>` |
| element, no children, void name | `<name attrs />` |
| element, no children, other name | `<name attrs></name>` |
| attribute | one leading space, then `name="escaped value"` |
| text | the escaped run |
| entity `e` | `&e;`, not escaped |
| comment `c` | `<!--escaped c-->` |

Three divergences to record, none of them a claim about the HTML Standard:

1. `<br />` is XHTML-style. The HTML Standard writes a void element `<br>`,
   with no solidus. This port follows TyXML's `xh_print_closedtag`, which
   emits `"<" ^ tag`, the attributes, then `" />"`.
2. TyXML has two printers in one file and they disagree about that space:
   the `Format`-based `Make_fmt.pp_closedtag` emits `<br/>`. This module
   follows `Make`, the string printer named in the slice brief.
3. `Make` escapes a comment's text with `encode_unsafe_char`, the same
   escaper as for a text run; `Make_fmt.pp_elt` instead applies
   `escape_comment`, a regular-expression rewrite of `-->` and its relatives
   that is not ported here.

`renderDoc` prefixes `html_f.ml`'s `Info.doctype`, which is
`compose_doctype "html" []`, that is `<!DOCTYPE html>`, and the newline
`Make_typed.print` emits after it when there is no advertisement. The
`xmlns` attribute that `Make_typed.print` injects into the root element
before printing is *not* injected here: it is a property of the typed
document wrapper, which this pin does not model.

## What is proved, and what is refused

`renderChars` is **not** injective on `RawNode`, and this module proves it:
`renderChars_not_injective` exhibits `text "&"` and `entity "amp"`, which
print identically, and `renderCharsList_not_injective` exhibits a text run
split in two. Serializer injectivity therefore has to be stated over a
sublanguage. `wf` names that sublanguage — no entity node, no empty text
run, no text run directly followed by another, and element and attribute
names spelled from `nameChar`, which `nameOk_markupName` shows every markup
name in the schema is — and `decode_render` proves that `decodeNode?`
inverts the printer on it, whence `renderChars_injective_of_wf` and
`render_injective_of_wf`.

The decoder is a decoder for the printer's own output alphabet, not an HTML
parser: ruling HP-8's refusal of a parse round trip is untouched. It has no
tokenizer, no named-character-reference table, no error recovery and no
knowledge of the content model, and on input outside the printer's image its
behaviour is unspecified — no theorem here says anything about it.

What is left open, plainly: injectivity is proved for `wf` trees and for no
larger class, and the two counterexamples above show that no such larger
class contains an entity node or two adjacent text runs. Whether the
remaining `wf` conditions (nonempty text runs, `nameChar` names) are
necessary as well as sufficient is not settled here.
-/

namespace Whatwg.Html.Print

open Whatwg.Html (RawNode)
open Whatwg.Html.Schema (Tag)
open Whatwg.Html.Schema (forall_tag_of_all)

/-! ## The void tag names, read from the schema -/

/-- The markup names TyXML's `emptytags` lists, derived from the schema's
`Tag.isVoid` and `Tag.markupName` rather than retyped. -/
def isVoidName (s : String) : Bool :=
  Tag.all.any (fun t => t.isVoid && t.markupName == some s)

/-- The fifteen names of `html_f.ml`'s `emptytags`, and nothing else. -/
theorem isVoidName_eq :
    ∀ s ∈ ["area", "base", "br", "col", "command", "embed", "hr", "img",
           "input", "keygen", "link", "meta", "param", "source", "wbr"],
      isVoidName s = true := by decide

/-- `div` is not a void name. -/
theorem isVoidName_div : isVoidName "div" = false := by decide

/-! ## The printer -/

/-- One attribute, as `xh_print_attrs` writes it: a leading space, the name
unescaped, `=`, and the escaped value in double quotes. -/
def renderAttr (attr : String × String) : List Char :=
  ' ' :: (attr.1.toList ++ '=' :: '"' :: (escape attr.2.toList ++ ['"']))

/-- The attribute list, in order. -/
def renderAttrs (attrs : List (String × String)) : List Char :=
  attrs.flatMap renderAttr

/-- The closing tag `</name>`. -/
def renderClose (name : String) : List Char :=
  '<' :: '/' :: (name.toList ++ ['>'])

mutual

/-- The serializer at `List Char`. -/
def renderChars : RawNode → List Char
  | .element name attrs children =>
      if children.isEmpty && isVoidName name then
        '<' :: (name.toList ++ renderAttrs attrs ++ [' ', '/', '>'])
      else
        '<' :: (name.toList ++ renderAttrs attrs ++ '>'
          :: (renderCharsList children ++ renderClose name))
  | .text content => escape content.toList
  | .entity name => '&' :: (name.toList ++ [';'])
  | .comment content => '<' :: '!' :: '-' :: '-' :: (escape content.toList ++ ['-', '-', '>'])

/-- The serializer of a forest, in order and with no separator. -/
def renderCharsList : List RawNode → List Char
  | [] => []
  | node :: rest => renderChars node ++ renderCharsList rest

end

/-- The public serializer. `String.ofList` is the only `String` construction
here. -/
def render (node : RawNode) : String := String.ofList (renderChars node)

/-- The public serializer of a forest. -/
def renderList (nodes : List RawNode) : String := String.ofList (renderCharsList nodes)

/-- `html_f.ml`'s `Info.doctype`: `Xml_print.compose_doctype "html" []`. -/
def doctype : String := "<!DOCTYPE html>"

/-- A whole document, as `Make_typed.print` composes it with no
advertisement: the doctype, a newline, then the tree. -/
def renderDoc (node : RawNode) : String :=
  doctype ++ "\n" ++ render node

/-! ## The `String` boundary -/

/-- The public serializer is the `List Char` serializer. -/
theorem toList_render (node : RawNode) : (render node).toList = renderChars node := by
  simp [render]

/-- The same, for a forest. -/
theorem toList_renderList (nodes : List RawNode) :
    (renderList nodes).toList = renderCharsList nodes := by
  simp [renderList]

/-- The document rendering is the doctype line followed by the tree. -/
theorem toList_renderDoc (node : RawNode) :
    (renderDoc node).toList = doctype.toList ++ '\n' :: renderChars node := by
  simp [renderDoc, toList_render]

/-! ## The text-run statement, lifted from the escaper -/

/-- No delimiter survives into the rendering of a text node: this is
`escape_no_delim` at the tree. It is the fact the decoder below turns into a
parse: a text run ends exactly at the next `<`. -/
theorem renderChars_text_no_delim (content : String) (d : Char) (hd : isDelim d = true) :
    d ∉ renderChars (.text content) := by
  simpa [renderChars] using escape_no_delim content.toList d hd

/-- No control character survives into the rendering of a text node. -/
theorem renderChars_text_no_control (content : String) (d : Char)
    (hd : d ∈ renderChars (.text content)) : isControl d = false := by
  simp only [renderChars] at hd
  exact escape_no_control content.toList d hd

/-- An attribute value is rendered inside double quotes and contains none,
so the quote that closes it is the next one. -/
theorem renderAttr_value_no_quote (attr : String × String) :
    '"' ∉ escape attr.2.toList := escape_no_delim attr.2.toList _ (by decide)

/-! ## The printer is not injective on `RawNode`

Two of the raw tree's constructors print into each other's language, and a
text run has no unique split, so the serializer cannot be injective on the
whole of `RawNode`. Both facts are exhibited rather than argued. -/

/-- `text "&"` and `entity "amp"` print identically: the escaper writes
`&amp;` for the first and TyXML writes entity references unescaped. -/
theorem renderChars_not_injective :
    ∃ a b : RawNode, a ≠ b ∧ renderChars a = renderChars b :=
  ⟨.text "&", .entity "amp", fun h => RawNode.noConfusion h, by decide⟩

/-- A text run split in two prints as the single run: adjacent text nodes are
not recoverable. -/
theorem renderCharsList_not_injective :
    ∃ a b : List RawNode, a ≠ b ∧ renderCharsList a = renderCharsList b :=
  ⟨[.text "a", .text "b"], [.text "ab"], by simp, by decide⟩

/-! ## The sublanguage the printer's output determines

`wf` names the trees the decoder below inverts: no entity node (it collides
with an escaped `&`), no empty text run (it prints as nothing), no text run
directly followed by another (their concatenation has no unique split), and
element and attribute names drawn from the alphabet every markup name in the
schema uses. -/

/-- The characters a markup name may use here: the alphanumerics, `-`, `:`
and `_`. Every name in `Whatwg.Html.Schema` is spelled from these. -/
def nameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == ':' || c == '_'

/-- A nonempty name spelled from `nameChar`. -/
def nameOk (s : String) : Bool := !s.toList.isEmpty && s.toList.all nameChar

/-- Every markup name the schema gives a tag is a `nameOk` name, so no
document built by the combinators of `Whatwg.Html.Node.Combinators` is
excluded by the name condition. -/
theorem nameOk_markupName : ∀ t : Tag, (t.markupName.elim true nameOk) = true :=
  forall_tag_of_all (fun t => t.markupName.elim true nameOk) (by decide)

/-- The same, in the form the proofs use. -/
theorem nameOk_of_markupName {t : Tag} {m : String} (h : t.markupName = some m) :
    nameOk m = true := by
  have ht := nameOk_markupName t
  rw [h] at ht
  exact ht

/-- Distinct membership of `nameChar` separates two characters. -/
theorem nameChar_ne {c d : Char} (h : nameChar c = true) (hd : nameChar d = false) : c ≠ d := by
  intro he
  rw [he, hd] at h
  exact Bool.noConfusion h

/-- A node whose rendering begins with `<`. -/
def startsMarkup : RawNode → Bool
  | .element _ _ _ => true
  | .comment _ => true
  | .text _ => false
  | .entity _ => false

/-- A text node may not be followed by a node whose rendering does not begin
with `<`, since the two runs would not be separable. -/
def textFollowOk : RawNode → List RawNode → Bool
  | .text _, node :: _ => startsMarkup node
  | .text _, [] => true
  | _, _ => true

mutual

/-- The trees the decoder below inverts. -/
def wf : RawNode → Bool
  | .element name attrs children =>
      nameOk name && attrs.all (fun attr => nameOk attr.1) && wfList children
  | .text content => !content.toList.isEmpty
  | .entity _ => false
  | .comment _ => true

/-- The forests the decoder below inverts. -/
def wfList : List RawNode → Bool
  | [] => true
  | node :: rest => wf node && wfList rest && textFollowOk node rest

end

/-! ## Scanning -/

/-- The longest prefix whose characters satisfy `p`, and the rest. -/
def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
      if p c then
        let tail := spanChars p rest
        (c :: tail.1, tail.2)
      else ([], c :: rest)

/-- A scan stops exactly where the next character fails the predicate. -/
theorem spanChars_append {p : Char → Bool} {l rest : List Char}
    (hl : ∀ c ∈ l, p c = true) (hr : ∀ c t, rest = c :: t → p c = false) :
    spanChars p (l ++ rest) = (l, rest) := by
  induction l with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c t => simp [spanChars, hr c t rfl]
  | cons c t ih =>
    have hc : p c = true := hl c (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx]))
    simp [spanChars, hc, ih']

/-! ## The decoder for the printer's own output

`decodeNode?` accepts the sublanguage `renderChars` emits and nothing else.
It is not an HTML parser (ruling HP-8): it has no tokenizer, no
named-character-reference table, no error recovery, and no knowledge of the
content model. Its only purpose is to invert the printer on `wf` trees, and
the theorem below is the whole of its specification.

The `Nat` argument is a recursion budget, so that the scans — which return
suffixes rather than structural subterms — need no well-founded recursion.
`weight` is a budget that always suffices. -/

mutual

/-- The decoding budget of a node. -/
def weight : RawNode → Nat
  | .element _ attrs children => 1 + attrs.length + weightList children
  | .text _ => 1
  | .entity _ => 1
  | .comment _ => 1

/-- The decoding budget of a forest. -/
def weightList : List RawNode → Nat
  | [] => 1
  | node :: rest => 1 + weight node + weightList rest

end

/-- The characters that end a markup name: a space, a solidus, or `>`. -/
def isNameChar (c : Char) : Bool := c != ' ' && c != '/' && c != '>'

/-- Strip a literal prefix, or fail. Every literal the decoder expects is
consumed through this function, so that both its success and its failure
reduce by `simp`. -/
def afterPrefix : List Char → List Char → Option (List Char)
  | [], l => some l
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p = c then afterPrefix ps cs else none

/-- A literal prefix is stripped from the list it was prepended to. -/
theorem afterPrefix_append (p l : List Char) : afterPrefix p (p ++ l) = some l := by
  induction p with
  | nil => rfl
  | cons c cs ih => simp [afterPrefix, ih]

/-- The attribute list of a start tag: repeated ` name="value"` until the
tag closes. The ` />` of a void tag is not an attribute. -/
def decodeAttrs : Nat → List Char → Option (List (String × String) × List Char)
  | 0, l => some ([], l)
  | fuel + 1, l =>
      match afterPrefix [' '] l with
      | none => some ([], l)
      | some tail =>
          match afterPrefix ['/'] tail with
          | some _ => some ([], l)
          | none =>
              let scanned := spanChars (fun c => c != '=') tail
              match afterPrefix ['=', '"'] scanned.2 with
              | none => none
              | some tail₁ =>
                  let value := spanChars (fun c => c != '"') tail₁
                  match afterPrefix ['"'] value.2 with
                  | none => none
                  | some tail₂ =>
                      match decodeAttrs fuel tail₂ with
                      | none => none
                      | some (attrs, tail₃) =>
                          some ((String.ofList scanned.1,
                            String.ofList (unescape value.1)) :: attrs, tail₃)

mutual

/-- One node of the printer's output, and what follows it. -/
def decodeNode? : Nat → List Char → Option (RawNode × List Char)
  | 0, _ => none
  | fuel + 1, l =>
      match afterPrefix ['<', '!', '-', '-'] l with
      | some tail =>
          let scanned := spanChars (fun c => c != '>') tail
          match afterPrefix ['>'] scanned.2 with
          | none => none
          | some tail₁ =>
              some (.comment (String.ofList (unescape scanned.1.dropLast.dropLast)), tail₁)
      | none =>
          match afterPrefix ['<'] l with
          | some tail =>
              let name := spanChars isNameChar tail
              match decodeAttrs fuel name.2 with
              | none => none
              | some (attrs, tail₁) =>
                  match afterPrefix [' ', '/', '>'] tail₁ with
                  | some tail₂ => some (.element (String.ofList name.1) attrs [], tail₂)
                  | none =>
                      match afterPrefix ['>'] tail₁ with
                      | none => none
                      | some tail₂ =>
                          match decodeNodes? fuel tail₂ with
                          | none => none
                          | some (children, tail₃) =>
                              match afterPrefix ['<', '/'] tail₃ with
                              | none => none
                              | some tail₄ =>
                                  let closing := spanChars (fun c => c != '>') tail₄
                                  match afterPrefix ['>'] closing.2 with
                                  | none => none
                                  | some tail₅ =>
                                      if closing.1 = name.1 then
                                        some (.element (String.ofList name.1) attrs children,
                                          tail₅)
                                      else none
          | none =>
              let scanned := spanChars (fun c => c != '<') l
              if scanned.1.isEmpty then none
              else some (.text (String.ofList (unescape scanned.1)), scanned.2)

/-- The children of an element: nodes until the closing tag or the end. -/
def decodeNodes? : Nat → List Char → Option (List RawNode × List Char)
  | 0, _ => none
  | fuel + 1, l =>
      match afterPrefix ['<', '/'] l with
      | some tail => some ([], '<' :: '/' :: tail)
      | none =>
          if l.isEmpty then some ([], l)
          else
            match decodeNode? fuel l with
            | none => none
            | some (node, tail) =>
                match decodeNodes? fuel tail with
                | none => none
                | some (nodes, tail₁) => some (node :: nodes, tail₁)

end

/-- The decoder at the top level, with a budget read from the length of the
input. That this budget always suffices is *not* proved here: every theorem
below is stated for `decodeNode?` with an explicit budget, and
`decodeNode?_render` supplies `weight node`. Evaluate with that budget rather
than this one — the length budget makes a kernel reduction needlessly
deep. -/
def decode? (l : List Char) : Option (RawNode × List Char) := decodeNode? l.length l

/-! ## The lemmas the round trip runs on -/

/-- No character escapes to nothing. -/
theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  unfold escapeChar
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp
  split
  · simp [numericRef]
  · simp

/-- No character of an escaped run is a delimiter. -/
theorem escape_mem_ne {l : List Char} {x d : Char} (hd : isDelim d = true)
    (hx : x ∈ escape l) : x ≠ d := fun he => escape_no_delim l d hd (he ▸ hx)

/-- A nonempty run escapes to a nonempty run. -/
theorem escape_ne_nil {l : List Char} (h : l ≠ []) : escape l ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons c cs =>
    simp only [escape, List.flatMap_cons, ne_eq, List.append_eq_nil_iff, not_and]
    exact fun hc => absurd hc (escapeChar_ne_nil c)

/-- The empty prefix consumes nothing. -/
theorem afterPrefix_nil (l : List Char) : afterPrefix [] l = some l := rfl

/-- A matching first character is consumed. -/
theorem afterPrefix_cons_self (c : Char) (ps l : List Char) :
    afterPrefix (c :: ps) (c :: l) = afterPrefix ps l := by simp [afterPrefix]

/-- A literal prefix fails as soon as its first character does. -/
theorem afterPrefix_head_ne {c : Char} {ps l r : List Char} (hl : l ≠ [])
    (h : ∀ x ∈ l, x ≠ c) : afterPrefix (c :: ps) (l ++ r) = none := by
  cases l with
  | nil => exact absurd rfl hl
  | cons d t =>
    have hcd : ¬ c = d := fun hc => (h d (by simp)) hc.symm
    simp [afterPrefix, hcd]

/-- A `nameOk` name is a nonempty run of `nameChar`s. -/
theorem nameOk_facts {s : String} (h : nameOk s = true) :
    s.toList ≠ [] ∧ ∀ x ∈ s.toList, nameChar x = true := by
  simp only [nameOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at h
  exact h

/-- A markup name is scanned in full: none of its characters ends a name. -/
theorem nameChar_isNameChar {c : Char} (h : nameChar c = true) : isNameChar c = true := by
  simp only [isNameChar, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> exact nameChar_ne h (by decide)

/-- The rendering of an attribute list either is empty or begins with the
space that separates the first attribute from the tag name. -/
theorem renderAttrs_head_not_name (attrs : List (String × String)) {r : List Char}
    (hr : ∀ c t, r = c :: t → isNameChar c = false) :
    ∀ c t, renderAttrs attrs ++ r = c :: t → isNameChar c = false := by
  cases attrs with
  | nil => simpa [renderAttrs] using hr
  | cons a as =>
    intro c t hct
    simp only [renderAttrs, List.flatMap_cons, renderAttr, List.cons_append] at hct
    have hc : c = ' ' := by injection hct with h _; exact h.symm
    subst hc
    decide

/-- A node whose rendering begins with `<`. -/
theorem renderChars_markup_head {node : RawNode} (h : startsMarkup node = true) :
    ∃ t, renderChars node = '<' :: t := by
  cases node with
  | element name attrs children =>
    by_cases hv : (children.isEmpty && isVoidName name) = true
    · exact ⟨name.toList ++ renderAttrs attrs ++ [' ', '/', '>'], by simp [renderChars, hv]⟩
    · exact ⟨name.toList ++ renderAttrs attrs ++ '>' :: (renderCharsList children
        ++ renderClose name), by simp [renderChars, hv]⟩
  | comment content => exact ⟨_, rfl⟩
  | text content => simp [startsMarkup] at h
  | entity name => simp [startsMarkup] at h

/-- Every node costs at least one unit of decoding budget. -/
theorem one_le_weight (node : RawNode) : 1 ≤ weight node := by
  cases node <;> simp only [weight] <;> omega

/-- Every forest costs at least one unit of decoding budget. -/
theorem one_le_weightList (nodes : List RawNode) : 1 ≤ weightList nodes := by
  cases nodes <;> simp only [weightList] <;> omega

/-! ## The attribute list decodes -/

/-- The attribute decoder inverts `xh_print_attrs` on names spelled from
`nameChar`, whenever what follows the list is the `>` or the ` />` that ends
a start tag. -/
theorem decodeAttrs_render : ∀ (attrs : List (String × String)) (fuel : Nat) (rest : List Char),
    attrs.all (fun attr => nameOk attr.1) = true → attrs.length ≤ fuel →
    ((∃ t, rest = '>' :: t) ∨ (∃ t, rest = ' ' :: '/' :: '>' :: t)) →
    decodeAttrs fuel (renderAttrs attrs ++ rest) = some (attrs, rest) := by
  intro attrs
  induction attrs with
  | nil =>
    intro fuel rest _ _ hrest
    cases fuel with
    | zero => simp [decodeAttrs, renderAttrs]
    | succ f =>
      rcases hrest with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · simp [decodeAttrs, renderAttrs, afterPrefix]
      · simp [decodeAttrs, renderAttrs, afterPrefix]
  | cons a as ih =>
    intro fuel rest hall hlen hrest
    cases fuel with
    | zero => simp at hlen
    | succ f =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hname, hnil⟩ := nameOk_facts hall.1
      have hlen' : as.length ≤ f := by simpa using hlen
      have ihs := ih f rest hall.2 hlen' hrest
      have hinput : renderAttrs (a :: as) ++ rest
          = ' ' :: (a.1.toList ++ ('=' :: '"'
              :: (escape a.2.toList ++ ('"' :: (renderAttrs as ++ rest))))) := by
        simp [renderAttrs, renderAttr]
      have hspan₁ : spanChars (fun c => c != '=')
            (a.1.toList ++ ('=' :: '"' :: (escape a.2.toList ++ ('"' :: (renderAttrs as ++ rest)))))
          = (a.1.toList, '=' :: '"' :: (escape a.2.toList ++ ('"' :: (renderAttrs as ++ rest)))) :=
        spanChars_append (fun x hx => by simpa using nameChar_ne (hnil x hx) (by decide))
          (fun c t hct => by injection hct with h _; subst h; decide)
      have hspan₂ : spanChars (fun c => c != '"')
            (escape a.2.toList ++ ('"' :: (renderAttrs as ++ rest)))
          = (escape a.2.toList, '"' :: (renderAttrs as ++ rest)) :=
        spanChars_append
          (fun x hx => by simpa using escape_mem_ne (d := '"') (by decide) hx)
          (fun c t hct => by injection hct with h _; subst h; decide)
      rw [hinput, decodeAttrs, afterPrefix_cons_self, afterPrefix_nil]
      dsimp only
      rw [afterPrefix_head_ne (c := '/') (ps := []) hname
        (fun x hx => nameChar_ne (hnil x hx) (by decide))]
      dsimp only
      rw [hspan₁]
      dsimp only
      rw [afterPrefix_cons_self, afterPrefix_cons_self, afterPrefix_nil]
      dsimp only
      rw [hspan₂]
      dsimp only
      rw [afterPrefix_cons_self, afterPrefix_nil]
      dsimp only
      rw [ihs]
      dsimp only
      simp [unescape_escape]

/-- A literal prefix fails on a different first character. -/
theorem afterPrefix_cons_ne {c d : Char} (h : ¬ c = d) (ps l : List Char) :
    afterPrefix (c :: ps) (d :: l) = none := by simp [afterPrefix, h]

/-- A nonempty literal prefix fails on the empty list. -/
theorem afterPrefix_nil_right (c : Char) (ps : List Char) : afterPrefix (c :: ps) [] = none := rfl

/-- A well-formed node renders to something. -/
theorem renderChars_ne_nil {node : RawNode} (h : wf node = true) : renderChars node ≠ [] := by
  cases node with
  | element name attrs children =>
    by_cases hv : (children.isEmpty && isVoidName name) = true <;> simp [renderChars, hv]
  | text content =>
    have : content.toList ≠ [] := by simpa [wf] using h
    simpa [renderChars] using escape_ne_nil this
  | entity name => simp [wf] at h
  | comment content => simp [renderChars]

/-- No well-formed node's rendering begins with a closing tag, so the child
decoder stops exactly at the closing tag of its parent. -/
theorem afterPrefix_close_ne {node : RawNode} (h : wf node = true) (r : List Char) :
    afterPrefix ['<', '/'] (renderChars node ++ r) = none := by
  cases node with
  | element name attrs children =>
    simp only [wf, Bool.and_eq_true] at h
    obtain ⟨hnnil, hnall⟩ := nameOk_facts h.1.1
    by_cases hv : (children.isEmpty && isVoidName name) = true
    · have : renderChars (RawNode.element name attrs children) ++ r
          = '<' :: (name.toList ++ (renderAttrs attrs ++ ([' ', '/', '>'] ++ r))) := by
        simp [renderChars, hv]
      rw [this, afterPrefix_cons_self]
      exact afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))
    · have : renderChars (RawNode.element name attrs children) ++ r
          = '<' :: (name.toList ++ (renderAttrs attrs
              ++ ('>' :: (renderCharsList children ++ renderClose name ++ r)))) := by
        simp [renderChars, hv]
      rw [this, afterPrefix_cons_self]
      exact afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))
  | text content =>
    have hne : content.toList ≠ [] := by simpa [wf] using h
    have : renderChars (RawNode.text content) ++ r = escape content.toList ++ r := by
      simp [renderChars]
    rw [this]
    exact afterPrefix_head_ne (escape_ne_nil hne)
      (fun x hx => escape_mem_ne (d := '<') (by decide) hx)
  | entity name => simp [wf] at h
  | comment content =>
    have : renderChars (RawNode.comment content) ++ r
        = '<' :: ('!' :: ('-' :: '-' :: (escape content.toList ++ ['-', '-', '>'] ++ r))) := by
      simp [renderChars]
    rw [this, afterPrefix_cons_self, afterPrefix_cons_ne (by decide)]

/-! ## The round trip

The decoder inverts the printer on every `wf` tree. Injectivity of the
printer over that sublanguage follows, and nothing stronger is claimed:
`renderChars_not_injective` above shows that no statement over the whole of
`RawNode` could hold. -/

/-- What the printer emits, the decoder reads back — node and forest at
once, by induction on the decoding budget. The side condition on a text
node's continuation is what makes the run's end unambiguous; `wf` supplies it
at every call site. -/
theorem decode_render : ∀ fuel : Nat,
    (∀ (node : RawNode) (rest : List Char), wf node = true → weight node ≤ fuel →
        (∀ content, node = .text content → (rest = [] ∨ ∃ t, rest = '<' :: t)) →
        decodeNode? fuel (renderChars node ++ rest) = some (node, rest))
      ∧ (∀ (nodes : List RawNode) (rest : List Char), wfList nodes = true →
        weightList nodes ≤ fuel → (rest = [] ∨ ∃ t, rest = '<' :: '/' :: t) →
        decodeNodes? fuel (renderCharsList nodes ++ rest) = some (nodes, rest)) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro node _ _ hweight _
      have := one_le_weight node
      omega
    · intro nodes _ _ hweight _
      have := one_le_weightList nodes
      omega
  | succ f ih =>
    refine ⟨?_, ?_⟩
    · intro node rest hwf hweight hrest
      cases node with
      | entity name => simp [wf] at hwf
      | text content =>
        have hne : content.toList ≠ [] := by simpa [wf] using hwf
        have hesc : escape content.toList ≠ [] := escape_ne_nil hne
        have hrest' := hrest content rfl
        have hspan : spanChars (fun c => c != '<') (escape content.toList ++ rest)
            = (escape content.toList, rest) :=
          spanChars_append (fun x hx => by simpa using escape_mem_ne (d := '<') (by decide) hx)
            (fun c t hct => by
              rcases hrest' with rfl | ⟨t', rfl⟩
              · exact absurd hct (by simp)
              · injection hct with h _; subst h; decide)
        have hinput : renderChars (RawNode.text content) ++ rest
            = escape content.toList ++ rest := by simp [renderChars]
        rw [hinput, decodeNode?,
          afterPrefix_head_ne hesc (fun x hx => escape_mem_ne (d := '<') (by decide) hx)]
        dsimp only
        rw [afterPrefix_head_ne hesc (fun x hx => escape_mem_ne (d := '<') (by decide) hx)]
        dsimp only
        rw [hspan]
        dsimp only
        rw [if_neg (by simpa using hesc)]
        simp [unescape_escape]
      | comment content =>
        have hspan : spanChars (fun c => c != '>')
              ((escape content.toList ++ ['-', '-']) ++ ('>' :: rest))
            = (escape content.toList ++ ['-', '-'], '>' :: rest) :=
          spanChars_append
            (fun x hx => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with hx | (rfl | rfl)
              · simpa using escape_mem_ne (d := '>') (by decide) hx
              · decide
              · decide)
            (fun c t hct => by injection hct with h _; subst h; decide)
        have hdrop : (escape content.toList ++ ['-', '-']).dropLast.dropLast
            = escape content.toList := by
          rw [show escape content.toList ++ ['-', '-']
              = (escape content.toList ++ ['-']) ++ ['-'] from by simp]
          rw [List.dropLast_concat, List.dropLast_concat]
        have hinput : renderChars (RawNode.comment content) ++ rest
            = ['<', '!', '-', '-'] ++ ((escape content.toList ++ ['-', '-']) ++ ('>' :: rest)) := by
          simp [renderChars]
        rw [hinput, decodeNode?, afterPrefix_append]
        dsimp only
        rw [hspan]
        dsimp only
        rw [afterPrefix_cons_self, afterPrefix_nil]
        dsimp only
        rw [hdrop, unescape_escape]
        simp
      | element name attrs children =>
        simp only [wf, Bool.and_eq_true] at hwf
        obtain ⟨⟨hname, hattrs⟩, hchildren⟩ := hwf
        obtain ⟨hnnil, hnall⟩ := nameOk_facts hname
        simp only [weight] at hweight
        have hlenattrs : attrs.length ≤ f := by
          have := one_le_weightList children
          omega
        have hwchildren : weightList children ≤ f := by omega
        by_cases hv : (children.isEmpty && isVoidName name) = true
        · have hnil : children = [] := by
            simp only [Bool.and_eq_true, List.isEmpty_iff] at hv
            exact hv.1
          have hinput : renderChars (RawNode.element name attrs children) ++ rest
              = '<' :: (name.toList ++ (renderAttrs attrs ++ ([' ', '/', '>'] ++ rest))) := by
            simp [renderChars, hv]
          have hspan : spanChars isNameChar
                (name.toList ++ (renderAttrs attrs ++ ([' ', '/', '>'] ++ rest)))
              = (name.toList, renderAttrs attrs ++ ([' ', '/', '>'] ++ rest)) :=
            spanChars_append (fun x hx => nameChar_isNameChar (hnall x hx))
              (renderAttrs_head_not_name attrs
                (fun c t hct => by injection hct with h _; subst h; decide))
          rw [hinput, decodeNode?, afterPrefix_cons_self,
            afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))]
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [hspan]
          dsimp only
          rw [decodeAttrs_render attrs f ([' ', '/', '>'] ++ rest) hattrs hlenattrs
            (Or.inr ⟨rest, rfl⟩)]
          dsimp only
          rw [afterPrefix_append]
          dsimp only
          simp [hnil]
        · have hinput : renderChars (RawNode.element name attrs children) ++ rest
              = '<' :: (name.toList ++ (renderAttrs attrs
                  ++ ('>' :: (renderCharsList children
                    ++ ('<' :: '/' :: (name.toList ++ ('>' :: rest))))))) := by
            simp [renderChars, hv, renderClose]
          have hspan : spanChars isNameChar
                (name.toList ++ (renderAttrs attrs
                  ++ ('>' :: (renderCharsList children
                    ++ ('<' :: '/' :: (name.toList ++ ('>' :: rest)))))))
              = (name.toList, renderAttrs attrs
                  ++ ('>' :: (renderCharsList children
                    ++ ('<' :: '/' :: (name.toList ++ ('>' :: rest)))))) :=
            spanChars_append (fun x hx => nameChar_isNameChar (hnall x hx))
              (renderAttrs_head_not_name attrs
                (fun c t hct => by injection hct with h _; subst h; decide))
          have hspan' : spanChars (fun c => c != '>') (name.toList ++ ('>' :: rest))
              = (name.toList, '>' :: rest) :=
            spanChars_append
              (fun x hx => by simpa using nameChar_ne (hnall x hx) (by decide))
              (fun c t hct => by injection hct with h _; subst h; decide)
          have hkids := ih.2 children ('<' :: '/' :: (name.toList ++ ('>' :: rest)))
            hchildren hwchildren (Or.inr ⟨name.toList ++ ('>' :: rest), rfl⟩)
          rw [hinput, decodeNode?, afterPrefix_cons_self,
            afterPrefix_head_ne hnnil (fun x hx => nameChar_ne (hnall x hx) (by decide))]
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [hspan]
          dsimp only
          rw [decodeAttrs_render attrs f
            ('>' :: (renderCharsList children
              ++ ('<' :: '/' :: (name.toList ++ ('>' :: rest))))) hattrs hlenattrs
            (Or.inl ⟨_, rfl⟩)]
          dsimp only
          rw [afterPrefix_cons_ne (by decide)]
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [hkids]
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [hspan']
          dsimp only
          rw [afterPrefix_cons_self, afterPrefix_nil]
          dsimp only
          rw [if_pos rfl]
          simp
    · intro nodes rest hwf hweight hrest
      cases nodes with
      | nil =>
        rcases hrest with rfl | ⟨t, rfl⟩
        · rw [show renderCharsList [] ++ ([] : List Char) = [] from by simp [renderCharsList],
            decodeNodes?]
          rfl
        · rw [show renderCharsList [] ++ ('<' :: '/' :: t) = ['<', '/'] ++ t from by
              simp [renderCharsList],
            decodeNodes?, afterPrefix_append]
      | cons node tail =>
        simp only [wfList, Bool.and_eq_true] at hwf
        obtain ⟨⟨hnode, htail⟩, hfollow⟩ := hwf
        simp only [weightList] at hweight
        have hwn : weight node ≤ f := by
          have := one_le_weightList tail
          omega
        have hwt : weightList tail ≤ f := by
          have := one_le_weight node
          omega
        have htext : ∀ content, node = .text content →
            (renderCharsList tail ++ rest = []
              ∨ ∃ t, renderCharsList tail ++ rest = '<' :: t) := by
          intro content hcontent
          cases tail with
          | nil =>
            rcases hrest with rfl | ⟨t, rfl⟩
            · exact Or.inl (by simp [renderCharsList])
            · exact Or.inr ⟨'/' :: t, by simp [renderCharsList]⟩
          | cons head' tail' =>
            subst hcontent
            simp only [textFollowOk] at hfollow
            obtain ⟨u, hu⟩ := renderChars_markup_head hfollow
            exact Or.inr ⟨u ++ (renderCharsList tail' ++ rest), by
              simp [renderCharsList, hu]⟩
        have hnode' := ih.1 node (renderCharsList tail ++ rest) hnode hwn htext
        have htail' := ih.2 tail rest htail hwt hrest
        have hinput : renderCharsList (node :: tail) ++ rest
            = renderChars node ++ (renderCharsList tail ++ rest) := by
          simp [renderCharsList]
        rw [hinput, decodeNodes?, afterPrefix_close_ne hnode]
        dsimp only
        rw [if_neg (by
          simp only [List.isEmpty_iff]
          exact List.append_ne_nil_of_left_ne_nil (renderChars_ne_nil hnode) _)]
        rw [hnode']
        dsimp only
        rw [htail']

/-- The round trip at a node, in the form a caller uses. -/
theorem decodeNode?_renderChars {node : RawNode} (hwf : wf node = true) (fuel : Nat)
    (hfuel : weight node ≤ fuel) (rest : List Char)
    (hrest : ∀ content, node = .text content → (rest = [] ∨ ∃ t, rest = '<' :: t)) :
    decodeNode? fuel (renderChars node ++ rest) = some (node, rest) :=
  (decode_render fuel).1 node rest hwf hfuel hrest

/-- A whole well-formed tree decodes from its own rendering. -/
theorem decodeNode?_render {node : RawNode} (hwf : wf node = true) :
    decodeNode? (weight node) (renderChars node) = some (node, []) := by
  have h := (decode_render (weight node)).1 node [] hwf (Nat.le_refl _) (fun _ _ => Or.inl rfl)
  simpa using h

/-- The serializer is injective on the sublanguage `wf` names. This is the
strongest injectivity statement available: `renderChars_not_injective` shows
the unrestricted one is false. -/
theorem renderChars_injective_of_wf {a b : RawNode} (ha : wf a = true) (hb : wf b = true)
    (h : renderChars a = renderChars b) : a = b := by
  have hfa := (decode_render (weight a + weight b)).1 a [] ha (by omega) (fun _ _ => Or.inl rfl)
  have hfb := (decode_render (weight a + weight b)).1 b [] hb (by omega) (fun _ _ => Or.inl rfl)
  rw [h] at hfa
  have heq : (some (a, []) : Option (RawNode × List Char)) = some (b, []) := hfa.symm.trans hfb
  simpa using heq

/-- The same at the `String` surface. -/
theorem render_injective_of_wf {a b : RawNode} (ha : wf a = true) (hb : wf b = true)
    (h : render a = render b) : a = b :=
  renderChars_injective_of_wf ha hb (by rw [← toList_render, ← toList_render, h])

end Whatwg.Html.Print

namespace Whatwg.Html

/-- Serialize a typed element, through erasure. -/
def Element.render {t : Schema.Tag} {inner : Schema.ContentSet} (e : Element t inner) : String :=
  Print.render e.toRaw

/-- Serialize a typed element as a whole document, with TyXML's doctype
line. -/
def Element.renderDoc {t : Schema.Tag} {inner : Schema.ContentSet} (e : Element t inner) : String :=
  Print.renderDoc e.toRaw

/-- Serialize an admitted child, through the raw node it carries. -/
def Child.render {set : Schema.ContentSet} (c : Child set) : String := Print.render c.raw

/-- Serializing a typed element is serializing its erasure; every theorem of
`Whatwg.Html.Print` applies to it through this equation. -/
theorem Element.render_eq {t : Schema.Tag} {inner : Schema.ContentSet} (e : Element t inner) :
    e.render = Print.render e.toRaw := rfl

/-- The same for a child. -/
theorem Child.render_eq {set : Schema.ContentSet} (c : Child set) :
    c.render = Print.render c.raw := rfl

end Whatwg.Html
