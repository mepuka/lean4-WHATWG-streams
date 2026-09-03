/-!
# Whatwg.Html.Node.Raw

The untyped first-order tree TyXML calls `Xml.elt`: elements with string
names and string attributes, text, entities, and comments. Slice H3.3 of
`docs/HTML-PACKAGE-PLAN.md`.

Schema anchors: `xml_sigs.mli` `elt` and `attrib`; `xml_print.ml` for what
the printer distinguishes. TyXML's `Xml.elt` is a private variant with the
constructors `Empty`, `Comment`, `EncodedPCDATA`, `PCDATA`, `Entity`,
`Leaf`, `Node`. This port keeps the four the HTML content model and the H4
serializer need — element, text, entity, comment — and folds `Leaf` into
`element` with an empty child list, because voidness is a property of the
tag (`Tag.isVoid`) rather than of the node. `Empty` and the two encoded
variants are not modelled at this pin: `Empty` exists in TyXML so that
`list_wrap` can splice nothing, which a Lean `List` does directly, and the
encoded variants belong to the printer slice.

Nothing here is checked against a content model. This is the target of
erasure (`Whatwg.Html.Node.Erasure`), not the tree an author builds; the
typed tree of `Whatwg.Html.Node.Typed` is where admission is decided.

Only `Inhabited` is derived. `DecidableEq` has no handler that applies to the
nested occurrence `List RawNode` at this toolchain, and the handlers for
`Repr` and `BEq` do apply but compile their recursion through a `partial`
auxiliary (`instBEqRawNode.beq._unsafe_rec`), which the repository's source
trust gate rejects. `BEq` and `Repr` are therefore written out below as
mutual structural recursions over the node and its forest; equality probes
over erased trees go through `rfl` or through that `BEq`.
-/

namespace Whatwg.Html

/-- An untyped node of the serializable tree: an element with a markup name,
string-valued attributes and children; a text run; a named entity reference;
or a comment. -/
inductive RawNode where
  | element (tag : String) (attrs : List (String × String)) (children : List RawNode)
  | text (content : String)
  | entity (name : String)
  | comment (content : String)
  deriving Inhabited

namespace RawNode

mutual

/-- Structural equality of two nodes. -/
def beq : RawNode → RawNode → Bool
  | .element name attrs children, .element name' attrs' children' =>
      name == name' && attrs == attrs' && beqList children children'
  | .text content, .text content' => content == content'
  | .entity name, .entity name' => name == name'
  | .comment content, .comment content' => content == content'
  | _, _ => false

/-- Structural equality of two forests, pairwise and in order. -/
def beqList : List RawNode → List RawNode → Bool
  | [], [] => true
  | node :: rest, node' :: rest' => beq node node' && beqList rest rest'
  | _, _ => false

end

instance : BEq RawNode := ⟨RawNode.beq⟩

mutual

/-- A constructor-shaped rendering of the node, used by the `Repr`
instance. -/
def render : RawNode → String
  | .element name attrs children =>
      "(RawNode.element " ++ reprStr name ++ " " ++ reprStr attrs
        ++ " [" ++ renderList children ++ "])"
  | .text content => "(RawNode.text " ++ reprStr content ++ ")"
  | .entity name => "(RawNode.entity " ++ reprStr name ++ ")"
  | .comment content => "(RawNode.comment " ++ reprStr content ++ ")"

/-- The same rendering for a forest, comma-separated. -/
def renderList : List RawNode → String
  | [] => ""
  | [node] => render node
  | node :: rest => render node ++ ", " ++ renderList rest

end

instance : Repr RawNode := ⟨fun node _ => Std.Format.text node.render⟩

mutual

/-- The number of nodes in the tree, counting the root. -/
def size : RawNode → Nat
  | .element _ _ children => 1 + sizeList children
  | .text _ => 1
  | .entity _ => 1
  | .comment _ => 1

/-- The number of nodes in a forest. -/
def sizeList : List RawNode → Nat
  | [] => 0
  | node :: rest => node.size + sizeList rest

end

mutual

/-- The nesting depth of the tree: a leaf has depth `1`. -/
def depth : RawNode → Nat
  | .element _ _ children => 1 + depthList children
  | .text _ => 1
  | .entity _ => 1
  | .comment _ => 1

/-- The greatest depth in a forest; `0` for the empty forest. -/
def depthList : List RawNode → Nat
  | [] => 0
  | node :: rest => max node.depth (depthList rest)

end

/-- The markup name of an element node; `none` for text, entity and comment
nodes. -/
def tagName? : RawNode → Option String
  | .element name _ _ => some name
  | .text _ => none
  | .entity _ => none
  | .comment _ => none

/-- The children of an element node; `[]` for every leaf node. -/
def childNodes : RawNode → List RawNode
  | .element _ _ children => children
  | .text _ => []
  | .entity _ => []
  | .comment _ => []

/-- The attributes of an element node; `[]` for every leaf node. -/
def attributes : RawNode → List (String × String)
  | .element _ attrs _ => attrs
  | .text _ => []
  | .entity _ => []
  | .comment _ => []

/-- A leaf node has depth `1`. -/
theorem depth_text (s : String) : (RawNode.text s).depth = 1 := rfl

/-- An element with no children has size `1`. -/
theorem size_element_nil (name : String) (attrs : List (String × String)) :
    (RawNode.element name attrs []).size = 1 := rfl

/-- The size of an element is one more than the size of its forest. -/
theorem size_element (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    (RawNode.element name attrs children).size = 1 + sizeList children := rfl

/-- The depth of an element is one more than the depth of its forest. -/
theorem depth_element (name : String) (attrs : List (String × String))
    (children : List RawNode) :
    (RawNode.element name attrs children).depth = 1 + depthList children := rfl

end RawNode

end Whatwg.Html
