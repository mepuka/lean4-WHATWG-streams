import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.Breakers

Negative probes for slice H3.3–H3.4: constructions that must be REJECTED at
elaboration. `#check_failure` succeeds only when the term fails to elaborate,
and the `#guard_msgs` docstring above each one pins the exact diagnostic, so
a probe that started failing for a different reason — a renamed combinator, a
syntax slip, an argument in the wrong position — would fail this file rather
than pass it silently. Each rejection below is the auto-parameter `h` of
`Child.of`/`Child.text` (child admission, `Whatwg.Html.Content.Admits`) or the
auto-parameter `_ha` of a combinator (attribute admission,
`Whatwg.Html.AttrsAdmitted`), and the pinned message names which.

The last two probes are rejected by the type checker rather than by a
`decide`: a nullary combinator has no children parameter at all, so a list of
children lands on its `attrs` argument and mismatches. Their diagnostics
mention the elaborator's recovery term and are not pinned; `(drop info)`
keeps the assertion at "this does not elaborate".

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Breakers

open Whatwg.Html
open Whatwg.Html.Schema (Tag ContentSet Attr)

-- Rejected by `Child.of`'s `h`: a `button` is not a member of
-- `phrasing_without_interactive`, which is `button`'s own content set.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: Tactic `decide` proved that the proposition
  Content.Admits ContentSet.phrasing_without_interactive Tag.button
is false
---
info: E.p [E.el (E.button [E.el (E.button [] [] ⋯) ⋯] [] ⋯) ⋯] [] ⋯ : Element Tag.p ContentSet.phrasing
-/
#guard_msgs in
#check_failure (E.p [E.el (E.button [E.el (E.button [])])] : Element .p .phrasing)

-- Rejected by `Child.of`'s `h`: `Div` is not a member of `phrasing`, which
-- is `p`'s own content set.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: Tactic `decide` proved that the proposition
  Content.Admits ContentSet.phrasing Tag.div
is false
---
info: E.p [E.el (E.div [] [] ⋯) ⋯] [] ⋯ : Element Tag.p ContentSet.phrasing
-/
#guard_msgs in
#check_failure (E.p [E.el (E.div [])] : Element .p .phrasing)

-- The transparent case, and the point of ruling HP-4. Rejected by the inner
-- `Child.of`'s `h`: unification assigned the link's content parameter
-- `childSet ContentSet.phrasing Tag.a`, which reduces to
-- `phrasing_without_interactive`, and that set does not name `Div`. The same
-- `E.a [E.el (E.div [])]` term is accepted under `div`, where the payload is
-- `flow5_without_interactive` (`WhatwgTest/Html/Builders.lean`).
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: Tactic `decide` proved that the proposition
  Content.Admits (childSet ContentSet.phrasing Tag.a) Tag.div
is false
---
info: E.p [E.el (E.a [E.el (E.div [] [] ⋯) ⋯] [] ⋯) ⋯] [] ⋯ : Element Tag.p ContentSet.phrasing
-/
#guard_msgs in
#check_failure (E.p [E.el (E.a [E.el (E.div [])])] : Element .p .phrasing)

-- Rejected by the inner `Child.of`'s `h`: no payload of a transparent link
-- names `A`, so a link never nests inside a link. TyXML's
-- `html_types.mli` comment at line 438 makes the same promise.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: Tactic `decide` proved that the proposition
  Content.Admits (childSet ContentSet.phrasing Tag.a) Tag.a
is false
---
info: E.p [E.el (E.a [E.el (E.a [] [] ⋯) ⋯] [] ⋯) ⋯] [] ⋯ : Element Tag.p ContentSet.phrasing
-/
#guard_msgs in
#check_failure (E.p [E.el (E.a [E.el (E.a [])])] : Element .p .phrasing)

-- Rejected by `Child.text`'s `h` (ruling HP-5): `PCDATA` is a tag like any
-- other and `ul_content_fun` names only `Li`.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: Tactic `decide` proved that the proposition
  Content.Admits ContentSet.ul_content_fun Tag.pcdata
is false
---
info: E.ul [E.txt "loose text" ⋯] [] ⋯ : Element Tag.ul ContentSet.ul_content_fun
-/
#guard_msgs in
#check_failure (E.ul [E.txt "loose text"] : Element .ul .ul_content_fun)

-- Rejected by `Child.of`'s `h`: `Title` is metadata, and `flow5` does not
-- name it.
/--
info: could not synthesize default value for parameter 'h' using tactics
---
info: Tactic `decide` proved that the proposition
  Content.Admits ContentSet.flow5 Tag.title
is false
---
info: E.body [E.el (E.title (E.txt "t" ⋯) [] ⋯) ⋯] [] ⋯ : Element Tag.body ContentSet.flow5
-/
#guard_msgs in
#check_failure (E.body [E.el (E.title (E.txt "t"))] : Element .body .flow5)

-- Rejected by `E.div`'s `_ha`: `Href` is not a member of `div_attrib`.
/--
info: could not synthesize default value for parameter '_ha' using tactics
---
info: Tactic `decide` proved that the proposition
  AttrsAdmitted Schema.AttrSet.div_attrib [A.a_href "/target"]
is false
---
info: E.div [] [A.a_href "/target"] ⋯ : Element Tag.div ContentSet.flow5
-/
#guard_msgs in
#check_failure (E.div [] [A.a_href "/target"] : Element .div .flow5)

-- Rejected by the type checker, not by a `decide`: `E.br` is nullary, so its
-- first explicit argument is `attrs : List (Attr × String)` and a `Child`
-- does not fit there. There is no children parameter to supply.
#guard_msgs (drop info) in
#check_failure (E.br [E.txt "x"] : Element .br .notag)

-- The same for `E.img`, whose two required labelled arguments are followed by
-- `attrs` and by nothing else.
#guard_msgs (drop info) in
#check_failure (E.img "/u" "a" [E.txt "x"] : Element .img .notag)

end WhatwgTest.Html.Breakers
