import Whatwg.Html.Schema
import Whatwg.Html.Node.Combinators

/-!
# WhatwgTest.Html.DecideBenchmark

The `decide` cost bound of slice H2 (`docs/HTML-PACKAGE-PLAN.md`, ruling
HP-6): membership in the largest content set, `flow5`, and in the void set
must be decided by the kernel in a bounded number of heartbeats, because
every admission obligation of the typed tree (H3) is discharged this way at
every node of every document. The generated membership functions are
constructor dispatch, so each check is one delta step and one iota step.

`maxHeartbeats` is the gate: an elaboration that exceeds it fails the
build. The bound is deliberately tight; a regression of the emitter to a
list scan would exceed it. Every example is a finite probe, reported as
such: it is evidence about the cost of two reductions, not a theorem about
the content model.
-/

namespace WhatwgTest.Html.DecideBenchmark

open Whatwg.Html.Schema
open Whatwg.Html

set_option maxHeartbeats 20 in
theorem flow5_div : Sets.flow5 .div = true := by decide

set_option maxHeartbeats 20 in
theorem flow5_head_false : Sets.flow5 .head = false := by decide

set_option maxHeartbeats 20 in
theorem phrasing_span : Sets.phrasing .span = true := by decide

set_option maxHeartbeats 20 in
theorem phrasing_div_false : Sets.phrasing .div = false := by decide

set_option maxHeartbeats 20 in
theorem contains_flow5_p : ContentSet.contains .flow5 .p = true := by decide

set_option maxHeartbeats 20 in
theorem void_br : Tag.isVoid .br = true := by decide

set_option maxHeartbeats 20 in
theorem void_div_false : Tag.isVoid .div = false := by decide

set_option maxHeartbeats 20 in
theorem common_class : AttrSets.common .«class» = true := by decide

/-! The same check through the kernel-only route the census ruled for
kernel checks (`decide +kernel`). -/
set_option maxHeartbeats 20 in
theorem flow5_div_kernel : Sets.flow5 .div = true := by decide +kernel

/-! ## Whole-tree cost at H3.3–H3.4

The two probes below build a typed tree rather than deciding one membership,
so each measures the whole per-node bill of `Whatwg.Html.Node.Typed`: for
every child, one `Content.Admits` decided by `decide` after `childSet` has
resolved the context through `ContentSet.transparentPayload`, and for every
element, one `AttrsAdmitted` over its (here empty) attribute list.

Measured on this pin by bisecting `maxHeartbeats` (the largest value that
still fails, then the smallest that passes):

| Probe | Nodes | Fails at | Passes at | Bound set here |
| --- | --- | --- | --- | --- |
| deep: 15 nested `div`, then `p`, then a text run | 17 | 350 | 375 | 1200 |
| wide: one `ul` with 30 `li`, each holding a text run | 61 | 550 | 600 | 1800 |

That is roughly 22 heartbeats per node on the deep tree and 10 on the wide
one. The two figures differ because the sets differ, not because the shape
does: every child of the deep tree is resolved against `flow5` or `phrasing`
and pays a `childSet` lookup in the payload table, while every child of the
wide tree is resolved against the one-tag set `ul_content_fun`. Neither probe
shows superlinear growth in the number of nodes at these sizes, which is what
the next slice needs to know before it decides whether a document of a few
thousand nodes can be elaborated at all. Each bound carries roughly a
threefold margin so that ordinary machine-to-machine variation does not turn
the gate red.

These are finite probes, reported as such: evidence about the cost of
elaborating two particular trees, not a theorem about the content model. -/

set_option maxHeartbeats 1200 in
/-- A tree nested fifteen `div` levels deep, with a `p` and a text run at the
bottom: seventeen nodes, seventeen admission obligations. -/
example : Element .div .flow5 :=
    E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el
    (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el (E.div [E.el
    (E.div [E.el (E.p [E.txt "leaf"])])])])])])])])])])])])])])])]

set_option maxHeartbeats 1800 in
/-- A wide tree: one `ul` with thirty `li`, each holding a text run. Sixty-one
nodes, sixty-one admission obligations. -/
example : Element .ul .ul_content_fun :=
    E.ul [E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]),
    E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el
    (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li
    [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt
    "item"]), E.el (E.li [E.txt "item"]), E.el (E.li [E.txt "item"])]

end WhatwgTest.Html.DecideBenchmark
