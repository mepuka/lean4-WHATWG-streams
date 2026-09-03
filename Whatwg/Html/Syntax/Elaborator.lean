/-!
# Html.Syntax.Elaborator.lean

Owner: the `html!` surface syntax and its elaborator: parsed tags become typed-tree terms whose admission obligations are discharged by `decide`, with diagnostics naming the parent, the child, and the content set that excluded it.

Schema anchors: none; a developer surface over the typed tree.

Opens in H5.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet
(`docs/HTML-PACKAGE-PLAN.md`).
-/
