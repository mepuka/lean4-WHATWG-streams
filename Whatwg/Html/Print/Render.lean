/-!
# Html.Print.Render.lean

Owner: the serializer: element open and close, attributes, void elements closed as TyXML closes them, and the injectivity statement on erased trees that stands in for a parse round trip until an HTML parser exists (ruling HP-8).

Schema anchors: `xml_print.ml` `Make_fmt` and `xh_print_closedtag`; `html_f.ml` `emptytags`.

Opens in H4.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet
(`docs/HTML-PACKAGE-PLAN.md`).
-/
