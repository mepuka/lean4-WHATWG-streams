/-!
# Html.Print.Escape.lean

Owner: text and attribute escaping: TyXML's `encode_unsafe_char` and `encode_unsafe_char_and_at`, with the soundness statement that no escaped text contains an unescaped `<`, `>`, `&`, or `"`.

Schema anchors: `xml_print.ml` lines `is_control` through `encode_unsafe_char_and_at`.

Opens in H4.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet
(`docs/HTML-PACKAGE-PLAN.md`).
-/
