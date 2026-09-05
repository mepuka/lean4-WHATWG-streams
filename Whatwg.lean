import Whatwg.Infra
import Whatwg.Streams
import Whatwg.Html

/-!
# Whatwg

WHATWG standards reified in Lean 4, one library per standard. `Whatwg.Infra`
is the Infra Standard, the value universe (pinned and empty at W5 of
`docs/WHATWG-PACKAGE-PLAN.md`); `Whatwg.Streams` is the Streams Standard;
`Whatwg.Html` is the HTML content model ported from TyXML under the HTML
Standard's authority (scaffolded at H1 of `docs/HTML-PACKAGE-PLAN.md`). A
consumer imports a standard's root, or this module for all of them.
-/
