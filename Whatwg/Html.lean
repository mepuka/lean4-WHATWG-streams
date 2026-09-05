import Whatwg.Html.Schema
import Whatwg.Html.Content.Admission
import Whatwg.Html.Content.Transparent
import Whatwg.Html.Content.Lattice
import Whatwg.Html.Content.Divergence
import Whatwg.Html.Node.Raw
import Whatwg.Html.Node.Typed
import Whatwg.Html.Node.Erasure
import Whatwg.Html.Node.Combinators
import Whatwg.Html.Print.Escape
import Whatwg.Html.Print.Render
import Whatwg.Html.Syntax.Elaborator
import Whatwg.Html.Bridge.Tyxml
import Whatwg.Html.Svg
import Whatwg.Html.Audit.Receipts

/-!
# Whatwg.Html

The HTML content model as a typed document algebra: a finite tag universe,
named content sets composed by inclusion, a decidable child-admission
relation, tag-indexed trees whose admission obligations are discharged at
construction, and a serializer. The schema is ported from OCaml TyXML, whose
polymorphic-variant row types encode the same content model; the HTML
Standard is the semantic owner against which every departure of that port is
recorded.

Authority pins (`SPEC-MANIFEST.md`, `docs/PROVENANCE.md`):

- TyXML 4.6.0, `ocsigen/tyxml` commit
  `d2916535536f2134bad7793a598ba5b7327cae41`, sealed under
  `vendor/tyxml-d2916535/`: the transcription source of the schema. The
  projection `generated/tyxml-html-schema.tsv`, regenerated and checked by
  `lake exe tyxmlschema`, is the one input the generated modules read.
- The HTML Standard, `whatwg/html` commit
  `746f2ede8a56bc01204e0f9cc23da33b37c6fbab` ("Review Draft Publication:
  July 2026"), `source` sealed under `vendor/whatwg-html-746f2ede/`: the
  semantic owner of every content model, and the reference every divergence
  row cites by span digest.

This root is the breadth scaffold of `docs/HTML-PACKAGE-PLAN.md` with H2 and
H3 landed: `Whatwg.Html.Schema` holds the generated data (tags, attributes,
content sets, element rows) behind the projection's drift gate,
`Whatwg.Html.Content` holds the lattice, transparent coherence and the
admission relation, `Whatwg.Html.Node` holds the raw tree, the tag-indexed
tree, its 111 element combinators and erasure, and H4 adds
`Whatwg.Html.Print` with the escaper, the serializer, and the decoder that
inverts the serializer on the sublanguage its own output determines.
`Whatwg.Html.Syntax`, `Whatwg.Html.Bridge`, `Whatwg.Html.Svg` and
`Whatwg.Html.Audit` are still a docstring and nothing else. Every semantic
declaration after this arrives behind a frozen contract packet.
-/
