import Whatwg.Html.Schema.Tags
import Whatwg.Html.Schema.Attributes
import Whatwg.Html.Schema.Families
import Whatwg.Html.Schema.ContentModel

/-!
# Whatwg.Html.Schema

The generated schema of the TyXML port (slice H2 of
`docs/HTML-PACKAGE-PLAN.md`): the element-tag and attribute-tag universes,
every named content set and attribute set as a constructor-dispatch
membership function, and one row per element and attribute constructor.
The four modules below are written by `lake exe tyxmlschema --write` from
the sealed TyXML sources and checked for byte drift by `lake exe
tyxmlschema`; nothing in them is authored, and nothing in them is a proof.
Declaration records for their constants inherit from the schema rows
(ruling HP-10).
-/
