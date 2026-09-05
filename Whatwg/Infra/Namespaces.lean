import Whatwg.Infra.Text.String

/-!
# Namespaces

Owner: the six namespace constants of section `namespaces` of
`vendor/whatwg-infra-3f984adc/infra.bs`.

Each is a string in the text's sense, so each is a `JsString` (ruling
INFRA-R1, `docs/INFRA-PROOF-PLAN.md` section 3) built from the quoted literal
by `JsString.ofLiteral`; the literals are ASCII, so every code unit is the
code point of one character and no surrogate pair arises.
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- The HTML namespace, section `namespaces`: "is
`http://www.w3.org/1999/xhtml`". -/
def htmlNamespace : JsString := JsString.ofLiteral "http://www.w3.org/1999/xhtml"

/-- The MathML namespace, section `namespaces`: "is
`http://www.w3.org/1998/Math/MathML`". -/
def mathMLNamespace : JsString := JsString.ofLiteral "http://www.w3.org/1998/Math/MathML"

/-- The SVG namespace, section `namespaces`: "is `http://www.w3.org/2000/svg`". -/
def svgNamespace : JsString := JsString.ofLiteral "http://www.w3.org/2000/svg"

/-- The XLink namespace, section `namespaces`: "is
`http://www.w3.org/1999/xlink`". -/
def xlinkNamespace : JsString := JsString.ofLiteral "http://www.w3.org/1999/xlink"

/-- The XML namespace, section `namespaces`: "is
`http://www.w3.org/XML/1998/namespace`". -/
def xmlNamespace : JsString := JsString.ofLiteral "http://www.w3.org/XML/1998/namespace"

/-- The XMLNS namespace, section `namespaces`: "is
`http://www.w3.org/2000/xmlns/`". -/
def xmlnsNamespace : JsString := JsString.ofLiteral "http://www.w3.org/2000/xmlns/"

end Whatwg.Infra
