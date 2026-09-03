import Whatwg.Html.Content.Lattice
import Whatwg.Html.Content.Transparent
import Whatwg.Html.Content.Admission

/-!
# WhatwgTest.Html.Lattice

Finite probes for slice H3.1–H3.2: the content-set lattice
(`Whatwg.Html.Content.Lattice`), transparent coherence
(`Whatwg.Html.Content.Transparent`) and the admission relation
(`Whatwg.Html.Content.Admission`).

Every probe below is a closed statement about two or three constructor
dispatches, decided by the kernel. A probe is evidence about the projected
TyXML 4.6.0 data at one point; the quantified statements are the theorems in
the modules themselves. The probes that record a surprise are marked as such:
they exist so that a regression of the H2 emitter that quietly repaired
TyXML's data would fail this file.

The repository's elaboration-time axiom gate in `WhatwgTest.lean` audits every
declaration compiled here, so no per-file axiom report is written.
-/

namespace WhatwgTest.Html.Lattice

open Whatwg.Html.Schema
open Whatwg.Html.Content

/-! ## Membership -/

example : Sets.flow5 .div = true := by decide

example : Sets.phrasing .div = false := by decide

example : Sets.phrasing .pcdata = true := by decide

example : Sets.flow5 .pcdata = true := by decide

example : Sets.phrasing_without_interactive .a = false := by decide

example : Sets.phrasing .a = true := by decide

example : Tag.isVoid .br = true := by decide

example : Sets.notag .div = false := by decide

/-! ## Inclusion -/

example : SubsetOf Sets.phrasing Sets.flow5 := phrasing_subset_flow5

example : Sets.flow5_without_interactive .div = (Sets.flow5 .div && !Excluded.flow5Interactive .div) := by
  decide

/-! ## Surprises in the projected data

Each of these four probes contradicts what the name of the set suggests, and
each is exactly what `vendor/tyxml-d2916535/lib/html_types.mli` says at the
pin. -/

/-- `phrasing_without_noscript` drops far more than `Noscript`: `Span` is a
phrasing tag and is not in it. -/
example : Sets.phrasing .span = true ∧ Sets.phrasing_without_noscript .span = false := by decide

/-- `core_phrasing_without_noscript` and `phrasing_without_noscript` are
disjoint; `Abbr` is in the first and not the second. -/
example : Sets.core_phrasing_without_noscript .abbr = true
    ∧ Sets.phrasing_without_noscript .abbr = false := by decide

/-- `phrasing_without_dfn` also drops `Embed`, `Iframe` and `Svg`. -/
example : Sets.phrasing .embed = true ∧ Sets.phrasing_without_dfn .embed = false := by decide

/-- `core_flow5_without_media` drops nothing at all. -/
example : Sets.core_flow5_without_media .div = Sets.core_flow5 .div := by decide

/-! ## Transparency -/

/-- The element-row notion and the content-set notion differ on `Noscript`. -/
example : Tag.isTransparent .noscript = false ∧ Sets.transparent .noscript = true := by decide

example : Tag.isTransparent .a = true := by decide

example : ContentSet.transparentPayload .flow5 .a = some .flow5_without_interactive := by decide

example : ContentSet.transparentPayload .phrasing .a = some .phrasing_without_interactive := by decide

example : ContentSet.transparentPayload .flow5 .audio = some .flow5_without_media := by decide

example : ContentSet.transparentPayload .flow5 .div = none := by decide

/-- The payload of `Del` in a `flow5_without_form` context readmits `Form`. -/
example : ContentSet.transparentPayload .flow5_without_form .del = some .flow5
    ∧ ContentSet.contains .flow5 .form = true
    ∧ ContentSet.contains .flow5_without_form .form = false := by decide

/-! ## The child-set resolver -/

example : resolveChildSet .a .phrasing = some .phrasing_without_interactive := by decide

example : resolveChildSet .a .flow5 = some .flow5_without_interactive := by decide

example : resolveChildSet .div .flow5 = some .flow5 := by decide

example : resolveChildSet .img .flow5 = some .notag := by decide

example : resolveChildSet .br .phrasing = some .notag := by decide

/-- `noscript` takes its context-sensitive payload, not the fixed
`flow5_without_noscript` of its element row. -/
example : resolveChildSet .noscript .phrasing = some .phrasing_without_noscript := by decide

example : resolveChildSet .noscript .flow5 = some .flow5_without_noscript := by decide

/-- `svg` has no content set in the projection, so the resolver returns
nothing for it. -/
example : resolveChildSet .svg .flow5 = none := by decide

/-! ## Admission -/

example : Admits .flow5 .div := by decide

example : ¬ Admits .phrasing .div := by decide

example : ¬ Admits .notag .div := by decide

example : Admits .phrasing_without_interactive .span := by decide

end WhatwgTest.Html.Lattice
