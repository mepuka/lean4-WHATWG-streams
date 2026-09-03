import Whatwg.Html.Schema

/-!
# Whatwg.Html.Content.Admission

The decidable child-admission relation of the TyXML port (slice H3, ruling
HP-6 of `docs/HTML-PACKAGE-PLAN.md`).

A child tag is admitted in a context exactly when the context's content set
names it. The content set of a context is produced by
`Whatwg.Html.Content.Transparent.resolveChildSet`, which resolves a parent
tag and its own context to the set its children are checked against; this
module owns only the last step, the membership test itself.

Two spellings are given. `admits` is the `Bool` test, which is the
constructor dispatch generated in slice H2 and nothing more. `Admits` is the
`Prop` an obligation is stated in, with the `Decidable` instance that lets a
use site discharge it by `decide`; the H2 cost measurement in
`WhatwgTest/Html/DecideBenchmark.lean` bounds that step at `maxHeartbeats 20`
for the largest set. `admits_iff` is the bridge, and it is definitional.

What a proof of `Admits ctx t` means: the tag `t` is a member of the TyXML
4.6.0 content set `ctx` as projected by slice H2. It is not a claim about the
HTML Standard's content model for any element; the recorded departures of the
port live in `Whatwg.Html.Content.Divergence`.
-/

namespace Whatwg.Html.Content

open Whatwg.Html.Schema

/-- The admission test: the context's content set names the child tag. -/
def admits (ctx : ContentSet) (child : Tag) : Bool := ctx.contains child

/-- Admission as a proposition, the form an obligation of the typed tree
takes. -/
def Admits (ctx : ContentSet) (child : Tag) : Prop := admits ctx child = true

/-- Admission is decidable by evaluation, so a use site closes an obligation
with `decide`. -/
instance instDecidableAdmits (ctx : ContentSet) (child : Tag) : Decidable (Admits ctx child) :=
  inferInstanceAs (Decidable (admits ctx child = true))

/-- The bridge between the two spellings, definitionally. -/
theorem admits_iff (ctx : ContentSet) (child : Tag) :
    Admits ctx child ↔ ctx.contains child = true := Iff.rfl

/-- `admits` is the generated membership function under another name. -/
theorem admits_eq_contains (ctx : ContentSet) (child : Tag) :
    admits ctx child = ctx.contains child := rfl

/-- The empty content set admits nothing. -/
theorem not_admits_notag (child : Tag) : ¬ Admits .notag child := by
  simp [Admits, admits, ContentSet.contains, Sets.notag]

end Whatwg.Html.Content
