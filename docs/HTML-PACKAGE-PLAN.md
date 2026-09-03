# Plan: `Whatwg.Html`, the HTML content model ported from TyXML

Status: **H0 and H1 executed, 2026-09-03** (this document, the pins, the
breadth scaffold, and the schema projection gate). Nothing semantic exists
yet: no theorem, no declaration under `Whatwg/Html/`.

This is the plan for the third library of the `whatwg` package: the HTML
content model as a typed document algebra, obtained by porting the schema
that OCaml TyXML encodes in polymorphic-variant row types, under the
authority of the WHATWG HTML Standard. It follows the family ruling of
`docs/WHATWG-PACKAGE-PLAN.md` (one library per standard) and the
development order of `AGENTS.md`. Facts were read at `main` `d3666e9`.

## 0. Review of the proposed architecture

The proposal this plan started from mapped TyXML's open polymorphic
variants, structural subtyping, and phantom variance onto Lean inductives,
decidable admission predicates, `by decide`, typeclasses, and a macro
front end, with an OCaml `compiler-libs` extractor producing a JSON schema
that a Lean generator consumes. The mapping is right in outline and is
adopted. Eleven points change, each because the proposal conflicts with a
rule this repository already has or with what TyXML actually contains at
the pin.

| # | Proposal | Finding | Ruling |
| --- | --- | --- | --- |
| R1 | namespace `Tyxml.Html`, a standalone package | this package is one library per standard, and the standard is HTML, not TyXML; TyXML is the transcription source of the schema and the HTML Standard is the semantic owner (`AGENTS.md` authority order) | library `Whatwg.Html`; TyXML pinned as a source under `vendor/`, the HTML Standard pinned as the semantic owner; HP-1, HP-2 |
| R2 | `ContentModel.custom (check : HtmlTag → Bool)` | a function inside canonical data violates the representation rule that program content is first-order; TyXML has no such case: every content model is a named closed row type | dropped; content models are named sets extracted from `html_types.mli` (HP-3) |
| R3 | a `Context` of three booleans (`interactiveAllowed`, `headingAllowed`, `sectioningAllowed`) | TyXML carries thirteen `_without_` families (`interactive`, `noscript`, `media`, `dfn`, `label`, `progress`, `meter`, `time`, `table`, `form`, `header_footer`, `interactive_header_footer`, `sectioning_heading_header_footer`) plus the `between_*` bounds; three flags cannot reproduce them and would silently widen the model | the port keeps TyXML's named sets exactly; a flag view, if ever wanted, is derived and proved against them (HP-3) |
| R4 | `.transparent` "checked at the enclosing level during elaboration" | TyXML checks transparency in the type: `a : ('a attrib, 'a, [> 'a a]) star` makes the result tag carry the content set the children were checked against, so `p [a [a []]]` fails at `p` and `p [noscript (a [a []])]` typechecks; TyXML also approximates `a`'s content as `flow5_without_interactive`, which is narrower than the standard's transparent model | model TyXML's scheme (HP-4); record the approximation as a divergence row (HP-2) |
| R5 | `HtmlNode.text {t} : HtmlNode t` | admits text under every tag, including void elements and `ul`; in TyXML text is the tag `` `PCDATA `` (`txt : [> txt] elt`), admitted only where a content set names it | text is a tag of the universe; admission decides it like any other child (HP-5) |
| R6 | `instance [Fact (isValidChild ctx child = true)] : ValidChild ctx child` | `Fact` instances are never synthesized automatically, so this instance never fires; the working route is `Decidable` and `decide` (the repository already rules `decide +kernel`) | admission obligations are propositions discharged by `decide`; no `Fact` (HP-6) |
| R7 | `macro_rules` for `html!` that hard-code `HtmlTag.img` and `HtmlTag.p` | the rules ignore their own arguments; shaping diagnostics ("`div` is not phrasing content under `p`") needs an elaborator with access to the decided proposition, not a macro | H5 is an `elab`, not `macro_rules` |
| R8 | OCaml `compiler-libs` extractor, JSON IR, `Lean.FromJson` generator | every gate that decides green is Lean (`AGENTS.md` "Gates"); the P1 census ruled `Lean.Json` out of generators; the repository's projections are TSV with a Lean drift gate; the OCaml reading belongs to the pin-time cross-check protocol of `docs/PROVENANCE.md`, like `shasum` beside the proved SHA-256 | `Gates/TyxmlSchema.lean` parses the sealed `.mli` bytes and writes `generated/tyxml-html-schema.tsv`; the OCaml reading is a cross-check recorded in PROVENANCE, never a gate (HP-7) |
| R9 | `T1: isValidChild ctx c = true ↔ W3C_Valid ctx c` | there is no machine-readable `W3C_Valid`; the HTML Standard states each element's content model in prose, per element | the standard's content models enter as authored rows transcribed from the pinned `source` with span digests (the census pattern), and T1 becomes "TyXML admission ↔ transcribed HTML-Standard admission, modulo a named divergence list" (HP-2, HP-8) |
| R10 | `T5: render ∘ eraseTypes ∘ parse` round trip | TyXML has no parser (it prints; `of_seq` imports from an external parser); the HTML parser is the largest algorithm on the platform (`docs/research/2026-09-01-web-reification-targets-survey.md`, row 22) | T5 is injectivity of the serializer on erased trees plus escaping soundness; a parse round trip is refused until a parser exists (HP-8) |
| R11 | the `HtmlTag` list in the proposal (`bdi`, `data`, `s`, `track`, `search`, ...) | TyXML 4.6.0 lacks several current elements and keeps obsolete ones (`command`, `keygen`, `menu`, `hgroup` with the old content model); the proposal's `AttrKey` likewise does not match TyXML's 204 `a_*` constructors | the universe is what the pin contains; every element the standard has and TyXML lacks, and every element TyXML has and the standard dropped, is a divergence row (HP-2) |

Two further corrections of fact. Void elements come from `html_f.ml`'s
`emptytags` (fifteen tags, `command` and `keygen` among them), not from
`xml_print.ml`, which is parametrised by that list. And TyXML already ships
a reflection tool, `syntax/reflect/reflect.ml`, built on `ppxlib` over the
same `.mli` files; it extracts what the PPX needs (attribute value parsers,
element assemblers, renames), not the content sets, so it is a partial
cross-check and not a substitute for the extractor.

## 1. Target shape

```text
vendor/tyxml-d2916535/            TyXML 4.6.0 at d2916535: lib/**, syntax/reflect/**, licenses
vendor/whatwg-html-746f2ede/      the HTML Standard source at the July 2026 Review Draft
generated/tyxml-html-schema.tsv   the schema projection: one row per type, val, and void tag
Gates/TyxmlSchema.lean            the projection generator and drift gate (`lake exe tyxmlschema`)
Whatwg/Html.lean                  root
Whatwg/Html/
  Schema/     Universe  Sets  Elements  Attributes  Void      generated from the projection (H2)
  Content/    Admission  Transparent  Lattice  Divergence     the decidable model and its lemmas (H3)
  Node/       Raw  Typed  Erasure                              trees (H3)
  Print/      Escape  Render                                   serializer (H4)
  Syntax/     Elaborator                                       `html!` (H5)
  Bridge/     Tyxml                                            port fidelity (H6)
  Svg.lean                                                     deferred (HP-9)
  Audit/      Receipts
WhatwgTest/Html/                  contracts, attacks, receipts, mirroring the areas (from H3)
```

Dependency direction, top to bottom: `Schema` → `Content` → `Node` →
`Print` → `Syntax`; `Bridge` reads everything; nothing under `Whatwg/Html/`
imports `Gates/`.

## 2. Rulings

| Id | Question | Ruling |
| --- | --- | --- |
| HP-1 | authority | the HTML Standard at `whatwg/html` `746f2ede` is the semantic owner; TyXML at `d2916535` is the transcription source of the schema and second-tier evidence for everything else. The port transcribes TyXML because its row types are machine-readable and the standard's content models are prose; the standard is the reference every transcription is checked against |
| HP-2 | divergence | every place where TyXML's typing departs from the standard is an authored row in `Whatwg/Html/Content/Divergence.lean` naming the element, the two content models, and the span digest of the standard's text; the analogue of a host-profile refusal row. A divergence is never repaired by editing the projection or the standard's row |
| HP-3 | content sets | named sets exactly as TyXML declares them, including the `_without_` families, `transparent*` with their type parameters, and the `between_*` bounds; inclusion is by the row-type inheritance TyXML writes, never by a hand-written category table |
| HP-4 | transparent elements | TyXML's scheme: a transparent element's result tag carries its content set; admission at a non-transparent parent looks through it. Not a context flag passed downward |
| HP-5 | text | `` `PCDATA `` is a tag of the universe admitted by the content sets that name it; entities and CDATA likewise map to `txt` |
| HP-6 | obligations | admission and attribute obligations are `Prop`s decided by `decide` over the finite universe; `native_decide` is forbidden as everywhere; the H3 packet measures `decide` cost on the largest set (`flow5`, roughly one hundred tags) before choosing between list membership and a `Fin`-indexed bitset |
| HP-7 | extractor | Lean, under `Gates/`, over the sealed bytes, producing a TSV projection with span digests and checked for byte drift; the OCaml `compiler-libs` reading is run once at each pin as a cross-check and recorded in `docs/PROVENANCE.md` |
| HP-8 | printer claims | escaping soundness and serializer injectivity on erased trees are the H4 theorems; a parse round trip is refused with a refusal theorem until a parser exists in this package |
| HP-9 | SVG | pinned with TyXML, no library; a future library sits beside `Whatwg.Html`, not under it, because SVG is a W3C standard |
| HP-10 | generated Lean source | H2 emits `Whatwg/Html/Schema/*.lean` from the projection with a `GENERATED` header and a byte-drift check in `lake exe tyxmlschema`; the generated modules carry no proof, only data and derived instances, so they need no proof graph, but their declarations still receive ownership records by inheritance from the schema row |
| HP-11 | the `source` pin | the whole 7.9 MB `source` is sealed rather than digest-only, so that divergence rows can anchor by span digest exactly as census rows do; the seal takes under a second |

## 3. Anticipated proof graph

The proposal's five-theorem DAG survives with the statements repaired:

| Node | Statement | Slice |
| --- | --- | --- |
| L1 | inclusion: for every pair of sets TyXML relates by inheritance, membership is monotone (`phrasing ⊆ flow5`, `x_without_y ⊆ x`, `core_x ⊆ x`) | H3 |
| L2 | separation: a void element's content set is empty; `notag` admits nothing | H3 |
| L3 | transparent coherence: admission through a transparent element equals admission of its children at the enclosing parent's set (TyXML's typing, stated as a lemma) | H3 |
| T1 | port fidelity: TyXML admission on the projection ↔ the standard's transcribed content model, modulo the divergence rows, for every element row | H6 |
| T2 | void emptiness: a typed tree never has children under a void tag | H3 |
| T3 | attributes: every attribute on a typed element is in that element's set; duplicates refused | H3 |
| T4 | tree well-formedness: admission is preserved under composition of admitted subtrees | H3 |
| T5 | escaping soundness and serializer injectivity on erased trees (HP-8) | H4 |

Every node names its assurance route in the H3 packet before its statement
is frozen; none is claimed here.

## 4. Slices

| Slice | Work | Exit gate |
| --- | --- | --- |
| H0 | this plan; pins fetched from the upstream git objects, sealed, cross-checked | `lake exe vendorseal` green; every new manifest row agrees with an independent `shasum -a 256`; PROVENANCE and SPEC-MANIFEST rows |
| H1 | breadth scaffold: root, eighteen declaration-free stubs, `Gates/TyxmlSchema.lean`, `generated/tyxml-html-schema.tsv`, CI step | `lake --wfail build` of every target; `lake exe tyxmlschema` PASS; the OCaml cross-check agrees on every row; the parity receipt unchanged (no declarations added) |
| H2 | the generated `Schema` modules from the projection; `decide`-cost measurement on `flow5` | drift check green in both directions; the axiom gate unchanged; declaration records by inheritance |
| H3 | the first breaker/builder packet: admission, transparent coherence, lattice lemmas, typed trees, erasure (L1–L3, T2–T4) | contract frozen red by a separate seat; battery green; receipts |
| H4 | escaping and the serializer (T5) | packet closed; TyXML's `test_html.ml` expectations replayed as finite probes |
| H5 | `html!` elaborator with diagnostics | error-message contract frozen; every proposal example elaborates or fails as stated |
| H6 | port fidelity (T1) over the full projection; the divergence list complete for every element section of the standard at the pin | T1 proved per element row; divergence rows with span digests; coverage block format for HTML |

## 5. Ledger

| Slice | Commit | Result |
| --- | --- | --- |
| H0 | (uncommitted, 2026-09-03) | pins fetched blob-by-blob from `ocsigen/tyxml` at `d2916535` (25 files, every blob object hash verified with `git hash-object --no-filters`) and `whatwg/html` at `746f2ede` (`source`, `LICENSE`, both verified); `lake exe vendorseal --write` regenerated the manifest (206 files, 5 trees); every one of the 27 new rows agrees with `shasum -a 256` |
| H1 | (uncommitted, 2026-09-03) | root, eighteen stubs, `Gates/TyxmlSchema.lean`, projection (560 type, 371 val, 15 void rows), CI step; OCaml `compiler-libs` cross-check identical on all 931 declarations; every gate green |
| H2 | (uncommitted, 2026-09-03) | `Gates/TyxmlSchemaEmit.lean` emits `Whatwg/Html/Schema/{Tags,Attributes,Families,ContentModel}.lean` from the same parse: 115 element tags, 111 element constructors (7 text constructors), 69 content sets (`flow5` 86 tags), 216 attribute tags and constructors, 118 attribute sets, 15 void tags; sets expanded from the pinned row types, never composed by hand (the boolean decomposition of the `_without_` families is an H3 lemma, not a definition); `lake exe tyxmlschema` checks the modules for byte drift; `WhatwgTest/Html/DecideBenchmark.lean` bounds `decide` on `flow5`, `phrasing`, the void set, and `common` at `maxHeartbeats 20`; the WP-7 parity receipt scoped to the pre-rename modules; markup spellings `reserved` (`a_reversed`) and `xml:lang` (`a_srclang`) found in `html_f.ml` at the pin, carried as written for the divergence list |
| H3.1–H3.2 | (uncommitted, 2026-09-03) | `Whatwg/Html/Content/{Lattice,Transparent,Admission}.lean` land L1, L2 and transparent coherence by reflection over `Tag.all` (115) and `ContentSet.all` (69): 27 `x_without_y ⊆ x` inclusions, 7 of the 8 `core_x ⊆ x` inclusions, 16 category inclusions into `flow5`, `phrasing` and `formatblock`, void content emptiness in element-row and `Tag.element?` form, and 27 boolean decompositions against exclusion predicates computed from the data rather than from the family names. Four departures recorded as theorems, not repaired: `core_flow5_without_{media,noscript}` and `core_phrasing_without_{media,noscript}` exclude nothing; `phrasing_without_noscript` is TyXML's transparent row alone (11 tags, equal to `transparent_without_noscript`), so `core_phrasing_without_noscript` is disjoint from it; `phrasing_without_{dfn,label,meter,progress,time}` also drop `Embed`, `Iframe` and `Svg`; `Sets.transparent` exceeds the element-row notion by `Noscript`, `Audio_interactive`, `Object_interactive` and `Video_interactive`. A transparent payload stays inside its context only for `flow5`, `phrasing` and `ruby_content_fun` — for the other 17 payload-carrying sets it does not — while every payload is inside `flow5`. `resolveChildSet` prefers the context payload over the element row; `WhatwgTest/Html/Lattice.lean` probes 33 points of the result |
| H3.3–H3.4 | (uncommitted, 2026-09-03) | `Whatwg/Html/Node/{Raw,Typed,Combinators,Erasure}.lean` land the trees and TyXML's constructor surface. `RawNode` is the four-constructor untyped tree with hand-written `BEq` and `Repr` (both deriving handlers compile a nested inductive through a `partial` auxiliary the trust gate rejects) and fuel-free `size`/`depth`. `Element t inner` carries TyXML's result row: `t` is the variant and `inner` the content set the children were checked against; `childSet set t` is `resolveChildSet` made total, and `Child.of : Element t (childSet set t) → Child set` makes unification assign a transparent combinator's `inner` from the child position, so `a` under `p` resolves to `phrasing_without_interactive` and `a` under `div` to `flow5_without_interactive`. The inference works with no fallback: Lean propagates the expected type into an application's result type before elaborating its arguments, so the `by decide` obligations are stated over assigned metavariables. 111 element combinators (87 star, 17 nullary, 4 unary, 3 special; 8 polymorphic in `inner`; 18 labelled forms of `html_sigs.mli` written by hand), 2 text constructors and 216 attribute helpers, produced from `elements` and `attributeCtors` by a hand-run script and NOT drift-checked. Simplified: `figure ?figcaption` is `` `Top `` only, `datalist ?children` and `menu ?children` are dropped, `svg` takes no children (HP-9), attribute values are `String`, and the two prefixed attribute constructors lose their name suffix. `WhatwgTest/Html/Builders.lean` elaborates 26 constructions including a whole document and 8 erasure probes; `WhatwgTest/Html/Breakers.lean` rejects 9, 7 of them with the exact diagnostic pinned by `#guard_msgs`. Whole-tree `decide` cost measured by bisection: 15 nested `div` (17 nodes) fails at 350 heartbeats and passes at 375; one `ul` with 30 `li` (61 nodes) fails at 550 and passes at 600 |
