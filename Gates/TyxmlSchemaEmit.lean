import Gates.TyxmlSchema

/-!
# Gates.TyxmlSchemaEmit

The H2 emitter of `docs/HTML-PACKAGE-PLAN.md`: from the same parse of the
sealed TyXML sources that `Gates.TyxmlSchema` projects to
`generated/tyxml-html-schema.tsv`, write the generated modules

- `Whatwg/Html/Schema/Tags.lean`: the element-tag universe, TyXML's
  markup names, and the void set;
- `Whatwg/Html/Schema/Attributes.lean`: the attribute-tag universe, the
  attribute constructors with their value types, and every named attribute
  set;
- `Whatwg/Html/Schema/Families.lean`: every named content set, expanded
  through TyXML's row-type inheritance into one constructor-dispatch
  function each; and
- `Whatwg/Html/Schema/ContentModel.lean`: one row per element constructor
  of `Html_sigs.T` with its kind, tag, content set, and attribute set.

`lake exe tyxmlschema` regenerates all four in memory and fails on any byte
of drift; `--write` writes them beside the projection.

## How a set is expanded

A polymorphic-variant row `[ | core_flow5 | (a, b, c, d) transparent ]`
contributes each tag it names directly and, for each inherited type, the
tags that type's body names, transitively. Type arguments are not expanded:
in `` `A of 'interactive `` the payload records which content set the
transparent element's children were checked against (ruling HP-4), and
membership of the tag `A` does not depend on it. Expansion follows the
path, so the mutually recursive `phrasing` family terminates without a
visited set beyond the current path. Every tag reached from a content set
is an element tag; every tag reached from an attribute set or named by an
`a_*` constructor is an attribute tag. The two universes overlap in OCaml's
single tag namespace (`` `Title ``, `` `Style ``, `` `Label ``) and are two
inductives here.

## Why constructor dispatch

Membership is emitted as a `match` listing the member constructors, so the
kernel decides `Sets.flow5 .div = true` by one delta and one iota step.
`WhatwgTest/Html/DecideBenchmark.lean` bounds that cost.

## Markup names

An element's markup name is the second string of its
`[@@reflect.element assembler markup]` attribute when present, else its
OCaml name; `html_f.ml`'s string literal is the cross-check. An attribute's
markup name is the first string literal of its `html_f.ml` binding (aliases
followed, `("data-" ^ name)` recorded as a prefix), which is where TyXML
actually spells it: two of those spellings, `a_reversed` as `reserved` and
`a_srclang` as `xml:lang`, are upstream defects at the pin and are carried
as written, for the divergence list.
-/

namespace Gates.TyxmlSchemaEmit

open Gates.Common
open Gates.TyxmlSchema

/-! ## Environment -/

structure Binding where
  name : String
  markup : String
  isPrefix : Bool
  deriving Repr, Inhabited

structure Env where
  types : Array Decl
  sigs : Array Decl
  bindings : Array Binding
  emptytags : Array String

def Env.type? (env : Env) (name : String) : Option Decl :=
  match env.types.find? (fun d => d.kind == "type" && d.name == name) with
  | some d => some d
  | none => env.sigs.find? (fun d => d.kind == "type" && d.name == name)

def Env.binding? (env : Env) (name : String) : Option Binding :=
  env.bindings.find? (·.name == name)

/-! ## `html_f.ml` bindings -/

private def firstStringAux (bs : ByteArray) (i stop : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    if Nat.ble stop i then none
    else
      let b := byteAt bs i
      if b == 0x28 && byteAt bs (i + 1) == 0x2a then
        match skipComment bs i with
        | .ok j => firstStringAux bs j stop fuel
        | .error _ => none
      else if b == 0x27 then
        if byteAt bs (i + 1) == 0x5c then
          match findByte bs 0x27 (i + 2) with
          | some j => firstStringAux bs (j + 1) stop fuel
          | none => none
        else if byteAt bs (i + 2) == 0x27 then firstStringAux bs (i + 3) stop fuel
        else firstStringAux bs (i + 1) stop fuel
      else if b == 0x22 then
        match skipString bs (i + 1) with
        | .ok j => some (i + 1, j - 1)
        | .error _ => none
      else firstStringAux bs (i + 1) stop fuel

private def skipSpacesAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 => if isSpace (byteAt bs i) then skipSpacesAux bs (i + 1) fuel else i

private def isLowerIdent (s : String) : Bool :=
  match s.toList with
  | c :: rest => (c.isLower || c == '_') && rest.all (fun c => c.isLower || c.isDigit || c == '_' || c == '\'')
  | [] => false

private def collectStartsAux (bs pat : ByteArray) (i : Nat) (acc : Array Nat) : Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    match findFrom bs pat i with
    | some j => collectStartsAux bs pat (j + 1) (acc.push j) fuel
    | none => acc

/-- Every top-level binding of `html_f.ml` (`\n  let name`) with the first
string literal of its body, or the identifier it aliases. -/
def rawBindings (bs : ByteArray) : Array (String × Option String × Option String × Bool) := Id.run do
  let pat := "\n  let ".toUTF8
  let starts := collectStartsAux bs pat 0 #[] (bs.size + 1)
  let mut out := #[]
  for k in [0:starts.size] do
    let start := starts[k]!
    let stop := if k + 1 < starts.size then starts[k + 1]! else bs.size
    let nameStart := start + pat.size
    let nameEnd := scanIdent bs nameStart
    let name := slice bs nameStart nameEnd
    match firstStringAux bs nameEnd stop (stop + 1) with
    | some (b, e) =>
      let after := skipSpacesAux bs (e + 1) (stop + 1)
      let isPrefix := byteAt bs after == 0x5e
      out := out.push (name, some (slice bs b e), none, isPrefix)
    | none =>
      match findByte bs 0x3d nameEnd with
      | some eq =>
        let rest := trimmed (slice bs (eq + 1) stop)
        out := out.push (name, none, if isLowerIdent rest then some rest else none, false)
      | none => out := out.push (name, none, none, false)
  return out

private def resolveAlias (raw : Array (String × Option String × Option String × Bool)) (name : String) :
    Nat → Option (String × Bool)
  | 0 => none
  | fuel + 1 =>
    match raw.find? (·.1 == name) with
    | some (_, some s, _, pre) => some (s, pre)
    | some (_, none, some alias, _) => resolveAlias raw alias fuel
    | _ => none

def bindings (bs : ByteArray) : Array Binding := Id.run do
  let raw := rawBindings bs
  let mut out := #[]
  for (name, _, _, _) in raw do
    match resolveAlias raw name 8 with
    | some (markup, isPrefix) => out := out.push { name, markup, isPrefix }
    | none => pure ()
  return out

/-! ## Expansion -/

/-- The parameter names of a type declaration, from its rendered parameter
list (`(+'interactive, +'noscript)` or `+'a` or empty). -/
def paramNames (params : String) : List String :=
  let cleaned := params.toList.filter (fun c => c != '(' && c != ')' && c != '+' && c != '-' && c != '\'')
  (String.ofList cleaned).splitOn "," |>.map trimmed |>.filter (· != "")

/-- A type with the substitution applied at its head (type variables only). -/
def substHead (subst : List (String × Ty)) : Ty → Ty
  | .var v => match subst.find? (·.1 == v) with
    | some (_, t) => t
    | none => .var v
  | t => t

/-- The content-set name a tag payload denotes, if it is a bare type name
(possibly through a substituted type variable); rows and other shapes carry
no content set. -/
def payloadName (subst : List (String × Ty)) (p : Ty) : Option String :=
  match substHead subst p with
  | .con [] n => some n
  | _ => none

mutual
  /-- Tags with their payload names, under a substitution of the enclosing
  type's parameters. -/
  def expand (env : Env) : Nat → List String → List (String × Ty) → Ty →
      Except String (List (String × Option String))
    | 0, _, _, _ => .error "expansion fuel exhausted"
    | fuel + 1, path, subst, t =>
      match t with
      | .row _ fields _ => expandFields env fuel path subst fields
      | .con args name =>
        if path.contains name then pure []
        else
          match env.type? name with
          | some d =>
            match d.ty with
            -- An abstract type (`notag`, `no_attribute_allowed`) names no tag.
            | .abstract => pure []
            | body =>
              let inner := (paramNames d.params).zip (args.map (substHead subst))
              expand env fuel (name :: path) inner body
          | none => .error s!"unknown type {name} in an expansion (path {path})"
      | .var v =>
        match subst.find? (·.1 == v) with
        | some (_, t) => expand env fuel path [] t
        | none => pure []
      | .alias t _ => expand env fuel path subst t
      | .annot t _ => expand env fuel path subst t
      | _ => .error s!"unexpected type shape in a variant expansion: {render renderFuel t}"
  def expandFields (env : Env) : Nat → List String → List (String × Ty) → List RowField →
      Except String (List (String × Option String))
    | 0, _, _, _ => .error "expansion fuel exhausted"
    | _, _, _, [] => pure []
    | fuel + 1, path, subst, f :: rest => do
      let here ← match f with
        | .tag n p => pure [(n, p.bind (payloadName subst))]
        | .inherit t => expand env fuel path subst t
      let more ← expandFields env fuel path subst rest
      pure (here ++ more)
end

/-- Tags of a type, with the payload each first occurrence carries. -/
def expandTagged (env : Env) (t : Ty) : Except String (List (String × Option String)) := do
  let tagged ← expand env 10000 [] [] t
  pure (tagged.foldl (fun acc (n, p) => if acc.any (·.1 == n) then acc else acc ++ [(n, p)]) [])

/-- The tags a type name expands to, deduplicated in first-occurrence order. -/
def expandName (env : Env) (name : String) : Except String (List String) := do
  let tagged ← expandTagged env (.con [] name)
  pure (tagged.map (·.1))

/-! Type names referenced by a type, arguments included. -/
mutual
  def refs : Nat → Ty → List String
    | 0, _ => []
    | fuel + 1, t =>
      match t with
      | .row _ fields _ => refsFields fuel fields
      | .con args name => name :: refsList fuel args
      | .alias t _ | .annot t _ => refs fuel t
      | .tuple items => refsList fuel items
      | .arrow _ d c => refs fuel d ++ refs fuel c
      | _ => []
  def refsList : Nat → List Ty → List String
    | 0, _ => []
    | _, [] => []
    | fuel + 1, t :: rest => refs fuel t ++ refsList fuel rest
  def refsFields : Nat → List RowField → List String
    | 0, _ => []
    | _, [] => []
    -- A tag's payload records an attribute constraint (`` `Li of li_attrib ``)
    -- or a transparent element's content parameter (`` `A of 'interactive ``);
    -- it never names a sibling content set, so the closure stops at it.
    | fuel + 1, .tag _ _ :: rest => refsFields fuel rest
    | fuel + 1, .inherit t :: rest => refs fuel t ++ refsFields fuel rest
end

/-- Transitive closure of type names under reference, from the given seeds,
restricted to names that resolve to a type with a body. -/
def closure (env : Env) (seeds : List String) : List String := Id.run do
  let mut done : List String := []
  let mut queue := seeds
  for _ in [0:4000] do
    match queue with
    | [] => break
    | n :: rest =>
      queue := rest
      if done.contains n then continue
      match env.type? n with
      | some d =>
        done := done ++ [n]
        queue := queue ++ refs 1000 d.ty
      | none => continue
  return done

/-- Follow `type x = y` and `type x = [ | y ]` chains to the set that carries
the tags, so an element's content set is named `flow5`, not
`div_content_fun`. -/
def canonicalName (env : Env) (name : String) : String := Id.run do
  let mut cur := name
  for _ in [0:32] do
    match env.type? cur with
    | some d =>
      match d.ty with
      | .con [] n => cur := n
      | .row _ [.inherit (.con [] n)] [] => cur := n
      | _ => break
    | none => break
  return cur

/-! ## Lean spelling -/

def leanKeywords : List String :=
  ["class", "section", "open", "for", "in", "at", "if", "then", "else", "do", "let", "fun",
   "match", "with", "end", "structure", "abbrev", "def", "theorem", "where", "namespace",
   "variable", "import", "instance", "example", "axiom", "by", "have", "show", "from", "mutual",
   "deriving", "private", "protected", "partial", "unsafe", "noncomputable", "inductive",
   "opaque", "macro", "syntax", "attribute", "local", "scoped", "universe", "calc", "suffices",
   "obtain", "exists", "forall", "hiding", "renaming", "using", "extends", "return", "break",
   "continue", "unless", "set_option", "omit", "include", "export", "nomatch", "nofun", "rec",
   "notation", "infix", "prefix", "postfix", "elab", "true", "false", "sorry", "admit", "try",
   "catch", "finally", "throw", "pure", "unfold", "generalizing", "type", "data", "this",
   "meta", "nonrec", "init", "run_cmd", "run_elab", "run_meta"]

/-- The Lean constructor name of a TyXML variant tag: first letter lowered,
guillemets when the result is a Lean keyword. -/
def ctorName (variant : String) : String :=
  -- The maximal leading run of upper-case letters is lowered: `OnClick` to
  -- `onClick`, `XMLns` to `xmlns`, `PCDATA` to `pcdata`, `H1` to `h1`.
  let chars := variant.toList
  let run := chars.takeWhile Char.isUpper
  let base := String.ofList (run.map Char.toLower ++ chars.drop run.length)
  if leanKeywords.contains base then "«" ++ base ++ "»" else base

/-- A set-membership function: constructor dispatch, eight members per line. -/
def emitBoolSet (fn : String) (doc : String) (domain : String) (members : List String) (domainCtors : List String) : String :=
  let members := domainCtors.filter members.contains
  if members.isEmpty then
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool := fun _ => false\n\n"
  else if members.length == domainCtors.length then
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool := fun _ => true\n\n"
  else
    let chunks := Id.run do
      let mut lines : List String := []
      let mut cur : List String := []
      for m in members do
        cur := cur ++ ["." ++ ctorName m]
        if cur.length == 8 then
          lines := lines ++ [String.intercalate " | " cur]
          cur := []
      if !cur.isEmpty then lines := lines ++ [String.intercalate " | " cur]
      lines
    let alts := String.intercalate "\n  | " chunks
    s!"/-- {doc} -/\ndef {fn} : {domain} → Bool\n  | {alts} => true\n  | _ => false\n\n"

def generatedHeader (moduleName : String) (summary : String) (imports : List String := []) : String :=
  String.join (imports.map fun m => s!"import {m}\n") ++ (if imports.isEmpty then "" else "\n") ++
  s!"/-!\n# Whatwg.Html.Schema.{moduleName}\n\n{summary}\n\n" ++
  "GENERATED by `lake exe tyxmlschema --write` from the sealed TyXML 4.6.0\n" ++
  s!"sources under `{vendorTree}/lib/` (`html_types.mli`, `html_sigs.mli`,\n" ++
  "`html_f.ml`; digests in the header of `generated/tyxml-html-schema.tsv`).\n" ++
  "DO NOT EDIT: `lake exe tyxmlschema` fails on any byte of drift. Slice H2 of\n" ++
  "`docs/HTML-PACKAGE-PLAN.md`; the emitter is `Gates/TyxmlSchemaEmit.lean`.\n" ++
  "Data and derived instances only: no proof lives here.\n-/\n\n"

/-! ## Schema extraction -/

inductive ElementKind where
  | star | unary | nullary | special
  deriving Repr, DecidableEq, Inhabited

structure ElementRow where
  name : String
  markup : String
  tag : String
  kind : ElementKind
  transparent : Bool
  content : Option String
  attribs : Option String
  deriving Repr, Inhabited

structure AttrRow where
  name : String
  markup : String
  isPrefix : Bool
  tag : String
  valueType : String
  kind : String
  deriving Repr, Inhabited

structure Schema where
  tags : List String
  attrs : List String
  contentSets : List String
  attrSets : List String
  /-- Inline attribute sets by element name, with their expansions. -/
  inlineAttrSets : List (String × List String)
  elements : List ElementRow
  textCtors : List String
  attributes : List AttrRow
  voidTags : List String

/-- Split an arrow type into its labelled arguments and result. -/
def argsOf : Ty → Nat → List (String × Ty) × Ty
  | t, 0 => ([], t)
  | .arrow label d c, fuel + 1 =>
    let (rest, r) := argsOf c fuel
    ((label, d) :: rest, r)
  | t, _ => ([], t)

/-- The type name an attribute-set position refers to: `[< div_attrib ]`,
a bare `title_attrib`, or `none` for an inline row. -/
def setNameOf : Ty → Option String
  | .row _ [.inherit (.con [] n)] [] => some n
  | .con [] n => some n
  | _ => none

def stringTypes : List String :=
  ["text", "cdata", "string", "id", "idref", "nmtoken", "name", "charset", "contenttype",
   "datetime", "frametarget", "languagecode", "fpi", "script_", "Xml.uri", "uri"]
def intTypes : List String := ["number", "pixels", "int"]
def floatTypes : List String := ["float_number", "float"]
def listTypes : List String :=
  ["idrefs", "nmtokens", "charsets", "contenttypes", "numbers", "coords", "linktypes", "mediadesc"]

/-- A coarse classification of an attribute's value type; the rendered OCaml
type is kept beside it as the authority. -/
def classifyValue (env : Env) : Ty → Nat → String
  | _, 0 => "other"
  | .con [] "unit", _ => "presence"
  | .con [inner] "wrap", fuel + 1 => classifyValue env inner fuel
  | .con [inner] "option", fuel + 1 => classifyValue env inner fuel
  | .con [_] "list", _ => "list"
  | .con [] "bool", _ => "bool"
  | .con [] "character", _ => "char"
  | .con [] "char", _ => "char"
  | .row .., _ => "enum"
  | .con [] n, fuel + 1 =>
    if stringTypes.contains n then "string"
    else if intTypes.contains n then "int"
    else if floatTypes.contains n then "float"
    else if listTypes.contains n then "list"
    else if n.endsWith "event_handler" then "handler"
    else
      match env.type? n with
      | some d =>
        match d.ty with
        | .row .. => "enum"
        | .con .. => classifyValue env d.ty fuel
        | _ => "other"
      | none => "other"
  | _, _ => "other"

def extract (env : Env) : Except String Schema := do
  let vals := env.sigs.filter (fun d => d.kind == "val" && d.modulePath == "T")
  -- Elements and text constructors.
  let mut elements : Array ElementRow := #[]
  let mut textCtors : Array String := #[]
  for d in vals do
    if d.name.startsWith "a_" then continue
    let (args, result) := argsOf d.ty 64
    let shape : Option (ElementKind × Option Ty × Option Ty × Ty) :=
      match result with
      | .con [a, c, r] "star" => some (.star, some a, some c, r)
      | .con [a, c, r] "unary" => some (.unary, some a, some c, r)
      | .con [a, r] "nullary" => some (.nullary, some a, none, r)
      | .con [r] "elt" =>
        let aArg := args.find? (·.1 == "?a")
        let attribTy := aArg.bind fun (_, t) =>
          match t with
          | .con [.con [inner] "attrib"] "list" => some inner
          | _ => none
        some (.special, attribTy, none, r)
      | _ => none
    let some (kind, attribTy, contentTy, resultTy) := shape | continue
    let resultTags ← expandTagged env resultTy
    match resultTags.map (·.1) with
    | ["PCDATA"] => textCtors := textCtors.push d.name
    | [tag] =>
      let markup :=
        let fromAttr := d.attrs.splitOn "; " |>.filterMap fun a =>
          if a.startsWith "reflect.element " then
            match (dropChars a "reflect.element ".length).splitOn " " with
            | [_, m] => some (dropLastChars (dropChars m 1) 1)
            | _ => none
          else none
        match fromAttr with
        | m :: _ => m
        | [] => d.name
      let transparent := contentTy matches some (.var _)
      let contentName : Option String :=
        match contentTy with
        | some t =>
          match setNameOf t with
          | some n => some (canonicalName env n)
          | none => none
        | none => none
      let contentName := match contentName with
        | some n => some n
        | none =>
          if (env.type? (d.name ++ "_content_fun")).isSome then some (canonicalName env (d.name ++ "_content_fun"))
          else none
      let attribName : Option String :=
        match attribTy with
        | some t =>
          match setNameOf t with
          | some n => if n.startsWith "svg" then none else some n
          | none => some (d.name ++ "_attrib_inline")
        | none => none
      elements := elements.push
        { name := d.name, markup, tag, kind, transparent, content := contentName, attribs := attribName }
    -- `tot`, `totl`, `toelt`, `of_seq`: untyped conversions whose result is a
    -- type variable name no tag and are not elements.
    | [] => continue
    | tags => throw s!"element {d.name}: result expands to {tags}, expected one tag"
  -- Attributes.
  let mut attributes : Array AttrRow := #[]
  for d in vals do
    unless d.name.startsWith "a_" do continue
    let (args, result) := argsOf d.ty 64
    let .con [r] "attrib" := result | throw s!"attribute {d.name}: result is not an attrib"
    let tagged ← expandTagged env r
    let [tag] := tagged.map (·.1) | throw s!"attribute {d.name}: result expands to {tagged.map (·.1)}"
    let some b := env.binding? d.name | throw s!"attribute {d.name}: no html_f.ml binding with a markup name"
    let valueType := String.intercalate " -> " (args.map fun (l, t) => (if l.isEmpty then "" else l ++ ":") ++ render renderFuel t)
    let kind := match args with
      | [(_, t)] => classifyValue env t 32
      | _ => "prefixed"
    attributes := attributes.push { name := d.name, markup := b.markup, isPrefix := b.isPrefix, tag, valueType, kind }
  -- Content sets: the closure from every element's content set.
  let contentSeeds := (elements.toList.filterMap (·.content)).eraseDups
  let contentSets := (closure env contentSeeds).toArray.qsort (· < ·) |>.toList
  let mut tagAcc : List String := []
  for s in contentSets do
    tagAcc := tagAcc ++ (← expandName env s)
  for e in elements do tagAcc := tagAcc ++ [e.tag]
  let tags := (tagAcc.eraseDups.toArray.qsort (· < ·)).toList
  -- Attribute sets: the closure from every element's attribute set, plus the
  -- inline rows spelled in place.
  let mut inlineSets : Array (String × List String) := #[]
  for d in vals do
    if d.name.startsWith "a_" then continue
    let (_, result) := argsOf d.ty 64
    let inlineRow : Option Ty := match result with
      | .con [a, _, _] "star" | .con [a, _, _] "unary" | .con [a, _] "nullary" =>
        if (setNameOf a).isNone then some a else none
      | _ => none
    match inlineRow with
    | some row => inlineSets := inlineSets.push (d.name ++ "_attrib_inline", (← expandTagged env row).map (·.1))
    | none => pure ()
  let attrSeeds := (elements.toList.filterMap (·.attribs)).filter (fun n => !n.endsWith "_inline") |>.eraseDups
  let attrSets := (closure env attrSeeds).toArray.qsort (· < ·) |>.toList
  let mut attrAcc : List String := []
  for s in attrSets do attrAcc := attrAcc ++ (← expandName env s)
  for (_, ts) in inlineSets do attrAcc := attrAcc ++ ts
  for a in attributes do attrAcc := attrAcc ++ [a.tag]
  let attrs := (attrAcc.eraseDups.toArray.qsort (· < ·)).toList
  -- Void tags, by markup name.
  let mut voidTags : List String := []
  for m in env.emptytags do
    let some e := elements.find? (·.markup == m) | throw s!"void tag {m} has no element constructor"
    voidTags := voidTags ++ [e.tag]
  return { tags, attrs, contentSets, attrSets, inlineAttrSets := inlineSets.toList
           elements := elements.toList, textCtors := textCtors.toList
           attributes := attributes.toList, voidTags }

/-! ## Emission -/

def emitEnum (name : String) (doc : String) (ctors : List String) : String :=
  let lines := Id.run do
    let mut out : List String := []
    let mut cur : List String := []
    for c in ctors do
      cur := cur ++ [ctorName c]
      if cur.length == 8 then
        out := out ++ ["  | " ++ String.intercalate " | " cur]
        cur := []
    if !cur.isEmpty then out := out ++ ["  | " ++ String.intercalate " | " cur]
    out
  s!"/-- {doc} -/\ninductive {name} where\n{String.intercalate "\n" lines}\n  deriving DecidableEq, Repr, Inhabited\n\n"

def emitStringFn (fn : String) (doc : String) (domain : String) (rows : List (String × String)) : String :=
  let alts := rows.map fun (c, s) => s!"  | .{ctorName c} => \"{s}\""
  s!"/-- {doc} -/\ndef {fn} : {domain} → String\n{String.intercalate "\n" alts}\n\n"

def emitAll (fn : String) (doc : String) (domain : String) (ctors : List String) : String :=
  let items := ctors.map fun c => "." ++ ctorName c
  let lines := Id.run do
    let mut out : List String := []
    let mut cur : List String := []
    for i in items do
      cur := cur ++ [i]
      if cur.length == 8 then
        out := out ++ ["   " ++ String.intercalate ", " cur ++ ","]
        cur := []
    if !cur.isEmpty then out := out ++ ["   " ++ String.intercalate ", " cur]
    out
  let body := String.intercalate "\n" lines
  let body := if body.endsWith "," then dropLastChars body 1 else body
  s!"/-- {doc} -/\ndef {fn} : List {domain} :=\n  [{dropChars body 3}]\n\n"

def emitTags (env : Env) (s : Schema) : Except String String := do
  let mut out := generatedHeader "Tags"
    ("The element-tag universe: every polymorphic-variant tag TyXML's content\nsets and element constructors name. A tag with no constructor of its own\n(`Img_interactive`, `PCDATA`, the `*_interactive` transparent variants)\nhas no markup name.")
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  out := out ++ emitEnum "Tag" "An element tag of the TyXML universe, in the order of its variant name." s.tags
  out := out ++ emitAll "Tag.all" "Every tag, in constructor order." "Tag" s.tags
  out := out ++ emitStringFn "Tag.variantName" "The OCaml variant name of the tag, as `html_types.mli` spells it." "Tag" (s.tags.map fun t => (t, t))
  let markups := s.tags.filterMap fun t =>
    match s.elements.find? (·.tag == t) with
    | some e => some (t, e.markup)
    | none => none
  let alts := markups.map fun (c, m) => s!"  | .{ctorName c} => some \"{m}\""
  out := out ++ "/-- The markup name TyXML emits for the tag, when a constructor exists\n(`table` and `tablex` share `Table`; the first constructor wins). -/\ndef Tag.markupName : Tag → Option String\n" ++
    String.intercalate "\n" alts ++ "\n  | _ => none\n\n"
  out := out ++ emitBoolSet "Tag.isVoid"
    ("The void elements: `html_f.ml`'s `emptytags`, which TyXML's printer closes\nas `<tag />`.") "Tag" s.voidTags s.tags
  let _ := env
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

def emitFamilies (env : Env) (s : Schema) : Except String String := do
  let mut out := generatedHeader "Families"
    ("Every named content set of `html_types.mli` reachable from an element's\ncontent model, expanded through row-type inheritance into a\nconstructor-dispatch membership function, and the `ContentSet` index over\nthem.") ["Whatwg.Html.Schema.Tags"]
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  for name in s.contentSets do
    let members ← expandName env name
    let some d := env.type? name | throw s!"content set {name} vanished"
    out := out ++ emitBoolSet s!"Sets.{name}"
      s!"`{name}` (`html_types.mli` line {d.line}): {members.length} of {s.tags.length} tags." "Tag" members s.tags
  out := out ++ emitEnum "ContentSet" "A named content set, by its TyXML type name." s.contentSets
  out := out ++ emitAll "ContentSet.all" "Every content set, in constructor order." "ContentSet" s.contentSets
  out := out ++ emitStringFn "ContentSet.tyxmlName" "The TyXML type name of the set." "ContentSet" (s.contentSets.map fun c => (c, c))
  let alts := s.contentSets.map fun c => s!"  | .{ctorName c}, t => Sets.{c} t"
  out := out ++ "/-- Membership, dispatching to the set's own function. -/\ndef ContentSet.contains : ContentSet → Tag → Bool\n" ++
    String.intercalate "\n" alts ++ "\n\n"
  let mut payloadAlts : List String := []
  for name in s.contentSets do
    let tagged ← expandTagged env (.con [] name)
    for (tag, payload) in tagged do
      match payload with
      | some p =>
        let p := canonicalName env p
        if s.contentSets.contains p then
          payloadAlts := payloadAlts ++ [s!"  | .{ctorName name}, .{ctorName tag} => some .{ctorName p}"]
      | none => pure ()
  out := out ++ "/-- TyXML's transparent rule: the content set the payload of a transparent\ntag assigns to that element's children when it appears in the given set\n(`` `A of flow5_without_interactive `` inside `flow5`, so a link in flow\ncontext may not contain interactive content). `none` when the set names the\ntag without a content-set payload (ruling HP-4). -/\ndef ContentSet.transparentPayload : ContentSet → Tag → Option ContentSet\n" ++
    String.intercalate "\n" payloadAlts ++ "\n  | _, _ => none\n\n"
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

def emitAttributes (env : Env) (s : Schema) : Except String String := do
  let mut out := generatedHeader "Attributes"
    ("The attribute-tag universe, the `a_*` constructors of `Html_sigs.T` with\nTyXML's markup spelling and value type, and every named attribute set\nexpanded into a membership function.")
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  out := out ++ emitEnum "Attr" "An attribute tag of the TyXML universe, in the order of its variant name." s.attrs
  out := out ++ emitAll "Attr.all" "Every attribute tag, in constructor order." "Attr" s.attrs
  out := out ++ emitStringFn "Attr.variantName" "The OCaml variant name of the attribute tag." "Attr" (s.attrs.map fun a => (a, a))
  out := out ++ "/-- A coarse classification of an attribute constructor's value; the\nrendered OCaml type beside it is the authority. -/\ninductive AttrValueKind where\n  | presence | string | int | float | bool | char | list | enum | handler | prefixed | other\n  deriving DecidableEq, Repr, Inhabited\n\n"
  out := out ++ "/-- One `a_*` constructor of `Html_sigs.T`. `markup` is the string\n`html_f.ml` emits (a prefix such as `data-` when `isPrefix`); `valueType` is\nthe constructor's argument type as written. -/\nstructure AttrCtor where\n  name : String\n  markup : String\n  isPrefix : Bool\n  tag : Attr\n  valueType : String\n  kind : AttrValueKind\n  deriving Repr, Inhabited\n\n"
  let rows := s.attributes.map fun a =>
    "   { name := \"" ++ a.name ++ "\", markup := \"" ++ a.markup ++ "\", isPrefix := " ++ toString a.isPrefix ++
      ", tag := ." ++ ctorName a.tag ++ ", valueType := \"" ++ a.valueType.replace "\"" "\\\"" ++ "\", kind := ." ++ a.kind ++ " }"
  out := out ++ "/-- Every attribute constructor, in source order. -/\ndef attributeCtors : List AttrCtor :=\n  [" ++
    dropChars (String.intercalate ",\n" rows) 3 ++ "]\n\n"
  for name in s.attrSets do
    let members ← expandName env name
    let some d := env.type? name | throw s!"attribute set {name} vanished"
    out := out ++ emitBoolSet s!"AttrSets.{name}"
      s!"`{name}` (`html_types.mli` line {d.line}): {members.length} of {s.attrs.length} attribute tags." "Attr" members s.attrs
  for (name, members) in s.inlineAttrSets do
    out := out ++ emitBoolSet s!"AttrSets.{name}"
      s!"the attribute row spelled inline in `html_sigs.mli` for `{dropLastChars name "_attrib_inline".length}`: {members.length} of {s.attrs.length} attribute tags." "Attr" members s.attrs
  let allSets := s.attrSets ++ s.inlineAttrSets.map (·.1)
  out := out ++ emitEnum "AttrSet" "A named attribute set, by its TyXML type name (inline rows by element)." allSets
  out := out ++ emitAll "AttrSet.all" "Every attribute set, in constructor order." "AttrSet" allSets
  let alts := allSets.map fun c => s!"  | .{ctorName c}, a => AttrSets.{c} a"
  out := out ++ "/-- Membership, dispatching to the set's own function. -/\ndef AttrSet.contains : AttrSet → Attr → Bool\n" ++
    String.intercalate "\n" alts ++ "\n\n"
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

def emitContentModel (env : Env) (s : Schema) : Except String String := do
  let mut out := generatedHeader "ContentModel"
    ("One row per element constructor of `Html_sigs.T`: its OCaml name, the\nmarkup name, its tag, its constructor kind, whether its content is\ntransparent (TyXML's `'a` content parameter, ruling HP-4), its content set,\nand its attribute set.") ["Whatwg.Html.Schema.Families", "Whatwg.Html.Schema.Attributes"]
  out := out ++ "namespace Whatwg.Html.Schema\n\n"
  out := out ++ "/-- The shape of an element constructor: `star` takes a list of children,\n`unary` exactly one, `nullary` none, `special` a labelled form spelled out in\n`html_sigs.mli`. -/\ninductive ElementKind where\n  | star | unary | nullary | special\n  deriving DecidableEq, Repr, Inhabited\n\n"
  out := out ++ "/-- One element constructor. `content` is `none` only where TyXML gives\nno content type (`svg`, whose children are SVG). -/\nstructure Element where\n  name : String\n  markup : String\n  tag : Tag\n  kind : ElementKind\n  transparent : Bool\n  content : Option ContentSet\n  attribs : Option AttrSet\n  deriving Repr, Inhabited\n\n"
  let rows := s.elements.map fun e =>
    let kind := match e.kind with
      | .star => "star" | .unary => "unary" | .nullary => "nullary" | .special => "special"
    let content := match e.content with | some c => s!"some .{ctorName c}" | none => "none"
    let attribs := match e.attribs with | some a => s!"some .{ctorName a}" | none => "none"
    "   { name := \"" ++ e.name ++ "\", markup := \"" ++ e.markup ++ "\", tag := ." ++ ctorName e.tag ++ ", kind := ." ++ kind ++
      ", transparent := " ++ toString e.transparent ++ ", content := " ++ content ++ ", attribs := " ++ attribs ++ " }"
  out := out ++ "/-- Every element constructor, in the order of `html_sigs.mli`. -/\ndef elements : List Element :=\n  [" ++
    dropChars (String.intercalate ",\n" rows) 3 ++ "]\n\n"
  let firstByTag := s.tags.filterMap fun t =>
    match s.elements.findIdx? (·.tag == t) with
    | some i => some (t, i)
    | none => none
  let alts := firstByTag.map fun (t, i) => s!"  | .{ctorName t} => some {i}"
  out := out ++ "/-- The position in `elements` of the first constructor of a tag; `none`\nfor a tag without one. -/\ndef Tag.elementIndex? : Tag → Option Nat\n" ++
    String.intercalate "\n" alts ++ "\n  | _ => none\n\n"
  out := out ++ "/-- The first constructor of a tag. -/\ndef Tag.element? (t : Tag) : Option Element :=\n  t.elementIndex?.bind (elements[·]?)\n\n"
  out := out ++ s!"/-- The text constructors of `Html_sigs.T` (result tag `PCDATA`): {String.intercalate ", " (s.textCtors.map fun n => "`" ++ n ++ "`")}. -/\ndef textCtors : List String := [{String.intercalate ", " (s.textCtors.map fun n => "\"" ++ n ++ "\"")}]\n\n"
  let _ := env
  out := out ++ "end Whatwg.Html.Schema\n"
  return out

/-! ## Driver -/

def modulePaths : List String :=
  ["Whatwg/Html/Schema/Tags.lean", "Whatwg/Html/Schema/Attributes.lean",
   "Whatwg/Html/Schema/Families.lean", "Whatwg/Html/Schema/ContentModel.lean"]

structure Emitted where
  files : List (String × String)
  schema : Schema

def loadEnv (root : System.FilePath) : IO Env := do
  let typesBytes ← readInput root htmlTypes
  let sigsBytes ← readInput root htmlSigs
  let fBytes ← readInput root htmlF
  let lift {α} (file : String) : Except String α → IO α
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"tyxml schema emit: {file}: {e}"
  let types ← lift "html_types.mli" (parseInterface "lib/html_types.mli" typesBytes)
  let sigs ← lift "html_sigs.mli" (parseInterface "lib/html_sigs.mli" sigsBytes)
  let tagRows ← lift "html_f.ml" (parseEmptyTags "lib/html_f.ml" fBytes)
  return { types, sigs, bindings := bindings fBytes, emptytags := tagRows.map (·.name) }

def emitModules (root : System.FilePath) : IO Emitted := do
  let env ← loadEnv root
  let lift {α} : Except String α → IO α
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"tyxml schema emit: {e}"
  let schema ← lift (extract env)
  let tags ← lift (emitTags env schema)
  let attrs ← lift (emitAttributes env schema)
  let fams ← lift (emitFamilies env schema)
  let model ← lift (emitContentModel env schema)
  return { files := modulePaths.zip [tags, attrs, fams, model], schema }

def summarize (s : Schema) : String :=
  s!"tyxml schema emit: {s.tags.length} tags, {s.elements.length} element constructors ({s.textCtors.length} text constructors), " ++
  s!"{s.contentSets.length} content sets, {s.attrs.length} attribute tags, {s.attributes.length} attribute constructors, " ++
  s!"{s.attrSets.length + s.inlineAttrSets.length} attribute sets, {s.voidTags.length} void tags\n"

def write (root : System.FilePath) : IO UInt32 := do
  let code ← Gates.TyxmlSchema.write root
  if code != 0 then return code
  let e ← emitModules root
  for (path, text) in e.files do
    IO.FS.writeFile (root / path) text
    IO.println s!"WROTE {path}"
  IO.print (summarize e.schema)
  return 0

def check (root : System.FilePath) : IO UInt32 := do
  let code ← Gates.TyxmlSchema.check root
  if code != 0 then return code
  let e ← emitModules root
  let mut failures : List String := []
  for (path, text) in e.files do
    let file := root / path
    unless ← file.pathExists do
      failures := failures ++ [s!"missing generated module {path}; run `lake exe tyxmlschema --write`"]
      continue
    let committed ← IO.FS.readFile file
    if committed != text then
      let firstDiff := ((lines text).zip (lines committed)).find? (fun (a, b) => a != b)
      failures := failures ++ [s!"drift in {path}" ++
        (match firstDiff with
         | some (a, b) => s!": regenerated `{a}` vs committed `{b}`"
         | none => s!": line counts differ ({(lines text).length} regenerated, {(lines committed).length} committed)")]
  if failures.isEmpty then
    IO.print (summarize e.schema)
    IO.println "PASS tyxml schema emit: the four generated Whatwg.Html.Schema modules are byte-identical to a fresh emission"
    return 0
  IO.eprintln s!"FAIL tyxml schema emit: {failures.length} problem(s)"
  for f in failures do IO.eprintln s!"  {f}"
  return 1

def usage : String :=
  "usage: lake exe tyxmlschema          check the projection and the generated Whatwg.Html.Schema modules\n" ++
  "       lake exe tyxmlschema --write  regenerate both from the sealed TyXML sources"

/-- Command-line entry, invoked by `bin/TyxmlSchema.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] => check root
  | ["--write"] => write root
  | _ =>
    IO.eprintln usage
    return 2

end Gates.TyxmlSchemaEmit
