import Gates.Common
import Gates.Sha256

/-!
# Gates.TyxmlSchema

The TyXML schema projection: `generated/tyxml-html-schema.tsv`, one row per
type declaration of `html_types.mli`, one per value declaration of
`html_sigs.mli`, and one per void tag of `html_f.ml`'s `emptytags`, read
from the sealed bytes under `vendor/tyxml-d2916535/`. Every row carries the
line and the SHA-256 of the declaration's byte span, so a generated
`Whatwg.Html.Schema` declaration can anchor to the pinned text exactly as a
census row anchors to `index.bs`.

`lake exe tyxmlschema` regenerates the projection in memory, refuses inputs
whose digests are not the pinned ones, and compares bytes with the committed
file. `lake exe tyxmlschema --write` writes it. The projection is generated:
repair the generator or re-pin the bytes, never the file by hand.

## What is parsed

A subset of OCaml interface syntax sufficient for the three files at the pin,
and nothing more: `type` and `and` declarations with parameters and either a
core type, an ordinary variant, or no body; `val` declarations; `module`,
`module type`, `open`, and `include` items, tracked only to record the module
path of each `val`; `[@@ ... ]` and `[@ ... ]` attributes, kept verbatim.
Core types cover type variables, constructor applications with dotted paths,
tuples, labelled and optional arrows, polymorphic-variant rows (`[ ]`,
`[< ]`, `[> ]`, `of` payloads, inheritance, lower bounds after `>`), and
`as` aliases. An unhandled shape is a parse error naming the byte offset, and
the gate fails: silently skipping a declaration would let the schema drift.

Comments are skipped with OCaml's nesting and string rules. `html_f.ml` is
an implementation file; only the bytes from `let emptytags =` to the closing
bracket are lexed.

## Representation

The file is a `ByteArray`, offsets are `Nat`, every loop is fuel-bounded by
a size the data carries, and classification is ASCII-first, following the
census generator and the R0 measurements it cites. Rendering of a parsed
type is a single canonical line, so the projection is diffable and
re-parseable by the H2 generator through this module's own parser.
-/

namespace Gates.TyxmlSchema

open Gates.Common

/-! ## Inputs -/

/-- A sealed input: its path relative to the repository root and the SHA-256
recorded for it in `generated/vendor-manifest.tsv` at the pin. -/
structure Input where
  relative : String
  digest : String

def vendorTree : String := "vendor/tyxml-d2916535"

def htmlTypes : Input :=
  { relative := vendorTree ++ "/lib/html_types.mli"
    digest := "0031c56d5bcc048b11ba47fd4d840235bfc52ced9722269510818c14004b3df3" }

def htmlSigs : Input :=
  { relative := vendorTree ++ "/lib/html_sigs.mli"
    digest := "5cf48b32cc19f4c9b400f388a749b1a8c0f4e5b058ae88e21ca568a899622f9b" }

def htmlF : Input :=
  { relative := vendorTree ++ "/lib/html_f.ml"
    digest := "4b777d7c2716e8e39c306a2c4018f3da7aee3bf7678ff3966bda6a441c793c57" }

def inputs : List Input := [htmlTypes, htmlSigs, htmlF]

def projectionPath (root : System.FilePath) : System.FilePath :=
  root / "generated" / "tyxml-html-schema.tsv"

/-! ## Byte primitives -/

@[inline] def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

@[inline] def isSpace (b : UInt8) : Bool :=
  b == 0x20 || b == 0x0a || b == 0x09 || b == 0x0d

@[inline] def isLower (b : UInt8) : Bool := 0x61 ≤ b && b ≤ 0x7a
@[inline] def isUpper (b : UInt8) : Bool := 0x41 ≤ b && b ≤ 0x5a
@[inline] def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39
@[inline] def isIdentStart (b : UInt8) : Bool := isLower b || isUpper b || b == 0x5f
@[inline] def isIdentChar (b : UInt8) : Bool := isIdentStart b || isDigit b

/-- The bytes `[b, e)` as text; invalid UTF-8 renders as a marker rather than
panicking, and the lexer only ever slices ASCII-delimited spans. -/
def slice (bs : ByteArray) (b e : Nat) : String :=
  (String.fromUTF8? (bs.extract b e)).getD "<invalid utf-8>"

private def matchAux (bs pat : ByteArray) (i j : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.ble pat.size j then true
    else if byteAt bs (i + j) == byteAt pat j then matchAux bs pat i (j + 1) fuel
    else false

def matchesAt (bs pat : ByteArray) (i : Nat) : Bool :=
  Nat.ble (i + pat.size) bs.size && matchAux bs pat i 0 (pat.size + 1)

private def findAux (bs pat : ByteArray) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if !Nat.ble (i + pat.size) bs.size then none
    else if matchesAt bs pat i then some i
    else findAux bs pat (i + 1) fuel

/-- The first occurrence of `pat` at or after `start`. -/
def findFrom (bs pat : ByteArray) (start : Nat) : Option Nat :=
  findAux bs pat start (bs.size + 1)

private def findByteAux (bs : ByteArray) (b : UInt8) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if Nat.ble bs.size i then none
    else if byteAt bs i == b then some i
    else findByteAux bs b (i + 1) fuel

def findByte (bs : ByteArray) (b : UInt8) (start : Nat) : Option Nat :=
  findByteAux bs b start (bs.size + 1)

private def newlinesAux (bs : ByteArray) (i upto acc : Nat) : Nat → Nat
  | 0 => acc
  | fuel + 1 =>
    if Nat.ble upto i then acc
    else newlinesAux bs (i + 1) upto (if byteAt bs i == 0x0a then acc + 1 else acc) fuel

/-- One-based line number of byte offset `i`. -/
def lineOf (bs : ByteArray) (i : Nat) : Nat := newlinesAux bs 0 i 0 (bs.size + 1) + 1

/-! ## Tokens -/

inductive TokKind where
  | ident | tag | tvar | str | num | sym
  deriving DecidableEq, Repr, Inhabited

structure Token where
  kind : TokKind
  text : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

private def scanIdentAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 => if isIdentChar (byteAt bs i) then scanIdentAux bs (i + 1) fuel else i

/-- End of the identifier run starting at `i`. -/
def scanIdent (bs : ByteArray) (i : Nat) : Nat := scanIdentAux bs i (bs.size + 1)

private def scanPathAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 =>
    let j := scanIdent bs i
    if byteAt bs j == 0x2e && isIdentStart (byteAt bs (j + 1)) then scanPathAux bs (j + 1) fuel
    else j

/-- End of a possibly dotted path (`Xml.W.ft`) starting at `i`. -/
def scanPath (bs : ByteArray) (i : Nat) : Nat := scanPathAux bs i (bs.size + 1)

private def scanDigitsAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 => if isDigit (byteAt bs i) then scanDigitsAux bs (i + 1) fuel else i

/-- Offset just past the string literal whose opening quote is at `i - 1`. -/
private def skipStringAux (bs : ByteArray) (i : Nat) : Nat → Except String Nat
  | 0 => .error "string literal scan exhausted fuel"
  | fuel + 1 =>
    if Nat.ble bs.size i then .error "unterminated string literal"
    else
      let b := byteAt bs i
      if b == 0x22 then .ok (i + 1)
      else if b == 0x5c then skipStringAux bs (i + 2) fuel
      else skipStringAux bs (i + 1) fuel

def skipString (bs : ByteArray) (i : Nat) : Except String Nat :=
  skipStringAux bs i (bs.size + 1)

/-- Offset just past the comment opening at `i` (which holds `(*`), honouring
nesting and string literals inside comments as OCaml's lexer does. -/
private def skipCommentAux (bs : ByteArray) (i depth : Nat) : Nat → Except String Nat
  | 0 => .error "comment scan exhausted fuel"
  | fuel + 1 =>
    if Nat.ble bs.size i then .error "unterminated comment"
    else if byteAt bs i == 0x28 && byteAt bs (i + 1) == 0x2a then
      skipCommentAux bs (i + 2) (depth + 1) fuel
    else if byteAt bs i == 0x2a && byteAt bs (i + 1) == 0x29 then
      if depth ≤ 1 then .ok (i + 2) else skipCommentAux bs (i + 2) (depth - 1) fuel
    else if byteAt bs i == 0x27 && byteAt bs (i + 1) == 0x22 && byteAt bs (i + 2) == 0x27 then
      skipCommentAux bs (i + 3) depth fuel
    else if byteAt bs i == 0x22 then
      match skipString bs (i + 1) with
      | .ok j => skipCommentAux bs j depth fuel
      | .error e => .error e
    else skipCommentAux bs (i + 1) depth fuel

def skipComment (bs : ByteArray) (i : Nat) : Except String Nat :=
  skipCommentAux bs i 0 (bs.size + 1)

/-- Multi-byte symbols first, then single bytes; `0` when no symbol starts
at `i`. -/
def symbolLength (bs : ByteArray) (i : Nat) : Nat :=
  let b0 := byteAt bs i
  let b1 := byteAt bs (i + 1)
  let b2 := byteAt bs (i + 2)
  if b0 == 0x5b && b1 == 0x40 && b2 == 0x40 then 3        -- [@@
  else if b0 == 0x5b && (b1 == 0x3c || b1 == 0x3e || b1 == 0x3d || b1 == 0x40) then 2  -- [< [> [= [@
  else if b0 == 0x2d && b1 == 0x3e then 2                   -- ->
  else if b0 == 0x3a && b1 == 0x3d then 2                   -- :=
  else if b0 == 0x3a && b1 == 0x3a then 2                   -- ::
  else if b0 == 0x40 && b1 == 0x40 then 2                   -- @@
  else if "[](){}|,:=*?~.;<>+-@!".toList.any (fun c => c.toNat == b0.toNat) then 1
  else 0

private def lexAux (bs : ByteArray) (stop i : Nat) (acc : Array Token) :
    Nat → Except String (Array Token)
  | 0 => .error "lexer exhausted fuel"
  | fuel + 1 =>
    if Nat.ble stop i then .ok acc
    else
      let b := byteAt bs i
      if isSpace b then lexAux bs stop (i + 1) acc fuel
      else if b == 0x28 && byteAt bs (i + 1) == 0x2a then
        match skipComment bs i with
        | .ok j => lexAux bs stop j acc fuel
        | .error e => .error s!"{e} (comment opened at byte {i})"
      else if b == 0x22 then
        match skipString bs (i + 1) with
        | .ok j =>
          lexAux bs stop j (acc.push { kind := .str, text := slice bs (i + 1) (j - 1), start := i, stop := j }) fuel
        | .error e => .error s!"{e} (opened at byte {i})"
      else if b == 0x60 && isIdentStart (byteAt bs (i + 1)) then
        let j := scanIdent bs (i + 1)
        lexAux bs stop j (acc.push { kind := .tag, text := slice bs (i + 1) j, start := i, stop := j }) fuel
      else if b == 0x27 && isIdentStart (byteAt bs (i + 1)) then
        let j := scanIdent bs (i + 1)
        lexAux bs stop j (acc.push { kind := .tvar, text := slice bs (i + 1) j, start := i, stop := j }) fuel
      else if isIdentStart b then
        let j := scanPath bs i
        lexAux bs stop j (acc.push { kind := .ident, text := slice bs i j, start := i, stop := j }) fuel
      else if isDigit b then
        let j := scanDigitsAux bs i (bs.size + 1)
        lexAux bs stop j (acc.push { kind := .num, text := slice bs i j, start := i, stop := j }) fuel
      else
        let n := symbolLength bs i
        if n == 0 then .error s!"unexpected byte {b} at offset {i} (line {lineOf bs i})"
        else lexAux bs stop (i + n) (acc.push { kind := .sym, text := slice bs i (i + n), start := i, stop := i + n }) fuel

/-- Tokens of the bytes `[start, stop)`. -/
def lexRange (bs : ByteArray) (start stop : Nat) : Except String (Array Token) :=
  lexAux bs stop start #[] (bs.size + 1)

def lex (bs : ByteArray) : Except String (Array Token) := lexRange bs 0 bs.size

/-! ## Types -/

mutual
  /-- A parsed OCaml core type, in the subset the pinned files use. -/
  inductive Ty where
    | var (name : String)
    | con (args : List Ty) (name : String)
    | tuple (items : List Ty)
    /-- `label` is empty for a plain arrow, `?x` for an optional argument,
    `x` for a labelled one. -/
    | arrow (label : String) (dom cod : Ty)
    /-- `kind` is `[`, `[<`, or `[>`; `lower` the tags after `>`. -/
    | row (kind : String) (fields : List RowField) (lower : List String)
    | alias (t : Ty) (v : String)
    | annot (t : Ty) (attr : String)
    | variant (ctors : List (String × Option Ty))
    | abstract
  inductive RowField where
    | tag (name : String) (payload : Option Ty)
    | inherit (t : Ty)
end

instance : Inhabited Ty := ⟨.abstract⟩
instance : Inhabited RowField := ⟨.inherit .abstract⟩

mutual
  def render : Nat → Ty → String
    | 0, _ => "<fuel>"
    | fuel + 1, t =>
      match t with
      | .var n => "'" ++ n
      | .con [] n => n
      | .con [a] n => renderAtom fuel a ++ " " ++ n
      | .con args n => "(" ++ renderList fuel args ++ ") " ++ n
      | .tuple items => renderTuple fuel items
      | .arrow label dom cod =>
        (if label.isEmpty then "" else label ++ ":") ++ renderArrowDom fuel dom ++ " -> " ++ render fuel cod
      | .row kind fields lower =>
        kind ++ " " ++ renderFields fuel fields ++
          (if lower.isEmpty then "" else " > " ++ String.intercalate " " (lower.map ("`" ++ ·))) ++ " ]"
      | .alias t v => renderArrowDom fuel t ++ " as '" ++ v
      | .annot t a => render fuel t ++ " [@" ++ a ++ "]"
      | .variant ctors => renderCtors fuel ctors
      | .abstract => "<abstract>"
  def renderAtom : Nat → Ty → String
    | 0, _ => "<fuel>"
    | fuel + 1, t =>
      match t with
      | .arrow .. | .tuple .. | .alias .. => "(" ++ render fuel t ++ ")"
      | _ => render fuel t
  def renderArrowDom : Nat → Ty → String
    | 0, _ => "<fuel>"
    | fuel + 1, t =>
      match t with
      | .arrow .. | .alias .. => "(" ++ render fuel t ++ ")"
      | _ => render fuel t
  def renderList : Nat → List Ty → String
    | 0, _ => "<fuel>"
    | _, [] => ""
    | fuel + 1, [t] => render fuel t
    | fuel + 1, t :: rest => render fuel t ++ ", " ++ renderList fuel rest
  def renderTuple : Nat → List Ty → String
    | 0, _ => "<fuel>"
    | _, [] => ""
    | fuel + 1, [t] => renderAtom fuel t
    | fuel + 1, t :: rest => renderAtom fuel t ++ " * " ++ renderTuple fuel rest
  def renderFields : Nat → List RowField → String
    | 0, _ => "<fuel>"
    | _, [] => ""
    | fuel + 1, [f] => renderField fuel f
    | fuel + 1, f :: rest => renderField fuel f ++ " | " ++ renderFields fuel rest
  def renderField : Nat → RowField → String
    | 0, _ => "<fuel>"
    | fuel + 1, f =>
      match f with
      | .tag n none => "`" ++ n
      | .tag n (some p) => "`" ++ n ++ " of " ++ render fuel p
      | .inherit t => render fuel t
  def renderCtors : Nat → List (String × Option Ty) → String
    | 0, _ => "<fuel>"
    | _, [] => ""
    | fuel + 1, (n, none) :: rest => "| " ++ n ++ (if rest.isEmpty then "" else " ") ++ renderCtors fuel rest
    | fuel + 1, (n, some p) :: rest =>
      "| " ++ n ++ " of " ++ render fuel p ++ (if rest.isEmpty then "" else " ") ++ renderCtors fuel rest
end

/-- Rendering fuel: no type in the pinned files nests a thousand deep. -/
def renderFuel : Nat := 1000

/-- The result type after every arrow. -/
def resultOf : Ty → Nat → Ty
  | t, 0 => t
  | .arrow _ _ cod, fuel + 1 => resultOf cod fuel
  | t, _ => t

/-- The outermost constructor name, if the type is an application. -/
def headCon : Ty → Option String
  | .con _ n => some n
  | .annot t _ => headCon' t
  | _ => none
where headCon' : Ty → Option String
  | .con _ n => some n
  | _ => none

/-! ## Parser -/

structure P where
  toks : Array Token
  bs : ByteArray

def eofToken : Token := { kind := .sym, text := "<eof>", start := 0, stop := 0 }

def P.tok (p : P) (i : Nat) : Token := p.toks.getD i eofToken
def P.isSym (p : P) (i : Nat) (s : String) : Bool :=
  let t := p.tok i; t.kind == .sym && t.text == s
def P.isIdent (p : P) (i : Nat) (s : String) : Bool :=
  let t := p.tok i; t.kind == .ident && t.text == s
def P.atEnd (p : P) (i : Nat) : Bool := Nat.ble p.toks.size i

def keywords : List String :=
  ["type", "and", "val", "of", "module", "sig", "end", "open", "include", "with",
   "as", "let", "in", "mutable", "private", "struct", "functor", "constraint"]

def P.isPlainIdent (p : P) (i : Nat) : Bool :=
  let t := p.tok i; t.kind == .ident && !keywords.contains t.text

def P.err {α : Type} (p : P) (i : Nat) (msg : String) : Except String α :=
  let t := p.tok i
  .error s!"{msg} at token {i} `{t.text}` (byte {t.start}, line {lineOf p.bs t.start})"

/-- Text of an attribute's tokens, quoted strings re-quoted. -/
private def tokenText (t : Token) : String :=
  if t.kind == .str then "\"" ++ t.text ++ "\""
  else if t.kind == .tag then "`" ++ t.text
  else if t.kind == .tvar then "'" ++ t.text
  else t.text

private def isOpenBracket (t : Token) : Bool :=
  t.kind == .sym && (t.text == "[" || t.text == "[<" || t.text == "[>" || t.text == "[=" ||
    t.text == "[@" || t.text == "[@@")

private def skipAttrAux (p : P) (i depth : Nat) (acc : List String) :
    Nat → Except String (String × Nat)
  | 0 => p.err i "attribute scan exhausted fuel"
  | fuel + 1 =>
    if p.atEnd i then p.err i "unterminated attribute"
    else
      let t := p.tok i
      if isOpenBracket t then skipAttrAux p (i + 1) (depth + 1) (acc ++ [tokenText t]) fuel
      else if p.isSym i "]" then
        if depth ≤ 1 then .ok (String.intercalate " " acc, i + 1)
        else skipAttrAux p (i + 1) (depth - 1) (acc ++ ["]"]) fuel
      else skipAttrAux p (i + 1) depth (acc ++ [tokenText t]) fuel

/-- The attribute starting at `i` (a `[@` or `[@@` token): its inner text and
the index after its closing bracket. -/
def skipAttr (p : P) (i : Nat) : Except String (String × Nat) :=
  skipAttrAux p (i + 1) 1 [] (p.toks.size + 1)

private def isCtorName (t : Token) : Bool :=
  t.kind == .ident && !t.text.toList.contains '.' &&
    (match t.text.toList with | c :: _ => c.isUpper | [] => false)

mutual
  def pTyp (p : P) : Nat → Nat → Except String (Ty × Nat)
    | 0, i => p.err i "parser fuel exhausted"
    | fuel + 1, i => do
      let (label, i) :=
        if p.isSym i "?" && (p.tok (i + 1)).kind == .ident && p.isSym (i + 2) ":" then
          ("?" ++ (p.tok (i + 1)).text, i + 3)
        else if p.isSym i "~" && (p.tok (i + 1)).kind == .ident && p.isSym (i + 2) ":" then
          ((p.tok (i + 1)).text, i + 3)
        else if p.isPlainIdent i && p.isSym (i + 1) ":" then
          ((p.tok i).text, i + 2)
        else ("", i)
      let (dom, j) ← pTuple p fuel i
      let (t, j) ←
        if p.isSym j "->" then do
          let (cod, k) ← pTyp p fuel (j + 1)
          pure (Ty.arrow label dom cod, k)
        else if label.isEmpty then pure (dom, j)
        else p.err j "labelled argument without an arrow"
      if p.isIdent j "as" && (p.tok (j + 1)).kind == .tvar then
        pure (Ty.alias t (p.tok (j + 1)).text, j + 2)
      else pure (t, j)
  def pTuple (p : P) : Nat → Nat → Except String (Ty × Nat)
    | 0, i => p.err i "parser fuel exhausted"
    | fuel + 1, i => do
      let (first, j) ← pApp p fuel i
      let (rest, k) ← pTupleRest p fuel j []
      if rest.isEmpty then pure (first, k) else pure (Ty.tuple (first :: rest), k)
  def pTupleRest (p : P) : Nat → Nat → List Ty → Except String (List Ty × Nat)
    | 0, i, _ => p.err i "parser fuel exhausted"
    | fuel + 1, i, acc =>
      if p.isSym i "*" then do
        let (t, j) ← pApp p fuel (i + 1)
        pTupleRest p fuel j (acc ++ [t])
      else pure (acc, i)
  def pApp (p : P) : Nat → Nat → Except String (Ty × Nat)
    | 0, i => p.err i "parser fuel exhausted"
    | fuel + 1, i => do
      let (args, j) ← pSimple p fuel i
      pPostfix p fuel args j
  def pPostfix (p : P) : Nat → List Ty → Nat → Except String (Ty × Nat)
    | 0, _, i => p.err i "parser fuel exhausted"
    | fuel + 1, args, i =>
      if p.isPlainIdent i && !p.isSym (i + 1) ":" then
        pPostfix p fuel [Ty.con args (p.tok i).text] (i + 1)
      else if p.isSym i "[@" then do
        let (a, j) ← skipAttr p i
        match args with
        | [t] => pPostfix p fuel [Ty.annot t a] j
        | _ => p.err i "attribute on a type argument list"
      else
        match args with
        | [t] => pure (t, i)
        | _ => p.err i "type argument list without a constructor"
  def pSimple (p : P) : Nat → Nat → Except String (List Ty × Nat)
    | 0, i => p.err i "parser fuel exhausted"
    | fuel + 1, i =>
      let t := p.tok i
      if t.kind == .tvar then pure ([Ty.var t.text], i + 1)
      else if p.isPlainIdent i then pure ([Ty.con [] t.text], i + 1)
      else if p.isSym i "(" then do
        let (first, j) ← pTyp p fuel (i + 1)
        let (rest, k) ← pParenRest p fuel j []
        if p.isSym k ")" then pure (first :: rest, k + 1) else p.err k "expected `)`"
      else if p.isSym i "[" || p.isSym i "[<" || p.isSym i "[>" then do
        let (r, j) ← pRow p fuel t.text (i + 1)
        pure ([r], j)
      else p.err i "expected a type"
  def pParenRest (p : P) : Nat → Nat → List Ty → Except String (List Ty × Nat)
    | 0, i, _ => p.err i "parser fuel exhausted"
    | fuel + 1, i, acc =>
      if p.isSym i "," then do
        let (t, j) ← pTyp p fuel (i + 1)
        pParenRest p fuel j (acc ++ [t])
      else pure (acc, i)
  def pRow (p : P) : Nat → String → Nat → Except String (Ty × Nat)
    | 0, _, i => p.err i "parser fuel exhausted"
    | fuel + 1, kind, i => do
      let i := if p.isSym i "|" then i + 1 else i
      let (fields, j) ← pFields p fuel i []
      let (lower, k) ← if p.isSym j ">" then pLower p fuel (j + 1) [] else pure ([], j)
      if p.isSym k "]" then pure (Ty.row kind fields lower, k + 1) else p.err k "expected `]`"
  def pFields (p : P) : Nat → Nat → List RowField → Except String (List RowField × Nat)
    | 0, i, _ => p.err i "parser fuel exhausted"
    | fuel + 1, i, acc =>
      if p.isSym i "]" || p.isSym i ">" then pure (acc, i)
      else do
        let (f, j) ← pField p fuel i
        if p.isSym j "|" then pFields p fuel (j + 1) (acc ++ [f]) else pure (acc ++ [f], j)
  def pField (p : P) : Nat → Nat → Except String (RowField × Nat)
    | 0, i => p.err i "parser fuel exhausted"
    | fuel + 1, i =>
      let t := p.tok i
      if t.kind == .tag then
        if p.isIdent (i + 1) "of" then do
          let (payload, j) ← pTyp p fuel (i + 2)
          pure (RowField.tag t.text (some payload), j)
        else pure (RowField.tag t.text none, i + 1)
      else do
        let (ty, j) ← pTyp p fuel i
        pure (RowField.inherit ty, j)
  def pLower (p : P) : Nat → Nat → List String → Except String (List String × Nat)
    | 0, i, _ => p.err i "parser fuel exhausted"
    | fuel + 1, i, acc =>
      if (p.tok i).kind == .tag then pLower p fuel (i + 1) (acc ++ [(p.tok i).text])
      else pure (acc, i)
end

/-- An ordinary variant body: `| A of t | B ...`. -/
private def pCtorsAux (p : P) (i : Nat) (acc : List (String × Option Ty)) :
    Nat → Except String (Ty × Nat)
  | 0 => p.err i "parser fuel exhausted"
  | fuel + 1 =>
    let i := if p.isSym i "|" then i + 1 else i
    if isCtorName (p.tok i) then
      let name := (p.tok i).text
      if p.isIdent (i + 1) "of" then do
        let (payload, j) ← pTyp p (p.toks.size + 1) (i + 2)
        let acc := acc ++ [(name, some payload)]
        if p.isSym j "|" then pCtorsAux p j acc fuel else pure (Ty.variant acc, j)
      else
        let acc := acc ++ [(name, none)]
        if p.isSym (i + 1) "|" then pCtorsAux p (i + 1) acc fuel else pure (Ty.variant acc, i + 1)
    else if acc.isEmpty then p.err i "expected a constructor"
    else pure (Ty.variant acc, i)

def pTypeBody (p : P) (i : Nat) : Except String (Ty × Nat) :=
  if p.isSym i "|" || (isCtorName (p.tok i) && (p.isIdent (i + 1) "of" || p.isSym (i + 1) "|")) then
    pCtorsAux p i [] (p.toks.size + 1)
  else pTyp p (p.toks.size + 1) i

/-- One type parameter with its variance, rendered as written. -/
private def pParam (p : P) (i : Nat) : Except String (String × Nat) :=
  let (v, i) := if p.isSym i "+" then ("+", i + 1) else if p.isSym i "-" then ("-", i + 1) else ("", i)
  if (p.tok i).kind == .tvar then .ok (v ++ "'" ++ (p.tok i).text, i + 1)
  else p.err i "expected a type parameter"

private def pParamsAux (p : P) (i : Nat) (acc : List String) : Nat → Except String (List String × Nat)
  | 0 => p.err i "parser fuel exhausted"
  | fuel + 1 => do
    let (s, j) ← pParam p i
    let acc := acc ++ [s]
    if p.isSym j "," then pParamsAux p (j + 1) acc fuel
    else if p.isSym j ")" then pure (acc, j + 1)
    else p.err j "expected `,` or `)` in type parameters"

/-- Type parameters before a type name: nothing, one, or a parenthesised list. -/
def pParams (p : P) (i : Nat) : Except String (String × Nat) :=
  if p.isSym i "(" then do
    let (ps, j) ← pParamsAux p (i + 1) [] (p.toks.size + 1)
    pure ("(" ++ String.intercalate ", " ps ++ ")", j)
  else if (p.tok i).kind == .tvar || p.isSym i "+" || p.isSym i "-" then pParam p i
  else pure ("", i)

private def pAttrsAux (p : P) (i : Nat) (acc : List String) : Nat → Except String (List String × Nat)
  | 0 => p.err i "parser fuel exhausted"
  | fuel + 1 =>
    if p.isSym i "[@@" then do
      let (a, j) ← skipAttr p i
      pAttrsAux p j (acc ++ [a]) fuel
    else pure (acc, i)

/-- Consecutive `[@@ ... ]` item attributes after a declaration. -/
def pAttrs (p : P) (i : Nat) : Except String (List String × Nat) :=
  pAttrsAux p i [] (p.toks.size + 1)

/-! ## Declarations -/

structure Decl where
  kind : String
  file : String
  line : Nat
  spanStart : Nat
  spanStop : Nat
  modulePath : String
  name : String
  params : String
  body : String
  attrs : String
  /-- Head constructor of the type after every arrow; summary-only, not a
  projection column. -/
  result : String
  /-- The parsed type, for the schema emitter; `.abstract` for a row without
  a body. Not a projection column. -/
  ty : Ty := .abstract
  deriving Inhabited

private def stopKeyword (t : Token) : Bool :=
  t.kind == .ident &&
    (t.text == "val" || t.text == "type" || t.text == "module" || t.text == "open" ||
     t.text == "include" || t.text == "end" || t.text == "sig")

/-- Scan a `module` item from just after its name. Returns `some j` with `j`
after a `sig` that opens a signature body, or `none` with the index of the
next item when the module has no inline signature. `with module`, `with
type`, `and module`, `and type` pairs inside constraints are consumed. -/
private def scanModuleAux (p : P) (i : Nat) : Nat → Except String (Option Nat × Nat)
  | 0 => p.err i "module scan exhausted fuel"
  | fuel + 1 =>
    if p.atEnd i then pure (none, i)
    else if p.isIdent i "sig" then pure (some (i + 1), i + 1)
    else if (p.isIdent i "with" || p.isIdent i "and") &&
        (p.isIdent (i + 1) "module" || p.isIdent (i + 1) "type") then
      scanModuleAux p (i + 2) fuel
    else if stopKeyword (p.tok i) then pure (none, i)
    else scanModuleAux p (i + 1) fuel

private def modulePathOf (stack : List String) : String :=
  String.intercalate "." stack.reverse

private def driveAux (p : P) (file : String) (i : Nat) (stack : List String) (acc : Array Decl) :
    Nat → Except String (Array Decl)
  | 0 => p.err i "declaration scan exhausted fuel"
  | fuel + 1 =>
    if p.atEnd i then
      if stack.isEmpty then pure acc else p.err i s!"unclosed module {modulePathOf stack}"
    else if p.isIdent i "type" || p.isIdent i "and" then do
      let start := (p.tok i).start
      let (params, j) ← pParams p (i + 1)
      unless (p.tok j).kind == .ident do p.err j "expected a type name"
      let name := (p.tok j).text
      let (body, k) ←
        if p.isSym (j + 1) "=" then pTypeBody p (j + 2) else pure (Ty.abstract, j + 1)
      let (attrs, k) ← pAttrs p k
      let stop := (p.tok (k - 1)).stop
      let d : Decl :=
        { kind := "type", file, line := lineOf p.bs start, spanStart := start, spanStop := stop
          modulePath := modulePathOf stack, name, params
          body := render renderFuel body, attrs := String.intercalate "; " attrs
          result := (headCon (resultOf body renderFuel)).getD "", ty := body }
      driveAux p file k stack (acc.push d) fuel
    else if p.isIdent i "val" then do
      let start := (p.tok i).start
      unless (p.tok (i + 1)).kind == .ident do p.err (i + 1) "expected a value name"
      let name := (p.tok (i + 1)).text
      unless p.isSym (i + 2) ":" do p.err (i + 2) "expected `:`"
      let (ty, k) ← pTyp p (p.toks.size + 1) (i + 3)
      let (attrs, k) ← pAttrs p k
      let stop := (p.tok (k - 1)).stop
      let d : Decl :=
        { kind := "val", file, line := lineOf p.bs start, spanStart := start, spanStop := stop
          modulePath := modulePathOf stack, name, params := ""
          body := render renderFuel ty, attrs := String.intercalate "; " attrs
          result := (headCon (resultOf ty renderFuel)).getD "", ty := ty }
      driveAux p file k stack (acc.push d) fuel
    else if p.isIdent i "module" then do
      let nameAt := if p.isIdent (i + 1) "type" then i + 2 else i + 1
      unless (p.tok nameAt).kind == .ident do p.err nameAt "expected a module name"
      let name := (p.tok nameAt).text
      let (opened, j) ← scanModuleAux p (nameAt + 1) (p.toks.size + 1)
      match opened with
      | some j => driveAux p file j (name :: stack) acc fuel
      | none => driveAux p file j stack acc fuel
    else if p.isIdent i "end" then
      match stack with
      | _ :: rest => driveAux p file (i + 1) rest acc fuel
      | [] => p.err i "`end` without an open signature"
    else if p.isIdent i "open" || p.isIdent i "include" then
      driveAux p file (i + 2) stack acc fuel
    else p.err i "unexpected token at item level"

/-- Every declaration of an interface file, in source order. -/
def parseInterface (file : String) (bs : ByteArray) : Except String (Array Decl) := do
  let toks ← lex bs
  driveAux { toks, bs } file 0 [] #[] (toks.size + 1)

/-- The `emptytags` rows of `html_f.ml`: one per string in the list, all
anchored to the span of the list itself. -/
def parseEmptyTags (file : String) (bs : ByteArray) : Except String (Array Decl) := do
  let pat := "let emptytags =".toUTF8
  let some start := findFrom bs pat 0 | .error s!"{file}: `let emptytags =` not found"
  let some close := findByte bs 0x5d (start + pat.size) | .error s!"{file}: emptytags list not closed"
  let stop := close + 1
  let toks ← lexRange bs start stop
  let p : P := { toks, bs }
  -- let emptytags = [ "a" ; "b" ; ... ]
  unless p.isIdent 0 "let" && p.isIdent 1 "emptytags" && p.isSym 2 "=" && p.isSym 3 "[" do
    p.err 0 "unexpected shape of the emptytags binding"
  let mut rows : Array Decl := #[]
  let mut i := 4
  let mut expectString := true
  for _ in [0:toks.size + 1] do
    if p.isSym i "]" then break
    if expectString then
      unless (p.tok i).kind == .str do p.err i "expected a tag string"
      rows := rows.push
        { kind := "emptytag", file, line := lineOf bs start, spanStart := start, spanStop := stop
          modulePath := "", name := (p.tok i).text, params := "", body := "", attrs := ""
          result := "" }
    else
      unless p.isSym i ";" do p.err i "expected `;`"
    expectString := !expectString
    i := i + 1
  unless p.isSym i "]" do p.err i "expected `]` closing the emptytags list"
  return rows

/-! ## Projection -/

/-- Refuse a field that would break the row structure. -/
private def checkField (row : Decl) (field : String) : Except String String :=
  if field.toList.any (fun c => c == '\t' || c == '\n' || c == '\r') then
    .error s!"{row.file}:{row.line} {row.name}: a field contains a tab or newline"
  else .ok field

def renderRow (bs : ByteArray) (d : Decl) : Except String String := do
  let digest := Gates.Sha256.hexDigest (bs.extract d.spanStart d.spanStop)
  let fields ← [d.kind, d.file, toString d.line, digest, d.modulePath, d.name, d.params, d.body, d.attrs].mapM
    (checkField d)
  return String.intercalate "\t" fields ++ "\n"

/-- Whether a `val` row of the main signature constructs an element: its
result is an `elt`, or one of the `star`, `unary`, `nullary` constructor
shapes `Html_sigs.T` abbreviates. -/
def isElementRow (d : Decl) : Bool :=
  d.kind == "val" && d.modulePath == "T" &&
    (d.result == "elt" || d.result == "star" || d.result == "unary" || d.result == "nullary")

/-- Whether a `val` row of the main signature constructs an attribute. -/
def isAttributeRow (d : Decl) : Bool :=
  d.kind == "val" && d.modulePath == "T" && d.name.startsWith "a_" && d.result == "attrib"

structure Generated where
  text : String
  types : Nat
  vals : Nat
  elements : Nat
  attributes : Nat
  emptytags : Nat

def header (rows : Nat) : String :=
  s!"#tyxml-html-schema format=1 generator=Gates.TyxmlSchema inputs={htmlTypes.relative},{htmlSigs.relative},{htmlF.relative} " ++
  s!"input-sha256={htmlTypes.digest},{htmlSigs.digest},{htmlF.digest} rows={rows} regenerate=lake exe tyxmlschema --write\n" ++
  "#kind\tfile\tline\tspan-sha256\tmodule\tname\tparams\tbody\tattrs\n"

/-- Read one sealed input, refusing any bytes but the pinned ones. -/
def readInput (root : System.FilePath) (input : Input) : IO ByteArray := do
  let path := root / input.relative
  unless ← path.pathExists do
    throw <| IO.userError s!"tyxml schema: missing input {input.relative}"
  let bs ← IO.FS.readBinFile path
  let digest := Gates.Sha256.hexDigest bs
  unless digest == input.digest do
    throw <| IO.userError
      s!"tyxml schema: {input.relative} has digest {digest}, expected the pinned {input.digest}; re-pin before regenerating"
  return bs

def generate (root : System.FilePath) : IO Generated := do
  let typesBytes ← readInput root htmlTypes
  let sigsBytes ← readInput root htmlSigs
  let fBytes ← readInput root htmlF
  let lift {α} (file : String) : Except String α → IO α
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"tyxml schema: {file}: {e}"
  let typeRows ← lift "html_types.mli" (parseInterface "lib/html_types.mli" typesBytes)
  let sigRows ← lift "html_sigs.mli" (parseInterface "lib/html_sigs.mli" sigsBytes)
  let tagRows ← lift "html_f.ml" (parseEmptyTags "lib/html_f.ml" fBytes)
  let mut body := ""
  for d in typeRows do body := body ++ (← lift d.file (renderRow typesBytes d))
  for d in sigRows do body := body ++ (← lift d.file (renderRow sigsBytes d))
  for d in tagRows do body := body ++ (← lift d.file (renderRow fBytes d))
  let all := typeRows ++ sigRows ++ tagRows
  return { text := header all.size ++ body
           types := (all.filter (·.kind == "type")).size
           vals := (all.filter (·.kind == "val")).size
           elements := (all.filter isElementRow).size
           attributes := (all.filter isAttributeRow).size
           emptytags := tagRows.size }

def summarize (g : Generated) : String :=
  s!"tyxml schema: {g.types} type rows, {g.vals} val rows ({g.elements} element constructors, " ++
  s!"{g.attributes} attribute constructors in Html_sigs.T), {g.emptytags} void tags\n"

def write (root : System.FilePath) : IO UInt32 := do
  let g ← generate root
  IO.FS.createDirAll (root / "generated")
  IO.FS.writeFile (projectionPath root) g.text
  IO.print (summarize g)
  IO.println s!"WROTE {← relativeTo root (projectionPath root)}"
  return 0

def check (root : System.FilePath) : IO UInt32 := do
  let path := projectionPath root
  unless ← path.pathExists do
    IO.eprintln s!"FAIL tyxml schema: missing projection {path}; run `lake exe tyxmlschema --write`"
    return 1
  let g ← generate root
  let committed ← IO.FS.readFile path
  if committed == g.text then
    IO.print (summarize g)
    IO.println "PASS tyxml schema: generated/tyxml-html-schema.tsv is byte-identical to a fresh regeneration from the sealed inputs"
    return 0
  let expected := lines g.text
  let actual := lines committed
  IO.eprintln s!"FAIL tyxml schema: projection drift ({actual.length} committed lines, {expected.length} regenerated)"
  let mut shown := 0
  for (e, a) in expected.zip actual do
    if e != a && shown < 20 then
      IO.eprintln s!"  regenerated: {e}"
      IO.eprintln s!"  committed:   {a}"
      shown := shown + 1
  return 1

def usage : String :=
  "usage: lake exe tyxmlschema          check generated/tyxml-html-schema.tsv against a regeneration\n" ++
  "       lake exe tyxmlschema --write  regenerate the projection from the sealed TyXML sources"

/-- Command-line entry, invoked by `bin/TyxmlSchema.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] => check root
  | ["--write"] => write root
  | _ =>
    IO.eprintln usage
    return 2

end Gates.TyxmlSchema
