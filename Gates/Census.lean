import Gates.Common
import Gates.Sha256

/-!
# Gates.Census

The specification algorithm census: the denominator of the coverage metric
defined in `docs/SPEC-COVERAGE.md`. One row per abstract operation, internal
slot, IDL member, stated piping requirement, and authored cross-cutting rule
of the pinned `index.bs`, each anchored to the pinned bytes by a byte string
that occurs exactly once and by the SHA-256 of its span.

`lake exe census --write` writes two projections:

- `generated/spec-algorithm-census.tsv`, the census itself; and
- `WhatwgStreamsTest/Audit/SpecCoverageRows.lean`, the frozen Lean row list
  the test-side numerator checks itself against.

`lake exe census` checks the input digest, anchor uniqueness, every span
digest, the disposition join, and byte-identity of both projections against a
fresh regeneration. `lake exe census --report` prints the coverage block.

## Representation, and the R0 evidence each choice rests on

The file is carried as a `ByteArray` read by `IO.FS.readBinFile`, and every
offset is a `Nat` byte offset. `docs/research/2026-09-01-lean-stdlib-strategy-and-performance.md`
section 8 measures that effectively the whole `String` and `String.Slice` API
reaches `Classical.choice` while `ByteArray.extract`, `.size`, `.get!` and
`.push` reach no axiom at all, and its section 10.4 records that
`String.length` counts characters while the census anchors byte spans: on
this file the two differ by 190. `String` appears here only to render output
and to read short attribute values, never to compute an offset.

Scanning is fuel-bounded structural recursion on a `Nat`, with the fuel taken
as a size the data already carries plus one, as
`docs/research/2026-09-01-lean4-nlp-learnings.md` section 6.3 records for
lean4-nlp's scanners; that satisfies the no-`partial` rule with no
well-founded recursion obligation, and section 3.1 of the stdlib document
measures that a `termination_by` definition costs nothing at runtime anyway.
Byte access goes through the total `byteAt` rather than `bs[i]!`: section 1.4
measures the total accessor at 0.67 ms against 0.74 ms for the panicking one
on this file, so avoiding the panic path costs nothing.

Classification is ASCII-first (section 6.2 of the lean4-nlp document): every
structural byte this scanner tests is below 0x80, and non-ASCII bytes are
only ever copied, never classified. Anchors are extended to a UTF-8 character
boundary so that a rendered anchor is always valid UTF-8.

Accumulation is into a single linearly-threaded `Array`, never into an
`Array (Array _)` indexed by a key: section 8 of the lean4-nlp document
measures an 868x penalty for the aliased nested shape, and section 2.2 of the
stdlib document explains it as one full copy per write.

Span digests go through `Gates.Sha256.hexDigest`; section 1.6 of the stdlib
document measures 229 span digests over 374,064 bytes at 7.98 ms compiled and
1447 ms under `#eval`, so the digest pass belongs in the compiled executable
and never in an elaboration-time check.
-/

namespace Gates.Census

/-! ## Byte primitives -/

/-- Total byte access: out of range reads as zero, so no scan can panic. -/
@[inline] def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

@[inline] def byteNat (bs : ByteArray) (i : Nat) : Nat := (byteAt bs i).toNat

@[inline] def isSpaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x0a || b == 0x09 || b == 0x0d

/-- A UTF-8 continuation byte, `10xxxxxx`. -/
@[inline] def isContinuationByte (b : UInt8) : Bool := (b.toNat &&& 0xc0) == 0x80

private def matchAux (bs pat : ByteArray) (i j : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.ble pat.size j then true
    else if byteAt bs (i + j) == byteAt pat j then matchAux bs pat i (j + 1) fuel
    else false

/-- Whether `pat` occurs in `bs` starting exactly at `i`. -/
def matchesAt (bs pat : ByteArray) (i : Nat) : Bool :=
  Nat.ble (i + pat.size) bs.size && matchAux bs pat i 0 (pat.size + 1)

private def findAux (bs pat : ByteArray) (i : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    if !Nat.ble (i + pat.size) bs.size then none
    else if matchesAt bs pat i then some i
    else findAux bs pat (i + 1) fuel

/-- The first occurrence of `pat` at or after `start`. Fuel is one per byte of
the subject, which is one more than the number of positions the scan can
visit. -/
def findFrom (bs pat : ByteArray) (start : Nat) : Option Nat :=
  findAux bs pat start (bs.size + 1)

private def collectAux (bs pat : ByteArray) (i : Nat) (acc : Array Nat) (cap : Nat) :
    Nat → Array Nat
  | 0 => acc
  | fuel + 1 =>
    if Nat.ble cap acc.size then acc
    else if !Nat.ble (i + pat.size) bs.size then acc
    else if matchesAt bs pat i then collectAux bs pat (i + 1) (acc.push i) cap fuel
    else collectAux bs pat (i + 1) acc cap fuel

/-- Every offset at which `pat` occurs, in increasing order, stopping once
`cap` offsets have been collected. The accumulator is threaded linearly, so
each `push` is in place. -/
def occurrences (bs pat : ByteArray) (cap : Nat) : Array Nat :=
  collectAux bs pat 0 #[] cap (bs.size + 1)

private def rangeEqAux (bs : ByteArray) (a b j n : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 =>
    if Nat.ble n j then true
    else if byteAt bs (a + j) == byteAt bs (b + j) then rangeEqAux bs a b (j + 1) n fuel
    else false

/-- Whether the `n` bytes at `a` equal the `n` bytes at `b`, both in range. -/
def rangeEq (bs : ByteArray) (a b n : Nat) : Bool :=
  Nat.ble (a + n) bs.size && Nat.ble (b + n) bs.size && rangeEqAux bs a b 0 n (n + 1)

private def alignAux (bs : ByteArray) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 =>
    if Nat.ble bs.size i then i
    else if isContinuationByte (byteAt bs i) then alignAux bs (i + 1) fuel
    else i

/-- The least offset at or after `i` that starts a UTF-8 character. A UTF-8
sequence is at most four bytes, so four steps always suffice. -/
def alignForward (bs : ByteArray) (i : Nat) : Nat := alignAux bs i 5

/-- The bytes `[b, e)` decoded as text, when they are valid UTF-8. -/
def sliceString? (bs : ByteArray) (b e : Nat) : Option String :=
  String.fromUTF8? (bs.extract b e)

/-! ## Small text utilities

These operate on `String` and are used only for names and rendering, never
to compute an offset. -/

@[inline] private def charNat (c : Char) : Nat := c.toNat
@[inline] private def isLowerC (c : Char) : Bool :=
  Nat.ble 0x61 (charNat c) && Nat.ble (charNat c) 0x7a
@[inline] private def isUpperC (c : Char) : Bool :=
  Nat.ble 0x41 (charNat c) && Nat.ble (charNat c) 0x5a
@[inline] private def isDigitC (c : Char) : Bool :=
  Nat.ble 0x30 (charNat c) && Nat.ble (charNat c) 0x39
@[inline] private def isIdentC (c : Char) : Bool :=
  isLowerC c || isUpperC c || isDigitC c || c == '_'
@[inline] private def lowerC (c : Char) : Char :=
  if isUpperC c then Char.ofNat (charNat c + 32) else c

/-- Kebab-case: ASCII letters and digits are kept and lowercased, a case
boundary inside a run of letters becomes a separator, every other byte run
becomes one separator, and separators never lead or trail. `BYOB` in
`ReadableStreamBYOBReader` stays one word because a separator is inserted
before an upper-case letter only when the previous character is lower-case or
a digit, or when the next character is lower-case. -/
def kebab (text : String) : String := Id.run do
  let a := text.toList.toArray
  let mut out : String := ""
  let mut lastDash := true
  for i in [0:a.size] do
    let c := a.getD i ' '
    if isLowerC c || isDigitC c then
      out := out.push c
      lastDash := false
    else if isUpperC c then
      let p := if i == 0 then ' ' else a.getD (i - 1) ' '
      let nextLower := isLowerC (a.getD (i + 1) ' ')
      if !lastDash && ((isLowerC p || isDigitC p) || (isUpperC p && nextLower)) then
        out := out.push '-'
      out := out.push (lowerC c)
      lastDash := false
    else
      if !lastDash then
        out := out.push '-'
      lastDash := true
  if out.endsWith "-" then Gates.Common.dropLastChars out 1 else out

/-- The interface or dictionary name of a `for=` attribute, flattened to one
lower-case word with no separators. This is Bikeshed's own spelling of a
member anchor (`dom-readablestream-locked`), and using it keeps a member id
distinct from the kebab-cased id of a same-named abstract operation:
`ReadableStream/close` becomes `readablestream-close` while the abstract
operation `ReadableStreamClose` becomes `readable-stream-close`. -/
def flattenName (text : String) : String := Id.run do
  let mut out : String := ""
  for c in text.toList do
    if isLowerC c || isDigitC c then out := out.push c
    else if isUpperC c then out := out.push (lowerC c)
  return out

/-- The trailing maximal run of identifier characters. -/
def trailingIdent (text : String) : String :=
  String.ofList (text.toList.reverse.takeWhile isIdentC).reverse

/-- The leading maximal run of identifier characters. -/
def leadingIdent (text : String) : String :=
  String.ofList (text.toList.takeWhile isIdentC)

/-- `text` without `prefix`, when it starts with it. Spelled here rather than
taken from the standard library because the 4.33.1 replacements for the
deprecated `String.stripPrefix` return a `String.Slice`, whose entry point
`String.toSlice` reaches `Classical.choice`. -/
def withoutPrefix (text pre : String) : String :=
  if text.startsWith pre then Gates.Common.dropChars text pre.length else text

/-- `text` without `suffix`, when it ends with it. -/
def withoutSuffix (text suf : String) : String :=
  if text.endsWith suf then Gates.Common.dropLastChars text suf.length else text

/-- Every run of space, tab, carriage return and newline collapsed to one
space, with no leading or trailing space. -/
def normalizeWhitespace (text : String) : String := Id.run do
  let mut out : String := ""
  let mut pendingSpace := false
  for c in text.toList do
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      pendingSpace := true
    else
      if pendingSpace && !out.isEmpty then out := out.push ' '
      pendingSpace := false
      out := out.push c
  return out

/-- Field escaping for the `|`-separated row format: a backslash escapes
itself, the field separator, and the three whitespace characters that would
otherwise break a row across lines. Every other byte is written through. -/
def escapeField (text : String) : String := Id.run do
  let mut out : String := ""
  for c in text.toList do
    if c == '\\' then out := out ++ "\\\\"
    else if c == '|' then out := out ++ "\\|"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\r' then out := out ++ "\\r"
    else if c == '\t' then out := out ++ "\\t"
    else out := out.push c
  return out

/-- Split one rendered row into its fields, undoing `escapeField`. -/
def splitRow (line : String) : Except String (Array String) := Id.run do
  let mut fields : Array String := #[]
  let mut current : String := ""
  let mut escaped := false
  let mut bad : Option String := none
  for c in line.toList do
    if escaped then
      escaped := false
      if c == '\\' then current := current.push '\\'
      else if c == '|' then current := current.push '|'
      else if c == 'n' then current := current.push '\n'
      else if c == 'r' then current := current.push '\r'
      else if c == 't' then current := current.push '\t'
      else bad := some s!"unknown escape \\{c}"
    else if c == '\\' then escaped := true
    else if c == '|' then
      fields := fields.push current
      current := ""
    else current := current.push c
  fields := fields.push current
  match bad with
  | some message => return .error message
  | none => if escaped then return .error "row ends with a dangling backslash" else return .ok fields

/-! ## Vocabulary -/

/-- The fixed row kinds of `docs/SPEC-COVERAGE.md`. -/
inductive Kind
  | idl
  | op
  | requirement
  | rule
  | slot
  deriving BEq, DecidableEq, Inhabited

def Kind.name : Kind → String
  | .idl => "idl"
  | .op => "op"
  | .requirement => "requirement"
  | .rule => "rule"
  | .slot => "slot"

def Kind.ofString? : String → Option Kind
  | "idl" => some .idl
  | "op" => some .op
  | "requirement" => some .requirement
  | "rule" => some .rule
  | "slot" => some .slot
  | _ => none

def Kind.all : List Kind := [.idl, .op, .requirement, .rule, .slot]

/-- The disposition vocabulary owned by `SPEC-MANIFEST.md`. -/
inductive Disposition
  | owned
  | requirement
  | foreignBoundary
  | hostOnly
  | refused
  | evidenceOnly
  | targetOnly
  deriving BEq, DecidableEq, Inhabited

def Disposition.name : Disposition → String
  | .owned => "owned"
  | .requirement => "requirement"
  | .foreignBoundary => "foreignBoundary"
  | .hostOnly => "hostOnly"
  | .refused => "refused"
  | .evidenceOnly => "evidenceOnly"
  | .targetOnly => "targetOnly"

def Disposition.ofString? : String → Option Disposition
  | "owned" => some .owned
  | "requirement" => some .requirement
  | "foreignBoundary" => some .foreignBoundary
  | "hostOnly" => some .hostOnly
  | "refused" => some .refused
  | "evidenceOnly" => some .evidenceOnly
  | "targetOnly" => some .targetOnly
  | _ => none

def Disposition.all : List Disposition :=
  [.owned, .requirement, .foreignBoundary, .hostOnly, .refused, .evidenceOnly, .targetOnly]

/-- A disposition outside the denominator, per `docs/SPEC-COVERAGE.md`. -/
def Disposition.excluded : Disposition → Bool
  | .evidenceOnly => true
  | .refused => true
  | .targetOnly => true
  | _ => false

/-- Coverage state. The middle constructor is spelled `partialCoverage`
because `partial` is a Lean keyword and the repository's source trust gate
rejects that token in an authored file; its external spelling is `partial`. -/
inductive CoverageState
  | absent
  | partialCoverage
  | green
  deriving BEq, DecidableEq, Inhabited

def CoverageState.name : CoverageState → String
  | .absent => "absent"
  | .partialCoverage => "partial"
  | .green => "green"

/-- One frozen numerator row. `WhatwgStreamsTest/Audit/SpecCoverage.lean` owns
the rules; this type is here so the generated row list and the census gate
share one spelling. -/
structure CoverageRow where
  id : String
  disposition : Disposition
  state : CoverageState
  witnesses : List String
  deriving Inhabited, BEq

/-! ## Rows -/

structure Row where
  kind : Kind
  id : String
  /-- Start of the anchor, always equal to `spanB`: the anchor is the span's
  own prefix, so locating the anchor locates the span. -/
  anchorB : Nat
  anchorE : Nat
  spanB : Nat
  spanE : Nat
  deriving Inhabited

def Row.sortKey (r : Row) : String := r.kind.name ++ "|" ++ r.id

/-! ## The pinned input -/

def inputRelativePath : String := "vendor/whatwg-streams-b9ba9f49/index.bs"

/-- The pin recorded in `SPEC-MANIFEST.md`. The generator refuses any other
bytes. -/
def inputDigest : String :=
  "24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440"

def censusRelativePath : String := "generated/spec-algorithm-census.tsv"

def rowsRelativePath : String := "WhatwgStreamsTest/Audit/SpecCoverageRows.lean"

def dispositionsRelativePath : String := "census/dispositions.tsv"

def overridesRelativePath : String := "census/overrides.tsv"

def rulesRelativePath : String := "census/rules.tsv"

def formatVersion : String := "1"

def regenerateCommand : String := "lake exe census --write"

/-! ## Section index -/

structure Heading where
  level : Nat
  id : String
  off : Nat
  deriving Inhabited

/-- Every `<h2>`, `<h3>` and `<h4>` that opens a line and carries an `id`
attribute, in document order. -/
def scanHeadings (bs : ByteArray) : Except String (Array Heading) := Id.run do
  let openTag := "<h".toUTF8
  let idKey := " id=\"".toUTF8
  let quote := "\"".toUTF8
  let mut out : Array Heading := #[]
  for i in occurrences bs openTag 4096 do
    if i != 0 && byteAt bs (i - 1) != 0x0a then continue
    let d := byteNat bs (i + 2)
    if d < 0x32 || d > 0x34 then continue
    if !matchesAt bs idKey (i + 3) then continue
    let vs := i + 3 + idKey.size
    match findFrom bs quote vs with
    | none => return .error s!"census: unterminated heading id at byte {i}"
    | some ve =>
      match sliceString? bs vs ve with
      | none => return .error s!"census: heading id at byte {i} is not valid UTF-8"
      | some name => out := out.push { level := d - 0x30, id := name, off := i }
  return .ok out

/-- The innermost enclosing `<h4>`, `<h3>` and `<h2>` ids at `off`, empty
where there is none. -/
def sectionPath (hs : Array Heading) (off : Nat) : String × String × String := Id.run do
  let mut h2 := ""
  let mut h3 := ""
  let mut h4 := ""
  for h in hs do
    if h.off > off then break
    if h.level == 2 then
      h2 := h.id; h3 := ""; h4 := ""
    else if h.level == 3 then
      h3 := h.id; h4 := ""
    else
      h4 := h.id
  return (h4, h3, h2)

/-! ## Attributes -/

private def attrAux (bs key : ByteArray) (i limit : Nat) : Nat → Option (Nat × Nat)
  | 0 => none
  | fuel + 1 =>
    if Nat.ble limit i then none
    else if matchesAt bs key i && (i == 0 || isSpaceByte (byteAt bs (i - 1))) then
      match findFrom bs (ByteArray.mk #[0x22]) (i + key.size) with
      | some ve => if Nat.ble ve limit then some (i + key.size, ve) else none
      | none => none
    else attrAux bs key (i + 1) limit fuel

/-- The value span of attribute `name` inside the tag `[tagB, tagE)`. The
attribute name must be preceded by whitespace, so `id=` is never read out of
`oldids=`. -/
def attrSpan? (bs : ByteArray) (tagB tagE : Nat) (name : String) : Option (Nat × Nat) :=
  attrAux bs (name ++ "=\"").toUTF8 tagB tagE (tagE - tagB + 1)

def attrText? (bs : ByteArray) (tagB tagE : Nat) (name : String) : Option String := do
  let (vs, ve) ← attrSpan? bs tagB tagE name
  sliceString? bs vs ve

/-! ## Anchors -/

/-- Anchor lengths tried in order. The anchor is the shortest prefix of the
row's span, aligned to a UTF-8 boundary, that occurs exactly once in the
pinned bytes. -/
def anchorLadder : List Nat :=
  [24, 32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048, 3072, 4096]

private def firstUnique (bs : ByteArray) (start : Nat) (rivals : Array Nat) :
    List Nat → Option Nat
  | [] => none
  | n :: rest =>
    let aligned := alignForward bs (start + n) - start
    if !Nat.ble (start + aligned) bs.size then none
    else if rivals.all (fun p => !rangeEq bs start p aligned) then some aligned
    else firstUnique bs start rivals rest

/-- The anchor length for a span starting at `start`, or the offset of a rival
occurrence that no admitted length separates. -/
def chooseAnchorLength (bs : ByteArray) (start : Nat) : Except Nat Nat := Id.run do
  let remaining := bs.size - start
  let baseWanted := if Nat.ble remaining 24 then remaining else 24
  let base := alignForward bs (start + baseWanted) - start
  let probe := bs.extract start (start + base)
  let rivals := (occurrences bs probe 4096).filter (fun p => p != start)
  if rivals.isEmpty then return .ok base
  let ladder := anchorLadder.filter (fun n => n > base) ++ [remaining]
  match firstUnique bs start rivals ladder with
  | some n => return .ok n
  | none => return .error (rivals.getD 0 0)

/-! ## Abstract-operation rows

Every algorithm block opens with the byte prefix `<div algorithm`, never the
closing bracket: `docs/research/2026-09-01-lean-stdlib-strategy-and-performance.md`
section 1.5 measures 229 occurrences of `<div algorithm>` against 248 of
`<div algorithm`, so keying on the bracket silently drops the 19 attributed
blocks.

The id is the specification's own identifier wherever the text supplies one,
in this order: the opener's `id`; then the block's first `<dfn>`, by its `id`,
else by the first alternative of its `lt`, else by its text, in the last two
cases prefixed by the flattened `for` class; and only then the opener's
`algorithm` attribute. Consulting the block's `<dfn>` before the `algorithm`
attribute is what keeps an exported wrapper distinct from the abstract
operation it wraps. -/

private def matchCloseAux (opens closes : Array Nat) (oi ci depth : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 =>
    match closes[ci]? with
    | none => none
    | some cv =>
      match opens[oi]? with
      | some ov =>
        if ov < cv then matchCloseAux opens closes (oi + 1) ci (depth + 1) fuel
        else if depth == 0 then some (cv + 6)
        else matchCloseAux opens closes oi (ci + 1) (depth - 1) fuel
      | none =>
        if depth == 0 then some (cv + 6)
        else matchCloseAux opens closes oi (ci + 1) (depth - 1) fuel

private def firstIndexAfter (xs : Array Nat) (bound : Nat) : Nat := Id.run do
  let mut i := 0
  for x in xs do
    if x > bound then return i
    i := i + 1
  return i

def scanOps (bs : ByteArray) : Except String (Array Row) := Id.run do
  let algOpen := "<div algorithm".toUTF8
  let divOpen := "<div".toUTF8
  let divClose := "</div>".toUTF8
  let gt := ">".toUTF8
  let dfnOpen := "<dfn".toUTF8
  let dfnClose := "</dfn>".toUTF8
  let opens := occurrences bs divOpen 4096
  let closes := occurrences bs divClose 4096
  let mut out : Array Row := #[]
  for i in occurrences bs algOpen 4096 do
    let some tagE := findFrom bs gt i
      | return .error s!"census: unterminated <div algorithm at byte {i}"
    let oi := firstIndexAfter opens i
    let ci := firstIndexAfter closes i
    let some blockEnd := matchCloseAux opens closes oi ci 0 (opens.size + closes.size + 1)
      | return .error s!"census: unbalanced algorithm block at byte {i}"
    let mut name : Option String := none
    match attrText? bs i (tagE + 1) "id" with
    | some divId => name := some (kebab divId)
    | none =>
      match findFrom bs dfnOpen (tagE + 1) with
      | some d =>
        if d < blockEnd then
          let some dfnTagE := findFrom bs gt d
            | return .error s!"census: unterminated <dfn at byte {d}"
          let owner :=
            match attrText? bs d (dfnTagE + 1) "for" with
            | some f => flattenName f ++ "-"
            | none => ""
          match attrText? bs d (dfnTagE + 1) "id" with
          | some dfnId => name := some (kebab dfnId)
          | none =>
            match attrText? bs d (dfnTagE + 1) "lt" with
            | some lt =>
              let head := (lt.splitOn "|").headD lt
              name := some (owner ++ kebab head)
            | none =>
              let some textE := findFrom bs dfnClose (dfnTagE + 1)
                | return .error s!"census: unterminated <dfn> text at byte {d}"
              let some text := sliceString? bs (dfnTagE + 1) textE
                | return .error s!"census: <dfn> text at byte {d} is not valid UTF-8"
              name := some (owner ++ kebab (normalizeWhitespace text))
      | none => pure ()
    if name.isNone then
      match attrText? bs i (tagE + 1) "algorithm" with
      | some alg => name := some (kebab alg)
      | none => return .error s!"census: algorithm block at byte {i} carries no derivable name"
    let some derived := name
      | return .error s!"census: algorithm block at byte {i} carries no derivable name"
    if derived.isEmpty then
      return .error s!"census: algorithm block at byte {i} derived an empty name"
    out := out.push { kind := .op, id := "op." ++ derived,
                      anchorB := i, anchorE := i, spanB := i, spanE := blockEnd }
  return .ok out

/-! ## Internal-slot rows

A candidate is any `[[Name]]` whose name is letters, digits, underscores and
spaces. Bikeshed writes a biblio reference the same way, so a candidate counts
as an internal slot only when at least one of its occurrences is preceded by
`\` (the escaped spelling the specification uses in algorithm text) or by `/`
(the class-qualified spelling inside a `[=Class/[[slot]]=]` autolink). On the
pinned bytes that rule admits 62 names and rejects exactly four —
`[[FETCH]]`, `[[COMPRESSION]]`, `[[ENCODING]]` and `[[WEBSOCKETS]]` — each of
which occurs only unqualified and is a bibliography citation.

A row is anchored at the first `<dfn>` that defines the name if there is one,
and otherwise at the first qualified occurrence. -/

private def slotNameAt (bs : ByteArray) (i : Nat) : Option (String × Nat) := Id.run do
  let mut j := i + 2
  let mut ok := true
  for _ in [0:48] do
    let b := byteNat bs j
    if b == 0x5d then break
    let isName :=
      (Nat.ble 0x41 b && Nat.ble b 0x5a) || (Nat.ble 0x61 b && Nat.ble b 0x7a) ||
      (Nat.ble 0x30 b && Nat.ble b 0x39) || b == 0x5f || b == 0x20
    if !isName then
      ok := false
      break
    j := j + 1
  if !ok then return none
  if byteNat bs j != 0x5d || byteNat bs (j + 1) != 0x5d then return none
  if j == i + 2 then return none
  match sliceString? bs (i + 2) j with
  | none => return none
  | some name => return some (name, j + 2)

structure SlotEntry where
  name : String
  firstQualified : Option Nat
  defining : Option Nat
  deriving Inhabited

def scanSlots (bs : ByteArray) : Except String (Array Row) := Id.run do
  let brackets := "[[".toUTF8
  let dfnOpen := "<dfn".toUTF8
  let gt := ">".toUTF8
  let closeBrackets := "]]".toUTF8
  let mut entries : Array SlotEntry := #[]
  -- Pass one: names, in first-appearance order, with the first qualified use.
  for i in occurrences bs brackets 8192 do
    match slotNameAt bs i with
    | none => pure ()
    | some (name, _) =>
      let prev := byteNat bs (i - 1)
      let qualified := i > 0 && (prev == 0x5c || prev == 0x2f)
      match entries.findIdx? (fun e => e.name == name) with
      | some k =>
        if qualified && (entries.getD k default).firstQualified.isNone then
          entries := entries.modify k (fun e => { e with firstQualified := some i })
      | none =>
        entries := entries.push
          { name := name, firstQualified := if qualified then some i else none, defining := none }
  -- Pass two: the first defining `<dfn>` for each name.
  for d in occurrences bs dfnOpen 4096 do
    let some tagE := findFrom bs gt d
      | return .error s!"census: unterminated <dfn at byte {d}"
    let named : Option String :=
      match attrSpan? bs d (tagE + 1) "lt" with
      | some (vs, _) => (slotNameAt bs vs).map (fun p => p.1)
      | none =>
        let afterTag := if byteNat bs (tagE + 1) == 0x5c then tagE + 2 else tagE + 1
        if byteNat bs afterTag == 0x5b && byteNat bs (afterTag + 1) == 0x5b then
          (slotNameAt bs afterTag).map (fun p => p.1)
        else none
    match named with
    | none => pure ()
    | some name =>
      match entries.findIdx? (fun e => e.name == name) with
      | none => pure ()
      | some k =>
        if (entries.getD k default).defining.isNone then
          entries := entries.modify k (fun e => { e with defining := some d })
  -- Emit one row per qualified name.
  let mut out : Array Row := #[]
  for e in entries do
    if e.firstQualified.isNone then continue
    let start := match e.defining with
      | some d => d
      | none => e.firstQualified.getD 0
    let some closeAt := findFrom bs closeBrackets start
      | return .error s!"census: unterminated internal slot at byte {start}"
    out := out.push { kind := .slot, id := "slot." ++ kebab e.name,
                      anchorB := start, anchorE := start, spanB := start, spanE := closeAt + 2 }
  return .ok out

/-! ## Web IDL rows

Every `<xmp class="idl">` block is read statement by statement: lines are
accumulated, with their leading and trailing whitespace dropped and joined by
one space, until the accumulation ends in `;` or `{`. A statement ending in
`{` opens an interface, interface mixin or dictionary and emits a declaration
row spanning the header itself; `};` closes it; a `callback` statement emits a
declaration row; and every statement inside a body emits a constructor,
attribute, method or dictionary-member row.

A `typedef`, `enum` or `includes` statement also emits an `idl` row, as
`SPEC-MANIFEST.md` rules under "Rulings made at P1 landing" and
`docs/SPEC-COVERAGE.md` records. A `typedef` and an `enum` each declare a
name, so each is identified the way an interface or dictionary declaration is,
by the kebab-cased name it declares. An `includes` statement declares no name
of its own: it relates two names that are themselves declaration rows, so it
is identified by both, as `<includer>-includes-<mixin>`. Every one of the
three is `hostOnly` at the boundary, which it reaches through its enclosing
section rather than through an override.

Any other top-level statement is counted rather than dropped silently, and the
count is reported. It is zero at the pin. -/

structure IdlStatement where
  text : String
  b : Nat
  e : Nat
  deriving Inhabited

private def lineEnd (bs : ByteArray) (i : Nat) : Nat :=
  match findFrom bs (ByteArray.mk #[0x0a]) i with
  | some n => n
  | none => bs.size

private def trimSpanStart (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut i := b
  for _ in [0:e - b] do
    if i < e && isSpaceByte (byteAt bs i) then i := i + 1 else break
  return i

private def trimSpanEnd (bs : ByteArray) (b e : Nat) : Nat := Id.run do
  let mut i := e
  for _ in [0:e - b] do
    if i > b && isSpaceByte (byteAt bs (i - 1)) then i := i - 1 else break
  return i

private def stripExtendedAttribute (text : String) : String :=
  if text.startsWith "[" then
    match text.splitOn "] " with
    | _ :: rest => Gates.Common.trimmed (String.intercalate "] " rest)
    | [] => text
  else text

def scanIdl (bs : ByteArray) : Except String (Array Row × Nat) := Id.run do
  let xmpOpen := "<xmp class=\"idl\">".toUTF8
  let xmpClose := "</xmp>".toUTF8
  let mut out : Array Row := #[]
  let mut skipped : Nat := 0
  for blockStart in occurrences bs xmpOpen 256 do
    let some blockEnd := findFrom bs xmpClose blockStart
      | return .error s!"census: unterminated IDL block at byte {blockStart}"
    let mut cursor := lineEnd bs blockStart + 1
    let mut owner : String := ""
    let mut ownerIsDictionary := false
    let mut acc : String := ""
    let mut accB : Nat := 0
    let mut accE : Nat := 0
    for _ in [0:4096] do
      if cursor >= blockEnd then break
      let le := lineEnd bs cursor
      let tb := trimSpanStart bs cursor le
      let te := trimSpanEnd bs tb le
      if tb < te then
        let some piece := sliceString? bs tb te
          | return .error s!"census: IDL line at byte {tb} is not valid UTF-8"
        if acc.isEmpty then
          acc := piece
          accB := tb
        else
          acc := acc ++ " " ++ piece
        accE := te
      cursor := le + 1
      if acc.isEmpty then continue
      if !(acc.endsWith ";" || acc.endsWith "{") then continue
      let statement := acc
      acc := ""
      if owner.isEmpty then
        if statement.endsWith "{" then
          let core := stripExtendedAttribute statement
          let words := (core.splitOn " ").filter (fun w => !w.isEmpty)
          match words with
          | ["interface", "mixin", name, "{"] =>
            owner := name; ownerIsDictionary := false
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          | ["interface", name, "{"] =>
            owner := name; ownerIsDictionary := false
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          | ["dictionary", name, "{"] =>
            owner := name; ownerIsDictionary := true
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          | _ => return .error s!"census: unrecognised IDL header at byte {accB}: {statement}"
        else if statement.startsWith "callback " then
          let name := trailingIdent ((statement.splitOn " =").headD statement)
          if name.isEmpty then
            return .error s!"census: callback at byte {accB} has no name"
          out := out.push { kind := .idl, id := "idl." ++ kebab name,
                            anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
        else
          let body := Gates.Common.trimmed (withoutSuffix statement ";")
          if body.startsWith "typedef " then
            let name := trailingIdent body
            if name.isEmpty then
              return .error s!"census: typedef at byte {accB} declares no name: {statement}"
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          else if body.startsWith "enum " then
            let name := leadingIdent (Gates.Common.trimmed (withoutPrefix body "enum "))
            if name.isEmpty then
              return .error s!"census: enum at byte {accB} declares no name: {statement}"
            out := out.push { kind := .idl, id := "idl." ++ kebab name,
                              anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
          else
            match body.splitOn " includes " with
            | [includer, included] =>
              let target := trailingIdent includer
              let mixinName := leadingIdent included
              if target.isEmpty || mixinName.isEmpty then
                return .error s!"census: includes statement at byte {accB} names no pair: {statement}"
              out := out.push
                { kind := .idl,
                  id := "idl." ++ kebab target ++ "-includes-" ++ kebab mixinName,
                  anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
            | _ => skipped := skipped + 1
      else if statement == "};" then
        owner := ""
        ownerIsDictionary := false
      else
        let body := Gates.Common.trimmed (withoutSuffix statement ";")
        let member :=
          if body.startsWith "constructor(" || body.startsWith "constructor (" then "constructor"
          else if body.startsWith "attribute " || body.startsWith "readonly attribute " then
            trailingIdent body
          else if ownerIsDictionary then
            trailingIdent ((body.splitOn " = ").headD body)
          else
            let head := (body.splitOn "(").headD body
            let t := trailingIdent head
            if t.isEmpty then leadingIdent head else t
        if member.isEmpty then
          return .error s!"census: IDL member at byte {accB} has no name: {statement}"
        out := out.push { kind := .idl, id := "idl." ++ flattenName owner ++ "-" ++ kebab member,
                          anchorB := accB, anchorE := accB, spanB := accB, spanE := accE }
    if !owner.isEmpty then
      return .error s!"census: IDL block at byte {blockStart} leaves {owner} unclosed"
  return .ok (out, skipped)

/-! ## Piping-requirement rows

The requirements are the bullet list inside the `ReadableStreamPipeTo`
algorithm block. A requirement row is one *top-level* bullet of that list: a
line whose first non-space character is `*`, at the smallest indentation any
such line in the block has. Its span runs from that `*` to the start of the
next line, at that indentation or shallower, that opens a list item (`*` or
`1.`), or to the end of the block, with trailing whitespace trimmed. Nested
bullets and numbered sub-steps therefore stay inside the requirement they
qualify rather than becoming rows of their own.

The id is the bullet's own `<dfn>` id when it has one, and otherwise the
kebab-cased lead-in of its `<strong>` label. -/

structure ListLine where
  off : Nat
  indent : Nat
  isBullet : Bool
  deriving Inhabited

def scanRequirements (bs : ByteArray) (opRows : Array Row) : Except String (Array Row) := Id.run do
  let marker := "<div algorithm=\"ReadableStreamPipeTo\">".toUTF8
  let some blockStart := findFrom bs marker 0
    | return .error "census: the ReadableStreamPipeTo algorithm block was not found"
  let some pipeRow := opRows.find? (fun r => r.spanB == blockStart)
    | return .error "census: the ReadableStreamPipeTo block is not an algorithm row"
  let blockEnd := pipeRow.spanE
  -- Collect every list-item line in the block.
  let mut items : Array ListLine := #[]
  let mut cursor := lineEnd bs blockStart + 1
  for _ in [0:8192] do
    if cursor >= blockEnd then break
    let le := lineEnd bs cursor
    let tb := trimSpanStart bs cursor le
    if tb < le then
      let indent := tb - cursor
      if byteNat bs tb == 0x2a && byteNat bs (tb + 1) == 0x20 then
        items := items.push { off := tb, indent := indent, isBullet := true }
      else if byteNat bs tb == 0x31 && byteNat bs (tb + 1) == 0x2e &&
              byteNat bs (tb + 2) == 0x20 then
        items := items.push { off := tb, indent := indent, isBullet := false }
    cursor := le + 1
  let bullets := items.filter (·.isBullet)
  if bullets.isEmpty then
    return .error "census: the ReadableStreamPipeTo block states no requirement bullets"
  let minIndent := bullets.foldl (fun acc it => if it.indent < acc then it.indent else acc) 1000
  let tops := bullets.filter (·.indent == minIndent)
  let mut out : Array Row := #[]
  for top in tops do
    let nextItem := items.find? (fun it => it.off > top.off && it.indent <= minIndent)
    let rawEnd := match nextItem with
      | some it => it.off - it.indent
      | none => blockEnd
    let spanE := trimSpanEnd bs top.off rawEnd
    let some text := sliceString? bs top.off spanE
      | return .error s!"census: requirement bullet at byte {top.off} is not valid UTF-8"
    let body := Gates.Common.trimmed (withoutPrefix text "*")
    let name :=
      if body.startsWith "<dfn " then
        match attrText? bs top.off spanE "id" with
        | some anchorId => kebab anchorId
        | none => ""
      else if body.startsWith "<strong>" then
        let rest := withoutPrefix body "<strong>"
        kebab ((rest.splitOn ":").headD rest)
      else ""
    if name.isEmpty then
      return .error s!"census: requirement bullet at byte {top.off} carries no derivable name"
    out := out.push { kind := .requirement, id := "requirement." ++ name,
                      anchorB := top.off, anchorE := top.off, spanB := top.off, spanE := spanE }
  return .ok out

/-! ## Authored cross-cutting rules

`census/rules.tsv` is the authored extension point for `rule` rows, which the
text states as prose rather than as an algorithm. Each line is
`<kebab-name>` TAB `<locator>`, where the locator must occur exactly once in
the pinned bytes; the span runs from the locator to the next blank line. The
file is empty at P1. -/

structure RuleInput where
  name : String
  locator : String
  deriving Inhabited

def parseRules (text : String) : Except String (Array RuleInput) := Id.run do
  let mut out : Array RuleInput := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [name, locator] =>
      if name.isEmpty || locator.isEmpty then
        return .error s!"{rulesRelativePath} line {lineNumber}: empty field"
      out := out.push { name := name, locator := locator }
    | _ => return .error s!"{rulesRelativePath} line {lineNumber}: expected two tab-separated fields"
  return .ok out

def scanRules (bs : ByteArray) (inputs : Array RuleInput) : Except String (Array Row) := Id.run do
  let blank := "\n\n".toUTF8
  let mut out : Array Row := #[]
  for input in inputs do
    let pat := input.locator.toUTF8
    let hits := occurrences bs pat 2
    if hits.size != 1 then
      return .error s!"census: rule {input.name} locator occurs {hits.size} times, expected exactly one"
    let start := hits.getD 0 0
    let stop := match findFrom bs blank start with
      | some n => n
      | none => bs.size
    out := out.push { kind := .rule, id := "rule." ++ kebab input.name,
                      anchorB := start, anchorE := start, spanB := start, spanE := stop }
  return .ok out

/-! ## The disposition join

`census/dispositions.tsv` is authored input seeded from the section table of
`SPEC-MANIFEST.md`: one line per `<section id>` TAB `<kind or *>` TAB
`<disposition>`. `census/overrides.tsv` is authored input for the rows a
section's own disposition does not describe: `<row id>` TAB `<disposition>`
TAB `<reason>`.

A row's disposition is resolved by taking its override if it has one, and
otherwise by walking its heading ancestry from the innermost `<h4>` outward to
the `<h2>`, at each level preferring a kind-specific line to the section's
wildcard line. A row that no line reaches fails generation: this generator
never invents a default. An authored line that no row uses also fails
generation, so an entry cannot outlive its reason. -/

structure DispositionRule where
  sectionId : String
  kind : Option Kind
  disposition : Disposition
  deriving Inhabited

structure OverrideRule where
  rowId : String
  disposition : Disposition
  reason : String
  deriving Inhabited

inductive JoinSource
  | fromOverride (index : Nat)
  | fromSection (index : Nat)
  deriving Inhabited

def parseDispositions (text : String) : Except String (Array DispositionRule) := Id.run do
  let mut out : Array DispositionRule := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [sectionId, kindText, dispositionText] =>
      let kind ← if kindText == "*" then pure none else
        match Kind.ofString? kindText with
        | some k => pure (some k)
        | none => return .error s!"{dispositionsRelativePath} line {lineNumber}: unknown kind {kindText}"
      let some disposition := Disposition.ofString? dispositionText
        | return .error s!"{dispositionsRelativePath} line {lineNumber}: unknown disposition {dispositionText}"
      if sectionId.isEmpty then
        return .error s!"{dispositionsRelativePath} line {lineNumber}: empty section id"
      if out.any (fun d => d.sectionId == sectionId && d.kind == kind) then
        return .error s!"{dispositionsRelativePath} line {lineNumber}: duplicate entry for {sectionId} {kindText}"
      out := out.push { sectionId := sectionId, kind := kind, disposition := disposition }
    | _ =>
      return .error s!"{dispositionsRelativePath} line {lineNumber}: expected three tab-separated fields"
  return .ok out

def parseOverrides (text : String) : Except String (Array OverrideRule) := Id.run do
  let mut out : Array OverrideRule := #[]
  let mut lineNumber := 0
  for line in Gates.Common.lines text do
    lineNumber := lineNumber + 1
    let trimmed := Gates.Common.trimmed line
    if trimmed.isEmpty || trimmed.startsWith "#" then continue
    match line.splitOn "\t" with
    | [rowId, dispositionText, reason] =>
      let some disposition := Disposition.ofString? dispositionText
        | return .error s!"{overridesRelativePath} line {lineNumber}: unknown disposition {dispositionText}"
      if rowId.isEmpty || reason.isEmpty then
        return .error s!"{overridesRelativePath} line {lineNumber}: empty field"
      if out.any (fun o => o.rowId == rowId) then
        return .error s!"{overridesRelativePath} line {lineNumber}: duplicate override for {rowId}"
      out := out.push { rowId := rowId, disposition := disposition, reason := reason }
    | _ =>
      return .error s!"{overridesRelativePath} line {lineNumber}: expected three tab-separated fields"
  return .ok out

def resolveDisposition (rules : Array DispositionRule) (overrides : Array OverrideRule)
    (path : String × String × String) (row : Row) : Option (Disposition × JoinSource) :=
  match overrides.findIdx? (fun o => o.rowId == row.id) with
  | some i => some ((overrides.getD i default).disposition, .fromOverride i)
  | none =>
    let atSection (sectionId : String) : Option (Disposition × JoinSource) :=
      if sectionId.isEmpty then none
      else
        match rules.findIdx? (fun d => d.sectionId == sectionId && d.kind == some row.kind) with
        | some i => some ((rules.getD i default).disposition, .fromSection i)
        | none =>
          match rules.findIdx? (fun d => d.sectionId == sectionId && d.kind == none) with
          | some i => some ((rules.getD i default).disposition, .fromSection i)
          | none => none
    let (h4, h3, h2) := path
    (atSection h4).orElse fun _ => (atSection h3).orElse fun _ => atSection h2

/-! ## Rendering -/

/-- Bytes of the span that the row's one-line summary is taken from. -/
def summaryLimit : Nat := 200

def renderRow (bs : ByteArray) (row : Row) : Except String String := do
  let some anchor := sliceString? bs row.anchorB row.anchorE
    | .error s!"census: the anchor of {row.id} is not valid UTF-8"
  let digest := Gates.Sha256.hexDigest (bs.extract row.spanB row.spanE)
  let wanted := alignForward bs (row.spanB + summaryLimit)
  let stop := if Nat.ble row.spanE wanted then row.spanE else wanted
  let some raw := sliceString? bs row.spanB stop
    | .error s!"census: the summary of {row.id} is not valid UTF-8"
  let summary := normalizeWhitespace raw
  .ok s!"{row.kind.name}|{row.id}|{escapeField anchor}|{row.spanB}|{row.spanE}|{digest}|{escapeField summary}"

def censusHeader (rowCount : Nat) : String :=
  s!"#census format={formatVersion} generator=Gates.Census input={inputRelativePath} " ++
  s!"input-sha256={inputDigest} rows={rowCount} regenerate={regenerateCommand}"

def renderCensus (bs : ByteArray) (rows : Array Row) : Except String String := do
  let mut out := censusHeader rows.size ++ "\n"
  for row in rows do
    out := out ++ (← renderRow bs row) ++ "\n"
  .ok out

def renderRowsModule (entries : Array CoverageRow) (denominator : Nat) : String := Id.run do
  let mut out :=
    "/-\nGENERATED FILE. Do not edit.\n\n" ++
    s!"Written by `{regenerateCommand}` (`Gates.Census`) from the pinned\n" ++
    s!"`{inputRelativePath}` (SHA-256 `{inputDigest}`), the census projection\n" ++
    s!"`{censusRelativePath}`, and the authored disposition inputs under `census/`.\n" ++
    "Format version " ++ formatVersion ++ ". `lake exe census` fails on any byte of drift.\n\n" ++
    "This is the frozen row list of the specification-coverage numerator:\n" ++
    "one entry per census row, carrying the row id, the joined disposition, the\n" ++
    "coverage state, and the witness list. `WhatwgStreamsTest/Audit/SpecCoverage.lean`\n" ++
    "owns the checks over it and `docs/SPEC-COVERAGE.md` owns the rules.\n-/\n\n" ++
    "import Gates\n\n" ++
    "namespace WhatwgStreamsTest.Audit.SpecCoverageRows\n\n" ++
    "open Gates.Census\n\n" ++
    "/-- One entry per census row, sorted by kind then id, as the census is. -/\n" ++
    "def rows : Array CoverageRow := #[\n"
  let mut index := 0
  for entry in entries do
    let witnesses := "[]"
    let comma := if index + 1 == entries.size then "" else ","
    out := out ++
      s!"  ⟨\"{entry.id}\", .{entry.disposition.name}, .absent, {witnesses}⟩{comma}\n"
    index := index + 1
  out := out ++ "]\n\n" ++
    s!"/-- Total census rows. -/\ndef rowTotal : Nat := {entries.size}\n\n" ++
    s!"/-- Rows inside the coverage denominator. -/\ndef denominator : Nat := {denominator}\n\n" ++
    "end WhatwgStreamsTest.Audit.SpecCoverageRows\n"
  return out

/-! ## Building the census -/

structure Built where
  rows : Array Row
  dispositions : Array Disposition
  paths : Array (String × String × String)
  skippedIdl : Nat
  censusText : String
  rowsModuleText : String
  denominator : Nat
  deriving Inhabited

private def countKind (rows : Array Row) (k : Kind) : Nat :=
  rows.foldl (fun acc r => if r.kind == k then acc + 1 else acc) 0

private def countDisposition (ds : Array Disposition) (d : Disposition) : Nat :=
  ds.foldl (fun acc x => if x == d then acc + 1 else acc) 0

def build (bs : ByteArray) (dispositionsText overridesText rulesText : String) :
    Except String Built := do
  let headings ← scanHeadings bs
  let ops ← scanOps bs
  let slots ← scanSlots bs
  let (idl, skippedIdl) ← scanIdl bs
  let requirements ← scanRequirements bs ops
  let ruleInputs ← parseRules rulesText
  let rules ← scanRules bs ruleInputs
  let dispositionRules ← parseDispositions dispositionsText
  let overrides ← parseOverrides overridesText
  let unsorted := ops ++ slots ++ idl ++ requirements ++ rules
  let sorted := unsorted.qsort (fun a b => a.sortKey < b.sortKey)
  -- Ids are unique, so the sort is total and its result is deterministic.
  let mut duplicates : Array String := #[]
  for i in [1:sorted.size] do
    if (sorted.getD i default).id == (sorted.getD (i - 1) default).id then
      duplicates := duplicates.push (sorted.getD i default).id
  unless duplicates.isEmpty do
    .error s!"census: duplicate row id(s): {duplicates.toList}"
  -- Anchors.
  let mut anchored : Array Row := #[]
  for row in sorted do
    match chooseAnchorLength bs row.spanB with
    | .error rival =>
      .error s!"census: no unique anchor for {row.id}; its span at byte {row.spanB} is repeated at byte {rival}"
    | .ok len => anchored := anchored.push { row with anchorE := row.anchorB + len }
  -- Dispositions.
  let mut dispositions : Array Disposition := #[]
  let mut paths : Array (String × String × String) := #[]
  let mut usedRules : Array Nat := #[]
  let mut usedOverrides : Array Nat := #[]
  let mut unresolved : Array String := #[]
  for row in anchored do
    let path := sectionPath headings row.spanB
    paths := paths.push path
    match resolveDisposition dispositionRules overrides path row with
    | none =>
      let (h4, h3, h2) := path
      unresolved := unresolved.push s!"{row.id} (sections {h2}/{h3}/{h4})"
      dispositions := dispositions.push .owned
    | some (d, source) =>
      dispositions := dispositions.push d
      match source with
      | .fromOverride i => usedOverrides := usedOverrides.push i
      | .fromSection i => usedRules := usedRules.push i
  unless unresolved.isEmpty do
    .error s!"census: no disposition for {unresolved.size} row(s): {unresolved.toList}"
  let mut stale : Array String := #[]
  for i in [0:dispositionRules.size] do
    unless usedRules.contains i do
      let entry := dispositionRules.getD i default
      let kindText := match entry.kind with | none => "*" | some k => k.name
      stale := stale.push s!"{dispositionsRelativePath}: {entry.sectionId} {kindText} matches no row"
  for i in [0:overrides.size] do
    unless usedOverrides.contains i do
      stale := stale.push s!"{overridesRelativePath}: {(overrides.getD i default).rowId} matches no row"
  unless stale.isEmpty do
    .error s!"census: {stale.size} authored disposition entr(ies) outlived their rows: {stale.toList}"
  let denominator :=
    dispositions.foldl (fun acc d => if d.excluded then acc else acc + 1) 0
  let censusText ← renderCensus bs anchored
  let mut coverageRows : Array CoverageRow := #[]
  for i in [0:anchored.size] do
    coverageRows := coverageRows.push
      { id := (anchored.getD i default).id, disposition := dispositions.getD i default,
        state := .absent, witnesses := [] }
  .ok { rows := anchored, dispositions := dispositions, paths := paths,
        skippedIdl := skippedIdl, censusText := censusText,
        rowsModuleText := renderRowsModule coverageRows denominator,
        denominator := denominator }

/-! ## Reading the pinned input -/

def readPinnedInput (root : System.FilePath) : IO (Except String ByteArray) := do
  let path := root / inputRelativePath
  unless ← path.pathExists do
    return .error s!"census: the pinned specification source is missing: {inputRelativePath}"
  let bytes ← IO.FS.readBinFile path
  let observed := Gates.Sha256.hexDigest bytes
  if observed != inputDigest then
    return .error
      s!"census: refusing bytes that are not the pin; {inputRelativePath} has SHA-256 {observed}, expected {inputDigest}"
  return .ok bytes

def readAuthored (root : System.FilePath) : IO (Except String (String × String × String)) := do
  let mut texts : Array String := #[]
  for relative in [dispositionsRelativePath, overridesRelativePath, rulesRelativePath] do
    let path := root / relative
    unless ← path.pathExists do
      return .error s!"census: missing authored input {relative}"
    texts := texts.push (← IO.FS.readFile path)
  return .ok (texts.getD 0 "", texts.getD 1 "", texts.getD 2 "")

def buildFromRoot (root : System.FilePath) : IO (Except String (ByteArray × Built)) := do
  match ← readPinnedInput root with
  | .error message => return .error message
  | .ok bytes =>
    match ← readAuthored root with
    | .error message => return .error message
    | .ok (dispositionsText, overridesText, rulesText) =>
      match build bytes dispositionsText overridesText rulesText with
      | .error message => return .error message
      | .ok built => return .ok (bytes, built)

/-! ## Commands -/

def summaryLine (built : Built) : String := Id.run do
  let mut kinds : Array String := #[]
  for k in Kind.all do
    kinds := kinds.push s!"{k.name} {countKind built.rows k}"
  let mut dispositionCounts : Array String := #[]
  for d in Disposition.all do
    dispositionCounts := dispositionCounts.push s!"{d.name} {countDisposition built.dispositions d}"
  let excluded := built.rows.size - built.denominator
  let text :=
    s!"census: {built.rows.size} rows ({String.intercalate ", " kinds.toList}); " ++
    s!"dispositions ({String.intercalate ", " dispositionCounts.toList}); " ++
    s!"denominator {built.denominator}, excluded {excluded}; " ++
    s!"{built.skippedIdl} IDL statement(s) outside the row vocabulary"
  return text

def write (root : System.FilePath) : IO UInt32 := do
  match ← buildFromRoot root with
  | .error message =>
    IO.eprintln s!"FAIL {message}"
    return 1
  | .ok (_, built) =>
    IO.FS.createDirAll (root / "generated")
    IO.FS.writeBinFile (root / censusRelativePath) built.censusText.toUTF8
    IO.FS.writeBinFile (root / rowsRelativePath) built.rowsModuleText.toUTF8
    IO.println (summaryLine built)
    IO.println s!"WROTE {censusRelativePath}"
    IO.println s!"WROTE {rowsRelativePath}"
    return 0

/-- Independent verification of one on-disk census line against the pinned
bytes: the anchor must occur exactly once, at the recorded span start, and the
digest of the recorded span must match. This path never consults the scanner,
so it fails on a hand-edited row as well as on a scanner change. -/
def verifyLine (bs : ByteArray) (line : String) (lineNumber : Nat) : Except String Unit := do
  let fields ← splitRow line
  if fields.size != 7 then
    .error s!"census line {lineNumber}: expected seven fields, found {fields.size}"
  let kindText := fields.getD 0 ""
  let rowId := fields.getD 1 ""
  let anchor := fields.getD 2 ""
  let some _ := Kind.ofString? kindText
    | .error s!"census line {lineNumber}: unknown kind {kindText}"
  let some spanB := (fields.getD 3 "").toNat?
    | .error s!"census line {lineNumber} ({rowId}): malformed span start"
  let some spanE := (fields.getD 4 "").toNat?
    | .error s!"census line {lineNumber} ({rowId}): malformed span end"
  let recorded := fields.getD 5 ""
  if !Nat.ble spanB spanE || !Nat.ble spanE bs.size then
    .error s!"census line {lineNumber} ({rowId}): span [{spanB}, {spanE}) is not inside the pinned bytes"
  let anchorBytes := anchor.toUTF8
  let hits := occurrences bs anchorBytes 4
  if hits.size != 1 then
    .error s!"census line {lineNumber} ({rowId}): anchor occurs {hits.size} time(s), expected exactly one"
  if hits.getD 0 0 != spanB then
    .error s!"census line {lineNumber} ({rowId}): anchor occurs at byte {hits.getD 0 0} but the span starts at {spanB}"
  let observed := Gates.Sha256.hexDigest (bs.extract spanB spanE)
  if observed != recorded then
    .error s!"census line {lineNumber} ({rowId}): span digest {observed} does not match the recorded {recorded}"
  .ok ()

def check (root : System.FilePath) : IO UInt32 := do
  match ← buildFromRoot root with
  | .error message =>
    IO.eprintln s!"FAIL {message}"
    return 1
  | .ok (bytes, built) =>
    let mut failures : Array String := #[]
    let censusPath := root / censusRelativePath
    let rowsPath := root / rowsRelativePath
    let mut onDisk : String := ""
    if ← censusPath.pathExists then
      onDisk ← IO.FS.readFile censusPath
      if onDisk.toUTF8 != built.censusText.toUTF8 then
        failures := failures.push
          s!"{censusRelativePath} is not byte-identical to a fresh regeneration; run `{regenerateCommand}`"
    else
      failures := failures.push s!"missing {censusRelativePath}; run `{regenerateCommand}`"
    if ← rowsPath.pathExists then
      let rowsOnDisk ← IO.FS.readFile rowsPath
      if rowsOnDisk.toUTF8 != built.rowsModuleText.toUTF8 then
        failures := failures.push
          s!"{rowsRelativePath} is not byte-identical to a fresh regeneration; run `{regenerateCommand}`"
    else
      failures := failures.push s!"missing {rowsRelativePath}; run `{regenerateCommand}`"
    -- Independent re-verification of every on-disk row.
    let allLines := Gates.Common.lines onDisk
    let expectedHeader := censusHeader built.rows.size
    match allLines with
    | [] => failures := failures.push s!"{censusRelativePath} is empty"
    | header :: dataLines =>
      if header != expectedHeader then
        failures := failures.push s!"{censusRelativePath} header line does not match the generator identity"
      let mut lineNumber := 1
      for line in dataLines do
        lineNumber := lineNumber + 1
        match verifyLine bytes line lineNumber with
        | .ok _ => pure ()
        | .error message => failures := failures.push message
      if dataLines.length != built.rows.size then
        failures := failures.push
          s!"{censusRelativePath} carries {dataLines.length} rows; the generator produced {built.rows.size}"
    if failures.isEmpty then
      IO.println (summaryLine built)
      IO.println
        s!"PASS census: input digest is the pin, every anchor occurs exactly once at its span start, every span digest recomputes, every row has exactly one disposition, and both projections are byte-identical to a fresh regeneration"
      return 0
    IO.eprintln s!"FAIL census: {failures.size} problem(s)"
    for failure in failures do IO.eprintln s!"  {failure}"
    return 1

/-- The coverage block of `docs/SPEC-COVERAGE.md`.

At P1 the numerator is empty, so `green` and `partial` are zero for every row
and the block is determined by the census and its dispositions.
`WhatwgStreamsTest/Audit/SpecCoverage.lean` fails the build if any row leaves
`absent` or acquires a witness, so that emptiness is gated rather than
assumed. The first witness moves this printer onto a Lean emit. -/
def report (root : System.FilePath) : IO UInt32 := do
  match ← buildFromRoot root with
  | .error message =>
    IO.eprintln s!"FAIL {message}"
    return 1
  | .ok (_, built) =>
    let total := built.rows.size
    let denominator := built.denominator
    let excluded := total - denominator
    let green := 0
    let partialCount := 0
    let absent := denominator - green - partialCount
    let ownedWithGreen := 0
    IO.println
      s!"WHATWG Streams (b9ba9f49) coverage: denominator {denominator}; owned-with-green {ownedWithGreen}/{denominator};"
    IO.println
      s!"green {green}, partial {partialCount}, absent {absent}; census {total} rows, {excluded} excluded"
    IO.println "partial:"
    return 0

def usage : String :=
  "usage: lake exe census           check the census against the pinned specification bytes\n" ++
  "       lake exe census --write   regenerate the census and the frozen coverage row list\n" ++
  "       lake exe census --report  print the coverage block of docs/SPEC-COVERAGE.md"

/-- Command-line entry, invoked by `bin/Census.lean`. -/
def cli (args : List String) : IO UInt32 := do
  let root ← Gates.Common.projectRoot
  match args with
  | [] => check root
  | ["--write"] => write root
  | ["--report"] => report root
  | _ =>
    IO.eprintln usage
    return 2

end Gates.Census
