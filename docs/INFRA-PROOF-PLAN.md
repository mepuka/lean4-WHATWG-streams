# The Infra Standard as proof obligations

Status: **DRAFT, 2026-09-03.** An analysis of `vendor/whatwg-infra-3f984adc/infra.bs`
at the W5 pin, written before any Infra census, contract, or declaration
exists. Every `INFRA-R*` item is a proposed ruling and every theorem shape is
a proposal; nothing here is proved and nothing here is a Model Claim. The
document answers three questions: what the pinned text obliges a model to
prove, which Lean carriers make those obligations statable, and how the
repository's existing P1 to P3 machinery (census, breadth scaffold, breaker
packet, proof graph) applies to a standard that is almost entirely
definitions rather than algorithm blocks.

Authority order for this document: the pinned `infra.bs` first;
`docs/REIFICATION-STRATEGY.md` (RS-1, Stratum V) for what an Infra theorem
is for; `docs/AGENT-ROUTING.md` for the leaf-versus-graph threshold;
`test/contracts/queue-with-sizes.contract.md` and `docs/DATA-DAG.md` as the
worked precedent for a packet over first-order data.

## 1. What the text is, measured

The Infra Standard is 2,405 lines and 178 non-ignored `<dfn>` definitions,
of which 177 carry `export`. Only 18 of them sit inside a `<div algorithm>`
block. The remaining definitions are one-sentence prose ("To byte-lowercase a
byte sequence, increase each byte in the range 0x41 to 0x5A by 0x20") or a
`<p>` ending in a colon followed by a bare `<ol>` of numbered steps (byte
prefix, byte less than, code unit prefix and suffix, the substrings, collect
a sequence of code points, the three splits, concatenate, map get, forgiving
base64 decode). There are no internal slots, no IDL, and no requirements
list of the piping kind.

Two consequences follow for the repository's machinery.

- The Streams census generator finds rows by `<div algorithm`, slot tables,
  and IDL blocks, so run unchanged over `infra.bs` it would yield 18 `op`
  rows and nothing else. The Infra census needs a definition-keyed row
  source (section 6).
- The `green` criterion of `docs/SPEC-COVERAGE.md` is "every step or clause
  is a named theorem". For a one-sentence definition the clause is the
  sentence, and the theorem is a pointwise characterization of the
  transcribed function. That is a lighter obligation per row than a Streams
  algorithm, and there are about eight times as many rows per packet.

Definitions by section, from the pinned bytes:

| Section | Definitions | Character |
| --- | --- | --- |
| `terminology`, `privacy`, `other-specs` | 5 | conformance vocabulary; no carrier |
| `algorithm-*`, `assertions` | 6 | control-flow conventions: abort when, if aborted, while, continue, break, Assert |
| `booleans`, `numbers` | 10 | boolean and nine N-bit integer ranges |
| `bytes`, `byte-sequences` | 12 | byte, ASCII byte, sequences, case folding, prefix, ordering, isomorphic decode |
| `code-points` | 21 | code point and its value, surrogates, scalar value, noncharacter, 14 ASCII and control classes |
| `strings` | 37 | code units, two lengths, three restricted string kinds, convert, prefix/suffix/order, six substring forms, codecs, case folding, whitespace, position-variable scanning, splits, concatenate |
| `singleton` | 4 | allowed, blocked, failure, success |
| `lists`, `stacks`, `queues`, `sets` | 43 | list vocabulary, stack and queue conventions, ordered set operations, the two ranges |
| `maps` | 18 | ordered map vocabulary |
| `structs`, `tuples` | 4 | struct, tuple, item, name |
| `json` | 10 | four JavaScript-value forms, five Infra-value forms, one conversion |
| `forgiving-base64` | 2 | encode by reference to RFC 4648 §4; decode fully specified |
| `namespaces` | 6 | six string constants |

## 2. What the Streams library already consumes

The join that decides packet order is which Infra definitions the Streams
text cites. Counting `[=list/…=]`, `[=map/…=]`, `[=set/…=]`, and
`[=struct/…=]` links in the pinned `index.bs`:

| Infra definition | Citations in Streams |
| --- | --- |
| list / is empty | 24 |
| map / exists | 25 |
| struct / items | 13 |
| list / append | 10 |
| list / for each | 9 |
| list / remove | 8 |
| list / size | 3 |
| set / append | 2 |

Streams cites nothing from the text families (strings, code points, bytes as
sequences), nothing from JSON, and nothing from base64. Every Streams
citation lands in the data-structure sections, so the data-structure packet
is the one whose theorems the P4 Streams packet can cite by row id instead
of citing Lean's `List` directly. That is the citation chain
`docs/SPEC-COVERAGE.md` wants and the reason section 7 opens with it.

## 3. Carriers: the rulings every packet depends on

Stratum V's deliverables are carriers, codecs, canonical forms, and the laws
between them (RS-1). The carriers are where the Infra text and Lean's
standard library disagree, and each disagreement is a ruling a breaker must
request rather than a choice a builder may make silently.

### INFRA-R1: a string is `List UInt16`, never Lean `String`

The pinned text: a string "is a sequence of 16-bit unsigned integers, also
known as code units", its length "is the number of code units it contains",
and its code point length is a second, different number. The spec's own
example is the string of code units 0xD83D, 0xDCA9, 0xD800, which "when
interpreted as containing code points" is U+1F4A9 followed by the lone
surrogate U+D800.

Lean's `String` is UTF-8 over `Char`, and `Char` excludes surrogates by its
`valid` field. So Lean `String` cannot represent the spec's example, and
`String.length` counts what the spec calls code point length. The R0
research already measured that nearly every `String` operation reaches
`Classical.choice`, which is a second reason to keep it out of the model.

Proposed carrier: `Whatwg.Infra.String := List UInt16` at the proof face,
with `Array UInt16` as a representation-edge realizer if one is ever needed.
The "interpreted as containing code points" conversion becomes a total
function `codePoints : List UInt16 → List CodePoint` transcribed from the
rule Infra's note states (pair a leading and a following trailing surrogate
into one scalar value; leave any other unit as its own code point). ECMA-262
§6.1.4 is the cited owner of that rule and needs a provenance row as
evidence, the way the reference implementation is evidence for Streams.

### INFRA-R2: a code point is a bounded number, never `Char`

A code point is "in the range U+0000 to U+10FFFF, inclusive" and a scalar
value is "a code point that is not a surrogate". `Char` is exactly the
scalar values, so `Char` is the right carrier for `ScalarValue` and the
wrong one for `CodePoint`.

Proposed carriers: `structure CodePoint where val : Nat; le : val ≤ 0x10FFFF`
(or `Fin 0x110000`), `ScalarValue := { c : CodePoint // ¬ c.Surrogate }`,
and a proved equivalence `ScalarValue ≃ Char` through `Char.valid`, which is
`val < 0xD800 ∨ (0xDFFF < val ∧ val < 0x110000)`. That equivalence is the
bridge edge of the text proof graph, and it is what lets a downstream
standard hand a scalar value string to a Lean `String` consumer with a
theorem rather than a cast. A scalar value string is then a `List UInt16`
whose `codePoints` are all scalar values, and its image under the
equivalence is a Lean `String`.

### INFRA-R3: "return nothing", "return failure", and asserted preconditions

The text returns "nothing" from `pop`, `peek`, and `dequeue` on an empty
container, returns the singleton `failure` from forgiving-base64 decode, and
guards the substrings, `slice`, and map `get` with `Assert:` steps on
indices. P3 already ruled `Option` for "return nothing" in
`DequeueValue` (`WS-DATA-CE-004`), and the coverage numerator already
discharges an assertion by typing when the carrier cannot represent its
negation.

Proposed ruling, extending both: `Option` for "nothing" and for the singleton
`failure` when the algorithm otherwise returns a value; the four singletons
as a two-constructor and a two-constructor inductive only where an algorithm
returns them bare; and an `Assert:` on an index becomes a hypothesis
argument (`(h : start + len ≤ s.length)`) so the step is discharged
`byTyping` and the function stays total without a clamp the text does not
state. The alternative, clamping, would invent behaviour on inputs the text
calls a bug in the calling document.

### INFRA-R4: normalize newlines is a single left-to-right pass

"Replace every U+000D CR U+000A LF code point pair with a single U+000A LF
code point, and then replace every remaining U+000D CR code point with a
U+000A LF code point." On the input CR CR LF the two readings differ: a
single non-overlapping pass gives CR LF, then LF LF, a result of length 2; a
pass repeated to a fixed point gives CR LF, then LF, a result of length 1.
The text does not say which. Hosts implement the single pass (the idiom is
`replace(/\r\n?/g, "\n")`), and "then" reads as sequencing rather than
iteration, so the proposed ruling is the single pass, with the length-2
result on CR CR LF frozen as the discriminating witness.

### INFRA-R5: map key equality is `DecidableEq κ`

The map section carries the editors' own comment "we have to define key
equality for this to be truly sound", and the text never does. The model
takes decidable equality on the key type as a parameter, which makes
"contains an entry with a given key" a decidable predicate and the no-
duplicate-keys invariant a `Nodup` on the projected keys. A standard that
keys a map by object identity (Streams does not; its maps are keyed by
strings and by first-order records) would supply its own equality.

### INFRA-R6: JSON numbers inherit the P3-R1 carrier question

An Infra value is "a string, boolean, number, null, list, or string-keyed
map". The number is a JavaScript Number, the same carrier P3 abstracted as
`SizeClass` and then ruled to the exact `DyadicSize`. The JSON value type
should be parameterized by its number type exactly as the queue was, so
that the P3-R1 answer instantiates it and no second ruling is opened. The
parameter also keeps the JSON packet free of any claim about `Float`.

### INFRA-R7: value semantics; aliasing is outside the model

"Clone" is defined as `slice` with default bounds, and the map clone note
says appending to a value inside a clone modifies the original, "as they
both point to the same list". In a first-order value model `clone l = l` is
a theorem and the aliasing example has no statement. The ruling records
that reference identity is a Stratum S concern owned by the consuming
standard's state carrier (RS-Q2), never by Infra. This is a claim boundary,
not a dropped step: the numerator can mark the aliasing note `evidenceOnly`.

### INFRA-R8: RFC 4648 §4 is a second pinned authority for encode

"Forgiving-base64 encode" is defined by reference to section 4 of RFC 4648
and decode looks up "Table 1: The Base 64 Alphabet" of the same RFC. Neither
the algorithm nor the table is in the pinned bytes. The precedent is FIPS
180-4 for SHA-256: pin the RFC text by digest under `docs/PROVENANCE.md`,
transcribe the alphabet and the encoder, and cite the RFC span the way the
hash lane cited FIPS sections. Without the pin the encode row cannot leave
`absent`, and the round-trip theorem of section 5 has one side undefined.

### Smaller rulings the packets will also need

| Id | Question | Proposed answer |
| --- | --- | --- |
| INFRA-R9 | `insert` is defined `for=list,set`; inserting an item an ordered set already contains breaks the no-duplicates semantic and the text is silent | a hypothesis argument on the set form, matching R3 |
| INFRA-R10 | "the range n to m, inclusive … as long as m ≥ n" leaves m < n unspecified; the exclusive form says m = n is empty | both forms total and empty when the bound condition fails; the decision is stated, so a later standard that relies on it cites a ruling and not an accident |
| INFRA-R11 | there is no `UInt128` in Lean core | `BitVec 128` for the 128-bit unsigned integer; `UInt8/16/32/64` and `Int8/16/32/64` for the others, with the range theorem per type as the row's witness |
| INFRA-R12 | struct and tuple have no carrier; each standard's structs become Lean `structure`s | the four rows are `owned` and discharged `byTyping`, since the Lean structure mechanism is the transcription |
| INFRA-R13 | the control-flow conventions (abort when, while, continue, break, Assert) | `evidenceOnly`; they are consumed by the transcription discipline (fuel-bounded recursion for `while`, hypothesis arguments for `Assert`, scoped shapes for `abort when` per RS-3), not modelled as values |

## 4. The obligation families

RS-1 names the Stratum V theorem shapes: codec round trips, injectivity of
encodings on canonical forms, normalization idempotence. Read against the
pinned text those become seven families, and every Infra row falls in
exactly one.

### 4.1 Classification predicates

Fourteen ASCII and control classes on code points, the noncharacter
predicate, two byte classes, four surrogate and scalar-value predicates,
and three restricted string kinds. Each is a
decidable predicate whose witness is its range characterization, for
example `isAsciiDigit c = true ↔ 0x30 ≤ c.val ∧ c.val ≤ 0x39`. The useful
theorems are the lattice the text states between them, since the URL and
MIME parsers branch on exactly these relations:

- ASCII digit ⊆ ASCII upper hex digit ⊆ ASCII hex digit, and likewise the
  lower form; ASCII alpha = upper ∪ lower; alphanumeric = digit ∪ alpha;
- surrogate = leading ∪ trailing with the two disjoint; scalar value =
  ¬ surrogate; C0 control ⊆ control; ASCII tab or newline ⊆ ASCII
  whitespace ⊆ C0 control or space;
- the noncharacter definition enumerates 34 values and a range of 32. The
  theorem that the enumeration equals the closed form
  `0xFDD0 ≤ v ≤ 0xFDEF ∨ v &&& 0xFFFE = 0xFFFE` is a fidelity check on the
  transcription, and its count, 66, is a `decide` receipt.

These rows satisfy every leaf condition of `docs/AGENT-ROUTING.md` and close
with leaf receipts linked to the text graph's construction edge.

### 4.2 Case folding and case-insensitive match

`byte-lowercase`, `byte-uppercase`, `ASCII lowercase`, `ASCII uppercase`, and
the two case-insensitive matches. Obligations: pointwise characterization
(a byte outside 0x41 to 0x5A is unchanged, which is the frame), length
preservation, idempotence, `lower ∘ upper = lower`, the case-insensitive
match is an equivalence relation, and the homomorphism
`isomorphicDecode (byteLowercase b) = asciiLowercase (isomorphicDecode b)`,
which is the first instance of RS-2's "atoms cross by homomorphism".

### 4.3 Prefix, suffix, and ordering

The text gives byte prefix, code unit prefix, and code unit suffix as
`while` loops with an index, and byte less than and code unit less than as
four-step comparisons whose third step asserts in a parenthesis that a
first differing index exists. Obligations:

- the loop equals the structural definition:
  `isPrefix p s = true ↔ ∃ t, s = p ++ t` (core's `List.IsPrefix`), and the
  suffix dually;
- the parenthetical is a theorem: if neither sequence is a prefix of the
  other, a least differing index exists;
- less-than is a strict total order (irreflexive, transitive, trichotomous)
  and agrees with lexicographic order on the unit lists;
- the note that code unit order is not code point order is an executable
  witness: U+FF5E is one unit 0xFF5E and U+1F600 is 0xD83D 0xDE00, so the
  smiley is code unit less than the tilde while its code point is greater.

Sort in ascending and descending order are stated as requirements
("containing the same items … sorted so that … relative order must be the
same"), so they take the `requirement` disposition: a specification
(permutation, sortedness under the supplied less-than, stability) realized
by a named algorithm, exactly as RS-6 treats piping but with no mask because
nothing is relational.

### 4.4 Substrings and the position variable

Six substring forms over code units and code points, and "collect a
sequence of code points" with its position variable that "updates the
position variable in the calling algorithm". The stateful reading
transcribes as a function returning the collected prefix and the new
position; the obligations are that the result is the longest prefix from
the position satisfying the condition (agreement with `List.takeWhile` on
the dropped list), that the new position is the old plus the result's
length, and that the position never passes the end. Substrings: result
length equals the requested length, `substring s 0 s.length = s`, the
positions-between-units reading (substring 0 to 0 of the empty string is
the empty string), and the spec's own 👽 example as a witness that the code
unit and code point substrings of the same positions differ.

### 4.5 Normalization and splitting

Strip newlines, normalize newlines (R4), strip leading and trailing ASCII
whitespace, strip and collapse ASCII whitespace, skip ASCII whitespace, the
three splits, and concatenate. These are the normalization-idempotence
family:

- each strip and normalize is idempotent, its result satisfies the
  normal-form predicate (no CR; no leading or trailing whitespace; no two
  adjacent whitespace and every whitespace is SPACE), and it is the identity
  on inputs already in normal form;
- strictly split then concatenate with the delimiter is the identity, and
  the converse holds exactly when no item contains the delimiter, with the
  failing case (`["a,b"]`) as a witness;
- split on ASCII whitespace yields nonempty tokens containing no whitespace
  and is invariant under strip-and-collapse of the input; split on commas
  keeps empty tokens (`",,"` gives three empty strings) and strips each
  token, which is the lenient-versus-strict contrast the text's note draws
  and a witness pins.

### 4.6 Codecs

Isomorphic encode and decode, ASCII encode and decode, the UTF-16 view of a
string (R1), and forgiving base64 (R8). These are RS-1's round trips and
canonical-form injectivity:

- `isomorphicEncode (isomorphicDecode b) = b` for every byte sequence, and
  `isomorphicDecode (isomorphicEncode s) = s` for every isomorphic string,
  with encode taking the isomorphic-string predicate as a hypothesis (R3);
- `codeUnits (codePoints u) = u` for every unit list, which is the total
  direction; `codePoints (codeUnits ps) = ps` only when `ps` has no adjacent
  leading-then-trailing pair, and that hypothesis is what a counterexample
  row records; `codePointLength ≤ length ≤ 2 · codePointLength`;
- `convert` (replace surrogates with U+FFFD) is idempotent, its result is a
  scalar value string, and it is the identity on scalar value strings;
- the note that isomorphic encode and UTF-8 encode agree on ASCII strings is
  a theorem owed jointly with the Encoding Standard, which is not pinned; the
  row stays `partial` with that bridge named until Encoding has its own pin;
- forgiving base64: `decode (encode b) = some b`; decode is invariant under
  inserting ASCII whitespace anywhere; the failure set is exactly the text's
  (after whitespace removal and padding strip, length ≡ 1 mod 4, or a code
  point outside the 64-symbol alphabet and `+`, `/`), as a decidable
  predicate; padding is stripped only at length ≡ 0 mod 4, so `"YQ="` fails
  while `"YQ"` and `"YQ=="` both decode to `` `a` ``; the text's own note
  that `"YQ"` and `"YR"` decode alike is the non-injectivity witness; and
  `encode (decode s) = s` holds exactly on the canonical inputs (no
  whitespace, padded, zero discarded bits), which is the injectivity-on-
  canonical-forms law. The alphabet's 64 symbols are distinct by `decide`.

### 4.7 Containers and their invariants

Lists, stacks, queues, ordered sets, the ranges, and maps. Lists are core
`List` with agreement lemmas per definition (`append` is `List.concat`,
`prepend` is cons, `has duplicates` is the negation of `Nodup`, `reverse`
is an involution, `slice` under its hypotheses is `drop` then `take`). Two
list definitions carry more than agreement: `remove` returns a boolean that
the text defines as "size decreased", so
`(remove p l).2 = true ↔ ∃ x ∈ l, p x`; and `insert` at index 0 is `prepend`.

Ordered sets and maps carry a checked invariant, `Nodup` on the items and
on the projected keys, and every operation must preserve it. That is what
puts them on the graph route. The laws the text fixes and a mutant could
break:

- set `append` and `prepend` are no-ops on a contained item; set `replace`
  replaces "the first instance of either" and removes the rest, and the
  text's two examples (« a, b, c » and « c, b, a » both give « c, b »)
  are executable witnesses; `equal` is subset both ways and is therefore
  coarser than list identity, so « a, b » and « b, a » are equal sets and
  different lists, which is worth a witness because the section's note says
  order is kept for interoperability;
- intersection and difference take their order from the first operand
  (sublist of it), union has the first operand as a prefix, and each has the
  expected membership characterization;
- `create` from a list keeps first occurrences (agreement with
  `List.eraseDups`);
- map `set` on a contained key updates in place and otherwise appends, so
  `keys (set m k v)` is `keys m` or `keys m ++ [k]`, and a mutant that
  moves an updated key to the end is observable through `get the keys`;
  `get (set m k v) k = some v`, `get (set m k v) k' = get m k'` for `k' ≠ k`,
  `size m = (keys m).length = m.entries.length`, `keys m` is `Nodup` from
  the invariant, and `values m` may repeat.

Stacks and queues are conventions on lists: `pop (push x s) = (some x, s)`,
`peek` agrees with `pop`, and `dequeue` after `enqueue` is FIFO. The Streams
P3 packet already proved a LIFO-versus-FIFO separation (`WS-DATA-CE-010`);
Streams' `[[queue]]` is defined through list `append` and `remove`, so the
Infra list rows and not the Infra queue rows are what its citations reach.

## 5. Which routes and which graphs

Applying the threshold of `docs/AGENT-ROUTING.md`:

| Family | Route | Why |
| --- | --- | --- |
| N-bit integers, booleans, singletons, namespaces, byte and code point classes | leaf receipts | finite alphabets and passive records; construction has no invariant beyond the type; each receipt links to the construction edge of its family graph |
| structs and tuples | `byTyping` rows | R12 |
| text: code points, strings, codecs, case, ordering, substrings, scanning, normalization, splits | graph `INFRA-PG-TEXT` | owns two semantic bridges (`ScalarValue ≃ Char`, the UTF-16 view), codec round trips, and normalization laws |
| data: lists, stacks, queues, ordered sets, ranges, maps, sort | graph `INFRA-PG-DATA` | checked `Nodup` invariants, a `requirement` row realized by an algorithm, composition laws |
| forgiving base64 | graph `INFRA-PG-BASE64` | refuses inputs with a stated failure set, codec round trip, a second pinned authority |
| JSON | graph `INFRA-PG-JSON` | a recursive value type with a `Nodup`-keyed map, conversions across the JavaScript boundary |

Each graph carries the ten edges. The edges that will stay `required-open`
longest are predictable: `bridges` on `INFRA-PG-TEXT` until Encoding is
pinned (the UTF-8 agreement note), `targets` everywhere until a Schema
lowering exists (the `effects` package at `5611c3a` ships `Effects/Algebra`
only and has no `Value` or `Schema` layer, so "Stratum V lowers as Schema"
has no Lean counterpart yet), and `bridges` on `INFRA-PG-JSON` for the
`%JSON.parse%` and `%JSON.stringify%` calls, which are foreign until a JSON
grammar atom exists at Stratum A.

The JSON graph deserves one design note. The Infra-value conversions are
stated over JavaScript values, and there is no JavaScript value model in
this estate. The first-order image of `JSON.parse` is small: null,
boolean, number, string, arrays, and plain objects with string keys in
`[[OwnPropertyKeys]]` order. A `JsonJsValue` inductive of exactly that shape
makes "convert a JSON-derived JavaScript value to an Infra value" and its
inverse total functions with a proved round trip in both directions, and
leaves only the two intrinsic calls as foreign-boundary rows with profiles.
The `!` (never abrupt) on the Infra-value serialization then has a real
obligation behind it: every value of the image stringifies, which the model
states and the host profile is checked against.

## 6. The census a definition-keyed standard needs

The generator keeps its representation (byte offsets, unique anchors, span
digests through `Hash.Sha256`, fuel-bounded scanning) and gains one row
source and one kind.

- Row source: every `<dfn export …>` outside `class=example`, `class=note`,
  and `ignore` attributes. The anchor is the `<dfn>` opener; the span runs
  from the start of the enclosing `<p>` or `<div algorithm>` to the end of
  the immediately following `<ol>` when the paragraph ends in a colon, and
  otherwise to the next blank line, which is the rule `census/rules.tsv`
  already uses for locators.
- Kind: the five kinds (`op`, `slot`, `idl`, `requirement`, `rule`) cover
  algorithms and predicates but not carrier definitions ("a byte sequence is
  a sequence of bytes"). Proposal: a sixth kind `type` for the 24 or so
  carrier rows, with predicates and one-sentence transformations as `op`.
  `docs/SPEC-COVERAGE.md` owns the kind vocabulary and takes the one-line
  change; `Gates.Census.Kind` gains a constructor.
- Duplicate names: `code unit substring` and `code point substring` each
  appear three times with distinct `lt=` attributes. The row id derives from
  the `lt=` text when present (`op.code-unit-substring-by-positions`), which
  keeps ids unique without inventing names.
- Inputs: `census/infra/dispositions.tsv`, `overrides.tsv`, `rules.tsv`
  beside the Streams set, selected by a generator argument; outputs
  `generated/infra-census.tsv` and `WhatwgTest/Audit/Infra/SpecCoverageRows.lean`.
  Coverage then reports two blocks with two denominators, as the scope note
  in `docs/SPEC-COVERAGE.md` anticipates.

Expected denominator, from the section table in section 1: 178 definitions,
less 5 conformance rows and 6 control-flow rows (`evidenceOnly` per R13),
less the four JavaScript-value JSON rows (`hostOnly`, they are intrinsic
calls), leaves 163, of which roughly 150 are `owned`, one is
`requirement` (the two sort rows share one specification), and the balance
are `foreignBoundary` at the JSON and Encoding edges. The census decides the
exact numbers; the estimate exists so a landed census far from it is
questioned.

## 7. Packet order and what each packet closes

Breadth precedes depth: the Infra P2 places a declaration-free stub per
module of section 8 first. Then packets in this order, each a
breaker-authored contract with a red battery, the P3 precedent scaled to
the family.

| Packet | Rows | Rulings consumed | Why this position |
| --- | --- | --- | --- |
| I1 data structures (`INFRA-PG-DATA`) | 61 | R3, R5, R7, R9, R10 | every Infra definition Streams cites is here, so P4 can cite Infra row ids; the invariants are `Nodup` and the laws are list algebra, the cheapest graph to close |
| I2 text carriers and codecs (`INFRA-PG-TEXT`, first half) | code points, strings, isomorphic and ASCII codecs, case, ordering, substrings | R1, R2, R3 | fixes the two carrier rulings every later standard depends on; the `ScalarValue ≃ Char` bridge is the first cross-carrier theorem |
| I3 scanning and normalization (`INFRA-PG-TEXT`, second half) | position variable, whitespace, splits, concatenate | R4 | the URL and MIME parsers consume exactly these; idempotence and split/concatenate round trips |
| I4 forgiving base64 (`INFRA-PG-BASE64`) | 2 rows, one external pin | R8 | the first complete Stratum V codec with a failure set, the model for every Stratum A atom's contract |
| I5 JSON (`INFRA-PG-JSON`) | 10 rows | R6, R12 | the recursive value universe; opens the first foreign-boundary profile in Infra |
| leaves, closed alongside I1 | integers, booleans, singletons, namespaces, byte and code point classes | R11, R13 | leaf receipts only; no packet of their own |

Sizing against P3: the queue packet froze 99 theorems over 10 census rows
because each Streams algorithm has several clauses and two refusal sets.
I1 has six times the rows and roughly one to three theorems per row (an
agreement lemma, an invariant-preservation lemma, a characterization), so
80 to 150 frozen statements is the expected battery, with the set `replace`
and map `set` laws and the sort requirement carrying most of the proof
effort.

## 8. Module tree

Mirroring `Whatwg/Streams`, one root per standard and one module per
family, every module reached from `Whatwg/Infra.lean`:

```text
Whatwg/Infra.lean
Whatwg/Infra/Primitive/Integer.lean     N-bit integers (R11)
Whatwg/Infra/Primitive/Singleton.lean   allowed, blocked, failure, success (R3)
Whatwg/Infra/Bytes/Byte.lean            byte, ASCII byte, value
Whatwg/Infra/Bytes/Sequence.lean        byte sequence, case folding, prefix, order, isomorphic decode
Whatwg/Infra/Text/CodePoint.lean        code point, surrogates, scalar value, classes, Char bridge (R2)
Whatwg/Infra/Text/String.lean           code units, code point view, restricted kinds, convert (R1)
Whatwg/Infra/Text/Order.lean            code unit prefix, suffix, less than
Whatwg/Infra/Text/Substring.lean        the six substrings
Whatwg/Infra/Text/Codec.lean            isomorphic encode, ASCII encode and decode
Whatwg/Infra/Text/Case.lean             ASCII lowercase, uppercase, case-insensitive
Whatwg/Infra/Text/Whitespace.lean       strip, normalize (R4), collapse
Whatwg/Infra/Text/Scan.lean             position variable, collect, skip, splits, concatenate
Whatwg/Infra/Data/List.lean             list vocabulary, stack and queue conventions
Whatwg/Infra/Data/OrderedSet.lean       ordered set with Nodup, set algebra, the ranges (R9, R10)
Whatwg/Infra/Data/OrderedMap.lean       ordered map with Nodup keys (R5)
Whatwg/Infra/Data/Sort.lean             the stable-sort requirement and its realizer
Whatwg/Infra/Json/Value.lean            InfraValue over a number parameter (R6)
Whatwg/Infra/Json/JsImage.lean          JsonJsValue and the two conversions
Whatwg/Infra/Json/Boundary.lean         %JSON.parse% and %JSON.stringify% profiles
Whatwg/Infra/Base64/Alphabet.lean       RFC 4648 Table 1 (R8)
Whatwg/Infra/Base64/Codec.lean          encode, forgiving decode, failure predicate
Whatwg/Infra/Namespaces.lean            six constants
Whatwg/Infra/Audit/Receipts.lean        as in Streams
Whatwg/Infra/Audit/Closure.lean
```

Test side: `WhatwgTest/Infra/…` batteries and axiom reports per packet,
`test/contracts/infra-<family>.contract.md`, counterexample ids `WI-<AREA>-CE-nnn`
(`WI-DATA-`, `WI-TEXT-`, `WI-B64-`, `WI-JSON-`) in the central register, and
`docs/INFRA-DAG.md` holding the four graphs the way `docs/DATA-DAG.md` holds
`DATA-PG-QUEUE`.

Import direction: `Whatwg.Infra` imports nothing from `Whatwg.Streams`, and
`Whatwg.Streams` may import `Whatwg.Infra` from P4 on. The P3 modules stay
as landed; whether `Whatwg.Streams.Data.Queue` later cites `op.list-append`
through an agreement lemma is a P4 decision and does not reopen P3.

## 9. Counterexample seeds

Attack shapes a breaker can mint on day one, each forcing a representation
or a statement. Ids are placeholders until the register assigns them.

| Seed | Attacked statement | Witness | Forced repair |
| --- | --- | --- | --- |
| WI-TEXT-1 | a code point may be `Char` | the spec's example units 0xD83D 0xDCA9 0xD800 have no `Char` image for the third | R2 |
| WI-TEXT-2 | a string may be Lean `String` | `"👽"` has spec length 2 and code point length 1; `String.length` gives 1 | R1 |
| WI-TEXT-3 | code unit order agrees with code point order | U+FF5E versus U+1F600 | none; the disagreement is the text's own note, frozen as a theorem |
| WI-TEXT-4 | normalize newlines may iterate to a fixed point | CR CR LF gives length 2 under one pass and 1 under iteration | R4 |
| WI-TEXT-5 | `codePoints` and `codeUnits` are inverse in both directions | the code point list [U+D83D, U+DE00] round-trips to [U+1F600] | the hypothesis on the units-of-points direction |
| WI-TEXT-6 | split on commas and split on whitespace agree up to delimiter | `",,"` versus `"  "` | none; the lenient-versus-strict contrast is frozen |
| WI-DATA-1 | map `set` on an existing key may append | `keys` order changes | the in-place law |
| WI-DATA-2 | set `equal` is list identity | « a, b » and « b, a » | `equal` as mutual subset, distinct from `is` |
| WI-DATA-3 | set `replace` may dedupe keeping the last occurrence | « c, b, a » replace a with c gives « b, c » under the mutant and « c, b » under the text | the first-instance law |
| WI-DATA-4 | `remove` may return unit | the boolean is "size decreased" | the return law |
| WI-B64-1 | padding may always be stripped | `"YQ="` must fail while `"YQ"` and `"YQ=="` succeed | the length ≡ 0 mod 4 guard |
| WI-B64-2 | decode is injective | `"YQ"` and `"YR"` | canonical-form statement of the encode-after-decode law |
| WI-B64-3 | whitespace inside the input fails | `"Y Q"` decodes | the removal step precedes every check |

## 10. What this document does not decide

The census numbers, the exact row ids, the kind vocabulary change, and every
`INFRA-R*` ruling wait for their owning process: the census generator's
`--standard infra` slice (an Infra P1 in `docs/WHATWG-PACKAGE-PLAN.md`
terms), then the I1 breaker packet, which states R3, R5, R7, R9, and R10 as
ruling requests in its section 6 the way the queue packet stated `P3-R1`. No
Lean declaration follows from this document, and `Whatwg/Infra.lean` stays
declaration-free until that packet is frozen.
