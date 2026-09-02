import Lean
import Lean.Util.CollectAxioms
import Gates
import Whatwg.Streams
import WhatwgTest.Audit.SpecCoverageRows

/-!
# Specification-coverage numerator

`docs/SPEC-COVERAGE.md` owns the metric; this module is its numerator side.
The frozen row list is `WhatwgTest/Audit/SpecCoverageRows.lean`, which
`lake exe census --write` generates alongside
`generated/spec-algorithm-census.tsv` so that a table of several hundred rows (450 at P1.1) is never
transcribed by hand. Both projections are covered by the census gate's
byte-for-byte drift check, so neither can be edited without failing
`lake exe census`.

The generated row list carries one fact per row, its joined disposition, and
gates every row `absent` with no witness. What is authored here is the freeze,
the checks, and the numerator proper: the coverage state of each row that has
left `absent`, the step-by-step justification behind that state, and the
witness theorems with their frozen statements.

## The emit, and why it is Lean data rather than a generated file

`lake exe census --report` prints the coverage block from `emit` below. The
census executable's root, `bin/Census.lean`, imports this module and hands
`emit` to `Gates.Census.cli`; `Gates/` cannot import a test-side module, so
the direction is inverted at the entry point rather than inside the gate.

The alternative the P1 landing left open was a generated projection under
`generated/` written at elaboration. It was rejected: the state and witness
columns of such a file are exactly the columns no `Gates/` code can
recompute, so its drift gate could only ever re-derive the census-owned
columns and the one number the estate quotes would sit on a hand-editable
line. Compiled Lean data cannot drift from the module that declares it, and
the checks below run before the executable that reads it can link. The cost
is recorded in `Gates/AGENTS.md`: `lake exe census --write` now needs this
module to elaborate, so a census change that invalidates the freeze is
repaired here in the same edit.

## What the elaboration-time gate below decides

- the frozen rows and the census projection carry the same ids in the same
  order and the same number of them, and the header agrees with the count;
- every disposition recorded in `census/overrides.tsv` reached its row, and
  every row that file names exists;
- the denominator recomputed from the frozen dispositions matches the frozen
  `expectedDenominator`, using the exclusion rule of `docs/SPEC-COVERAGE.md`;
- every claimed row exists, is claimed once, and is inside the denominator: a
  witness on an excluded row fails the build;
- every step of a claimed row carries at least one justification, and the
  claimed state is the one the step table forces: `green` exactly when no step
  is left to a foreign boundary, `partial` exactly when at least one is;
- every witness names a constant that exists, is a `theorem`, and whose kernel
  receipt is inside the ceiling and equal to the receipt frozen below;
- the witness set, the receipt table, the `StatementSnapshot` list, and the
  `#check (@name : proposition)` ascriptions in this file agree in every
  direction and in the same order; and
- every row that is not claimed is `absent` with no witness, and the three
  expected totals hold.

A row is `green` only when every step or clause of its pinned algorithm text
is a named theorem over the Lean model. Two step kinds are not theorems and
are recorded as such: a step left to a foreign boundary (`DATA-FB-*` of
`docs/DATA-DAG.md`), which forces `partial`; and an `Assert:` step whose
negation the model's typing makes unrepresentable, which is discharged by
construction and leaves nothing to prove. The second reading is a judgment,
disclosed here so it can be overturned in one place: requiring a theorem for
those assertion steps as well would move `op.enqueue-value-with-size`,
`op.dequeue-value`, `op.peek-queue-value` and `op.reset-queue` from `green` to
`partial`, and no other row.

Reading files at elaboration puts this module in `MetaM`, which reaches
`Classical.choice`, so its exact name is listed in
`WhatwgTest/Audit/AxiomGate.lean`'s `auditImplementationModules`. The
section-to-disposition join itself is not recomputed here: it needs the pinned
`index.bs`, and `lake exe census` is the gate that owns it.
-/

open Lean

universe u

namespace WhatwgTest.Audit.SpecCoverage

open Gates.Census

/-- Census rows frozen for this commit. A change here is deliberate. -/
def expectedRowTotal : Nat := 450

/-- Rows inside the coverage denominator, that is, rows whose disposition is
not `evidenceOnly`, `refused` or `targetOnly`. -/
def expectedDenominator : Nat := 410

/-- Rows whose every step or clause is a named theorem. -/
def expectedGreen : Nat := 12

/-- Rows with at least one witness and at least one step left to a foreign
boundary. -/
def expectedPartialCount : Nat := 6

/-- Rows inside the denominator with no witness. -/
def expectedAbsentInDenominator : Nat := 392

/-- The frozen numerator rows: id and disposition, every state `absent`. The
states and witnesses are layered on by `claims` below. -/
def rows : Array CoverageRow := SpecCoverageRows.rows

/-! ## The claim vocabulary -/

/-- Why one step or clause of a pinned algorithm is or is not covered. -/
inductive Justification where
  /-- A named `theorem` over the Lean model, frozen by an ascription below. -/
  | theoremWitness (name : String)
  /-- An `Assert:` step whose negation the model's typing cannot represent, so
  no proposition is left to prove. Never used for a step that states an
  action, a result, or a refusal. -/
  | byTyping (reason : String)
  /-- A step this packet drops rather than models, named by its
  `docs/DATA-DAG.md` foreign-boundary row. One of these anywhere in the step
  table forces `partial`. -/
  | atBoundary (boundary : String) (note : String)
  deriving Inhabited

/-- One step or clause of the pinned algorithm text, with its justifications.
`text` is the pinned wording, shortened but never paraphrased into a claim the
text does not make. -/
structure Step where
  label : String
  text : String
  justifications : List Justification
  deriving Inhabited

/-- One census row that has left `absent`. -/
structure RowClaim where
  id : String
  state : CoverageState
  /-- The observation mask the witnesses are stated under. This family is
  equational over first-order data and its contract states no mask; that is
  recorded here rather than a mask being invented. -/
  mask : String
  /-- What the state means for this row, and what `partial` is short of. -/
  comment : String
  steps : List Step
  deriving Inhabited

private def theoremNamesOf (justifications : List Justification) : List String :=
  justifications.foldl
    (fun acc justification =>
      match justification with
      | .theoremWitness name => acc ++ [name]
      | _ => acc)
    []

private def hasBoundary (step : Step) : Bool :=
  step.justifications.any fun justification =>
    match justification with
    | .atBoundary _ _ => true
    | _ => false

/-- The row's witnesses, in step order, without repetition. -/
def RowClaim.witnesses (claim : RowClaim) : List String :=
  claim.steps.foldl
    (fun acc step =>
      (theoremNamesOf step.justifications).foldl
        (fun inner name => if inner.contains name then inner else inner ++ [name])
        acc)
    []

private def thm (name : String) : Justification := .theoremWitness name

/-! ## The claims

One entry per census row that P3 moves. Every step text below was read from
the pinned `vendor/whatwg-streams-b9ba9f49/index.bs` at the byte span
`generated/spec-algorithm-census.tsv` records for the row, not from
`docs/DATA-DAG.md`, which proposes states and does not decide them. -/

private def queueMask : String :=
  "none: every operation of this family is a total function of first-order data and the frozen contract states no observation mask"

/-- The claimed rows. -/
def claims : Array RowClaim := #[
  { id := "op.enqueue-value-with-size"
    state := .green
    mask := queueMask
    comment :=
      "Every step that states an action or a refusal is a named theorem. Step 1 is an Assert about slot presence: the argument type Queue carries both slots, so the assertion has no representable negation and nothing is left to prove. The Web IDL conversion that produces the size is upstream of this algorithm, not a step of it."
    steps := [
      { label := "step 1"
        text := "Assert: |container| has [[queue]] and [[queueTotalSize]] internal slots."
        justifications := [.byTyping "Queue carries entries and totalSize as fields; no well-typed call can violate the assertion"] },
      { label := "step 2"
        text := "If ! IsNonNegativeNumber(|size|) is false, throw a RangeError exception."
        justifications := [
          thm "Whatwg.Streams.Data.enqueueValueWithSize_error_iff",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_refuses_nan",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_refuses_negative",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_refuses_negInfinity"] },
      { label := "step 3"
        text := "If |size| is +infinity, throw a RangeError exception."
        justifications := [
          thm "Whatwg.Streams.Data.enqueueValueWithSize_error_iff",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_refuses_posInfinity"] },
      { label := "step 4"
        text := "Append a new value-with-size with value |value| and size |size| to |container|.[[queue]]."
        justifications := [thm "Whatwg.Streams.Data.enqueueValueWithSize_entries"] },
      { label := "step 5"
        text := "Set |container|.[[queueTotalSize]] to |container|.[[queueTotalSize]] + |size|."
        justifications := [thm "Whatwg.Streams.Data.enqueueValueWithSize_totalSize"] }] },
  { id := "op.dequeue-value"
    state := .green
    mask := queueMask
    comment :=
      "Steps 2 through 7 are named theorems. Step 6's clamp is modelled inside the totalSize equation and, under the ruled exact carrier, additionally proved unreachable: it is witnessed as present-and-vacuous rather than as a taken branch. Step 1 is an Assert the type discharges."
    steps := [
      { label := "step 1"
        text := "Assert: |container| has [[queue]] and [[queueTotalSize]] internal slots."
        justifications := [.byTyping "Queue carries entries and totalSize as fields; no well-typed call can violate the assertion"] },
      { label := "step 2"
        text := "Assert: |container|.[[queue]] is not empty."
        justifications := [thm "Whatwg.Streams.Data.dequeueValue_isNone_iff"] },
      { label := "step 3"
        text := "Let |valueWithSize| be |container|.[[queue]][0]."
        justifications := [thm "Whatwg.Streams.Data.dequeueValue_value_eq_head"] },
      { label := "step 4"
        text := "Remove |valueWithSize| from |container|.[[queue]]."
        justifications := [thm "Whatwg.Streams.Data.dequeueValue_entries"] },
      { label := "step 5"
        text := "Set |container|.[[queueTotalSize]] to |container|.[[queueTotalSize]] minus |valueWithSize|'s size."
        justifications := [thm "Whatwg.Streams.Data.dequeueValue_totalSize"] },
      { label := "step 6"
        text := "If |container|.[[queueTotalSize]] < 0, set |container|.[[queueTotalSize]] to 0. (This can occur due to rounding errors.)"
        justifications := [
          thm "Whatwg.Streams.Data.dequeueValue_totalSize",
          thm "Whatwg.Streams.Data.dequeueValue_totalSize_not_negative",
          thm "Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact"] },
      { label := "step 7"
        text := "Return |valueWithSize|'s value."
        justifications := [thm "Whatwg.Streams.Data.dequeueValue_value_eq_head"] }] },
  { id := "op.peek-queue-value"
    state := .green
    mask := queueMask
    comment :=
      "Steps 2 through 4 are named theorems, and the FIFO agreement with DequeueValue is proved beside them. Step 1 is an Assert the type discharges."
    steps := [
      { label := "step 1"
        text := "Assert: |container| has [[queue]] and [[queueTotalSize]] internal slots."
        justifications := [.byTyping "Queue carries entries and totalSize as fields; no well-typed call can violate the assertion"] },
      { label := "step 2"
        text := "Assert: |container|.[[queue]] is not empty."
        justifications := [thm "Whatwg.Streams.Data.peekQueueValue_isSome_iff"] },
      { label := "step 3"
        text := "Let |valueWithSize| be |container|.[[queue]][0]."
        justifications := [thm "Whatwg.Streams.Data.peekQueueValue_eq_head"] },
      { label := "step 4"
        text := "Return |valueWithSize|'s value."
        justifications := [
          thm "Whatwg.Streams.Data.peekQueueValue_eq_head",
          thm "Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue"] }] },
  { id := "op.reset-queue"
    state := .green
    mask := queueMask
    comment :=
      "Both assignments are named theorems, and the pair of them is stated at once by resetQueue_eq. Step 1 is an Assert the type discharges."
    steps := [
      { label := "step 1"
        text := "Assert: |container| has [[queue]] and [[queueTotalSize]] internal slots."
        justifications := [.byTyping "Queue carries entries and totalSize as fields; no well-typed call can violate the assertion"] },
      { label := "step 2"
        text := "Set |container|.[[queue]] to a new empty list."
        justifications := [
          thm "Whatwg.Streams.Data.resetQueue_entries",
          thm "Whatwg.Streams.Data.resetQueue_eq"] },
      { label := "step 3"
        text := "Set |container|.[[queueTotalSize]] to 0."
        justifications := [
          thm "Whatwg.Streams.Data.resetQueue_totalSize",
          thm "Whatwg.Streams.Data.resetQueue_eq"] }] },
  { id := "op.is-non-negative-number"
    state := .partialCoverage
    mask := queueMask
    comment :=
      "Short of green by step 1: the Web IDL type test has no counterpart on a typed carrier and is foreign boundary DATA-FB-IDL-DOUBLE. Steps 2, 3 and 4 are the definitional equation together with the three classified constants."
    steps := [
      { label := "step 1"
        text := "If |v| is not a Number, return false."
        justifications := [.atBoundary "DATA-FB-IDL-DOUBLE" "the model receives an already-converted carrier value, so the type test is not statable"] },
      { label := "step 2"
        text := "If |v| is NaN, return false."
        justifications := [
          thm "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq",
          thm "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_nan"] },
      { label := "step 3"
        text := "If |v| < 0, return false."
        justifications := [
          thm "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq",
          thm "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_negInfinity"] },
      { label := "step 4"
        text := "Return true."
        justifications := [
          thm "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq",
          thm "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_posInfinity"] }] },
  { id := "op.validate-and-normalize-high-water-mark"
    state := .green
    mask := queueMask
    comment :=
      "The algorithm behind this anchor id is ExtractHighWaterMark and normalizes nothing; every one of its four steps is a named theorem, and the note that +infinity is explicitly allowed is proved rather than assumed."
    steps := [
      { label := "step 1"
        text := "If |strategy|[highWaterMark] does not exist, return |defaultHWM|."
        justifications := [thm "Whatwg.Streams.Data.extractHighWaterMark_absent"] },
      { label := "step 2"
        text := "Let |highWaterMark| be |strategy|[highWaterMark]."
        justifications := [thm "Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted"] },
      { label := "step 3"
        text := "If |highWaterMark| is NaN or |highWaterMark| < 0, throw a RangeError exception."
        justifications := [
          thm "Whatwg.Streams.Data.extractHighWaterMark_error_iff",
          thm "Whatwg.Streams.Data.extractHighWaterMark_refuses_nan",
          thm "Whatwg.Streams.Data.extractHighWaterMark_refuses_negative",
          thm "Whatwg.Streams.Data.extractHighWaterMark_refuses_negInfinity"] },
      { label := "step 4"
        text := "Return |highWaterMark|."
        justifications := [thm "Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted"] },
      { label := "note"
        text := "+infinity is explicitly allowed as a valid high water mark. It causes backpressure to never be applied."
        justifications := [thm "Whatwg.Streams.Data.extractHighWaterMark_allows_posInfinity"] }] },
  { id := "op.make-size-algorithm-from-size-function"
    state := .green
    mask := queueMask
    comment :=
      "Both branches and the inner invocation are named theorems. The callback's body is never modelled (DATA-FB-CALLBACK): step 2.1 is witnessed as the oracle application it is, which is what the estate's representation rule makes of a foreign body, and is not a step left unproved."
    steps := [
      { label := "step 1"
        text := "If |strategy|[size] does not exist, return an algorithm that returns 1."
        justifications := [
          thm "Whatwg.Streams.Data.extractSizeAlgorithm_absent",
          thm "Whatwg.Streams.Data.extractSizeAlgorithm_absent_invoke",
          thm "Whatwg.Streams.Data.SizeAlgorithm.invoke_one"] },
      { label := "step 2"
        text := "Return an algorithm that performs the following steps, taking a |chunk| argument."
        justifications := [thm "Whatwg.Streams.Data.extractSizeAlgorithm_present"] },
      { label := "step 2.1"
        text := "Return the result of invoking |strategy|[size] with argument list of |chunk|."
        justifications := [thm "Whatwg.Streams.Data.SizeAlgorithm.invoke_foreign"] }] },
  { id := "op.cqs-constructor"
    state := .green
    mask := queueMask
    comment :=
      "The one constructor step is a named theorem, and that the constructor validates nothing is witnessed by a NaN high water mark being stored and read back. The dictionary member arrives already converted to an unrestricted double, which is upstream of this algorithm."
    steps := [
      { label := "step 1"
        text := "Set this.[[highWaterMark]] to |init|[highWaterMark]."
        justifications := [
          thm "Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark",
          thm "Whatwg.Streams.Data.CountQueuingStrategy.make_accepts_nan"] }] },
  { id := "op.cqs-high-water-mark"
    state := .green
    mask := queueMask
    comment :=
      "The getter is the slot projection, and the theorem states the observable content of the step: what the constructor stored is what the getter returns."
    steps := [
      { label := "step 1"
        text := "Return this.[[highWaterMark]]."
        justifications := [thm "Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark"] }] },
  { id := "op.cqs-size"
    state := .partialCoverage
    mask := queueMask
    comment :=
      "Short of green by its only step: the relevant-global lookup is foreign boundary DATA-FB-REALM, and the pinned WPT observation of one function object per realm is refused rather than modelled. What is proved is that the getter yields the named realm function and that the class read as a strategy dictionary carries that name."
    steps := [
      { label := "step 1"
        text := "Return this's relevant global object's count queuing strategy size function."
        justifications := [
          .atBoundary "DATA-FB-REALM" "relevant-global lookup and per-realm function identity are not modelled; the name is an argument",
          thm "Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm_eq",
          thm "Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_size"] }] },
  { id := "op.count-queuing-strategy-size-function"
    state := .partialCoverage
    mask := queueMask
    comment :=
      "Short of green by steps 2 and 3: CreateBuiltinFunction, the function's length and name, the realm, the callback context, and the per-global installation are host construction and are not modelled. Step 1's behaviour is proved of every oracle satisfying CountSizeProfile, which is that step transcribed as a hypothesis on the foreign boundary."
    steps := [
      { label := "step 1"
        text := "Let |steps| be the following steps: Return 1."
        justifications := [
          thm "Whatwg.Streams.Data.CountQueuingStrategy.size_answers_one",
          thm "Whatwg.Streams.Data.CountQueuingStrategy.size_ignores_chunk",
          thm "Whatwg.Streams.Data.CountQueuingStrategy.size_never_throws"] },
      { label := "step 2"
        text := "Let |F| be ! CreateBuiltinFunction(|steps|, 0, size, empty list, |globalObject|'s relevant Realm)."
        justifications := [.atBoundary "DATA-FB-REALM" "host function construction, its length and name, and the realm are not modelled"] },
      { label := "step 3"
        text := "Set |globalObject|'s count queuing strategy size function to a Function that represents a reference to |F|, with callback context equal to |globalObject|'s relevant settings object."
        justifications := [.atBoundary "DATA-FB-REALM" "per-global installation and callback context are not modelled"] }] },
  { id := "op.blqs-constructor"
    state := .green
    mask := queueMask
    comment :=
      "The one constructor step is a named theorem, with a NaN high water mark stored and read back to witness that nothing is validated here."
    steps := [
      { label := "step 1"
        text := "Set this.[[highWaterMark]] to |init|[highWaterMark]."
        justifications := [
          thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark",
          thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_accepts_nan"] }] },
  { id := "op.blqs-high-water-mark"
    state := .green
    mask := queueMask
    comment :=
      "The getter is the slot projection, and the theorem states that what the constructor stored is what the getter returns."
    steps := [
      { label := "step 1"
        text := "Return this.[[highWaterMark]]."
        justifications := [thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark"] }] },
  { id := "op.blqs-size"
    state := .partialCoverage
    mask := queueMask
    comment :=
      "Short of green by its only step, for the same reason as op.cqs-size: the relevant-global lookup is DATA-FB-REALM."
    steps := [
      { label := "step 1"
        text := "Return this's relevant global object's byte length queuing strategy size function."
        justifications := [
          .atBoundary "DATA-FB-REALM" "relevant-global lookup and per-realm function identity are not modelled; the name is an argument",
          thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq",
          thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size"] }] },
  { id := "op.byte-length-queuing-strategy-size-function"
    state := .partialCoverage
    mask := queueMask
    comment :=
      "Short of green by all three steps: GetV itself is DATA-FB-CALLBACK, and CreateBuiltinFunction with its length and name, the realm, the callback context and the per-global installation are host construction. What is proved is the Web IDL reading of each of the three answers GetV can give, and that an absent byteLength becomes NaN and is then refused by the enqueue that follows."
    steps := [
      { label := "step 1"
        text := "Let |steps| be the following steps, given |chunk|: Return ? GetV(|chunk|, byteLength)."
        justifications := [
          .atBoundary "DATA-FB-CALLBACK" "the GetV call itself is not modelled; its three answers enter as typed decisions",
          thm "Whatwg.Streams.Data.byteLengthSize_number",
          thm "Whatwg.Streams.Data.byteLengthSize_undefined",
          thm "Whatwg.Streams.Data.byteLengthSize_thrown",
          thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.size_eq_byteLength",
          thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused"] },
      { label := "step 2"
        text := "Let |F| be ! CreateBuiltinFunction(|steps|, 1, size, empty list, |globalObject|'s relevant Realm)."
        justifications := [.atBoundary "DATA-FB-REALM" "host function construction, its length and name, and the realm are not modelled"] },
      { label := "step 3"
        text := "Set |globalObject|'s byte length queuing strategy size function to a Function that represents a reference to |F|, with callback context equal to |globalObject|'s relevant settings object."
        justifications := [.atBoundary "DATA-FB-REALM" "per-global installation and callback context are not modelled"] }] },
  { id := "slot.queue"
    state := .green
    mask := queueMask
    comment :=
      "A slot row has clauses rather than steps. The content clause is the type of the field, and every write the four queue-with-sizes operations perform on the slot is a named theorem. The slot's installation on a specific stream object is a P4, P5 and P6 question and is not a clause of this row."
    steps := [
      { label := "clause 1"
        text := "[[queue]] is a list of value-with-sizes, where a value-with-size is a struct with the two items value and size."
        justifications := [.byTyping "Queue.entries has type List (QueueEntry a Size) and QueueEntry carries value and size, so the clause has no representable violation"] },
      { label := "clause 2"
        text := "Various specification objects contain a queue-with-sizes, represented by the object having two paired internal slots, always named [[queue]] and [[queueTotalSize]]; the following abstract operations ensure that the two internal slots stay synchronized."
        justifications := [
          thm "Whatwg.Streams.Data.Queue.empty_entries",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_entries",
          thm "Whatwg.Streams.Data.dequeueValue_entries",
          thm "Whatwg.Streams.Data.resetQueue_entries"] }] },
  { id := "slot.queue-total-size"
    state := .partialCoverage
    mask := queueMask
    comment :=
      "Short of green by the carrier clause: the slot is defined as a JavaScript Number and the ruled model carrier is exact, so the running total the specification warns about is not reproduced. DATA-FB-ROUNDING names the gap and counterexample WS-DATA-CE-001 measures it at one ulp of 1.0. Every write of the slot by the four operations, and its relation to the sizes in [[queue]], are named theorems."
    steps := [
      { label := "clause 1"
        text := "[[queueTotalSize]] is a JavaScript Number, i.e. a double-precision floating point number; keeping a running total is not equivalent to adding up the size of all chunks in [[queue]]."
        justifications := [.atBoundary "DATA-FB-ROUNDING" "the ruled carrier is exact, so the specification's own rounding warning has no model counterpart"] },
      { label := "clause 2"
        text := "The total size of all the chunks stored in [[queue]], kept synchronized with it by the four abstract operations."
        justifications := [
          thm "Whatwg.Streams.Data.Queue.WF_iff",
          thm "Whatwg.Streams.Data.Queue.empty_totalSize",
          thm "Whatwg.Streams.Data.enqueueValueWithSize_totalSize",
          thm "Whatwg.Streams.Data.dequeueValue_totalSize",
          thm "Whatwg.Streams.Data.resetQueue_totalSize"] }] },
  { id := "slot.high-water-mark"
    state := .green
    mask := queueMask
    comment :=
      "The census carries this slot for ByteLengthQueuingStrategy, whose pinned text is the whole of the row: instances have the slot, and it stores the value given in the constructor. CountQueuingStrategy defines a slot of the same name at its own anchor and the census carries no second row for it; that is recorded as a P1.1 question in docs/DATA-DAG.md and is not settled here."
    steps := [
      { label := "clause 1"
        text := "Instances of ByteLengthQueuingStrategy have a [[highWaterMark]] internal slot."
        justifications := [.byTyping "ByteLengthQueuingStrategy carries highWaterMark as its one field"] },
      { label := "clause 2"
        text := "storing the value given in the constructor."
        justifications := [thm "Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark"] }] }]

/-! ## Receipts

The kernel receipt of every witness, measured with `#print axioms` and frozen
here. The gate recomputes each one and fails on drift in either direction; the
ceiling is `propext`, `Quot.sound` and `Classical.choice` (ruling R-11). -/

/-- Each witness with the axiom set `#print axioms` reports for it. -/
def witnessReceipts : List (String × String) := [
  ("Whatwg.Streams.Data.enqueueValueWithSize_error_iff", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_refuses_nan", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_refuses_negative", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_refuses_negInfinity", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_refuses_posInfinity", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_entries", "propext"),
  ("Whatwg.Streams.Data.enqueueValueWithSize_totalSize", "propext"),
  ("Whatwg.Streams.Data.dequeueValue_isNone_iff", "propext"),
  ("Whatwg.Streams.Data.dequeueValue_value_eq_head", "propext"),
  ("Whatwg.Streams.Data.dequeueValue_entries", "propext"),
  ("Whatwg.Streams.Data.dequeueValue_totalSize", "propext"),
  ("Whatwg.Streams.Data.dequeueValue_totalSize_not_negative", "propext"),
  ("Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact", "propext"),
  ("Whatwg.Streams.Data.peekQueueValue_isSome_iff", "propext"),
  ("Whatwg.Streams.Data.peekQueueValue_eq_head", "propext"),
  ("Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue", "propext"),
  ("Whatwg.Streams.Data.resetQueue_entries", "none"),
  ("Whatwg.Streams.Data.resetQueue_eq", "none"),
  ("Whatwg.Streams.Data.resetQueue_totalSize", "none"),
  ("Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq", "none"),
  ("Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_nan", "propext"),
  ("Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_negInfinity", "propext"),
  ("Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_posInfinity", "propext"),
  ("Whatwg.Streams.Data.extractHighWaterMark_absent", "none"),
  ("Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted", "propext"),
  ("Whatwg.Streams.Data.extractHighWaterMark_error_iff", "propext"),
  ("Whatwg.Streams.Data.extractHighWaterMark_refuses_nan", "propext"),
  ("Whatwg.Streams.Data.extractHighWaterMark_refuses_negative", "propext"),
  ("Whatwg.Streams.Data.extractHighWaterMark_refuses_negInfinity", "propext"),
  ("Whatwg.Streams.Data.extractHighWaterMark_allows_posInfinity", "propext"),
  ("Whatwg.Streams.Data.extractSizeAlgorithm_absent", "none"),
  ("Whatwg.Streams.Data.extractSizeAlgorithm_absent_invoke", "none"),
  ("Whatwg.Streams.Data.SizeAlgorithm.invoke_one", "none"),
  ("Whatwg.Streams.Data.extractSizeAlgorithm_present", "none"),
  ("Whatwg.Streams.Data.SizeAlgorithm.invoke_foreign", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.make_accepts_nan", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm_eq", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_size", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.size_answers_one", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.size_ignores_chunk", "none"),
  ("Whatwg.Streams.Data.CountQueuingStrategy.size_never_throws", "propext"),
  ("Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark", "none"),
  ("Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_accepts_nan", "none"),
  ("Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq", "none"),
  ("Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size", "none"),
  ("Whatwg.Streams.Data.byteLengthSize_number", "none"),
  ("Whatwg.Streams.Data.byteLengthSize_undefined", "none"),
  ("Whatwg.Streams.Data.byteLengthSize_thrown", "none"),
  ("Whatwg.Streams.Data.ByteLengthQueuingStrategy.size_eq_byteLength", "none"),
  ("Whatwg.Streams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused", "propext"),
  ("Whatwg.Streams.Data.Queue.empty_entries", "none"),
  ("Whatwg.Streams.Data.Queue.WF_iff", "none"),
  ("Whatwg.Streams.Data.Queue.empty_totalSize", "none")
]

/-! ## StatementSnapshot

Every witness name, in the order the claims first reach it, and in the same
order as the `#check (@name : proposition)` ascriptions at the end of this
file. The gate checks the three orders against each other. -/

/-- Every witness name, in claim order. -/
def statementSnapshot : List String := [
  "Whatwg.Streams.Data.enqueueValueWithSize_error_iff",
  "Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible",
  "Whatwg.Streams.Data.enqueueValueWithSize_refuses_nan",
  "Whatwg.Streams.Data.enqueueValueWithSize_refuses_negative",
  "Whatwg.Streams.Data.enqueueValueWithSize_refuses_negInfinity",
  "Whatwg.Streams.Data.enqueueValueWithSize_refuses_posInfinity",
  "Whatwg.Streams.Data.enqueueValueWithSize_entries",
  "Whatwg.Streams.Data.enqueueValueWithSize_totalSize",
  "Whatwg.Streams.Data.dequeueValue_isNone_iff",
  "Whatwg.Streams.Data.dequeueValue_value_eq_head",
  "Whatwg.Streams.Data.dequeueValue_entries",
  "Whatwg.Streams.Data.dequeueValue_totalSize",
  "Whatwg.Streams.Data.dequeueValue_totalSize_not_negative",
  "Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact",
  "Whatwg.Streams.Data.peekQueueValue_isSome_iff",
  "Whatwg.Streams.Data.peekQueueValue_eq_head",
  "Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue",
  "Whatwg.Streams.Data.resetQueue_entries",
  "Whatwg.Streams.Data.resetQueue_eq",
  "Whatwg.Streams.Data.resetQueue_totalSize",
  "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq",
  "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_nan",
  "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_negInfinity",
  "Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_posInfinity",
  "Whatwg.Streams.Data.extractHighWaterMark_absent",
  "Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted",
  "Whatwg.Streams.Data.extractHighWaterMark_error_iff",
  "Whatwg.Streams.Data.extractHighWaterMark_refuses_nan",
  "Whatwg.Streams.Data.extractHighWaterMark_refuses_negative",
  "Whatwg.Streams.Data.extractHighWaterMark_refuses_negInfinity",
  "Whatwg.Streams.Data.extractHighWaterMark_allows_posInfinity",
  "Whatwg.Streams.Data.extractSizeAlgorithm_absent",
  "Whatwg.Streams.Data.extractSizeAlgorithm_absent_invoke",
  "Whatwg.Streams.Data.SizeAlgorithm.invoke_one",
  "Whatwg.Streams.Data.extractSizeAlgorithm_present",
  "Whatwg.Streams.Data.SizeAlgorithm.invoke_foreign",
  "Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark",
  "Whatwg.Streams.Data.CountQueuingStrategy.make_accepts_nan",
  "Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm_eq",
  "Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_size",
  "Whatwg.Streams.Data.CountQueuingStrategy.size_answers_one",
  "Whatwg.Streams.Data.CountQueuingStrategy.size_ignores_chunk",
  "Whatwg.Streams.Data.CountQueuingStrategy.size_never_throws",
  "Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark",
  "Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_accepts_nan",
  "Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq",
  "Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size",
  "Whatwg.Streams.Data.byteLengthSize_number",
  "Whatwg.Streams.Data.byteLengthSize_undefined",
  "Whatwg.Streams.Data.byteLengthSize_thrown",
  "Whatwg.Streams.Data.ByteLengthQueuingStrategy.size_eq_byteLength",
  "Whatwg.Streams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused",
  "Whatwg.Streams.Data.Queue.empty_entries",
  "Whatwg.Streams.Data.Queue.WF_iff",
  "Whatwg.Streams.Data.Queue.empty_totalSize"
]

/-! ## The emit

The numerator's rows: the frozen row list with the claimed states and
witnesses layered on. `bin/Census.lean` hands this to `Gates.Census.cli`,
which prints the coverage block from it and cross-checks it against a fresh
census regeneration. -/

def emit : Array CoverageRow :=
  rows.map fun row =>
    match claims.find? (fun claim => claim.id == row.id) with
    | none => row
    | some claim => { row with state := claim.state, witnesses := claim.witnesses }

/-! ## The gate -/

private def findProjectRoot (directory : System.FilePath) : IO System.FilePath := do
  let mut current := directory
  for _ in [0:64] do
    if ← (current / "Whatwg.lean").pathExists then
      return current
    match current.parent with
    | some parent => current := parent
    | none => throw <| IO.userError "spec coverage gate: could not locate the project root"
  throw <| IO.userError "spec coverage gate: project-root search exceeded 64 parents"

/-- The `kind|id` pairs of the census projection, in file order, with the row
count its header records. -/
def parseCensus (text : String) : Except String (Array String × Nat) := Id.run do
  match Gates.Common.lines text with
  | [] => return .error "the census projection is empty"
  | header :: dataLines =>
    let expectedHeader := censusHeader dataLines.length
    if header != expectedHeader then
      return .error "the census projection header does not record its own row count and generator identity"
    let mut ids : Array String := #[]
    let mut lineNumber := 1
    for line in dataLines do
      lineNumber := lineNumber + 1
      match splitRow line with
      | .error message => return .error s!"census line {lineNumber}: {message}"
      | .ok fields =>
        if fields.size != 7 then
          return .error s!"census line {lineNumber}: expected seven fields, found {fields.size}"
        let kindText := fields.getD 0 ""
        let rowId := fields.getD 1 ""
        match Kind.ofString? kindText with
        | none => return .error s!"census line {lineNumber}: unknown kind {kindText}"
        | some kind =>
          if !rowId.startsWith (kind.name ++ ".") then
            return .error s!"census line {lineNumber}: row id {rowId} does not carry its own kind"
          ids := ids.push rowId
    return .ok (ids, dataLines.length)

/-- A dotted string as a `Name`, so that a witness can be authored as text and
resolved against the compiled environment. -/
private def nameOfString (text : String) : Name :=
  (text.splitOn ".").foldl (fun acc component => Name.mkStr acc component) Name.anonymous

/-- The receipt spelling of a measured axiom set: the axiom names in the order
Lean reports them, or `none`. -/
private def renderReceipt (axioms : Array Name) : String :=
  if axioms.isEmpty then "none"
  else String.intercalate ", " (axioms.toList.map fun axiomName => axiomName.toString)

private def ceiling : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- The witness names of every `#check (@name :` ascription in this file, in
file order. The ascriptions are what freeze the exact statements, so the gate
reads them back rather than trusting that they were kept in step. -/
private def ascriptionNames (source : String) : List String :=
  (Gates.Common.lines source).foldl
    (fun acc line =>
      if line.startsWith "#check (@" then
        let rest := Gates.Common.dropChars line "#check (@".length
        acc ++ [(rest.splitOn " ").headD rest]
      else acc)
    []

open Elab Command in
elab "#spec_coverage_gate" : command => do
  let environment ← getEnv
  let sourceFile := System.FilePath.mk (← getFileName)
  let some sourceDirectory := sourceFile.parent
    | throwError "spec coverage gate: source file has no parent directory"
  let projectRoot ← liftIO <| findProjectRoot sourceDirectory
  let censusPath := projectRoot / censusRelativePath
  unless ← liftIO censusPath.pathExists do
    throwError "spec coverage gate: missing {censusRelativePath}; run `{regenerateCommand}`"
  let overridesPath := projectRoot / overridesRelativePath
  unless ← liftIO overridesPath.pathExists do
    throwError "spec coverage gate: missing {overridesRelativePath}"
  let censusText ← liftIO <| IO.FS.readFile censusPath
  let overridesText ← liftIO <| IO.FS.readFile overridesPath
  let sourceText ← liftIO <| IO.FS.readFile sourceFile

  let (censusIds, headerCount) ←
    match parseCensus censusText with
    | .ok pair => pure pair
    | .error message => throwError "spec coverage gate: {message}"
  let overrides ←
    match parseOverrides overridesText with
    | .ok parsed => pure parsed
    | .error message => throwError "spec coverage gate: {message}"

  -- Counts, frozen against the authored literals in this file.
  if rows.size != expectedRowTotal then
    throwError "spec coverage gate: the frozen row list holds {rows.size} rows; expectedRowTotal is {expectedRowTotal}"
  if SpecCoverageRows.rowTotal != expectedRowTotal then
    throwError "spec coverage gate: the generated rowTotal is {SpecCoverageRows.rowTotal}; expectedRowTotal is {expectedRowTotal}"
  if censusIds.size != expectedRowTotal then
    throwError "spec coverage gate: {censusRelativePath} holds {censusIds.size} rows; expectedRowTotal is {expectedRowTotal}"
  if headerCount != expectedRowTotal then
    throwError "spec coverage gate: the census header records {headerCount} rows; expectedRowTotal is {expectedRowTotal}"

  -- Ids, in both directions and in order. Both files are sorted by kind then
  -- id, so equality of the sequences is equality of the sets plus the order.
  for i in [0:expectedRowTotal] do
    let frozen := (rows.getD i default).id
    let projected := censusIds.getD i ""
    if frozen != projected then
      throwError "spec coverage gate: row {i} is {frozen} in the frozen list and {projected} in {censusRelativePath}"
  for id in censusIds do
    unless rows.any (fun r => r.id == id) do
      throwError "spec coverage gate: {censusRelativePath} carries {id}, which the frozen list does not"
  for row in rows do
    unless censusIds.contains row.id do
      throwError "spec coverage gate: the frozen list carries {row.id}, which {censusRelativePath} does not"

  -- Row ids are unique.
  for i in [1:rows.size] do
    if (rows.getD i default).id == (rows.getD (i - 1) default).id then
      throwError "spec coverage gate: duplicate frozen row id {(rows.getD i default).id}"

  -- Every authored override reached its row, and named a row that exists.
  for entry in overrides do
    match rows.find? (fun r => r.id == entry.rowId) with
    | none =>
      throwError "spec coverage gate: {overridesRelativePath} names {entry.rowId}, which is not a census row"
    | some row =>
      if row.disposition != entry.disposition then
        throwError "spec coverage gate: {entry.rowId} carries {row.disposition.name} but {overridesRelativePath} dispositions it {entry.disposition.name}"

  -- The denominator, recomputed from the frozen dispositions.
  let denominator := rows.foldl (fun acc r => if r.disposition.excluded then acc else acc + 1) 0
  if denominator != expectedDenominator then
    throwError "spec coverage gate: the frozen dispositions give a denominator of {denominator}; expectedDenominator is {expectedDenominator}"
  if SpecCoverageRows.denominator != expectedDenominator then
    throwError "spec coverage gate: the generated denominator is {SpecCoverageRows.denominator}; expectedDenominator is {expectedDenominator}"

  -- Every claim names a census row once, inside the denominator, and states a
  -- coverage state its own step table forces.
  let mut seen : Array String := #[]
  let mut witnessOrder : List String := []
  for claim in claims do
    if seen.contains claim.id then
      throwError "spec coverage gate: {claim.id} is claimed twice"
    seen := seen.push claim.id
    let some row := rows.find? (fun r => r.id == claim.id)
      | throwError "spec coverage gate: {claim.id} is claimed but is not a census row"
    if row.disposition.excluded then
      throwError "spec coverage gate: {claim.id} is dispositioned {row.disposition.name}, which is outside the denominator, yet carries witnesses"
    if claim.state == CoverageState.absent then
      throwError "spec coverage gate: {claim.id} is claimed yet states absent; an absent row carries no claim"
    if claim.mask.isEmpty then
      throwError "spec coverage gate: {claim.id} names no observation mask"
    if claim.comment.isEmpty then
      throwError "spec coverage gate: {claim.id} carries no comment"
    if claim.steps.isEmpty then
      throwError "spec coverage gate: {claim.id} lists no step of its pinned algorithm text"
    let mut boundarySteps : List String := []
    for step in claim.steps do
      if step.justifications.isEmpty then
        throwError "spec coverage gate: {claim.id} {step.label} carries no justification"
      if hasBoundary step then
        boundarySteps := boundarySteps ++ [step.label]
    if claim.state == CoverageState.green && !boundarySteps.isEmpty then
      throwError "spec coverage gate: {claim.id} is green, but {boundarySteps} of its pinned text is left to a foreign boundary; the state that step table forces is partial"
    if claim.state == CoverageState.partialCoverage && boundarySteps.isEmpty then
      throwError "spec coverage gate: {claim.id} is partial, yet no step of it is left to a foreign boundary"
    if claim.witnesses.isEmpty then
      throwError "spec coverage gate: {claim.id} left absent with no witness"
    for name in claim.witnesses do
      unless witnessOrder.contains name do
        witnessOrder := witnessOrder ++ [name]

  -- Every witness resolves to a theorem whose receipt is frozen and inside
  -- the ceiling.
  for name in witnessOrder do
    let witnessName := nameOfString name
    match environment.find? witnessName with
    | none => throwError "spec coverage gate: witness {name} names no declaration"
    | some (.thmInfo _) =>
      let axioms ← collectAxioms witnessName
      for axiomName in axioms do
        unless ceiling.contains axiomName do
          throwError "spec coverage gate: witness {name} reaches {axiomName}, which is outside the ceiling {ceiling}"
      let measured := renderReceipt axioms
      match witnessReceipts.find? (fun entry => entry.1 == name) with
      | none => throwError "spec coverage gate: witness {name} has no frozen receipt"
      | some entry =>
        if entry.2 != measured then
          throwError "spec coverage gate: witness {name} carries the frozen receipt {entry.2} and measures {measured}"
    | some _ => throwError "spec coverage gate: witness {name} is not a theorem"

  -- The receipt table, the snapshot list, and the ascriptions in this file
  -- agree with the witness set in both directions and in the same order.
  for entry in witnessReceipts do
    unless witnessOrder.contains entry.1 do
      throwError "spec coverage gate: the receipt table carries {entry.1}, which no row claims"
  if witnessReceipts.length != witnessOrder.length then
    throwError "spec coverage gate: the receipt table holds {witnessReceipts.length} entries and the claims name {witnessOrder.length} witnesses"
  if statementSnapshot != witnessOrder then
    throwError "spec coverage gate: the StatementSnapshot list is not the witness names in claim order"
  let ascriptions := ascriptionNames sourceText
  if ascriptions != witnessOrder then
    throwError "spec coverage gate: the #check ascriptions of this file are {ascriptions.length} names in an order that is not the {witnessOrder.length} witness names in claim order"

  -- Every row the claims do not name is absent with no witness, and the emit
  -- carries the claims exactly.
  for row in rows do
    unless seen.contains row.id do
      if row.state != CoverageState.absent then
        throwError "spec coverage gate: {row.id} is {row.state.name} in the frozen list yet carries no claim"
      unless row.witnesses.isEmpty do
        throwError "spec coverage gate: {row.id} carries witnesses {row.witnesses} yet no claim"
  if emit.size != rows.size then
    throwError "spec coverage gate: the emit holds {emit.size} rows and the frozen list {rows.size}"
  for i in [0:rows.size] do
    if (emit.getD i default).id != (rows.getD i default).id then
      throwError "spec coverage gate: the emit reorders row {i}"

  -- The totals, frozen against the authored literals.
  let green := emit.foldl (fun acc row => if row.state == CoverageState.green then acc + 1 else acc) 0
  let partialRows :=
    emit.foldl (fun acc row => if row.state == CoverageState.partialCoverage then acc + 1 else acc) 0
  if green != expectedGreen then
    throwError "spec coverage gate: {green} rows are green; expectedGreen is {expectedGreen}"
  if partialRows != expectedPartialCount then
    throwError "spec coverage gate: {partialRows} rows are partial; expectedPartialCount is {expectedPartialCount}"
  if expectedGreen + expectedPartialCount + expectedAbsentInDenominator != expectedDenominator then
    throwError "spec coverage gate: the expected totals do not add up to expectedDenominator {expectedDenominator}"

  let excluded := expectedRowTotal - expectedDenominator
  logInfo
    m!"Whatwg spec coverage gate: {expectedRowTotal} frozen rows agree with {censusRelativePath} in both directions; denominator {expectedDenominator}, {excluded} excluded; {overrides.size} authored override(s) applied; {claims.size} claimed row(s) carrying {witnessOrder.length} witness theorem(s) with frozen statements and receipts; {expectedGreen} green, {expectedPartialCount} partial, {expectedAbsentInDenominator} absent inside the denominator"

end WhatwgTest.Audit.SpecCoverage

open WhatwgTest.Audit.SpecCoverage in
#spec_coverage_gate

/-! ## Statement ascriptions

One `#check (@name : proposition)` per witness, transcribed from `#check @name`
output. A proof that changes its statement fails here before it can move a
coverage state.

Every line below is pretty-printer output rather than an authored binder, so
the unused-variable linter is scoped off for this section and nothing else: a
universally quantified type variable that the proposition reaches only through
another argument's type reads as unused, and renaming it would stop the
transcription being verbatim. Package ruling R-6, warnings as errors, stands
everywhere else in this file. -/

section StatementSnapshot
set_option linter.unusedVariables false

#check (@Whatwg.Streams.Data.enqueueValueWithSize_error_iff :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size), Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.error Whatwg.Streams.Data.RangeError.rangeError ↔ sizes.isNonNegativeNumber size = false ∨ sizes.isPositiveInfinity size = true)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size), Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.error Whatwg.Streams.Data.RangeError.rangeError ↔ ¬sizes.Admissible size)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_nan :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (value : α), sizes.Classified → Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.nan = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_negative :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size), sizes.isNegative size = true → Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_negInfinity :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (value : α), sizes.Classified → Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.negInfinity = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_posInfinity :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (value : α), sizes.Classified → Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.posInfinity = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_entries :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size), Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' → q'.entries = q.entries ++ [{ value := value, size := size }])
#check (@Whatwg.Streams.Data.enqueueValueWithSize_totalSize :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size), Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' → q'.totalSize = sizes.add q.totalSize size)
#check (@Whatwg.Streams.Data.dequeueValue_isNone_iff :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), Whatwg.Streams.Data.dequeueValue sizes q = none ↔ q.entries = [])
#check (@Whatwg.Streams.Data.dequeueValue_value_eq_head :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), Option.map Prod.fst (Whatwg.Streams.Data.dequeueValue sizes q) = Option.map Whatwg.Streams.Data.QueueEntry.value q.entries.head?)
#check (@Whatwg.Streams.Data.dequeueValue_entries :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q q' : Whatwg.Streams.Data.Queue α Size) (value : α), Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') → q'.entries = q.entries.tail)
#check (@Whatwg.Streams.Data.dequeueValue_totalSize :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (entry : Whatwg.Streams.Data.QueueEntry α Size) (rest : List (Whatwg.Streams.Data.QueueEntry α Size)), q.entries = entry :: rest → Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') → q'.totalSize = sizes.clampNonNegative (sizes.sub q.totalSize entry.size))
#check (@Whatwg.Streams.Data.dequeueValue_totalSize_not_negative :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q q' : Whatwg.Streams.Data.Queue α Size) (value : α), sizes.Ordered → Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') → sizes.isNegative q'.totalSize = false)
#check (@Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) (entry : Whatwg.Streams.Data.QueueEntry α Size) (rest : List (Whatwg.Streams.Data.QueueEntry α Size)), sizes.Classified → sizes.Ordered → sizes.Exact → Whatwg.Streams.Data.Queue.WF sizes q → Whatwg.Streams.Data.Queue.SizesAdmissible sizes q → q.entries = entry :: rest → sizes.isNegative (sizes.sub q.totalSize entry.size) = false)
#check (@Whatwg.Streams.Data.peekQueueValue_isSome_iff :
  ∀ {α Size : Type u} (q : Whatwg.Streams.Data.Queue α Size), (Whatwg.Streams.Data.peekQueueValue q).isSome = true ↔ q.entries ≠ [])
#check (@Whatwg.Streams.Data.peekQueueValue_eq_head :
  ∀ {α Size : Type u} (q : Whatwg.Streams.Data.Queue α Size), Whatwg.Streams.Data.peekQueueValue q = Option.map Whatwg.Streams.Data.QueueEntry.value q.entries.head?)
#check (@Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), Whatwg.Streams.Data.peekQueueValue q = Option.map Prod.fst (Whatwg.Streams.Data.dequeueValue sizes q))
#check (@Whatwg.Streams.Data.resetQueue_entries :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), (Whatwg.Streams.Data.resetQueue sizes q).entries = [])
#check (@Whatwg.Streams.Data.resetQueue_eq :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), Whatwg.Streams.Data.resetQueue sizes q = { entries := [], totalSize := sizes.zero })
#check (@Whatwg.Streams.Data.resetQueue_totalSize :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), (Whatwg.Streams.Data.resetQueue sizes q).totalSize = sizes.zero)
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq :
  ∀ {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (v : Size), sizes.isNonNegativeNumber v = (!sizes.isNaN v && !sizes.isNegative v))
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_nan :
  ∀ {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), sizes.Classified → sizes.isNonNegativeNumber sizes.nan = false)
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_negInfinity :
  ∀ {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), sizes.Classified → sizes.isNonNegativeNumber sizes.negInfinity = false)
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_posInfinity :
  ∀ {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), sizes.Classified → sizes.isNonNegativeNumber sizes.posInfinity = true)
#check (@Whatwg.Streams.Data.extractHighWaterMark_absent :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size), strategy.highWaterMark = none → Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.ok defaultHWM)
#check (@Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM highWaterMark highWaterMark' : Size), strategy.highWaterMark = some highWaterMark → Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.ok highWaterMark' → highWaterMark' = highWaterMark)
#check (@Whatwg.Streams.Data.extractHighWaterMark_error_iff :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size), Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.error Whatwg.Streams.Data.RangeError.rangeError ↔ ∃ highWaterMark, strategy.highWaterMark = some highWaterMark ∧ (sizes.isNaN highWaterMark = true ∨ sizes.isNegative highWaterMark = true))
#check (@Whatwg.Streams.Data.extractHighWaterMark_refuses_nan :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size), sizes.Classified → strategy.highWaterMark = some sizes.nan → Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.extractHighWaterMark_refuses_negative :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM highWaterMark : Size), strategy.highWaterMark = some highWaterMark → sizes.isNegative highWaterMark = true → Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.extractHighWaterMark_refuses_negInfinity :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size), sizes.Classified → strategy.highWaterMark = some sizes.negInfinity → Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.extractHighWaterMark_allows_posInfinity :
  ∀ {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size), sizes.Classified → strategy.highWaterMark = some sizes.posInfinity → Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM = Except.ok sizes.posInfinity)
#check (@Whatwg.Streams.Data.extractSizeAlgorithm_absent :
  ∀ {σ Size : Type u} (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size), strategy.size = none → Whatwg.Streams.Data.extractSizeAlgorithm strategy = Whatwg.Streams.Data.SizeAlgorithm.one)
#check (@Whatwg.Streams.Data.extractSizeAlgorithm_absent_invoke :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α), strategy.size = none → Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.extractSizeAlgorithm strategy) chunk = Whatwg.Streams.Data.SizeAnswer.value sizes.one)
#check (@Whatwg.Streams.Data.SizeAlgorithm.invoke_one :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α), Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle Whatwg.Streams.Data.SizeAlgorithm.one chunk = Whatwg.Streams.Data.SizeAnswer.value sizes.one)
#check (@Whatwg.Streams.Data.extractSizeAlgorithm_present :
  ∀ {σ Size : Type u} (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (name : σ), strategy.size = some name → Whatwg.Streams.Data.extractSizeAlgorithm strategy = Whatwg.Streams.Data.SizeAlgorithm.foreign name)
#check (@Whatwg.Streams.Data.SizeAlgorithm.invoke_foreign :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε) (name : σ) (chunk : α), Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.SizeAlgorithm.foreign name) chunk = oracle name chunk)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark :
  ∀ {Size : Type u} (highWaterMark : Size), (Whatwg.Streams.Data.CountQueuingStrategy.make highWaterMark).highWaterMark = highWaterMark)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.make_accepts_nan :
  ∀ {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), (Whatwg.Streams.Data.CountQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm_eq :
  ∀ {σ : Type u} (countName : σ), Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName = Whatwg.Streams.Data.SizeAlgorithm.foreign countName)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_size :
  ∀ {σ Size : Type u} (countName : σ) (self : Whatwg.Streams.Data.CountQueuingStrategy Size), (Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy countName self).size = some countName)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.size_answers_one :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε), Whatwg.Streams.Data.CountSizeProfile sizes countName oracle → ∀ (chunk : α), Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk = Whatwg.Streams.Data.SizeAnswer.value sizes.one)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.size_ignores_chunk :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε), Whatwg.Streams.Data.CountSizeProfile sizes countName oracle → ∀ (left right : α), Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) left = Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) right)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.size_never_throws :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε), Whatwg.Streams.Data.CountSizeProfile sizes countName oracle → ∀ (chunk : α) (reason : ε), Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk ≠ Whatwg.Streams.Data.SizeAnswer.thrown reason)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark :
  ∀ {Size : Type u} (highWaterMark : Size), (Whatwg.Streams.Data.ByteLengthQueuingStrategy.make highWaterMark).highWaterMark = highWaterMark)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_accepts_nan :
  ∀ {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), (Whatwg.Streams.Data.ByteLengthQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq :
  ∀ {σ : Type u} (byteLengthName : σ), Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName = Whatwg.Streams.Data.SizeAlgorithm.foreign byteLengthName)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size :
  ∀ {σ Size : Type u} (byteLengthName : σ) (self : Whatwg.Streams.Data.ByteLengthQueuingStrategy Size), (Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).size = some byteLengthName)
#check (@Whatwg.Streams.Data.byteLengthSize_number :
  ∀ {ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (n : Size), Whatwg.Streams.Data.byteLengthSize sizes (Whatwg.Streams.Data.ByteLengthAnswer.number n) = Whatwg.Streams.Data.SizeAnswer.value n)
#check (@Whatwg.Streams.Data.byteLengthSize_undefined :
  ∀ {ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), Whatwg.Streams.Data.byteLengthSize sizes Whatwg.Streams.Data.ByteLengthAnswer.undefined = Whatwg.Streams.Data.SizeAnswer.value sizes.nan)
#check (@Whatwg.Streams.Data.byteLengthSize_thrown :
  ∀ {ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (reason : ε), Whatwg.Streams.Data.byteLengthSize sizes (Whatwg.Streams.Data.ByteLengthAnswer.thrown reason) = Whatwg.Streams.Data.SizeAnswer.thrown reason)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.size_eq_byteLength :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (byteLengthName : σ) (byteLength : α → Whatwg.Streams.Data.ByteLengthAnswer Size ε) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε), Whatwg.Streams.Data.ByteLengthSizeProfile sizes byteLengthName byteLength oracle → ∀ (chunk : α), Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk = Whatwg.Streams.Data.byteLengthSize sizes (byteLength chunk))
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused :
  ∀ {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (byteLengthName : σ) (byteLength : α → Whatwg.Streams.Data.ByteLengthAnswer Size ε) (oracle : σ → α → Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α) (q : Whatwg.Streams.Data.Queue α Size) (value : α), Whatwg.Streams.Data.ByteLengthSizeProfile sizes byteLengthName byteLength oracle → sizes.Classified → byteLength chunk = Whatwg.Streams.Data.ByteLengthAnswer.undefined → Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle (Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk = Whatwg.Streams.Data.SizeAnswer.value sizes.nan ∧ Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.nan = Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.Queue.empty_entries :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), (Whatwg.Streams.Data.Queue.empty sizes).entries = [])
#check (@Whatwg.Streams.Data.Queue.WF_iff :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size), Whatwg.Streams.Data.Queue.WF sizes q ↔ q.totalSize = Whatwg.Streams.Data.sizeSum sizes q.entries)
#check (@Whatwg.Streams.Data.Queue.empty_totalSize :
  ∀ {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size), (Whatwg.Streams.Data.Queue.empty sizes).totalSize = sizes.zero)

end StatementSnapshot
