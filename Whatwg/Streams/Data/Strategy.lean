import Whatwg.Streams.Data.Queue

/-!
# Data.Strategy.lean

Owner: queuing-strategy data at the data layer: a size function as
first-order data, a high-water mark, and the desired size read off a queue
against that mark.

Spec anchors: `queuing-strategies`, `queue-with-sizes`.

Opens in P3.

This is the carrier. The specification-facing classes and the abstract
operations that build one live under `Whatwg/Streams/Strategy`, which the
architecture table keeps as its own area.

The P3 packet amends that split for two carriers only. Rows 9 and 10 of the
`DATA-PG-QUEUE` existing-type table in `docs/DATA-DAG.md` place
`CountQueuingStrategy` and `ByteLengthQueuingStrategy` in this module, because
each is nothing but its one `[[highWaterMark]]` slot and the named conversion
into `QueuingStrategy`; the class surface that reads those slots — the
constructors, the getters, and the realm lookup they perform — stays with
`Whatwg/Streams/Strategy` and is not opened here. `docs/ARCHITECTURE.md` still
records the older split and is a needed doc change, reported with this
handoff.

The public surface below is the one frozen by
`test/contracts/queue-with-sizes.contract.md` (D5 through D8) and ascribed by
`WhatwgTest/Streams/Data/QueueContract.lean`. Every definition is a
transcription of the census row named in its docstring, read from the pinned
bytes of `vendor/whatwg-streams-b9ba9f49/index.bs` at the span that
`generated/spec-algorithm-census.tsv` records for that row.

Per DB-02 no host-supplied algorithm is a Lean function here. A size callback
is a **name** drawn from an externally admitted alphabet, and each invocation's
answer is a typed decision supplied by an oracle; that is foreign boundary
`DATA-FB-CALLBACK`, with `CountSizeProfile` and `ByteLengthSizeProfile` as the
two profiles this packet needs.
-/

set_option autoImplicit false

universe u

namespace Whatwg.Streams.Data

/-! ## D5 — size algorithms and the foreign boundary -/

/-- The two shapes `ExtractSizeAlgorithm` returns: census row
`op.make-size-algorithm-from-size-function`, span digest
`1a5e282855cfe10300f0c72ba41fe2fa9b6120e5a5d45d363c6b829d48b4f9f4`. "If
`|strategy|["size"]` does not exist, return an algorithm that returns 1",
otherwise "return an algorithm that ... returns the result of invoking
`|strategy|["size"]` with argument list « `|chunk|` »".

`foreign` carries a **name**, never a stored Lean function: the oracle
supplies the answer, which is `DATA-FB-CALLBACK`. -/
inductive SizeAlgorithm (σ : Type u)
  /-- "An algorithm that returns 1". -/
  | one
  /-- The named host callback whose invocation the oracle answers. -/
  | foreign (name : σ)
deriving DecidableEq, Repr

/-- The typed decision a size callback returns. The pinned WPT test "Writable
stream: throwing strategy.size method" observes that a `size` callback that
throws rejects the write with the thrown value, so the answer alphabet has a
throw arm and not only a value arm.

Its IDL type is `unrestricted double (any chunk)` (census row
`idl.queuing-strategy-size`); the Web IDL conversion that produces the double
is `DATA-FB-IDL-DOUBLE` and the model receives the already-converted value. -/
inductive SizeAnswer (Size : Type u) (ε : Type u)
  /-- The callback returned a size. -/
  | value (size : Size)
  /-- The callback threw, carrying an opaque reason. -/
  | thrown (reason : ε)
deriving DecidableEq

/-- The three answers `GetV(|chunk|, "byteLength")` can give, from census row
`op.byte-length-queuing-strategy-size-function`, span digest
`78fcbfe6afebb52a8c6369e5a20e7907e996dfa344622b8e0a8ff843867756e3`: "Return ?
`GetV(|chunk|, "byteLength")`", where the `?` propagates an abrupt completion.

The pinned WPT test "ByteLengthQueuingStrategy: size behaves as expected with
strange arguments" observes all three: `1024` for a chunk with the property,
`undefined` for `'potato'` and `{}`, and a re-thrown error for a throwing
getter. A total `α → Size` cannot express two of the three. -/
inductive ByteLengthAnswer (Size : Type u) (ε : Type u)
  /-- The property was present and converted to a number. -/
  | number (n : Size)
  /-- The property was absent; Web IDL converts `undefined` to `NaN`. -/
  | undefined
  /-- The getter threw. -/
  | thrown (reason : ε)
deriving DecidableEq

/-- Invoking the algorithm `ExtractSizeAlgorithm` returned, on one chunk.
`one` answers with the carrier's `1` and reads nothing; `foreign` hands the
name and the chunk to the oracle, which is the whole of the modelled
invocation (census row `op.make-size-algorithm-from-size-function`, step 2.1).
The invocation machinery itself is `DATA-FB-CALLBACK`. -/
def SizeAlgorithm.invoke {α σ ε Size : Type u} (sizes : SizeClass Size)
    (oracle : σ → α → SizeAnswer Size ε) (algorithm : SizeAlgorithm σ) (chunk : α) :
    SizeAnswer Size ε :=
  match algorithm with
  | .one => .value sizes.one
  | .foreign name => oracle name chunk

/-- The Web IDL `unrestricted double` conversion of a `GetV` answer, as the
byte-length size function's callback type performs it: a number passes
through, an absent property becomes `NaN`, and a throw propagates.

Breaker finding B4: `undefined` becoming `NaN` is not an error at the
callback; it is the enqueue that follows which refuses the `NaN`, which
`ByteLengthQueuingStrategy.undefined_byteLength_refused` states. -/
def byteLengthSize {ε Size : Type u} (sizes : SizeClass Size)
    (answer : ByteLengthAnswer Size ε) : SizeAnswer Size ε :=
  match answer with
  | .number n => .value n
  | .undefined => .value sizes.nan
  | .thrown reason => .thrown reason

/-! ## D6 — the strategy dictionary and the two extraction algorithms -/

/-- The `QueuingStrategy` dictionary as the two extraction algorithms consume
it: census row `idl.queuing-strategy`, span digest
`57409b2926c5fb9209b87fcc5258a0f4142ec4c49383e99042700e4e97c2f0d1`, with
members `idl.queuingstrategy-high-water-mark` and `idl.queuingstrategy-size`.

Both fields are `Option` because the pinned algorithms branch on
"does not exist" in the map, which is not the same as a present `undefined`.
The `size` member is a name, never a stored function, per DB-02. -/
structure QueuingStrategy (σ : Type u) (Size : Type u) : Type u where
  /-- `|strategy|["highWaterMark"]`, absent as `none`. -/
  highWaterMark : Option Size
  /-- `|strategy|["size"]`, absent as `none`; present as the callback's name. -/
  size : Option σ

/-- `ExtractHighWaterMark(|strategy|, |defaultHWM|)`, census row
`op.validate-and-normalize-high-water-mark`, span digest
`d9303084d19b298241323f639194c712749ed58918a76c12407a64ef58940c25`:

1. "If `|strategy|["highWaterMark"]` does not exist, return `|defaultHWM|`."
2. "Let `|highWaterMark|` be `|strategy|["highWaterMark"]`."
3. "If `|highWaterMark|` is NaN or `|highWaterMark|` &lt; 0, throw a
   `RangeError` exception."
4. "Return `|highWaterMark|`."

Breaker finding B1: despite the anchor id, the algorithm at this pin is named
`ExtractHighWaterMark` and normalizes nothing. There is no
`ValidateAndNormalizeHighWaterMark` operation in the census, and
`extractHighWaterMark_id_on_accepted` is the identity law that replaces the
idempotence law the stale name invites — a clamping mutant is idempotent too
(`WS-DATA-CE-009`).

Breaker finding B2: the refusal set here and the refusal set of
`EnqueueValueWithSize` differ on exactly one value. The note beside this
algorithm is explicit: "+∞ is explicitly allowed as a valid high water mark.
It causes backpressure to never be applied." -/
def extractHighWaterMark {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM : Size) : Except RangeError Size :=
  match strategy.highWaterMark with
  | none => .ok defaultHWM
  | some highWaterMark =>
      if sizes.isNaN highWaterMark || sizes.isNegative highWaterMark then .error .rangeError
      else .ok highWaterMark

/-- `ExtractSizeAlgorithm(|strategy|)`, census row
`op.make-size-algorithm-from-size-function`, span digest
`1a5e282855cfe10300f0c72ba41fe2fa9b6120e5a5d45d363c6b829d48b4f9f4`: the
constant-one algorithm when the member is absent, and otherwise the algorithm
that invokes the member on its chunk. -/
def extractSizeAlgorithm {σ Size : Type u} (strategy : QueuingStrategy σ Size) :
    SizeAlgorithm σ :=
  match strategy.size with
  | none => .one
  | some name => .foreign name

/-! ## D7 — the two built-in strategy classes -/

/-- `CountQueuingStrategy`'s one internal slot, from `cqs-internal-slots`
(census rows `op.cqs-constructor`, span digest
`de1004ef5fa453cafaa4d6547d7a897458724ad48615edf940ed2f607b5a4b99`, and
`op.cqs-high-water-mark`, span digest
`8d27fa67d52c8bb2c3ce70f320396b0b810b3cba8bfd4a9a08a4b0d72b91a886`).

The size function is deliberately **not** a field: the pinned text puts it on
the global object, and the pinned WPT observes one function object per realm
shared by every instance. Realm identity is refused rather than modelled
(`DATA-FB-REALM`, `realm_identity_refused`). -/
structure CountQueuingStrategy (Size : Type u) : Type u where
  /-- `[[highWaterMark]]`, stored exactly as given: "Note that the provided
  high water mark will not be validated ahead of time." -/
  highWaterMark : Size
deriving DecidableEq

/-- `ByteLengthQueuingStrategy`'s one internal slot: census rows
`op.blqs-constructor`, span digest
`41cc2f42f4c500b7d1dceac0206678d34c17760463fda3ca8a150fa004ad1831`,
`op.blqs-high-water-mark`, span digest
`9a7624ba35a0d5801efd5b10a038f4a19d78db5d19bec4bc105facaeac07e981`, and
`slot.high-water-mark`, span digest
`031fc84bad2024528c52bc137f7b7deb0ffed9e3f20fc25ccae81b3eec82aabb`.

Deliberately a separate type from `CountQueuingStrategy`: the two classes have
the same shape and different size functions, and identifying them would erase
the one difference that matters. -/
structure ByteLengthQueuingStrategy (Size : Type u) : Type u where
  /-- `[[highWaterMark]]`, stored exactly as given and never validated. -/
  highWaterMark : Size
deriving DecidableEq

namespace CountQueuingStrategy

/-- The `new CountQueuingStrategy(|init|)` constructor steps, census row
`op.cqs-constructor`: "Set `[=this=].[[highWaterMark]]` to
`|init|["highWaterMark"]`", and nothing else. No validation happens here;
breaker finding B3 records that a `NaN` high water mark is constructible and
observable, and the pinned WPT `highWaterMarkConversions` table observes the
stored value being read back. -/
def make {Size : Type u} (highWaterMark : Size) : CountQueuingStrategy Size :=
  { highWaterMark := highWaterMark }

/-- The realm's count queuing strategy size function, as a named callback:
census row `op.cqs-size`, span digest
`fefd07087350e048c081e7d6b0bf281eca998b0d0066661f4caa85e0def84812`, "Return
`[=this=]`'s relevant global object's count queuing strategy size function".
The relevant-global lookup is `DATA-FB-REALM`, so the name is an argument. -/
def sizeAlgorithm {σ : Type u} (countName : σ) : SizeAlgorithm σ :=
  .foreign countName

/-- The class read as the dictionary the extraction algorithms consume: the
slot becomes the present `highWaterMark` member, and the realm's size function
name becomes the present `size` member. -/
def toQueuingStrategy {σ Size : Type u} (countName : σ) (self : CountQueuingStrategy Size) :
    QueuingStrategy σ Size :=
  { highWaterMark := some self.highWaterMark, size := some countName }

end CountQueuingStrategy

namespace ByteLengthQueuingStrategy

/-- The `new ByteLengthQueuingStrategy(|init|)` constructor steps, census row
`op.blqs-constructor`: "Set `[=this=].[[highWaterMark]]` to
`|init|["highWaterMark"]`", and nothing else. -/
def make {Size : Type u} (highWaterMark : Size) : ByteLengthQueuingStrategy Size :=
  { highWaterMark := highWaterMark }

/-- The realm's byte length queuing strategy size function, as a named
callback: census row `op.blqs-size`, span digest
`6dbadacd352e203151e2fba3cec6de1d0be92acc6e359513a276eeba2aea1946`, "Return
`[=this=]`'s relevant global object's byte length queuing strategy size
function". -/
def sizeAlgorithm {σ : Type u} (byteLengthName : σ) : SizeAlgorithm σ :=
  .foreign byteLengthName

/-- The class read as the dictionary the extraction algorithms consume. -/
def toQueuingStrategy {σ Size : Type u} (byteLengthName : σ)
    (self : ByteLengthQueuingStrategy Size) : QueuingStrategy σ Size :=
  { highWaterMark := some self.highWaterMark, size := some byteLengthName }

end ByteLengthQueuingStrategy

/-! ## D8 — the two foreign-boundary profiles -/

/-- What the oracle must answer for the count queuing strategy size function:
census row `op.count-queuing-strategy-size-function`, span digest
`bc07b231685ee08abe1c76ca4a85f04e41443cc6e0a7e33b6f6f24ced3609a4b`, whose
steps are "Return 1".

The quantification over **every** chunk is the modelled form of the pinned WPT
observation that the function returns `1` for `undefined`, `null`, a string,
`{}`, a chunk, a getter, and a getter that throws: it never reads its
argument. The `CreateBuiltinFunction` steps, the function's `length` and
`name`, and the callback context are host construction and are not modelled. -/
structure CountSizeProfile {α σ ε Size : Type u} (sizes : SizeClass Size) (countName : σ)
    (oracle : σ → α → SizeAnswer Size ε) : Prop where
  /-- The oracle answers `1` on every chunk. -/
  answers_one : ∀ chunk : α, oracle countName chunk = SizeAnswer.value sizes.one

/-- What the oracle must answer for the byte length queuing strategy size
function: census row `op.byte-length-queuing-strategy-size-function`, span
digest `78fcbfe6afebb52a8c6369e5a20e7907e996dfa344622b8e0a8ff843867756e3`. The
`GetV` itself is `DATA-FB-CALLBACK`; the profile says the oracle's answer is
the Web IDL conversion of whatever `GetV` returned. -/
structure ByteLengthSizeProfile {α σ ε Size : Type u} (sizes : SizeClass Size)
    (byteLengthName : σ) (byteLength : α → ByteLengthAnswer Size ε)
    (oracle : σ → α → SizeAnswer Size ε) : Prop where
  /-- The oracle answers the converted `GetV` answer on every chunk. -/
  answers_byteLength : ∀ chunk : α,
    oracle byteLengthName chunk = byteLengthSize sizes (byteLength chunk)

/-! ## S7 — the extraction algorithms

Census rows `op.validate-and-normalize-high-water-mark` and
`op.make-size-algorithm-from-size-function`. -/

/-- Step 1 read off the dictionary rather than off the strategy record. -/
theorem extractHighWaterMark_absent {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM : Size)
    (habsent : strategy.highWaterMark = none) :
    extractHighWaterMark sizes strategy defaultHWM = Except.ok defaultHWM := by
  unfold extractHighWaterMark
  rw [habsent]

/-- Steps 2 to 4 read off the dictionary. -/
private theorem extractHighWaterMark_of_some {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM highWaterMark : Size)
    (hpresent : strategy.highWaterMark = some highWaterMark) :
    extractHighWaterMark sizes strategy defaultHWM =
      (if sizes.isNaN highWaterMark || sizes.isNegative highWaterMark then
        Except.error RangeError.rangeError
      else Except.ok highWaterMark) := by
  unfold extractHighWaterMark
  rw [hpresent]

private theorem extractHighWaterMark_of_accepted {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM highWaterMark : Size)
    (hpresent : strategy.highWaterMark = some highWaterMark)
    (hnan : sizes.isNaN highWaterMark = false)
    (hneg : sizes.isNegative highWaterMark = false) :
    extractHighWaterMark sizes strategy defaultHWM = Except.ok highWaterMark := by
  rw [extractHighWaterMark_of_some sizes strategy defaultHWM highWaterMark hpresent, hnan, hneg]
  simp

private theorem extractHighWaterMark_of_refused {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM highWaterMark : Size)
    (hpresent : strategy.highWaterMark = some highWaterMark)
    (hbad : sizes.isNaN highWaterMark = true ∨ sizes.isNegative highWaterMark = true) :
    extractHighWaterMark sizes strategy defaultHWM = Except.error RangeError.rangeError := by
  rw [extractHighWaterMark_of_some sizes strategy defaultHWM highWaterMark hpresent]
  cases hbad with
  | inl hnan => rw [hnan]; simp
  | inr hneg => rw [hneg]; simp

theorem extractHighWaterMark_error_iff {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM : Size) :
    extractHighWaterMark sizes strategy defaultHWM = Except.error RangeError.rangeError ↔
      (∃ highWaterMark, strategy.highWaterMark = some highWaterMark ∧
        (sizes.isNaN highWaterMark = true ∨ sizes.isNegative highWaterMark = true)) := by
  constructor
  · intro herror
    cases hhwm : strategy.highWaterMark with
    | none =>
        rw [extractHighWaterMark_absent sizes strategy defaultHWM hhwm] at herror
        simp at herror
    | some highWaterMark =>
        cases hnan : sizes.isNaN highWaterMark with
        | true => exact ⟨highWaterMark, by first | rfl | exact hhwm, Or.inl hnan⟩
        | false =>
            cases hneg : sizes.isNegative highWaterMark with
            | true => exact ⟨highWaterMark, by first | rfl | exact hhwm, Or.inr hneg⟩
            | false =>
                rw [extractHighWaterMark_of_accepted sizes strategy defaultHWM highWaterMark
                  hhwm hnan hneg] at herror
                simp at herror
  · intro hexists
    cases hexists with
    | intro highWaterMark hpair =>
        exact extractHighWaterMark_of_refused sizes strategy defaultHWM highWaterMark
          hpair.1 hpair.2

theorem extractHighWaterMark_refuses_nan {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM : Size) (classified : sizes.Classified)
    (hpresent : strategy.highWaterMark = some sizes.nan) :
    extractHighWaterMark sizes strategy defaultHWM = Except.error RangeError.rangeError :=
  extractHighWaterMark_of_refused sizes strategy defaultHWM sizes.nan hpresent
    (Or.inl classified.nan_isNaN)

theorem extractHighWaterMark_refuses_negative {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM highWaterMark : Size)
    (hpresent : strategy.highWaterMark = some highWaterMark)
    (hneg : sizes.isNegative highWaterMark = true) :
    extractHighWaterMark sizes strategy defaultHWM = Except.error RangeError.rangeError :=
  extractHighWaterMark_of_refused sizes strategy defaultHWM highWaterMark hpresent (Or.inr hneg)

theorem extractHighWaterMark_refuses_negInfinity {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM : Size) (classified : sizes.Classified)
    (hpresent : strategy.highWaterMark = some sizes.negInfinity) :
    extractHighWaterMark sizes strategy defaultHWM = Except.error RangeError.rangeError :=
  extractHighWaterMark_of_refused sizes strategy defaultHWM sizes.negInfinity hpresent
    (Or.inr classified.negInfinity_negative)

/-- "+∞ is explicitly allowed as a valid high water mark." The pinned WPT list
of high water marks that must throw is `[-1, -Infinity, NaN, 'foo', {}]`, and
`Infinity` is deliberately absent from it. -/
theorem extractHighWaterMark_allows_posInfinity {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM : Size) (classified : sizes.Classified)
    (hpresent : strategy.highWaterMark = some sizes.posInfinity) :
    extractHighWaterMark sizes strategy defaultHWM = Except.ok sizes.posInfinity :=
  extractHighWaterMark_of_accepted sizes strategy defaultHWM sizes.posInfinity hpresent
    classified.posInfinity_not_nan classified.posInfinity_not_negative

/-- The algorithm at this pin returns its input unchanged. This is the law
that catches the clamping mutant of `WS-DATA-CE-009`, which an idempotence law
does not. -/
theorem extractHighWaterMark_id_on_accepted {σ Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (defaultHWM highWaterMark highWaterMark' : Size)
    (hpresent : strategy.highWaterMark = some highWaterMark)
    (hok : extractHighWaterMark sizes strategy defaultHWM = Except.ok highWaterMark') :
    highWaterMark' = highWaterMark := by
  cases hnan : sizes.isNaN highWaterMark with
  | true =>
      rw [extractHighWaterMark_of_refused sizes strategy defaultHWM highWaterMark hpresent
        (Or.inl hnan)] at hok
      simp at hok
  | false =>
      cases hneg : sizes.isNegative highWaterMark with
      | true =>
          rw [extractHighWaterMark_of_refused sizes strategy defaultHWM highWaterMark hpresent
            (Or.inr hneg)] at hok
          simp at hok
      | false =>
          rw [extractHighWaterMark_of_accepted sizes strategy defaultHWM highWaterMark hpresent
            hnan hneg] at hok
          exact (Except.ok.inj hok).symm

/-- Breaker finding B2 as one theorem: the same value is a legal high water
mark and an illegal size. Frozen as a conjunction so that a model which shares
one predicate between the two algorithms cannot satisfy it under any carrier
(`WS-DATA-CE-008`). -/
theorem extractHighWaterMark_disagrees_with_enqueue_on_posInfinity
    {α σ Size : Type u} (sizes : SizeClass Size) (strategy : QueuingStrategy σ Size)
    (defaultHWM : Size) (q : Queue α Size) (value : α) (classified : sizes.Classified)
    (hpresent : strategy.highWaterMark = some sizes.posInfinity) :
    extractHighWaterMark sizes strategy defaultHWM = Except.ok sizes.posInfinity ∧
      enqueueValueWithSize sizes q value sizes.posInfinity =
        Except.error RangeError.rangeError :=
  ⟨extractHighWaterMark_allows_posInfinity sizes strategy defaultHWM classified hpresent,
    enqueueValueWithSize_refuses_posInfinity sizes q value classified⟩

theorem extractSizeAlgorithm_absent {σ Size : Type u} (strategy : QueuingStrategy σ Size)
    (habsent : strategy.size = none) : extractSizeAlgorithm strategy = SizeAlgorithm.one := by
  unfold extractSizeAlgorithm
  rw [habsent]

theorem extractSizeAlgorithm_present {σ Size : Type u} (strategy : QueuingStrategy σ Size)
    (name : σ) (hpresent : strategy.size = some name) :
    extractSizeAlgorithm strategy = SizeAlgorithm.foreign name := by
  unfold extractSizeAlgorithm
  rw [hpresent]

theorem SizeAlgorithm.invoke_one {α σ ε Size : Type u} (sizes : SizeClass Size)
    (oracle : σ → α → SizeAnswer Size ε) (chunk : α) :
    SizeAlgorithm.invoke sizes oracle SizeAlgorithm.one chunk = SizeAnswer.value sizes.one := rfl

theorem SizeAlgorithm.invoke_foreign {α σ ε Size : Type u} (sizes : SizeClass Size)
    (oracle : σ → α → SizeAnswer Size ε) (name : σ) (chunk : α) :
    SizeAlgorithm.invoke sizes oracle (SizeAlgorithm.foreign name) chunk = oracle name chunk := rfl

theorem extractSizeAlgorithm_absent_invoke {α σ ε Size : Type u} (sizes : SizeClass Size)
    (strategy : QueuingStrategy σ Size) (oracle : σ → α → SizeAnswer Size ε) (chunk : α)
    (habsent : strategy.size = none) :
    SizeAlgorithm.invoke sizes oracle (extractSizeAlgorithm strategy) chunk =
      SizeAnswer.value sizes.one := by
  rw [extractSizeAlgorithm_absent strategy habsent]
  exact SizeAlgorithm.invoke_one sizes oracle chunk

/-! ## S8 — the built-in strategies and their profiles

Census rows `op.cqs-constructor`, `op.cqs-high-water-mark`, `op.cqs-size`,
`op.count-queuing-strategy-size-function`, `op.blqs-constructor`,
`op.blqs-high-water-mark`, `op.blqs-size`,
`op.byte-length-queuing-strategy-size-function`, `slot.high-water-mark`. -/

namespace CountQueuingStrategy

theorem make_highWaterMark {Size : Type u} (highWaterMark : Size) :
    (CountQueuingStrategy.make highWaterMark : CountQueuingStrategy Size).highWaterMark =
      highWaterMark := rfl

/-- "Note that the provided high water mark will not be validated ahead of
time." The constructor stores whatever it is given, for every value of the
carrier. -/
theorem make_does_not_validate {Size : Type u} (highWaterMark : Size) :
    (CountQueuingStrategy.make highWaterMark : CountQueuingStrategy Size).highWaterMark =
      highWaterMark := rfl

/-- Breaker finding B3: a `NaN` high water mark is constructible and
observable. The pinned WPT `highWaterMarkConversions` table observes exactly
this, reading the stored value back through the getter. -/
theorem make_accepts_nan {Size : Type u} (sizes : SizeClass Size) :
    (CountQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan := rfl

theorem sizeAlgorithm_eq {σ : Type u} (countName : σ) :
    CountQueuingStrategy.sizeAlgorithm countName = SizeAlgorithm.foreign countName := rfl

theorem toQueuingStrategy_highWaterMark {σ Size : Type u} (countName : σ)
    (self : CountQueuingStrategy Size) :
    (CountQueuingStrategy.toQueuingStrategy countName self).highWaterMark =
      some self.highWaterMark := rfl

theorem toQueuingStrategy_size {σ Size : Type u} (countName : σ)
    (self : CountQueuingStrategy Size) :
    (CountQueuingStrategy.toQueuingStrategy countName self).size = some countName := rfl

theorem extract_size_algorithm {σ Size : Type u} (countName : σ)
    (self : CountQueuingStrategy Size) :
    extractSizeAlgorithm (CountQueuingStrategy.toQueuingStrategy countName self) =
      CountQueuingStrategy.sizeAlgorithm countName := rfl

/-- "Let `|steps|` be the following steps: Return 1." -/
theorem size_answers_one {α σ ε Size : Type u} (sizes : SizeClass Size) (countName : σ)
    (oracle : σ → α → SizeAnswer Size ε)
    (profile : CountSizeProfile sizes countName oracle) (chunk : α) :
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) chunk =
      SizeAnswer.value sizes.one :=
  profile.answers_one chunk

/-- It never reads its argument: the modelled half of the pinned WPT
observation that the count size function returns `1` even for a chunk whose
getter throws. -/
theorem size_ignores_chunk {α σ ε Size : Type u} (sizes : SizeClass Size) (countName : σ)
    (oracle : σ → α → SizeAnswer Size ε)
    (profile : CountSizeProfile sizes countName oracle) (left right : α) :
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) left =
      SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) right := by
  rw [size_answers_one sizes countName oracle profile left,
    size_answers_one sizes countName oracle profile right]

theorem size_never_throws {α σ ε Size : Type u} (sizes : SizeClass Size) (countName : σ)
    (oracle : σ → α → SizeAnswer Size ε)
    (profile : CountSizeProfile sizes countName oracle) (chunk : α) (reason : ε) :
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) chunk ≠
      SizeAnswer.thrown reason := by
  intro hthrown
  rw [size_answers_one sizes countName oracle profile chunk] at hthrown
  simp at hthrown

/-- Every size the count strategy produces is one `EnqueueValueWithSize`
accepts, so a count-strategy stream never refuses its own chunk sizes. -/
theorem enqueue_accepts {α σ ε Size : Type u} (sizes : SizeClass Size) (countName : σ)
    (oracle : σ → α → SizeAnswer Size ε) (chunk : α) (size : Size)
    (profile : CountSizeProfile sizes countName oracle) (ordered : sizes.Ordered)
    (hanswer : SizeAlgorithm.invoke sizes oracle
      (CountQueuingStrategy.sizeAlgorithm countName) chunk = SizeAnswer.value size) :
    sizes.Admissible size := by
  rw [size_answers_one sizes countName oracle profile chunk] at hanswer
  have hone : sizes.one = size := by simpa using hanswer
  rw [← hone]
  exact ordered.one_admissible

end CountQueuingStrategy

namespace ByteLengthQueuingStrategy

theorem make_highWaterMark {Size : Type u} (highWaterMark : Size) :
    (ByteLengthQueuingStrategy.make highWaterMark :
      ByteLengthQueuingStrategy Size).highWaterMark = highWaterMark := rfl

theorem make_accepts_nan {Size : Type u} (sizes : SizeClass Size) :
    (ByteLengthQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan := rfl

theorem sizeAlgorithm_eq {σ : Type u} (byteLengthName : σ) :
    ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName =
      SizeAlgorithm.foreign byteLengthName := rfl

theorem toQueuingStrategy_highWaterMark {σ Size : Type u} (byteLengthName : σ)
    (self : ByteLengthQueuingStrategy Size) :
    (ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).highWaterMark =
      some self.highWaterMark := rfl

theorem toQueuingStrategy_size {σ Size : Type u} (byteLengthName : σ)
    (self : ByteLengthQueuingStrategy Size) :
    (ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).size =
      some byteLengthName := rfl

end ByteLengthQueuingStrategy

theorem byteLengthSize_number {ε Size : Type u} (sizes : SizeClass Size) (n : Size) :
    byteLengthSize sizes (ByteLengthAnswer.number n : ByteLengthAnswer Size ε) =
      SizeAnswer.value n := rfl

/-- Breaker finding B4: an absent `byteLength` property is `undefined` at the
callback, and the Web IDL `unrestricted double` conversion makes that `NaN`. -/
theorem byteLengthSize_undefined {ε Size : Type u} (sizes : SizeClass Size) :
    byteLengthSize sizes (ByteLengthAnswer.undefined : ByteLengthAnswer Size ε) =
      SizeAnswer.value sizes.nan := rfl

theorem byteLengthSize_thrown {ε Size : Type u} (sizes : SizeClass Size) (reason : ε) :
    byteLengthSize sizes (ByteLengthAnswer.thrown reason : ByteLengthAnswer Size ε) =
      SizeAnswer.thrown reason := rfl

namespace ByteLengthQueuingStrategy

theorem size_eq_byteLength {α σ ε Size : Type u} (sizes : SizeClass Size) (byteLengthName : σ)
    (byteLength : α → ByteLengthAnswer Size ε) (oracle : σ → α → SizeAnswer Size ε)
    (profile : ByteLengthSizeProfile sizes byteLengthName byteLength oracle) (chunk : α) :
    SizeAlgorithm.invoke sizes oracle
        (ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk =
      byteLengthSize sizes (byteLength chunk) :=
  profile.answers_byteLength chunk

/-- The composite the pinned WPT forces: a chunk with no `byteLength` yields
`undefined`, the Web IDL conversion makes that `NaN`, and the enqueue that
follows refuses it with a `RangeError`. -/
theorem undefined_byteLength_refused {α σ ε Size : Type u} (sizes : SizeClass Size)
    (byteLengthName : σ) (byteLength : α → ByteLengthAnswer Size ε)
    (oracle : σ → α → SizeAnswer Size ε) (chunk : α) (q : Queue α Size) (value : α)
    (profile : ByteLengthSizeProfile sizes byteLengthName byteLength oracle)
    (classified : sizes.Classified)
    (hundefined : byteLength chunk = ByteLengthAnswer.undefined) :
    SizeAlgorithm.invoke sizes oracle
        (ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk =
      SizeAnswer.value sizes.nan ∧
    enqueueValueWithSize sizes q value sizes.nan = Except.error RangeError.rangeError := by
  constructor
  · rw [size_eq_byteLength sizes byteLengthName byteLength oracle profile chunk, hundefined]
    exact byteLengthSize_undefined sizes
  · exact enqueueValueWithSize_refuses_nan sizes q value classified

end ByteLengthQueuingStrategy

/-- The theorem-shaped refusal of `DATA-FB-REALM`. The pinned WPT
`queuing-strategies-size-function-per-global.window.js` observes two realms
producing different size-function objects, whereas every Lean minting function
is a function of its argument: equal realms mint equal names, and nothing here
can make two realms differ. Realm distinctness is therefore the caller's
obligation, and every law above takes the size function's name as an
argument. -/
theorem realm_identity_refused {γ σ : Type u} (mint : γ → σ) (left right : γ)
    (hrealms : left = right) : mint left = mint right :=
  congrArg mint hrealms

end Whatwg.Streams.Data
