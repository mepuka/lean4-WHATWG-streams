# Pass A — domain contract for queue-with-sizes and the queuing strategies (P3)

Status: **FROZEN / RED, breaker-authored 2026-09-02.** The P3 breaker seat
authored it. No statement below may be weakened by the builder.

Implementation fence (the builder's only writable Lean surface for this
packet):

- `WhatwgStreams/Data/Queue.lean`
- `WhatwgStreams/Data/Strategy.lean`

Lean battery: `WhatwgStreamsTest/Data/QueueContract.lean`
Axiom report: `WhatwgStreamsTest/Data/QueueAxiomReport.lean`
Counterexamples: `WS-DATA-CE-001` through `WS-DATA-CE-010` in
`test/counterexamples/REGISTER.md`; witnesses in
`WhatwgStreamsTest/Counterexamples/Data/Queue.lean`; attack shapes in
`test/counterexamples/data/ATTACKS.md`
Proof graph: `DATA-PG-QUEUE` in `docs/DATA-DAG.md`

Pinned specification: `vendor/whatwg-streams-b9ba9f49/index.bs`, sections
`queue-with-sizes`, `qs-api`, `blqs-class`, `cqs-class`, `qs-abstract-ops`,
and the `misc-abstract-ops` operation `IsNonNegativeNumber`. Every row is
cited by census row id from `generated/spec-algorithm-census.tsv` and by the
anchor text of the pinned bytes, never by line number.

Pinned host corpus: `vendor/wpt-480fdfcd/streams/`, files
`queuing-strategies.any.js`,
`queuing-strategies-size-function-per-global.window.js`,
`readable-streams/floating-point-total-queue-size.any.js`,
`writable-streams/floating-point-total-queue-size.any.js`,
`readable-streams/bad-strategies.any.js`,
`writable-streams/bad-strategies.any.js`. Every WPT expectation quoted below
was read first-hand from those pinned files.

**This packet contains one ruling request, `P3-R1`, which the breaker states
and does not decide.** It is in section 6. The declaration surface is
parameterized so that any of its three answers instantiates the same frozen
statements.

---

## 1. Claim boundary

This packet freezes one bounded model: the specification's
"queue-with-sizes" data structure and the queuing-strategy extraction
algorithms, as first-order data with total operations, over an **abstract size
carrier** supplied as an explicit `SizeClass` record.

It claims that each named clause of each census row listed in
`docs/DATA-DAG.md` "Census rows this packet targets" has an exact theorem over
the Lean model, and it names, in the `DATA-FB-*` rows of that document,
exactly what was dropped: the ECMAScript Number carrier and its rounding, the
Web IDL unrestricted-double conversion, realm identity of the two built-in
size functions, and the body of any host-supplied `size` callback.

It does **not**:

- claim that any `SizeClass` instance is the ECMAScript Number type;
- model promises, controllers, streams, readers, writers, `desiredSize`, or
  backpressure — `desiredSize` is quoted in section 6 only as evidence about
  what the carrier choice makes observable, and belongs to P4 and P5;
- model the Web IDL conversion of a JavaScript value to an unrestricted
  double (`'foo'` and `{}` become `NaN` at the host boundary, and that
  boundary is `hostOnly`);
- model the body of a host `size` callback. Per DB-02 a host-supplied body is
  not a computation in this model: `QueuingStrategy.size` carries a **name**
  drawn from an externally admitted alphabet, and each invocation's answer is
  a typed decision supplied by an oracle;
- state any observation-mask claim of its own. Every operation here is a total
  function of first-order data, so nothing in this packet is relational. The
  masks M1 and M2 enter only where section 6 explains which mask a carrier
  disagreement would be visible under, and that is evidence for the ruling,
  not a theorem of this packet.

The strategy `size` callback is a **foreign boundary** whose answer is a
`SizeAnswer`: a `Size`, or a throw carrying an opaque reason.

## 2. CATEGORIES

- `inductive-data` — entries, queues, strategies, size algorithms and answers
  are first-order records and finite alphabets over externally owned
  parameters;
- `total-functions` — every operation is a total, kernel-reducible function of
  its arguments and of the supplied `SizeClass`; there is no relation, no
  fuel, and no partiality anywhere;
- `admission-and-refusal` — `EnqueueValueWithSize` and `ExtractHighWaterMark`
  each refuse a stated set of sizes with a `RangeError`, and the two sets are
  **different**. This is why the assurance route is a graph and not a leaf;
- `invariants` — the relation between `[[queueTotalSize]]` and the sizes in
  `[[queue]]` is a stated invariant whose truth depends on the carrier, and
  the specification says in its own text that it fails for the carrier the
  specification uses;
- `algebraic-laws` — append/remove-at-zero order, the clamp, reset, and the
  agreement of peek with dequeue;
- `foreign-boundary` — the two built-in size functions and any user `size`
  callback enter as named decisions with profiles;
- `counterexamples` — ten proved witnesses force the representation;
- `claim-scope` — the carrier boundary is named and ruled on, not silently
  modelled.

## 3. REQUIRES

1. Lean core at the repository's pinned toolchain `leanprover/lean4:v4.33.1`.
   No Mathlib, no Std beyond what core provides, no Lake dependency.
2. `WhatwgStreams/Data/Queue.lean` imports nothing from `WhatwgStreams`.
   `WhatwgStreams/Data/Strategy.lean` imports `WhatwgStreams.Data.Queue` and
   nothing else from `WhatwgStreams`. Neither imports `Sha256`, `Gates`, or
   anything under `WhatwgStreamsTest`. Both must be reachable from
   `WhatwgStreams.lean`, which the module-closure gate in
   `WhatwgStreamsTest/Audit/AxiomGate.lean` enforces, and which is also what
   makes the battery's single `import WhatwgStreams` sufficient (section 8).
3. `Size`, the chunk type `α`, the size-callback name alphabet `σ`, and the
   throw-reason alphabet `ε` are opaque parameters. No constructor, decidable
   equality, order, or default value of any of them is assumed beyond the
   instance binders written in the frozen signatures.
4. `DecidableEq` is derived, never classical. `Classical.choice`,
   `native_decide`, `sorry`, `admit`, the `partial` modifier, the `unsafe`
   modifier, and new axioms are not allowed in the packet or the
   implementation. The axiom ceiling for every public theorem is `propext` and
   `Quot.sound`.
5. Universe policy: one explicit `Type u` carries `α`, `σ`, `ε` and `Size`.
   `RangeError` is a parameterless inductive in `Type`.
6. Auxiliary lemmas beyond the list in section 5 are permitted but must be
   `private`, so the generated declaration snapshot has no unannotated public
   export.
7. This packet declares no arithmetic instance. It declares the `SizeClass`
   record and its three property predicates; the instance arrives with the
   `P3-R1` ruling, in a module this contract does not fence.

## 4. What the pinned specification says

Read first-hand from the pinned bytes. Quoted anchor text, never line numbers.

**`slot.queue` / `slot.queue-total-size`.** A queue-with-sizes is "two paired
internal slots, always named \[[queue]] and \[[queueTotalSize]]. \[[queue]] is
a list of value-with-sizes, and \[[queueTotalSize]] is a JavaScript Number,
i.e. a double-precision floating point number." A `value-with-size` is "a
struct with the two items value and size."

**The warning that decides this packet's shape.** The `queue-with-sizes`
section carries a normative-adjacent warning in its own text: "Due to the
limited precision of floating-point arithmetic, the framework specified here,
of keeping a running total in the \[[queueTotalSize]] slot, is *not*
equivalent to adding up the size of all chunks in \[[queue]]."

**`op.enqueue-value-with-size`.** Steps, in order: assert the slots exist; "If
! IsNonNegativeNumber(|size|) is false, throw a RangeError exception"; "If
|size| is +∞, throw a RangeError exception"; append a new value-with-size;
"Set |container|.\[[queueTotalSize]] to |container|.\[[queueTotalSize]] +
|size|." The two refusals are **two separate steps in a fixed order**.

**`op.is-non-negative-number`.** "If |v| is not a Number, return false. If |v|
is NaN, return false. If |v| < 0, return false. Return true." So `-∞` is
refused by the first refusal step and `+∞` by the second.

**`op.dequeue-value`.** Assert the slots; "Assert: |container|.\[[queue]] is
not empty"; take element `0`; remove it; subtract its size from the running
total; "If |container|.\[[queueTotalSize]] < 0, set
|container|.\[[queueTotalSize]] to 0. (This can occur due to rounding
errors.)"; return the value. The clamp exists **only** because of rounding;
the specification says so in that parenthesis.

**`op.peek-queue-value`.** Assert the slots; assert non-empty; take element
`0`; return its value. It touches neither slot.

**`op.reset-queue`.** Assert the slots; set `[[queue]]` to a new empty list;
set `[[queueTotalSize]]` to `0`. Unconditionally, with no clamp and no
arithmetic.

**`op.validate-and-normalize-high-water-mark`.** The anchor id is
`validate-and-normalize-high-water-mark`, but at this pin the algorithm it
anchors is named `ExtractHighWaterMark(|strategy|, |defaultHWM|)` and it
normalizes nothing: "If |strategy|["highWaterMark"] does not exist, return
|defaultHWM|." "If |highWaterMark| is NaN or |highWaterMark| < 0, throw a
RangeError exception." "Return |highWaterMark|." Its note is explicit: "+∞ is
explicitly allowed as a valid high water mark. It causes backpressure to never
be applied."

> **Breaker finding B1.** There is no `ValidateAndNormalizeHighWaterMark`
> algorithm at this pin, and no normalization step anywhere. A declaration of
> that name would model a row the census does not contain. This contract
> freezes `extractHighWaterMark` only, and freezes an **identity** law on its
> accepted inputs in place of the normalization-idempotence law a stale name
> would invite. `WS-DATA-CE-009` is the attack.

> **Breaker finding B2.** The refusal set of `EnqueueValueWithSize` and the
> refusal set of `ExtractHighWaterMark` differ on exactly one value: `+∞` is
> refused as a size and allowed as a high water mark. A model that shares one
> predicate between them is wrong and contradicts the pinned WPT corpus in
> both directions. `WS-DATA-CE-008` is the attack.

**`op.make-size-algorithm-from-size-function`.** `ExtractSizeAlgorithm(|strategy|)`:
"If |strategy|["size"] does not exist, return an algorithm that returns 1."
Otherwise "Return an algorithm that performs the following steps, taking a
|chunk| argument: Return the result of invoking |strategy|["size"] with
argument list « |chunk| »."

**`op.count-queuing-strategy-size-function`.** Every global object has an
associated count queuing strategy size function whose steps are "Return 1",
built with `CreateBuiltinFunction` with length `0` in that global's realm.

**`op.byte-length-queuing-strategy-size-function`.** The same, with steps
"Return ? GetV(|chunk|, "`byteLength`")" and length `1`. The `?` is a
propagating abrupt completion: this getter can throw.

**`op.cqs-constructor` / `op.blqs-constructor`.** Each sets its
`[[highWaterMark]]` slot to `init["highWaterMark"]` and does nothing else. The
prose beside them is explicit: "Note that the provided high water mark will not
be validated ahead of time. Instead, if it is negative, NaN, or not a number,
the resulting CountQueuingStrategy will cause the corresponding stream
constructor to throw."

> **Breaker finding B3.** Neither strategy class validates. A
> `CountQueuingStrategy` whose `[[highWaterMark]]` is `NaN` is constructible
> and observable, so the strategy record must be able to hold `NaN` and `-∞`.
> The pinned WPT `queuing-strategies.any.js` observes exactly this, in the
> table it calls `highWaterMarkConversions`: `-Infinity` maps to `-Infinity`,
> `NaN` to `NaN`, `'foo'` to `NaN`, `{}` to `NaN`, `false` to `0`, `true` to
> `1`, `'0'` to `0`, and the constructed strategy's `highWaterMark` getter
> returns that stored value.

## 5. What the pinned host corpus observes

Host observations under the WPT profile. None of them is a theorem, and none
of them repairs a statement; they constrain which statements may be written.

| Pinned file and test | Observation |
| --- | --- |
| `readable-streams/bad-strategies.any.js`, "Readable stream: invalid strategy.size return value" | every size in `[NaN, -Infinity, Infinity, -1]` makes `enqueue` throw a `RangeError`. `Infinity` and `-Infinity` are refused by **different** steps of `EnqueueValueWithSize` |
| the same file, "Readable stream: invalid strategy.highWaterMark" | every high water mark in `[-1, -Infinity, NaN, 'foo', {}]` makes construction throw a `RangeError`. **`Infinity` is absent from this list** |
| `writable-streams/bad-strategies.any.js`, the two tests of the same names | the same two lists, for the writable side |
| the same file, "Writable stream: throwing strategy.size method" | a `size` callback that throws rejects the write and the writer's `closed` with the thrown value: the boundary has a throw answer, not only a value answer |
| `queuing-strategies.any.js`, "CountQueuingStrategy: size behaves as expected with strange arguments" | the count size function returns `1` for `undefined`, `null`, a string, `{}`, a chunk, a getter, **and a getter that throws**. It never reads its argument |
| the same file, "ByteLengthQueuingStrategy: size behaves as expected with strange arguments" | the byte-length size function throws a `TypeError` on `undefined` and `null`, returns **`undefined`** for `'potato'` and `{}`, returns `1024` for `{ byteLength: 1024 }`, and re-throws a throwing getter |
| the same file, "`…`: highWaterMark constructor values are converted per the unrestricted double rules" | the `highWaterMarkConversions` table of finding B3 |
| the same file, "`…`: size is the same function across all instances" | within one realm the size function is one object |
| `queuing-strategies-size-function-per-global.window.js` | across two realms the size functions are **different objects** |
| `readable-streams/floating-point-total-queue-size.any.js` and its writable twin | the four double-arithmetic cases quoted in section 6 |

> **Breaker finding B4.** The byte-length size function returning `undefined`
> for a chunk with no `byteLength` property is not an error at the callback:
> the Web IDL callback type is `unrestricted double (any chunk)`, so
> `undefined` is converted to `NaN`, which then makes `EnqueueValueWithSize`
> throw a `RangeError`. A model of that function as a total `α → Size` cannot
> express the `undefined` answer or the throw answer, and would contradict two
> pinned WPT assertions. This contract therefore freezes a three-armed
> `ByteLengthAnswer`, and a profile relating it to the oracle, in place of the
> total function.

## 6. `P3-R1` — the ruling request: which carrier is `Size`?

**The breaker states this and does not decide it.** The default is option (i).

### 6.1 The disagreement, pinned exactly

The pinned WPT case
`readable-streams/floating-point-total-queue-size.any.js`, test "Floating point
arithmetic must manifest near 0 (total ends up positive, but clamped)",
enqueues `1e-16`, enqueues `1`, and then reads:

```js
controller.enqueue(1e-16);
assert_equals(controller.desiredSize, 0 - 1e-16, …);
controller.enqueue(1);
assert_equals(controller.desiredSize, 0 - 1e-16 - 1, …);
return reader.read().then(() => {
  assert_equals(controller.desiredSize, 0 - 1e-16 - 1 + 1e-16, …);
  return reader.read();
}).then(() => {
  assert_equals(controller.desiredSize, 0, '[[queueTotalSize]] must clamp to 0 if it becomes negative');
});
```

with `highWaterMark: 0` and `size(x) { return x; }`. The file's own header says
why these cases exist: "It is important that implementations give the same
result in these edge cases so that developers do not come to depend on
non-standard behaviour."

The exact binary64 values, read off the literals with
`BitConverter.DoubleToInt64Bits`:

| Quantity | Exact value |
| --- | --- |
| the double nearest `1e-16` | `8112963841460668 × 2^(-106)` |
| the double `1.0` | `2^106 × 2^(-106)` |
| `1e-16 + 1` in binary64 | `1.0` exactly — the addend is below the half-ulp of `1.0` and vanishes |
| `(1e-16 + 1) - 1e-16` in binary64 | `9007199254740991 × 2^(-53)`, printed `0.9999999999999999` |
| the same under exact arithmetic | `1` |
| the gap | exactly `2^(-53)`, one ulp of `1.0` |

The third assertion is the discriminating one, and it discriminates even at
the JavaScript boundary: `0 - 1e-16 - 1 + 1e-16` evaluates to
`-0.9999999999999999`, whereas an exact model computes `-1`, and those are two
different doubles. The first two assertions do **not** discriminate: both
evaluate to `-1e-16` and `-1` under either arithmetic.

`WS-DATA-CE-001` pre-registers this disagreement. Its witness is proved, green
today, in `WhatwgStreamsTest/Counterexamples/Data/Queue.lean`, over an exact
`Int` grid of `2^(-106)` units with a round-to-nearest-even function at 53
significant bits, so it reproduces binary64 on this case without using
`Float`.

### 6.2 What each option can and cannot prove

| | (i) exact carrier, default | (ii) modelled binary64 | (iii) `Nat` sizes only |
| --- | --- | --- | --- |
| `Queue.WF` (`totalSize` = sum of sizes) preserved by enqueue and dequeue | **provable** | **false**, by `ce001_wf_broken`, and the specification's own warning says so | provable |
| the `DequeueValue` step-6 clamp | **unreachable**; the only theorem available is that the branch is never taken (`ce001_clamp_unreachable_exact`). The step is witnessed as vacuous, not as a branch | reachable and witnessed as a branch (`ce001_clamp_reachable_rounded`) | unreachable, same as (i) |
| the four `floating-point-total-queue-size` WPT cases | **cannot** be reproduced; they become host-only rows under mask M1 in the harness ledger | reproducible in principle | cannot be reproduced |
| `+∞` as a legal high water mark (`op.validate-and-normalize-high-water-mark`) | needs an explicit point at infinity beside the exact values | native | **impossible**: `Nat` has no `+∞`, so this pinned requirement cannot be modelled |
| the refusals of `NaN`, `+∞`, `-∞` and negatives | statable, with an extended carrier | native | **vacuous**: no `Nat` is `NaN`, so every refusal law is satisfied by an implementation that never refuses (`ce007_nan_refusal_is_vacuous`) |
| cost | a dyadic-rational or rational value type plus three special points; core has no `Rat` in the semantic tree, so the value type is built from `Int`/`Nat` here | a software binary64 with rounding, guard digits, subnormals and overflow: a sub-project the size of this whole packet | small |
| kernel reachability | full: every law is `decide`-able on ground instances | full, at the price above | full |

> **Breaker finding B5.** Lean's `Float` is not an available answer for option
> (ii). Its operations are opaque `extern` constants, so no equation between
> two `Float` expressions reduces in the kernel, and the only tactic that
> decides one is `native_decide`, which `WhatwgStreamsTest/Audit/AxiomGate.lean`
> forbids by shape. A `Float`-based model could carry executable checks only,
> and only outside this repository's gates. Option (ii) therefore means a
> **modelled** binary64, not `Float`.

> **Breaker finding B6.** Option (iii) is refuted by the pinned text, not
> merely expensive: `+∞` is an explicitly allowed high water mark, and a
> `Nat`-only carrier cannot represent it. It is listed for completeness.

### 6.3 The default, and what a different ruling costs

**Default: option (i)**, an exact carrier extended with `nan`, `posInfinity`
and `negInfinity`, with the host's rounding declared a foreign boundary
(`DATA-FB-ROUNDING` in `docs/DATA-DAG.md`) and the four
`floating-point-total-queue-size` cases marked host-only under mask M1.

The declaration surface in section 7 is written so that the ruling changes an
**instance**, never a statement:

- no operation mentions a concrete size type; each takes a `SizeClass Size`
  record;
- every law that needs exactness carries a `SizeClass.Exact` hypothesis, so
  under option (ii) those laws are simply not applicable and none is reopened;
- `SizeClass.Classified` fixes the three special constants, so no instance can
  make a refusal law vacuous;
- the `DequeueValue` clamp is in the model under every option, so option (i)
  does not delete a specification step; it adds
  `dequeueValue_clamp_unreachable_of_exact` beside it.

Under option (ii) the builder supplies a non-`Exact` instance, and exactly
three of the ninety-nine frozen theorems become inapplicable: `sizeSum_cons`,
`dequeueValue_wf`, and `dequeueValue_clamp_unreachable_of_exact`. Those are
the only three that carry a `SizeClass.Exact` hypothesis. Notably
`enqueueValueWithSize_wf` is **not** among them: it needs no exactness,
because `sizeSum` is a left fold and `sizeSum_append_singleton` takes the
same step the running total takes, so enqueue cannot drift and only dequeue
can. `docs/DATA-DAG.md` records this as the cost of that ruling. No signature
changes, and no other statement changes.

## 7. Public declarations

Binder names may differ. Public names, constructor order and fields, argument
roles, result types, and theorem propositions are frozen by the Lean battery's
`#check (@name : proposition)` ascriptions. **The battery is the authority**;
the Lean shown here is a reading aid. Every declaration lives in namespace
`WhatwgStreams.Data`. Every theorem's binders are, in order, the type
parameters actually mentioned, taken from `{α σ ε Size : Type u}`, then the
`SizeClass` record, then the explicit arguments.

### Existing-type and duplicate-prevention rows

The eleven rows, with owners, relationships, specification anchors, span
digests and assurance routes, are in `docs/DATA-DAG.md` "Existing-type rows".
They are not restated here.

### D0 — the refusal tag

```lean
inductive RangeError
  | rangeError
deriving DecidableEq, Repr
```

The `{{RangeError}}` of `op.enqueue-value-with-size` and
`op.validate-and-normalize-high-water-mark`. It is the only exception this
calculus can raise. See open question `P3-R2` in section 12.

### D1 — the size carrier interface

```lean
structure SizeClass (Size : Type u) where
  zero : Size
  one : Size
  nan : Size
  posInfinity : Size
  negInfinity : Size
  add : Size -> Size -> Size
  sub : Size -> Size -> Size
  isNaN : Size -> Bool
  isNegative : Size -> Bool
  isInfinite : Size -> Bool

SizeClass.Admissible : SizeClass Size -> Size -> Prop
SizeClass.isNonNegativeNumber : SizeClass Size -> Size -> Bool
SizeClass.isPositiveInfinity : SizeClass Size -> Size -> Bool
SizeClass.clampNonNegative : SizeClass Size -> Size -> Size
```

`Admissible` is the set `EnqueueValueWithSize` accepts: not `NaN`, not
negative, not infinite. `isNonNegativeNumber` is `op.is-non-negative-number`
restricted to a carrier whose values are already Numbers; the "is not a
Number" step is a Web IDL boundary and is `hostOnly`.

The three special constants are **fields, not derived**. That is the
anti-vacuity device of finding in section 6.2: an instance must exhibit a
`NaN`, a `+∞` and a `-∞`, so no refusal law can be satisfied for want of a
witness.

### D2 — the three carrier property predicates

```lean
structure SizeClass.Classified (sizes : SizeClass Size) : Prop where
  nan_isNaN                : sizes.isNaN sizes.nan = true
  nan_not_negative         : sizes.isNegative sizes.nan = false
  nan_not_infinite         : sizes.isInfinite sizes.nan = false
  posInfinity_infinite     : sizes.isInfinite sizes.posInfinity = true
  posInfinity_not_negative : sizes.isNegative sizes.posInfinity = false
  posInfinity_not_nan      : sizes.isNaN sizes.posInfinity = false
  negInfinity_infinite     : sizes.isInfinite sizes.negInfinity = true
  negInfinity_negative     : sizes.isNegative sizes.negInfinity = true
  negInfinity_not_nan      : sizes.isNaN sizes.negInfinity = false
  nan_isolated : forall v, sizes.isNaN v = true ->
    sizes.isNegative v = false /\ sizes.isInfinite v = false

structure SizeClass.Ordered (sizes : SizeClass Size) : Prop where
  zero_admissible : sizes.Admissible sizes.zero
  one_admissible  : sizes.Admissible sizes.one
  add_admissible  : forall a b, sizes.Admissible a -> sizes.Admissible b ->
    sizes.Admissible (sizes.add a b)

structure SizeClass.Exact (sizes : SizeClass Size) : Prop where
  add_assoc : forall a b c, sizes.Admissible a -> sizes.Admissible b -> sizes.Admissible c ->
    sizes.add (sizes.add a b) c = sizes.add a (sizes.add b c)
  add_comm : forall a b, sizes.Admissible a -> sizes.Admissible b ->
    sizes.add a b = sizes.add b a
  zero_add : forall a, sizes.Admissible a -> sizes.add sizes.zero a = a
  sub_add_cancel : forall a b, sizes.Admissible a -> sizes.Admissible b ->
    sizes.sub (sizes.add a b) b = a
```

Every equation in `Exact` is guarded by `Admissible`. Unguarded they are false
of **any** carrier that has a `NaN`, exact or not: `sub_add_cancel a nan`
would demand `nan = a`. A builder who drops the guards freezes a predicate no
instance satisfies, and every law that depends on it becomes vacuous.

`Ordered.add_admissible` is where overflow lives: it is true of an exact
carrier and false of a bounded one, which is a second, independent way the
`P3-R1` ruling shows up in the statements.

### D3 — the queue

```lean
structure QueueEntry (α : Type u) (Size : Type u) where
  value : α
  size : Size
deriving DecidableEq, Repr

structure Queue (α : Type u) (Size : Type u) where
  entries : List (QueueEntry α Size)
  totalSize : Size
deriving DecidableEq

Queue.empty : SizeClass Size -> Queue α Size
sizeSum : SizeClass Size -> List (QueueEntry α Size) -> Size
Queue.WF : SizeClass Size -> Queue α Size -> Prop
Queue.SizesAdmissible : SizeClass Size -> Queue α Size -> Prop
instance : [DecidableEq Size] -> Decidable (Queue.WF sizes q)
```

`QueueEntry` is `value-with-size`, whose two items the pinned text names
`value` and `size`, in that order.

**The `WF` decision, ruled here and frozen.** `Queue.WF` is a separate `Prop`
with a decidable instance. It is **not** baked into the structure. The
argument is the specification's own warning quoted in section 4: keeping a
running total "is *not* equivalent to adding up the size of all chunks in
\[[queue]]". A structure that made `totalSize = sizeSum entries`
unconstructible-otherwise would make the specification's own reachable states
unrepresentable, and would make it impossible for P4 and P5 to model a
conforming host that has drifted. The house rule that an invariant stated in
prose becomes unconstructible shapes applies where the specification asserts
the invariant; here the specification denies it. `WS-DATA-CE-001` is the
witness that the denial is real, and `resetQueue_wf` is the one place the invariant
is restored unconditionally.

`sizeSum` is a **left** fold from `zero`, in the order
`EnqueueValueWithSize` accumulates. Under a rounding carrier a right fold
gives a different answer for the same queue; `WS-DATA-CE-002` is that attack.

### D4 — the four queue-with-sizes operations

```lean
enqueueValueWithSize : SizeClass Size -> Queue α Size -> α -> Size ->
  Except RangeError (Queue α Size)
dequeueValue : SizeClass Size -> Queue α Size -> Option (α × Queue α Size)
peekQueueValue : Queue α Size -> Option α
resetQueue : SizeClass Size -> Queue α Size -> Queue α Size
```

Frozen definitions:

```lean
enqueueValueWithSize sizes q value size =
  if sizes.isNonNegativeNumber size = false then .error .rangeError
  else if sizes.isPositiveInfinity size then .error .rangeError
  else .ok { entries := q.entries ++ [{ value := value, size := size }],
             totalSize := sizes.add q.totalSize size }

dequeueValue sizes q =
  match q.entries with
  | [] => none
  | entry :: rest =>
      some (entry.value,
        { entries := rest,
          totalSize := sizes.clampNonNegative (sizes.sub q.totalSize entry.size) })

peekQueueValue q =
  match q.entries with
  | [] => none
  | entry :: _ => some entry.value

resetQueue sizes _ = { entries := [], totalSize := sizes.zero }
```

`peekQueueValue` takes **no** `SizeClass` and returns **no** queue. Both
absences are deliberate and are the packet's strongest statement that
`PeekQueueValue` touches neither slot: the mutation `WS-DATA-CE-005` attacks
is not expressible in the frozen result type. A builder who widens the result
to a pair fails the ascription.

`dequeueValue`'s `Option` is the model of the specification's "Assert:
\[[queue]] is not empty". The assertion is stated as the precondition of the
laws that need it, and `dequeueValue_isSome_iff` is the theorem that the `none` arm
is reached on exactly the empty queue. `WS-DATA-CE-004` attacks answering on
an empty queue.

### D5 — size algorithms and the foreign boundary

```lean
inductive SizeAlgorithm (σ : Type u)
  | one
  | foreign (name : σ)
deriving DecidableEq, Repr

inductive SizeAnswer (Size : Type u) (ε : Type u)
  | value (size : Size)
  | thrown (reason : ε)
deriving DecidableEq

inductive ByteLengthAnswer (Size : Type u) (ε : Type u)
  | number (n : Size)
  | undefined
  | thrown (reason : ε)
deriving DecidableEq

SizeAlgorithm.invoke : SizeClass Size -> (σ -> α -> SizeAnswer Size ε) ->
  SizeAlgorithm σ -> α -> SizeAnswer Size ε
byteLengthSize : SizeClass Size -> ByteLengthAnswer Size ε -> SizeAnswer Size ε
```

`SizeAlgorithm.one` is the "algorithm that returns 1" of
`op.make-size-algorithm-from-size-function`. `SizeAlgorithm.foreign` carries a
**name**, never a Lean function, per DB-02; the oracle argument supplies the
answer. `ByteLengthAnswer.undefined` is finding B4: the property is absent, the
Web IDL conversion yields `NaN`, and the enqueue that follows refuses it.

### D6 — the strategy dictionary and the two extraction algorithms

```lean
structure QueuingStrategy (σ : Type u) (Size : Type u) where
  highWaterMark : Option Size
  size : Option σ

extractHighWaterMark : SizeClass Size -> QueuingStrategy σ Size -> Size ->
  Except RangeError Size
extractSizeAlgorithm : QueuingStrategy σ Size -> SizeAlgorithm σ
```

Both fields are `Option` because the pinned algorithms branch on "does not
exist" in the `QueuingStrategy` map, which is not the same as a present
`undefined`. Frozen definitions:

```lean
extractHighWaterMark sizes strategy defaultHWM =
  match strategy.highWaterMark with
  | none => .ok defaultHWM
  | some highWaterMark =>
      if sizes.isNaN highWaterMark || sizes.isNegative highWaterMark then .error .rangeError
      else .ok highWaterMark

extractSizeAlgorithm strategy =
  match strategy.size with
  | none => .one
  | some name => .foreign name
```

### D7 — the two built-in strategy classes

```lean
structure CountQueuingStrategy (Size : Type u) where
  highWaterMark : Size
deriving DecidableEq

structure ByteLengthQueuingStrategy (Size : Type u) where
  highWaterMark : Size
deriving DecidableEq

CountQueuingStrategy.make : Size -> CountQueuingStrategy Size
CountQueuingStrategy.sizeAlgorithm : σ -> SizeAlgorithm σ
CountQueuingStrategy.toQueuingStrategy : σ -> CountQueuingStrategy Size -> QueuingStrategy σ Size

ByteLengthQueuingStrategy.make : Size -> ByteLengthQueuingStrategy Size
ByteLengthQueuingStrategy.sizeAlgorithm : σ -> SizeAlgorithm σ
ByteLengthQueuingStrategy.toQueuingStrategy : σ -> ByteLengthQueuingStrategy Size ->
  QueuingStrategy σ Size
```

Each class carries only its `[[highWaterMark]]` slot, which is exactly what
`blqs-internal-slots` and `cqs-internal-slots` say instances have. The size
function is **not** a field: the pinned text puts it on the global object, and
the pinned WPT observes it is one object per realm shared by every instance.
Each `sizeAlgorithm` therefore takes the realm's name for that function as its
argument, and realm identity is refused rather than modelled
(`realm_identity_refused`).

### D8 — the two foreign-boundary profiles

```lean
structure CountSizeProfile (sizes : SizeClass Size) (countName : σ)
    (oracle : σ -> α -> SizeAnswer Size ε) : Prop where
  answers_one : forall chunk, oracle countName chunk = SizeAnswer.value sizes.one

structure ByteLengthSizeProfile (sizes : SizeClass Size) (byteLengthName : σ)
    (byteLength : α -> ByteLengthAnswer Size ε)
    (oracle : σ -> α -> SizeAnswer Size ε) : Prop where
  answers_byteLength : forall chunk,
    oracle byteLengthName chunk = byteLengthSize sizes (byteLength chunk)
```

These are the "typed decisions with a profile" of DB-02 and the representation
rules. `CountSizeProfile.answers_one` is quantified over **every** chunk, which
is the modelled form of the pinned WPT observation that the count size function
returns `1` even for a chunk whose getter throws: it never reads its argument.

## 8. Why the battery imports `WhatwgStreams` and not the fenced modules

The battery's only import of the production tree is `import WhatwgStreams`.

At the base commit of this packet the two fenced modules do not exist in this
worktree; the P2 seat creates the breadth stubs on `main`. A battery that
imported `WhatwgStreams.Data.Queue` directly would fail to **resolve an
import**, which is not a clean red result: the effect4 precedent requires the
red phase to fail with unknown-identifier and unknown-constant diagnostics
only, and a Lake import failure is neither. Importing the production root is
sufficient because the module-closure gate in
`WhatwgStreamsTest/Audit/AxiomGate.lean` requires every source file under
`WhatwgStreams/` to be reachable from `WhatwgStreams.lean`, so the builder
cannot land the fenced modules without making them visible through that root.
The measured behaviour of both spellings is recorded in the P3 handoff.

## 9. ENSURES — public theorem spine

Every proposition is frozen in the Lean battery by exact ascription. A weaker
statement does not satisfy this contract. Ninety-nine theorems, in battery
order. Each group names the census rows it witnesses.

### S1 — classification and admission (census: `op.is-non-negative-number`)

```lean
SizeClass.isNonNegativeNumber_eq :
  sizes.isNonNegativeNumber v = (!sizes.isNaN v && !sizes.isNegative v)
SizeClass.isPositiveInfinity_eq :
  sizes.isPositiveInfinity v = (sizes.isInfinite v && !sizes.isNegative v)
SizeClass.admissible_iff :
  sizes.Admissible v <->
    (sizes.isNaN v = false /\ sizes.isNegative v = false /\ sizes.isInfinite v = false)
SizeClass.not_admissible_nan : ¬ sizes.Admissible sizes.nan
SizeClass.not_admissible_posInfinity : Classified sizes -> ¬ sizes.Admissible sizes.posInfinity
SizeClass.not_admissible_negInfinity : Classified sizes -> ¬ sizes.Admissible sizes.negInfinity
SizeClass.isNonNegativeNumber_nan : sizes.isNonNegativeNumber sizes.nan = false
SizeClass.isNonNegativeNumber_negInfinity :
  Classified sizes -> sizes.isNonNegativeNumber sizes.negInfinity = false
SizeClass.isNonNegativeNumber_posInfinity :
  Classified sizes -> sizes.isNonNegativeNumber sizes.posInfinity = true
SizeClass.clampNonNegative_of_negative :
  sizes.isNegative v = true -> sizes.clampNonNegative v = sizes.zero
SizeClass.clampNonNegative_of_nonneg :
  sizes.isNegative v = false -> sizes.clampNonNegative v = v
SizeClass.clampNonNegative_not_negative :
  Ordered sizes -> sizes.isNegative (sizes.clampNonNegative v) = false
```

`isNonNegativeNumber_posInfinity` is the theorem that pins the two-step
structure of `EnqueueValueWithSize`: `+∞` passes the first refusal and is
caught only by the second. Without it a one-step model would satisfy every
other law here.

### S2 — the queue carrier and the sum (census: `slot.queue`, `slot.queue-total-size`)

```lean
Queue.empty_entries : (Queue.empty sizes : Queue α Size).entries = []
Queue.empty_totalSize : (Queue.empty sizes : Queue α Size).totalSize = sizes.zero
sizeSum_nil : sizeSum sizes ([] : List (QueueEntry α Size)) = sizes.zero
sizeSum_append_singleton :
  sizeSum sizes (entries ++ [entry]) = sizes.add (sizeSum sizes entries) entry.size
sizeSum_cons :
  Exact sizes -> Ordered sizes -> sizes.Admissible entry.size ->
    (forall e, e ∈ entries -> sizes.Admissible e.size) ->
      sizeSum sizes (entry :: entries) = sizes.add entry.size (sizeSum sizes entries)
sizeSum_admissible :
  Ordered sizes -> (forall e, e ∈ entries -> sizes.Admissible e.size) ->
    sizes.Admissible (sizeSum sizes entries)
Queue.WF_iff : q.WF sizes <-> q.totalSize = sizeSum sizes q.entries
Queue.WF_empty : (Queue.empty sizes : Queue α Size).WF sizes
Queue.SizesAdmissible_iff :
  q.SizesAdmissible sizes <-> forall entry, entry ∈ q.entries -> sizes.Admissible entry.size
Queue.SizesAdmissible_empty : (Queue.empty sizes : Queue α Size).SizesAdmissible sizes
```

`sizeSum_cons` is the only place the left fold has to be turned around, and it
is exactly the lemma `dequeueValue_wf` needs. It carries `Exact` because it is false
without it: `WS-DATA-CE-002` exhibits a carrier and a three-entry queue on
which the two fold directions differ.

### S3 — enqueue (census: `op.enqueue-value-with-size`)

```lean
enqueueValueWithSize_error_iff :
  enqueueValueWithSize sizes q value size = .error .rangeError <->
    (sizes.isNonNegativeNumber size = false \/ sizes.isPositiveInfinity size = true)
enqueueValueWithSize_error_iff_not_admissible :
  enqueueValueWithSize sizes q value size = .error .rangeError <-> ¬ sizes.Admissible size
enqueueValueWithSize_refuses_nan :
  enqueueValueWithSize sizes q value sizes.nan = .error .rangeError
enqueueValueWithSize_refuses_negative :
  sizes.isNegative size = true -> enqueueValueWithSize sizes q value size = .error .rangeError
enqueueValueWithSize_refuses_posInfinity :
  Classified sizes -> enqueueValueWithSize sizes q value sizes.posInfinity = .error .rangeError
enqueueValueWithSize_refuses_negInfinity :
  Classified sizes -> enqueueValueWithSize sizes q value sizes.negInfinity = .error .rangeError
enqueueValueWithSize_ok_iff :
  (exists q', enqueueValueWithSize sizes q value size = .ok q') <-> sizes.Admissible size
enqueueValueWithSize_eq_of_admissible :
  sizes.Admissible size ->
    enqueueValueWithSize sizes q value size =
      .ok { entries := q.entries ++ [{ value := value, size := size }],
            totalSize := sizes.add q.totalSize size }
enqueueValueWithSize_entries :
  enqueueValueWithSize sizes q value size = .ok q' ->
    q'.entries = q.entries ++ [{ value := value, size := size }]
enqueueValueWithSize_totalSize :
  enqueueValueWithSize sizes q value size = .ok q' -> q'.totalSize = sizes.add q.totalSize size
enqueueValueWithSize_length :
  enqueueValueWithSize sizes q value size = .ok q' -> q'.entries.length = q.entries.length + 1
enqueueValueWithSize_sizesAdmissible :
  q.SizesAdmissible sizes -> enqueueValueWithSize sizes q value size = .ok q' ->
    q'.SizesAdmissible sizes
enqueueValueWithSize_totalSize_admissible :
  Ordered sizes -> sizes.Admissible q.totalSize ->
    enqueueValueWithSize sizes q value size = .ok q' -> sizes.Admissible q'.totalSize
enqueueValueWithSize_wf :
  q.WF sizes -> enqueueValueWithSize sizes q value size = .ok q' -> q'.WF sizes
```

`enqueueValueWithSize_entries` is the append, and it is what
`WS-DATA-CE-010` attacks: a model that prepends keeps the total, the length,
and the multiset of entries, and is caught by nothing else here.

`enqueueValueWithSize_wf` needs no `Ordered`: `sizeSum (es ++ [e])` is
literally `add (sizeSum es) e.size` by `sizeSum_append_singleton`, so the
running total and the fold take the same step. That is the structural reason
enqueue never drifts and dequeue does.

### S4 — dequeue (census: `op.dequeue-value`)

```lean
dequeueValue_nil : dequeueValue sizes { entries := [], totalSize := total } = none
dequeueValue_cons :
  dequeueValue sizes { entries := entry :: rest, totalSize := total } =
    some (entry.value,
      { entries := rest, totalSize := sizes.clampNonNegative (sizes.sub total entry.size) })
dequeueValue_isSome_iff : (dequeueValue sizes q).isSome = true <-> q.entries ≠ []
dequeueValue_isNone_iff : dequeueValue sizes q = none <-> q.entries = []
dequeueValue_value_eq_head :
  (dequeueValue sizes q).map Prod.fst = q.entries.head?.map QueueEntry.value
dequeueValue_entries :
  dequeueValue sizes q = some (value, q') -> q'.entries = q.entries.tail
dequeueValue_length :
  dequeueValue sizes q = some (value, q') -> q.entries.length = q'.entries.length + 1
dequeueValue_totalSize :
  q.entries = entry :: rest -> dequeueValue sizes q = some (value, q') ->
    q'.totalSize = sizes.clampNonNegative (sizes.sub q.totalSize entry.size)
dequeueValue_totalSize_not_negative :
  Ordered sizes -> dequeueValue sizes q = some (value, q') ->
    sizes.isNegative q'.totalSize = false
dequeueValue_sizesAdmissible :
  q.SizesAdmissible sizes -> dequeueValue sizes q = some (value, q') ->
    q'.SizesAdmissible sizes
dequeueValue_wf :
  Classified sizes -> Ordered sizes -> Exact sizes ->
    q.WF sizes -> q.SizesAdmissible sizes -> dequeueValue sizes q = some (value, q') ->
      q'.WF sizes
dequeueValue_clamp_unreachable_of_exact :
  Classified sizes -> Ordered sizes -> Exact sizes ->
    q.WF sizes -> q.SizesAdmissible sizes -> q.entries = entry :: rest ->
      sizes.isNegative (sizes.sub q.totalSize entry.size) = false
```

`dequeueValue_clamp_unreachable_of_exact` is the vacuity theorem of section
6.2: under an exact carrier the specification's step 6 branch is never taken.
It is frozen so that the cost of ruling `P3-R1` in favour of option (i) is a
theorem in the tree rather than a remark in a document, and so that a later
ruling that adopts option (ii) has something explicit to supersede.

### S5 — FIFO and peek (census: `op.peek-queue-value`, `op.dequeue-value`)

```lean
peekQueueValue_nil : peekQueueValue ({ entries := [], totalSize := total } : Queue α Size) = none
peekQueueValue_cons :
  peekQueueValue { entries := entry :: rest, totalSize := total } = some entry.value
peekQueueValue_eq_head : peekQueueValue q = q.entries.head?.map QueueEntry.value
peekQueueValue_agrees_dequeueValue :
  peekQueueValue q = (dequeueValue sizes q).map Prod.fst
peekQueueValue_isSome_iff : (peekQueueValue q).isSome = true <-> q.entries ≠ []
dequeueValue_enqueueValueWithSize_empty :
  q.entries = [] -> enqueueValueWithSize sizes q value size = .ok q' ->
    (dequeueValue sizes q').map Prod.fst = some value
dequeueValue_enqueueValueWithSize_nonempty :
  q.entries = entry :: rest -> enqueueValueWithSize sizes q value size = .ok q' ->
    (dequeueValue sizes q').map Prod.fst = some entry.value
peekQueueValue_enqueueValueWithSize_nonempty :
  q.entries = entry :: rest -> enqueueValueWithSize sizes q value size = .ok q' ->
    peekQueueValue q' = some entry.value
```

`dequeueValue_enqueueValueWithSize_nonempty` is the sharp FIFO statement: an
enqueue onto a non-empty queue does not change what the next dequeue answers.

### S6 — reset (census: `op.reset-queue`)

```lean
resetQueue_eq : resetQueue sizes q = { entries := [], totalSize := sizes.zero }
resetQueue_entries : (resetQueue sizes q).entries = []
resetQueue_totalSize : (resetQueue sizes q).totalSize = sizes.zero
resetQueue_wf : (resetQueue sizes q).WF sizes
resetQueue_sizesAdmissible : (resetQueue sizes q).SizesAdmissible sizes
resetQueue_idempotent : resetQueue sizes (resetQueue sizes q) = resetQueue sizes q
resetQueue_eq_empty : resetQueue sizes q = Queue.empty sizes
resetQueue_dequeueValue : dequeueValue sizes (resetQueue sizes q) = none
```

`resetQueue_wf` carries **no** carrier hypothesis. Reset is the one operation
that restores the invariant whatever the arithmetic did before it, because it
writes `0` rather than computing it. `WS-DATA-CE-006` attacks a reset that
keeps the running total, which is the shape a drifting implementation is
tempted into.

### S7 — the extraction algorithms (census: `op.validate-and-normalize-high-water-mark`, `op.make-size-algorithm-from-size-function`)

```lean
extractHighWaterMark_absent :
  strategy.highWaterMark = none ->
    extractHighWaterMark sizes strategy defaultHWM = .ok defaultHWM
extractHighWaterMark_error_iff :
  extractHighWaterMark sizes strategy defaultHWM = .error .rangeError <->
    (exists highWaterMark, strategy.highWaterMark = some highWaterMark /\
      (sizes.isNaN highWaterMark = true \/ sizes.isNegative highWaterMark = true))
extractHighWaterMark_refuses_nan :
  strategy.highWaterMark = some sizes.nan ->
    extractHighWaterMark sizes strategy defaultHWM = .error .rangeError
extractHighWaterMark_refuses_negative :
  strategy.highWaterMark = some highWaterMark -> sizes.isNegative highWaterMark = true ->
    extractHighWaterMark sizes strategy defaultHWM = .error .rangeError
extractHighWaterMark_refuses_negInfinity :
  Classified sizes -> strategy.highWaterMark = some sizes.negInfinity ->
    extractHighWaterMark sizes strategy defaultHWM = .error .rangeError
extractHighWaterMark_allows_posInfinity :
  Classified sizes -> strategy.highWaterMark = some sizes.posInfinity ->
    extractHighWaterMark sizes strategy defaultHWM = .ok sizes.posInfinity
extractHighWaterMark_id_on_accepted :
  strategy.highWaterMark = some highWaterMark ->
    extractHighWaterMark sizes strategy defaultHWM = .ok highWaterMark' ->
      highWaterMark' = highWaterMark
extractHighWaterMark_disagrees_with_enqueue_on_posInfinity :
  Classified sizes -> strategy.highWaterMark = some sizes.posInfinity ->
    extractHighWaterMark sizes strategy defaultHWM = .ok sizes.posInfinity /\
      enqueueValueWithSize sizes q value sizes.posInfinity = .error .rangeError
extractSizeAlgorithm_absent :
  strategy.size = none -> extractSizeAlgorithm strategy = SizeAlgorithm.one
extractSizeAlgorithm_present :
  strategy.size = some name -> extractSizeAlgorithm strategy = SizeAlgorithm.foreign name
SizeAlgorithm.invoke_one :
  SizeAlgorithm.invoke sizes oracle SizeAlgorithm.one chunk = SizeAnswer.value sizes.one
SizeAlgorithm.invoke_foreign :
  SizeAlgorithm.invoke sizes oracle (SizeAlgorithm.foreign name) chunk = oracle name chunk
extractSizeAlgorithm_absent_invoke :
  strategy.size = none ->
    SizeAlgorithm.invoke sizes oracle (extractSizeAlgorithm strategy) chunk =
      SizeAnswer.value sizes.one
```

`extractHighWaterMark_disagrees_with_enqueue_on_posInfinity` is finding B2
stated as one theorem: the same value is a legal high water mark and an
illegal size. It is frozen as a conjunction so that a builder who unifies the
two predicates cannot satisfy it under any carrier.

`extractHighWaterMark_id_on_accepted` replaces the normalization-idempotence
law of finding B1. `WS-DATA-CE-009` shows why: a clamping mutant **is**
idempotent, so idempotence does not catch it and the identity law does.

### S8 — the built-in strategies and their profiles (census: `op.cqs-constructor`, `op.cqs-high-water-mark`, `op.cqs-size`, `op.count-queuing-strategy-size-function`, `op.blqs-constructor`, `op.blqs-high-water-mark`, `op.blqs-size`, `op.byte-length-queuing-strategy-size-function`, `slot.high-water-mark`)

```lean
CountQueuingStrategy.make_highWaterMark :
  (CountQueuingStrategy.make highWaterMark : CountQueuingStrategy Size).highWaterMark =
    highWaterMark
CountQueuingStrategy.make_does_not_validate :
  forall highWaterMark : Size,
    (CountQueuingStrategy.make highWaterMark).highWaterMark = highWaterMark
CountQueuingStrategy.make_accepts_nan :
  (CountQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan
CountQueuingStrategy.sizeAlgorithm_eq :
  CountQueuingStrategy.sizeAlgorithm countName = SizeAlgorithm.foreign countName
CountQueuingStrategy.toQueuingStrategy_highWaterMark :
  (CountQueuingStrategy.toQueuingStrategy countName self).highWaterMark =
    some self.highWaterMark
CountQueuingStrategy.toQueuingStrategy_size :
  (CountQueuingStrategy.toQueuingStrategy countName self).size = some countName
CountQueuingStrategy.extract_size_algorithm :
  extractSizeAlgorithm (CountQueuingStrategy.toQueuingStrategy countName self) =
    CountQueuingStrategy.sizeAlgorithm countName
CountQueuingStrategy.size_answers_one :
  CountSizeProfile sizes countName oracle -> forall chunk,
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) chunk =
      SizeAnswer.value sizes.one
CountQueuingStrategy.size_ignores_chunk :
  CountSizeProfile sizes countName oracle -> forall left right,
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) left =
      SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) right
CountQueuingStrategy.size_never_throws :
  CountSizeProfile sizes countName oracle -> forall chunk reason,
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) chunk ≠
      SizeAnswer.thrown reason
CountQueuingStrategy.enqueue_accepts :
  CountSizeProfile sizes countName oracle -> Ordered sizes ->
    SizeAlgorithm.invoke sizes oracle (CountQueuingStrategy.sizeAlgorithm countName) chunk =
      SizeAnswer.value size -> sizes.Admissible size

ByteLengthQueuingStrategy.make_highWaterMark :
  (ByteLengthQueuingStrategy.make highWaterMark : ByteLengthQueuingStrategy Size).highWaterMark =
    highWaterMark
ByteLengthQueuingStrategy.make_accepts_nan :
  (ByteLengthQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan
ByteLengthQueuingStrategy.sizeAlgorithm_eq :
  ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName = SizeAlgorithm.foreign byteLengthName
ByteLengthQueuingStrategy.toQueuingStrategy_highWaterMark :
  (ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).highWaterMark =
    some self.highWaterMark
ByteLengthQueuingStrategy.toQueuingStrategy_size :
  (ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).size = some byteLengthName
byteLengthSize_number : byteLengthSize sizes (ByteLengthAnswer.number n) = SizeAnswer.value n
byteLengthSize_undefined :
  byteLengthSize sizes (ByteLengthAnswer.undefined : ByteLengthAnswer Size ε) =
    SizeAnswer.value sizes.nan
byteLengthSize_thrown :
  byteLengthSize sizes (ByteLengthAnswer.thrown reason) = SizeAnswer.thrown reason
ByteLengthQueuingStrategy.size_eq_byteLength :
  ByteLengthSizeProfile sizes byteLengthName byteLength oracle -> forall chunk,
    SizeAlgorithm.invoke sizes oracle
        (ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk =
      byteLengthSize sizes (byteLength chunk)
ByteLengthQueuingStrategy.undefined_byteLength_refused :
  ByteLengthSizeProfile sizes byteLengthName byteLength oracle ->
    byteLength chunk = ByteLengthAnswer.undefined ->
      SizeAlgorithm.invoke sizes oracle
          (ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk =
        SizeAnswer.value sizes.nan /\
      enqueueValueWithSize sizes q value sizes.nan = .error .rangeError

realm_identity_refused :
  forall (mint : γ -> σ) (left right : γ), left = right -> mint left = mint right
```

`ByteLengthQueuingStrategy.undefined_byteLength_refused` is finding B4 as one
theorem: a chunk with no `byteLength` produces `NaN`, and that `NaN` is
refused by the enqueue that follows. `CountQueuingStrategy.size_never_throws`
and `size_ignores_chunk` are the modelled halves of the pinned WPT observation
that the count size function survives a throwing getter.

`realm_identity_refused` is the theorem-shaped refusal of
`DATA-FB-REALM`, on the pattern of `Scope.key_freshness_refused` in the
lean4-effect4 scope packet: every Lean minting function is a function of its
argument, whereas the pinned WPT observes two realms producing different size
function objects. Realm distinctness is therefore the caller's obligation and
every law that needs it takes the name as an argument.

## 10. Census row to obligation map

The clause-by-clause table, the rows this packet can turn `green`, the rows
that stay short of it, and the reason for each, are in `docs/DATA-DAG.md`
"Census rows this packet targets". They are not duplicated here, because two
copies of a clause map is the ownership error the root router forbids.

This contract proposes coverage states. It does not change any. The coverage
states live in `WhatwgStreamsTest/Audit/SpecCoverage.lean`, whose change lands
with the builder's witnesses under a separate claim, as
`docs/SPEC-COVERAGE.md` requires.

## 11. Counterexample obligations

| ID | Frozen attack | Forced repair |
| --- | --- | --- |
| `WS-DATA-CE-001` | the running total may be kept in a rounding carrier and still equal the sum of the queued sizes | rule `P3-R1`; state every invariant law under `SizeClass.Exact`, so that a rounding instance loses the law instead of falsifying it |
| `WS-DATA-CE-002` | `sizeSum` may fold in either direction | fold left, from `zero`, in the order the enqueue algorithm accumulates |
| `WS-DATA-CE-003` | a negative size may be appended and subtracted later | refuse it, before the append, with a `RangeError` |
| `WS-DATA-CE-004` | `DequeueValue` may answer on an empty queue | `Option`, with `dequeueValue_isNone_iff` pinning the empty case exactly |
| `WS-DATA-CE-005` | `PeekQueueValue` may return a queue beside the value | freeze the result type as `Option α`, so the mutation is not expressible |
| `WS-DATA-CE-006` | `ResetQueue` may keep the running total | write `zero` outright; `resetQueue_wf` holds with no carrier hypothesis |
| `WS-DATA-CE-007` | the refusal laws may be satisfied on a carrier that has no `NaN` | make `nan`, `posInfinity` and `negInfinity` fields of `SizeClass` and classify them in `SizeClass.Classified` |
| `WS-DATA-CE-008` | one predicate may serve both `EnqueueValueWithSize` and `ExtractHighWaterMark` | two predicates; `+∞` is refused as a size and accepted as a high water mark, frozen together in one theorem |
| `WS-DATA-CE-009` | `ExtractHighWaterMark` may normalize, since its anchor id still says so | freeze the identity law on accepted inputs; idempotence does not catch a clamping mutant |
| `WS-DATA-CE-010` | the queue may be a stack | append on enqueue, remove index `0` on dequeue; totals, lengths and multisets do not separate the two |

The ten witnesses are finite self-contained breaker models in
`WhatwgStreamsTest/Counterexamples/Data/Queue.lean`, in a `Breaker` namespace
that shares no name with the frozen surface. They prove the attacks, not the
production laws, and they remain executable after the repair lands.

## 12. Trust and acceptance

The checker is Lean's kernel at the pinned toolchain. `decide` is allowed for
finite propositions. `native_decide`, `sorry`, `admit`, `Classical.choice` and
new axioms are not allowed in the packet or the implementation.

Known traps for this packet:

- `Float` is not usable in any proof here; see finding B5.
- an unguarded `SizeClass.Exact` is satisfied by no carrier that has a `NaN`;
  see D2.
- `decide` over the breaker's rounding model needs a raised `maxRecDepth`
  because the bit-length budget unfolds during elaboration. That is an
  elaborator resource bound, not a trust boundary, and the counterexample
  module records it in a comment.

The breaker phase is accepted when

```sh
lake build WhatwgStreamsTest.Counterexamples.Data.Queue
```

exits zero, while `lake --wfail build` fails on exactly the two declared red
modules, and

```sh
lake exe trustselftest
```

passes, which is the proof that the declaration in
`test/fixtures/trust-gate/known-red.txt` is exact in both directions.

**What a clean red phase looks like here, measured.** Run each red module
directly, as the lean4-effect4 precedent does, because Lake's default error cap
of 100 hides the rest and an in-file `set_option maxErrors` does not reach the
frontend's counter:

```sh
lake env lean -DmaxErrors=10000 WhatwgStreamsTest/Data/QueueContract.lean
lake env lean -DmaxErrors=10000 WhatwgStreamsTest/Data/QueueAxiomReport.lean
```

`QueueAxiomReport` gives 99 diagnostics, every one an unknown constant.
`QueueContract` gives 638: 618 unknown identifiers, and 20 that are strictly
downstream of them — five `declaration uses 'sorry'` warnings on the five
probe definitions of the executable-falsifier section, and fifteen `cannot
evaluate code` errors on the `#guard` probes those definitions feed. That is a
weaker acceptance condition than the effect4 packet's "unknown identifiers
only", and the difference is exactly the executable falsifiers: a `#guard` over
a surface that does not exist cannot fail any other way. There must be **no**
parse error, no import error, no type mismatch, and no failure in the battery's
own helper code. Three defects of those kinds were found and repaired while
this packet was frozen: a doc comment cannot precede `#check`, the ASCII
`forall` has no `x ∈ s` binder form, and a structure literal whose expected
type is an unknown identifier needs an explicit ascription.

The builder phase requires all four files plus the whole project build to exit
zero, with `#print axioms` receipts inside `propext`/`Quot.sound` for every one
of the ninety-nine public theorems, recorded in
`WhatwgStreamsTest/Data/QueueAxiomReport.lean`. It does not authorize any
coverage-number change.

## 13. Open questions and handoffs

**`P3-R1`** — the size carrier. Section 6. Default option (i). This is the one
question that must be answered before the builder starts, because the
instance, not the statements, depends on it.

**`P3-R2`** — one exception carrier, or one per calculus. `RangeError` is
declared here as the only exception this calculus raises. P4 and P5 need
`TypeError` as well, and the piping requirements need a general reason. RS-Q3
in `docs/REIFICATION-STRATEGY.md` asks the same question from the Web IDL side.
Recommendation: leave `RangeError` as it stands and require the P4 packet to
state an embedding theorem rather than widening this one, because widening it
now would freeze a shape before the consumer that needs it exists.

**`P3-R3`** — whether `sizeSum` should be public. It exists so `Queue.WF` has
something to be about and so `WS-DATA-CE-002` has a target. Recommendation:
keep it public. The sum of the queued sizes is the quantity the specification's
own warning is about, and hiding it would make the one invariant this packet
cares about unstatable outside the module.

Handoffs:

1. → **coordinator**: rule `P3-R1`, and review `P3-R2` and `P3-R3`. Findings
   B1 and B2 change what the builder is asked to declare relative to the P3
   dispatch brief, and finding B4 changes the shape of the byte-length size
   boundary; all three are recorded above with their evidence.
2. → **the P3 builder seat**: implement D0 through D8 exactly, each definition
   carrying its census row id in a docstring, and each cited anchor verified
   against the pinned `index.bs` bytes the way section 4 was produced. Do not
   edit this packet, the battery, or the counterexample module. Remove the two
   entries from `test/fixtures/trust-gate/known-red.txt` the moment they go
   green, and not before.
