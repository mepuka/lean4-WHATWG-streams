# Queue-with-sizes attack shapes (area `DATA`)

The attacks this area defends against are readings of the pinned
`queue-with-sizes` and queuing-strategy sections that a careful person could
arrive at, that satisfy most of the laws the packet freezes, and that
contradict either the specification text or the pinned Web Platform Tests.
Nothing here is a claim about a host.

The witnesses are in `WhatwgTest/Streams/Counterexamples/Data/Queue.lean`. Each
is a Lean theorem closed by `decide`, so the evidence is kernel reduction with
no compiler in the trust path. They live in a `Breaker` namespace and share no
name with the frozen surface, so they prove the attacks and not the production
laws, and they stay executable after the repair.

The packet is `test/contracts/queue-with-sizes.contract.md`; the rows are
`WS-DATA-CE-001` through `WS-DATA-CE-010` in `test/counterexamples/REGISTER.md`.

## Why the carrier is the centre of this area

Four of the ten shapes below are about arithmetic rather than about the queue.
That is not an accident of taste. The pinned text says, in its own warning,
that keeping a running total in `[[queueTotalSize]]` "is *not* equivalent to
adding up the size of all chunks in \[[queue]]", and the pinned WPT files
`readable-streams/floating-point-total-queue-size.any.js` and its writable twin
exist to force every implementation to agree on the cases where that matters.
The invariant a reader most wants to state about this data structure is the one
the specification denies. Ruling request `P3-R1` is about which of the two
readings the model takes, and `WS-DATA-CE-001` is what makes the choice
concrete rather than a preference.

## The shapes

### The running total drifts (`WS-DATA-CE-001`)

The obvious invariant of a queue-with-sizes is that `[[queueTotalSize]]` equals
the sum of the sizes of the entries in `[[queue]]`. It is false under the
specification's own carrier.

The pinned case is `readable-streams/floating-point-total-queue-size.any.js`,
test "Floating point arithmetic must manifest near 0 (total ends up positive,
but clamped)", with `highWaterMark: 0` and `size(x) { return x; }`. Enqueue
`1e-16`, enqueue `1`, dequeue `1e-16`. In binary64 the second addend vanishes
into `1.0`, and the later subtraction lands on `0.9999999999999999`, one ulp
below where it started. In exact arithmetic it lands on `1`. The WPT assertion
`assert_equals(controller.desiredSize, 0 - 1e-16 - 1 + 1e-16, …)` demands the
first answer, and the file's header says why: "It is important that
implementations give the same result in these edge cases so that developers do
not come to depend on non-standard behaviour."

The witness works over an exact `Int` grid of `2^(-106)` units with a
round-to-nearest-even function at 53 significant bits, so it reproduces
binary64 on this case without using `Float`. It could not use `Float`:
Lean's `Float` operations are opaque `extern` constants, no equation between
two of them reduces in the kernel, and the only tactic that decides one is
`native_decide`, which this repository forbids by shape.

The divergence is not confined to mask M2. `ce001_desired_size_exact` and
`ce001_desired_size_rounded` show that with a high water mark of `1` the exact
model's `desiredSize` is exactly zero and the rounding model's is strictly
positive, so the underlying source is pulled in one and not the other, and the
chunk sequence a consumer observes can differ. That is mask M1.

The same witness pins the other half of the ruling's cost:
`ce001_clamp_reachable_rounded` shows the next dequeue drives the rounding
carrier's total below zero, which is the only reason `DequeueValue` step 6
exists, and `ce001_clamp_unreachable_exact` shows the exact carrier lands on
zero, so that step's branch is never taken.

### The fold direction is observable (`WS-DATA-CE-002`)

`Queue.WF` compares the running total with a fold over the entries, and the
fold has a direction. Under an exact carrier the two directions agree and the
choice looks cosmetic. Under a rounding carrier they do not: for the three
sizes `[1, 1e-16, 1e-16]` the left fold gives `1` and the right fold gives
`1 + 2^(-52)`.

The left fold, from `zero`, is the order `EnqueueValueWithSize` accumulates in,
so it is the one that makes `enqueueValueWithSize_wf` a one-step argument. A
right fold would make the same theorem false of the same implementation.

### Enqueue accepts a negative size (`WS-DATA-CE-003`)

`EnqueueValueWithSize` refuses a size that fails `IsNonNegativeNumber` before
it appends anything. A model that appends first, or that refuses only `NaN`,
lets the running total go negative while the queue is non-empty — a state no
conforming host reaches, and one that then interacts with the step-6 clamp to
hide itself.

The pinned WPT list is `[NaN, -Infinity, Infinity, -1]`, from "Readable stream:
invalid strategy.size return value" and its writable twin. `-1` is the member
this shape is about; the other three are `WS-DATA-CE-007`.

### Dequeue answers on an empty queue (`WS-DATA-CE-004`)

`DequeueValue` asserts `[[queue]]` is not empty. An assertion is not a runtime
check, so a model is free to return a default instead. The witness proves the
two readings agree on every non-empty queue, so no positive case discriminates
them: only the empty case does, and only if the result type can express
refusal. That is why the frozen result type is `Option (α × Queue α Size)` and
why `dequeueValue_isNone_iff` pins the refusal to exactly the empty queue.

### Peek mutates (`WS-DATA-CE-005`)

`PeekQueueValue` reads `[[queue]][0]` and touches neither slot. A model that
threads the container through it — plausible if it is written beside
`DequeueValue` and shares its shape — returns the same value, so a value-only
comparison never catches it. The witness catches it by comparing the container,
and by peeking twice.

The frozen repair is stronger than a law: `peekQueueValue`'s result type is
`Option α` and it takes no `SizeClass`, so the mutation is not expressible.
A builder who widens the result to a pair fails the ascription rather than a
theorem.

### Reset keeps the running total (`WS-DATA-CE-006`)

`ResetQueue` sets `[[queueTotalSize]]` to `0` outright. An implementation that
has been carrying a drifting total is tempted to preserve it, or to recompute
it from the now-empty queue rather than writing the literal. The first is
caught here. The second is not distinguishable in this model and does not need
to be: an empty fold is `zero`.

Reset is the one operation whose result satisfies the sum invariant whatever
the arithmetic did before it — enqueue only preserves an invariant it was
already given — which is why `resetQueue_wf` needs no carrier hypothesis at all.

### The refusal laws go vacuous (`WS-DATA-CE-007`)

This is the shape that costs the most to discover, because everything looks
green.

`EnqueueValueWithSize` refuses `NaN`, negative sizes and `+∞`. State those
refusals over a carrier that cannot represent `NaN` or `+∞` — `Nat`, or any
exact numeric type without special points — and every one of them is satisfied
by an implementation that refuses nothing at all. `ce007_nan_refusal_is_vacuous`
proves exactly that: on a carrier whose `isNaN` is constantly false, an enqueue
that never returns an error still satisfies the frozen `NaN` refusal law.

The frozen repair is structural rather than a side condition: `nan`,
`posInfinity` and `negInfinity` are **fields** of `SizeClass`, and
`SizeClass.Classified` fixes how each is classified. An instance must therefore
exhibit the three values, and no refusal law can be satisfied for want of a
witness.

### One refusal predicate for both algorithms (`WS-DATA-CE-008`)

`EnqueueValueWithSize` refuses `+∞` as a size. `ExtractHighWaterMark` accepts
`+∞` as a high water mark, and the pinned text says so in a note: "+∞ is
explicitly allowed as a valid high water mark. It causes backpressure to never
be applied." The pinned WPT lists agree in both directions: `Infinity` is in
the list of sizes that must throw, and it is deliberately absent from the list
of high water marks that must throw, which is `[-1, -Infinity, NaN, 'foo',
{}]`.

A model with one shared "is this a usable number" predicate is therefore wrong,
and wrong in a way that is invisible from either algorithm alone. The witness
proves the two rules agree on every other pinned input, so `+∞` is the only
value that separates them, and the packet freezes the disagreement as a single
conjunction so a builder cannot satisfy it by unifying the two.

### `ExtractHighWaterMark` normalizes (`WS-DATA-CE-009`)

The algorithm's anchor id in the pinned bytes is
`validate-and-normalize-high-water-mark`, left over from a revision that had a
normalizing step. At this pin there is none: the algorithm returns its input
unchanged, and there is no `ValidateAndNormalizeHighWaterMark` operation in the
census at all. The stale name invites a model that clamps `+∞`, or coerces, or
otherwise "normalizes".

The instructive part is the law that does **not** catch it. A clamping mutant
is idempotent, because its clamped value is a fixed point, so an
idempotence-of-normalization law passes on the mutant. Only the identity law on
accepted inputs catches it, and that is what the packet freezes.

### The queue is a stack (`WS-DATA-CE-010`)

`EnqueueValueWithSize` appends; `DequeueValue` removes index `0`. A model that
pushes onto the front and pops the front keeps the running total, the length,
and the multiset of entries, so no total-size law, no length law and no
membership law separates it from the right one. Only the order does.

The witness states it as a two-enqueue run whose dequeue answers `1` in the
reference and `2` in the mutant, and separately proves the totals and lengths
agree. `PeekQueueValue` and `DequeueValue` break together, which is why
`peekQueueValue_agrees_dequeueValue` is frozen: the pair is the sharpest single
statement of FIFO available without a multiset argument.
