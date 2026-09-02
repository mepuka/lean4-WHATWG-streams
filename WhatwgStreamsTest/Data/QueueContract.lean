import WhatwgStreams

/-
Contract packet: `test/contracts/queue-with-sizes.contract.md`

Breaker-owned red battery for P3, queue-with-sizes and the queuing
strategies. The implementation phase must not edit this file. It is red until
`WhatwgStreams/Data/Queue.lean` and `WhatwgStreams/Data/Strategy.lean` declare
the frozen surface and `WhatwgStreams.lean` reaches them.

Every public declaration is frozen by an exact `#check (@name : proposition)`
ascription, so no weaker statement satisfies this contract. Names are written
fully qualified and this module deliberately does not `open WhatwgStreams`, so
a locally shadowed spelling cannot silently satisfy an ascription.

The single production import is the library root, not the two fenced modules.
Section 8 of the contract records why: at the base commit the fenced modules
do not exist, and an unresolvable import is a build failure of a different
kind from the unknown-identifier failures a clean red phase is made of. The
module-closure gate in `WhatwgStreamsTest/Audit/AxiomGate.lean` guarantees the
root reaches them once they land.

Pinned specification: `vendor/whatwg-streams-b9ba9f49/index.bs`, cited by
census row id from `generated/spec-algorithm-census.tsv`.
Pinned host corpus: `vendor/wpt-480fdfcd/streams/`.
-/

set_option autoImplicit false

-- During the red phase every ascription in this file reports an unknown
-- identifier, and Lake's default cap of 100 hides the rest. That cap is set
-- from the frontend's initial options, which an in-file set_option does not
-- reach, so the whole diagnostic list is obtained on the command line instead:
--   lake env lean -DmaxErrors=10000 WhatwgStreamsTest/Data/QueueContract.lean
-- Section 12 of the contract packet records what that run must show.

namespace WhatwgStreamsTest.Data.QueueContract

universe u

section RefusalTag

/-! D0: the refusal tag. The `{{RangeError}}` of `op.enqueue-value-with-size`
and `op.validate-and-normalize-high-water-mark`. -/

#check (@WhatwgStreams.Data.RangeError : Type)
#check (@WhatwgStreams.Data.RangeError.rangeError : WhatwgStreams.Data.RangeError)

example : DecidableEq WhatwgStreams.Data.RangeError := inferInstance
example : Repr WhatwgStreams.Data.RangeError := inferInstance

end RefusalTag

section SizeSurface

/-! D1 and D2: the size carrier interface and its three property predicates.

`[[queueTotalSize]]` is "a JavaScript Number, i.e. a double-precision floating
point number" (`slot.queue-total-size`). Which Lean carrier stands for that is
ruling request `P3-R1`; this surface is written so the ruling changes an
instance and no statement. The three special constants are fields rather than
derived predicates so that no instance can satisfy a refusal law for want of a
witness. -/

#check (@WhatwgStreams.Data.SizeClass : Type u -> Type u)
#check (@WhatwgStreams.Data.SizeClass.zero :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.one :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.nan :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.posInfinity :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.negInfinity :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.add :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.sub :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Size -> Size)
#check (@WhatwgStreams.Data.SizeClass.isNaN :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Bool)
#check (@WhatwgStreams.Data.SizeClass.isNegative :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Bool)
#check (@WhatwgStreams.Data.SizeClass.isInfinite :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Bool)

#check (@WhatwgStreams.Data.SizeClass.Admissible :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Prop)
#check (@WhatwgStreams.Data.SizeClass.isNonNegativeNumber :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Bool)
#check (@WhatwgStreams.Data.SizeClass.isPositiveInfinity :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Bool)
#check (@WhatwgStreams.Data.SizeClass.clampNonNegative :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Size -> Size)

#check (@WhatwgStreams.Data.SizeClass.Classified :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Prop)
#check (@WhatwgStreams.Data.SizeClass.Ordered :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Prop)
#check (@WhatwgStreams.Data.SizeClass.Exact :
  forall {Size : Type u}, WhatwgStreams.Data.SizeClass Size -> Prop)

/-! The `Exact` equations are guarded by `Admissible`. Unguarded they are false
of every carrier that has a `NaN`, so a builder who drops a guard freezes a
predicate no instance satisfies. -/
#check (@WhatwgStreams.Data.SizeClass.Exact.sub_add_cancel :
  forall {Size : Type u} {sizes : WhatwgStreams.Data.SizeClass Size},
    sizes.Exact -> forall a b : Size, sizes.Admissible a -> sizes.Admissible b ->
      sizes.sub (sizes.add a b) b = a)
#check (@WhatwgStreams.Data.SizeClass.Exact.add_assoc :
  forall {Size : Type u} {sizes : WhatwgStreams.Data.SizeClass Size},
    sizes.Exact -> forall a b c : Size,
      sizes.Admissible a -> sizes.Admissible b -> sizes.Admissible c ->
        sizes.add (sizes.add a b) c = sizes.add a (sizes.add b c))
#check (@WhatwgStreams.Data.SizeClass.Exact.add_comm :
  forall {Size : Type u} {sizes : WhatwgStreams.Data.SizeClass Size},
    sizes.Exact -> forall a b : Size, sizes.Admissible a -> sizes.Admissible b ->
      sizes.add a b = sizes.add b a)
#check (@WhatwgStreams.Data.SizeClass.Exact.zero_add :
  forall {Size : Type u} {sizes : WhatwgStreams.Data.SizeClass Size},
    sizes.Exact -> forall a : Size, sizes.Admissible a -> sizes.add sizes.zero a = a)
#check (@WhatwgStreams.Data.SizeClass.Ordered.add_admissible :
  forall {Size : Type u} {sizes : WhatwgStreams.Data.SizeClass Size},
    sizes.Ordered -> forall a b : Size, sizes.Admissible a -> sizes.Admissible b ->
      sizes.Admissible (sizes.add a b))
#check (@WhatwgStreams.Data.SizeClass.Classified.nan_isolated :
  forall {Size : Type u} {sizes : WhatwgStreams.Data.SizeClass Size},
    sizes.Classified -> forall v : Size, sizes.isNaN v = true ->
      sizes.isNegative v = false /\ sizes.isInfinite v = false)

end SizeSurface

section QueueSurface

/-! D3: the queue-with-sizes carrier (census: `slot.queue`,
`slot.queue-total-size`).

A `value-with-size` is "a struct with the two items value and size", and the
two paired slots are "always named \[[queue]] and \[[queueTotalSize]]". -/

#check (@WhatwgStreams.Data.QueueEntry : Type u -> Type u -> Type u)
#check (@WhatwgStreams.Data.QueueEntry.mk :
  forall {α Size : Type u}, α -> Size -> WhatwgStreams.Data.QueueEntry α Size)
#check (@WhatwgStreams.Data.QueueEntry.value :
  forall {α Size : Type u}, WhatwgStreams.Data.QueueEntry α Size -> α)
#check (@WhatwgStreams.Data.QueueEntry.size :
  forall {α Size : Type u}, WhatwgStreams.Data.QueueEntry α Size -> Size)

#check (@WhatwgStreams.Data.Queue : Type u -> Type u -> Type u)
#check (@WhatwgStreams.Data.Queue.mk :
  forall {α Size : Type u},
    List (WhatwgStreams.Data.QueueEntry α Size) -> Size -> WhatwgStreams.Data.Queue α Size)
#check (@WhatwgStreams.Data.Queue.entries :
  forall {α Size : Type u},
    WhatwgStreams.Data.Queue α Size -> List (WhatwgStreams.Data.QueueEntry α Size))
#check (@WhatwgStreams.Data.Queue.totalSize :
  forall {α Size : Type u}, WhatwgStreams.Data.Queue α Size -> Size)

example {α Size : Type u} [DecidableEq α] [DecidableEq Size] :
    DecidableEq (WhatwgStreams.Data.QueueEntry α Size) := inferInstance
example {α Size : Type u} [DecidableEq α] [DecidableEq Size] :
    DecidableEq (WhatwgStreams.Data.Queue α Size) := inferInstance

#check (@WhatwgStreams.Data.Queue.empty :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.Queue α Size)
#check (@WhatwgStreams.Data.sizeSum :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    List (WhatwgStreams.Data.QueueEntry α Size) -> Size)
#check (@WhatwgStreams.Data.Queue.WF :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.Queue α Size -> Prop)
#check (@WhatwgStreams.Data.Queue.SizesAdmissible :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.Queue α Size -> Prop)

/-! `Queue.WF` is a separate decidable `Prop`, not a field invariant. The
pinned text says the running total "is *not* equivalent to adding up the size
of all chunks in \[[queue]]", so a structure that made the invariant
unconstructible-otherwise could not represent the specification's own
reachable states. -/
example {α Size : Type u} [DecidableEq Size]
    (sizes : WhatwgStreams.Data.SizeClass Size) (q : WhatwgStreams.Data.Queue α Size) :
    Decidable (WhatwgStreams.Data.Queue.WF sizes q) := inferInstance

end QueueSurface

section OperationSurface

/-! D4 through D8: the four queue-with-sizes operations, the size algebra, the
strategy dictionary and the two built-in classes. -/

#check (@WhatwgStreams.Data.enqueueValueWithSize :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.Queue α Size -> α -> Size ->
      Except WhatwgStreams.Data.RangeError (WhatwgStreams.Data.Queue α Size))
#check (@WhatwgStreams.Data.dequeueValue :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.Queue α Size -> Option (α × WhatwgStreams.Data.Queue α Size))
#check (@WhatwgStreams.Data.peekQueueValue :
  forall {α Size : Type u}, WhatwgStreams.Data.Queue α Size -> Option α)
#check (@WhatwgStreams.Data.resetQueue :
  forall {α Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.Queue α Size -> WhatwgStreams.Data.Queue α Size)

#check (@WhatwgStreams.Data.SizeAlgorithm : Type u -> Type u)
#check (@WhatwgStreams.Data.SizeAlgorithm.one :
  forall {σ : Type u}, WhatwgStreams.Data.SizeAlgorithm σ)
#check (@WhatwgStreams.Data.SizeAlgorithm.foreign :
  forall {σ : Type u}, σ -> WhatwgStreams.Data.SizeAlgorithm σ)
#check (@WhatwgStreams.Data.SizeAnswer : Type u -> Type u -> Type u)
#check (@WhatwgStreams.Data.SizeAnswer.value :
  forall {Size ε : Type u}, Size -> WhatwgStreams.Data.SizeAnswer Size ε)
#check (@WhatwgStreams.Data.SizeAnswer.thrown :
  forall {Size ε : Type u}, ε -> WhatwgStreams.Data.SizeAnswer Size ε)
#check (@WhatwgStreams.Data.ByteLengthAnswer : Type u -> Type u -> Type u)
#check (@WhatwgStreams.Data.ByteLengthAnswer.number :
  forall {Size ε : Type u}, Size -> WhatwgStreams.Data.ByteLengthAnswer Size ε)
#check (@WhatwgStreams.Data.ByteLengthAnswer.undefined :
  forall {Size ε : Type u}, WhatwgStreams.Data.ByteLengthAnswer Size ε)
#check (@WhatwgStreams.Data.ByteLengthAnswer.thrown :
  forall {Size ε : Type u}, ε -> WhatwgStreams.Data.ByteLengthAnswer Size ε)

#check (@WhatwgStreams.Data.SizeAlgorithm.invoke :
  forall {α σ ε Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    (σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) ->
      WhatwgStreams.Data.SizeAlgorithm σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε)
#check (@WhatwgStreams.Data.byteLengthSize :
  forall {ε Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.ByteLengthAnswer Size ε -> WhatwgStreams.Data.SizeAnswer Size ε)

#check (@WhatwgStreams.Data.QueuingStrategy : Type u -> Type u -> Type u)
#check (@WhatwgStreams.Data.QueuingStrategy.mk :
  forall {σ Size : Type u}, Option Size -> Option σ ->
    WhatwgStreams.Data.QueuingStrategy σ Size)
#check (@WhatwgStreams.Data.QueuingStrategy.highWaterMark :
  forall {σ Size : Type u}, WhatwgStreams.Data.QueuingStrategy σ Size -> Option Size)
#check (@WhatwgStreams.Data.QueuingStrategy.size :
  forall {σ Size : Type u}, WhatwgStreams.Data.QueuingStrategy σ Size -> Option σ)

#check (@WhatwgStreams.Data.extractHighWaterMark :
  forall {σ Size : Type u}, WhatwgStreams.Data.SizeClass Size ->
    WhatwgStreams.Data.QueuingStrategy σ Size -> Size ->
      Except WhatwgStreams.Data.RangeError Size)
#check (@WhatwgStreams.Data.extractSizeAlgorithm :
  forall {σ Size : Type u}, WhatwgStreams.Data.QueuingStrategy σ Size ->
    WhatwgStreams.Data.SizeAlgorithm σ)

#check (@WhatwgStreams.Data.CountQueuingStrategy : Type u -> Type u)
#check (@WhatwgStreams.Data.CountQueuingStrategy.highWaterMark :
  forall {Size : Type u}, WhatwgStreams.Data.CountQueuingStrategy Size -> Size)
#check (@WhatwgStreams.Data.CountQueuingStrategy.make :
  forall {Size : Type u}, Size -> WhatwgStreams.Data.CountQueuingStrategy Size)
#check (@WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm :
  forall {σ : Type u}, σ -> WhatwgStreams.Data.SizeAlgorithm σ)
#check (@WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy :
  forall {σ Size : Type u}, σ -> WhatwgStreams.Data.CountQueuingStrategy Size ->
    WhatwgStreams.Data.QueuingStrategy σ Size)

#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy : Type u -> Type u)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.highWaterMark :
  forall {Size : Type u}, WhatwgStreams.Data.ByteLengthQueuingStrategy Size -> Size)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.make :
  forall {Size : Type u}, Size -> WhatwgStreams.Data.ByteLengthQueuingStrategy Size)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.sizeAlgorithm :
  forall {σ : Type u}, σ -> WhatwgStreams.Data.SizeAlgorithm σ)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy :
  forall {σ Size : Type u}, σ -> WhatwgStreams.Data.ByteLengthQueuingStrategy Size ->
    WhatwgStreams.Data.QueuingStrategy σ Size)

#check (@WhatwgStreams.Data.CountSizeProfile :
  forall {α σ ε Size : Type u}, WhatwgStreams.Data.SizeClass Size -> σ ->
    (σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) -> Prop)
#check (@WhatwgStreams.Data.ByteLengthSizeProfile :
  forall {α σ ε Size : Type u}, WhatwgStreams.Data.SizeClass Size -> σ ->
    (α -> WhatwgStreams.Data.ByteLengthAnswer Size ε) ->
      (σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) -> Prop)

end OperationSurface

section S1_Classification

/-! S1: classification and admission (census: `op.is-non-negative-number`).

"If |v| is not a Number, return false. If |v| is NaN, return false. If |v| < 0,
return false. Return true." The "is not a Number" step is a Web IDL boundary
and is `hostOnly`; the carrier's values are already Numbers. -/

#check (@WhatwgStreams.Data.SizeClass.isNonNegativeNumber_eq :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (v : Size),
    sizes.isNonNegativeNumber v = (!sizes.isNaN v && !sizes.isNegative v))
#check (@WhatwgStreams.Data.SizeClass.isPositiveInfinity_eq :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (v : Size),
    sizes.isPositiveInfinity v = (sizes.isInfinite v && !sizes.isNegative v))
#check (@WhatwgStreams.Data.SizeClass.admissible_iff :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (v : Size),
    sizes.Admissible v <->
      (sizes.isNaN v = false /\ sizes.isNegative v = false /\ sizes.isInfinite v = false))
#check (@WhatwgStreams.Data.SizeClass.not_admissible_nan :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Classified -> ¬ sizes.Admissible sizes.nan)
#check (@WhatwgStreams.Data.SizeClass.not_admissible_posInfinity :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Classified -> ¬ sizes.Admissible sizes.posInfinity)
#check (@WhatwgStreams.Data.SizeClass.not_admissible_negInfinity :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Classified -> ¬ sizes.Admissible sizes.negInfinity)
#check (@WhatwgStreams.Data.SizeClass.isNonNegativeNumber_nan :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Classified -> sizes.isNonNegativeNumber sizes.nan = false)
#check (@WhatwgStreams.Data.SizeClass.isNonNegativeNumber_negInfinity :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Classified -> sizes.isNonNegativeNumber sizes.negInfinity = false)

/-! The theorem that pins the two-step structure of `EnqueueValueWithSize`:
`+∞` passes `IsNonNegativeNumber` and is refused only by the second step. A
one-step model satisfies every other law in this battery. -/
#check (@WhatwgStreams.Data.SizeClass.isNonNegativeNumber_posInfinity :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Classified -> sizes.isNonNegativeNumber sizes.posInfinity = true)

#check (@WhatwgStreams.Data.SizeClass.clampNonNegative_of_negative :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (v : Size),
    sizes.isNegative v = true -> sizes.clampNonNegative v = sizes.zero)
#check (@WhatwgStreams.Data.SizeClass.clampNonNegative_of_nonneg :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (v : Size),
    sizes.isNegative v = false -> sizes.clampNonNegative v = v)
#check (@WhatwgStreams.Data.SizeClass.clampNonNegative_not_negative :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    sizes.Ordered -> forall v : Size, sizes.isNegative (sizes.clampNonNegative v) = false)

end S1_Classification

section S2_Sum

/-! S2: the queue carrier and the sum (census: `slot.queue`,
`slot.queue-total-size`). -/

#check (@WhatwgStreams.Data.Queue.empty_entries :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    (WhatwgStreams.Data.Queue.empty sizes : WhatwgStreams.Data.Queue α Size).entries = [])
#check (@WhatwgStreams.Data.Queue.empty_totalSize :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    (WhatwgStreams.Data.Queue.empty sizes : WhatwgStreams.Data.Queue α Size).totalSize =
      sizes.zero)
#check (@WhatwgStreams.Data.sizeSum_nil :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    WhatwgStreams.Data.sizeSum sizes ([] : List (WhatwgStreams.Data.QueueEntry α Size)) =
      sizes.zero)

/-! `sizeSum` folds left, from `zero`, in the order `EnqueueValueWithSize`
accumulates. `WS-DATA-CE-002` exhibits a carrier on which the two fold
directions differ, so the direction is not cosmetic. -/
#check (@WhatwgStreams.Data.sizeSum_append_singleton :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (entries : List (WhatwgStreams.Data.QueueEntry α Size))
    (entry : WhatwgStreams.Data.QueueEntry α Size),
      WhatwgStreams.Data.sizeSum sizes (entries ++ [entry]) =
        sizes.add (WhatwgStreams.Data.sizeSum sizes entries) entry.size)
#check (@WhatwgStreams.Data.sizeSum_cons :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (entry : WhatwgStreams.Data.QueueEntry α Size)
    (entries : List (WhatwgStreams.Data.QueueEntry α Size)),
      sizes.Exact -> sizes.Ordered -> sizes.Admissible entry.size ->
        (forall e, e ∈ entries -> sizes.Admissible e.size) ->
          WhatwgStreams.Data.sizeSum sizes (entry :: entries) =
            sizes.add entry.size (WhatwgStreams.Data.sizeSum sizes entries))
#check (@WhatwgStreams.Data.sizeSum_admissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (entries : List (WhatwgStreams.Data.QueueEntry α Size)),
      sizes.Ordered -> (forall e, e ∈ entries -> sizes.Admissible e.size) ->
        sizes.Admissible (WhatwgStreams.Data.sizeSum sizes entries))
#check (@WhatwgStreams.Data.Queue.WF_iff :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.Queue.WF sizes q <->
        q.totalSize = WhatwgStreams.Data.sizeSum sizes q.entries)
#check (@WhatwgStreams.Data.Queue.WF_empty :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    WhatwgStreams.Data.Queue.WF sizes
      (WhatwgStreams.Data.Queue.empty sizes : WhatwgStreams.Data.Queue α Size))
#check (@WhatwgStreams.Data.Queue.SizesAdmissible_iff :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.Queue.SizesAdmissible sizes q <->
        forall entry, entry ∈ q.entries -> sizes.Admissible entry.size)
#check (@WhatwgStreams.Data.Queue.SizesAdmissible_empty :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    WhatwgStreams.Data.Queue.SizesAdmissible sizes
      (WhatwgStreams.Data.Queue.empty sizes : WhatwgStreams.Data.Queue α Size))

end S2_Sum

section S3_Enqueue

/-! S3: enqueue (census: `op.enqueue-value-with-size`).

"If ! IsNonNegativeNumber(|size|) is false, throw a RangeError exception. If
|size| is +∞, throw a RangeError exception. Append a new value-with-size ... Set
|container|.\[[queueTotalSize]] to |container|.\[[queueTotalSize]] + |size|." -/

#check (@WhatwgStreams.Data.enqueueValueWithSize_error_iff :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.enqueueValueWithSize sizes q value size =
          Except.error WhatwgStreams.Data.RangeError.rangeError <->
        (sizes.isNonNegativeNumber size = false \/ sizes.isPositiveInfinity size = true))
#check (@WhatwgStreams.Data.enqueueValueWithSize_error_iff_not_admissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.enqueueValueWithSize sizes q value size =
          Except.error WhatwgStreams.Data.RangeError.rangeError <->
        ¬ sizes.Admissible size)
#check (@WhatwgStreams.Data.enqueueValueWithSize_refuses_nan :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α),
      sizes.Classified ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value sizes.nan =
          Except.error WhatwgStreams.Data.RangeError.rangeError)
#check (@WhatwgStreams.Data.enqueueValueWithSize_refuses_negative :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      sizes.isNegative size = true ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size =
          Except.error WhatwgStreams.Data.RangeError.rangeError)
#check (@WhatwgStreams.Data.enqueueValueWithSize_refuses_posInfinity :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α),
      sizes.Classified ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value sizes.posInfinity =
          Except.error WhatwgStreams.Data.RangeError.rangeError)
#check (@WhatwgStreams.Data.enqueueValueWithSize_refuses_negInfinity :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α),
      sizes.Classified ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value sizes.negInfinity =
          Except.error WhatwgStreams.Data.RangeError.rangeError)
#check (@WhatwgStreams.Data.enqueueValueWithSize_ok_iff :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      (exists q', WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q') <->
        sizes.Admissible size)
#check (@WhatwgStreams.Data.enqueueValueWithSize_eq_of_admissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      sizes.Admissible size ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size =
          Except.ok ({ entries := q.entries ++ [{ value := value, size := size }],
                       totalSize := sizes.add q.totalSize size } :
            WhatwgStreams.Data.Queue α Size))

/-! The append. `WS-DATA-CE-010` attacks a model that prepends; it keeps the
total, the length and the multiset of entries, and is caught by nothing else
here. -/
#check (@WhatwgStreams.Data.enqueueValueWithSize_entries :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
        q'.entries = q.entries ++
          [({ value := value, size := size } : WhatwgStreams.Data.QueueEntry α Size)])
#check (@WhatwgStreams.Data.enqueueValueWithSize_totalSize :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
        q'.totalSize = sizes.add q.totalSize size)
#check (@WhatwgStreams.Data.enqueueValueWithSize_length :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
        q'.entries.length = q.entries.length + 1)
#check (@WhatwgStreams.Data.enqueueValueWithSize_sizesAdmissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.Queue.SizesAdmissible sizes q ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          WhatwgStreams.Data.Queue.SizesAdmissible sizes q')
#check (@WhatwgStreams.Data.enqueueValueWithSize_totalSize_admissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      sizes.Ordered -> sizes.Admissible q.totalSize ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          sizes.Admissible q'.totalSize)

/-! Enqueue never drifts: the running total and the fold take the same step,
by `sizeSum_append_singleton`. Dequeue does drift, which is `P3-R1`. -/
#check (@WhatwgStreams.Data.enqueueValueWithSize_wf :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      WhatwgStreams.Data.Queue.WF sizes q ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          WhatwgStreams.Data.Queue.WF sizes q')

end S3_Enqueue

section S4_Dequeue

/-! S4: dequeue (census: `op.dequeue-value`).

"Assert: |container|.\[[queue]] is not empty. Let |valueWithSize| be
|container|.\[[queue]][0]. Remove |valueWithSize| ... Set
|container|.\[[queueTotalSize]] to |container|.\[[queueTotalSize]] −
|valueWithSize|'s size. If |container|.\[[queueTotalSize]] < 0, set
|container|.\[[queueTotalSize]] to 0. (This can occur due to rounding errors.)" -/

#check (@WhatwgStreams.Data.dequeueValue_nil :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (total : Size),
    WhatwgStreams.Data.dequeueValue sizes
        ({ entries := [], totalSize := total } : WhatwgStreams.Data.Queue α Size) = none)
#check (@WhatwgStreams.Data.dequeueValue_cons :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (total : Size)
    (entry : WhatwgStreams.Data.QueueEntry α Size)
    (rest : List (WhatwgStreams.Data.QueueEntry α Size)),
      WhatwgStreams.Data.dequeueValue sizes
          ({ entries := entry :: rest, totalSize := total } : WhatwgStreams.Data.Queue α Size) =
        some (entry.value,
          ({ entries := rest,
             totalSize := sizes.clampNonNegative (sizes.sub total entry.size) } :
            WhatwgStreams.Data.Queue α Size)))
#check (@WhatwgStreams.Data.dequeueValue_isSome_iff :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      (WhatwgStreams.Data.dequeueValue sizes q).isSome = true <-> q.entries ≠ [])
#check (@WhatwgStreams.Data.dequeueValue_isNone_iff :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.dequeueValue sizes q = none <-> q.entries = [])
#check (@WhatwgStreams.Data.dequeueValue_value_eq_head :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      (WhatwgStreams.Data.dequeueValue sizes q).map Prod.fst =
        q.entries.head?.map WhatwgStreams.Data.QueueEntry.value)
#check (@WhatwgStreams.Data.dequeueValue_entries :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α),
      WhatwgStreams.Data.dequeueValue sizes q = some (value, q') ->
        q'.entries = q.entries.tail)
#check (@WhatwgStreams.Data.dequeueValue_length :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α),
      WhatwgStreams.Data.dequeueValue sizes q = some (value, q') ->
        q.entries.length = q'.entries.length + 1)
#check (@WhatwgStreams.Data.dequeueValue_totalSize :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α)
    (entry : WhatwgStreams.Data.QueueEntry α Size)
    (rest : List (WhatwgStreams.Data.QueueEntry α Size)),
      q.entries = entry :: rest ->
        WhatwgStreams.Data.dequeueValue sizes q = some (value, q') ->
          q'.totalSize = sizes.clampNonNegative (sizes.sub q.totalSize entry.size))
#check (@WhatwgStreams.Data.dequeueValue_totalSize_not_negative :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α),
      sizes.Ordered -> WhatwgStreams.Data.dequeueValue sizes q = some (value, q') ->
        sizes.isNegative q'.totalSize = false)
#check (@WhatwgStreams.Data.dequeueValue_sizesAdmissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α),
      WhatwgStreams.Data.Queue.SizesAdmissible sizes q ->
        WhatwgStreams.Data.dequeueValue sizes q = some (value, q') ->
          WhatwgStreams.Data.Queue.SizesAdmissible sizes q')

/-! Preservation of the running-total invariant by dequeue is exactly what a
rounding carrier destroys. `WS-DATA-CE-001` is the pre-registered witness, and
the `Exact` hypothesis is where ruling `P3-R1` lands. -/
#check (@WhatwgStreams.Data.dequeueValue_wf :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α),
      sizes.Classified -> sizes.Ordered -> sizes.Exact ->
        WhatwgStreams.Data.Queue.WF sizes q ->
          WhatwgStreams.Data.Queue.SizesAdmissible sizes q ->
            WhatwgStreams.Data.dequeueValue sizes q = some (value, q') ->
              WhatwgStreams.Data.Queue.WF sizes q')

/-! Under an exact carrier the clamp of step 6 is never taken. The step is
witnessed as vacuous rather than as a branch, which is the cost of ruling
`P3-R1` in favour of option (i), stated as a theorem in the tree. -/
#check (@WhatwgStreams.Data.dequeueValue_clamp_unreachable_of_exact :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size)
    (entry : WhatwgStreams.Data.QueueEntry α Size)
    (rest : List (WhatwgStreams.Data.QueueEntry α Size)),
      sizes.Classified -> sizes.Ordered -> sizes.Exact ->
        WhatwgStreams.Data.Queue.WF sizes q ->
          WhatwgStreams.Data.Queue.SizesAdmissible sizes q ->
            q.entries = entry :: rest ->
              sizes.isNegative (sizes.sub q.totalSize entry.size) = false)

end S4_Dequeue

section S5_Fifo

/-! S5: FIFO and peek (census: `op.peek-queue-value`, `op.dequeue-value`).

`PeekQueueValue` takes no `SizeClass` and returns no queue. Both absences are
the packet's statement that it touches neither slot: the mutation
`WS-DATA-CE-005` attacks is not expressible in this result type. -/

#check (@WhatwgStreams.Data.peekQueueValue_nil :
  forall {α Size : Type u} (total : Size),
    WhatwgStreams.Data.peekQueueValue
      ({ entries := [], totalSize := total } : WhatwgStreams.Data.Queue α Size) = none)
#check (@WhatwgStreams.Data.peekQueueValue_cons :
  forall {α Size : Type u} (total : Size) (entry : WhatwgStreams.Data.QueueEntry α Size)
    (rest : List (WhatwgStreams.Data.QueueEntry α Size)),
      WhatwgStreams.Data.peekQueueValue
          ({ entries := entry :: rest, totalSize := total } : WhatwgStreams.Data.Queue α Size) =
        some entry.value)
#check (@WhatwgStreams.Data.peekQueueValue_eq_head :
  forall {α Size : Type u} (q : WhatwgStreams.Data.Queue α Size),
    WhatwgStreams.Data.peekQueueValue q =
      q.entries.head?.map WhatwgStreams.Data.QueueEntry.value)
#check (@WhatwgStreams.Data.peekQueueValue_agrees_dequeueValue :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.peekQueueValue q =
        (WhatwgStreams.Data.dequeueValue sizes q).map Prod.fst)
#check (@WhatwgStreams.Data.peekQueueValue_isSome_iff :
  forall {α Size : Type u} (q : WhatwgStreams.Data.Queue α Size),
    (WhatwgStreams.Data.peekQueueValue q).isSome = true <-> q.entries ≠ [])
#check (@WhatwgStreams.Data.dequeueValue_enqueueValueWithSize_empty :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size),
      q.entries = [] ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          (WhatwgStreams.Data.dequeueValue sizes q').map Prod.fst = some value)

/-! The sharp FIFO statement: an enqueue onto a non-empty queue does not change
what the next dequeue answers. -/
#check (@WhatwgStreams.Data.dequeueValue_enqueueValueWithSize_nonempty :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size)
    (entry : WhatwgStreams.Data.QueueEntry α Size)
    (rest : List (WhatwgStreams.Data.QueueEntry α Size)),
      q.entries = entry :: rest ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          (WhatwgStreams.Data.dequeueValue sizes q').map Prod.fst = some entry.value)
#check (@WhatwgStreams.Data.peekQueueValue_enqueueValueWithSize_nonempty :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q q' : WhatwgStreams.Data.Queue α Size) (value : α) (size : Size)
    (entry : WhatwgStreams.Data.QueueEntry α Size)
    (rest : List (WhatwgStreams.Data.QueueEntry α Size)),
      q.entries = entry :: rest ->
        WhatwgStreams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          WhatwgStreams.Data.peekQueueValue q' = some entry.value)

end S5_Fifo

section S6_Reset

/-! S6: reset (census: `op.reset-queue`).

"Set |container|.\[[queue]] to a new empty list. Set
|container|.\[[queueTotalSize]] to 0." Unconditionally, with no arithmetic, so
`resetQueue_wf` carries no carrier hypothesis. -/

#check (@WhatwgStreams.Data.resetQueue_eq :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.resetQueue sizes q =
        ({ entries := [], totalSize := sizes.zero } : WhatwgStreams.Data.Queue α Size))
#check (@WhatwgStreams.Data.resetQueue_entries :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      (WhatwgStreams.Data.resetQueue sizes q).entries = [])
#check (@WhatwgStreams.Data.resetQueue_totalSize :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      (WhatwgStreams.Data.resetQueue sizes q).totalSize = sizes.zero)
#check (@WhatwgStreams.Data.resetQueue_wf :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.Queue.WF sizes (WhatwgStreams.Data.resetQueue sizes q))
#check (@WhatwgStreams.Data.resetQueue_sizesAdmissible :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.Queue.SizesAdmissible sizes (WhatwgStreams.Data.resetQueue sizes q))
#check (@WhatwgStreams.Data.resetQueue_idempotent :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.resetQueue sizes (WhatwgStreams.Data.resetQueue sizes q) =
        WhatwgStreams.Data.resetQueue sizes q)
#check (@WhatwgStreams.Data.resetQueue_eq_empty :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.resetQueue sizes q = WhatwgStreams.Data.Queue.empty sizes)
#check (@WhatwgStreams.Data.resetQueue_dequeueValue :
  forall {α Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (q : WhatwgStreams.Data.Queue α Size),
      WhatwgStreams.Data.dequeueValue sizes (WhatwgStreams.Data.resetQueue sizes q) = none)

end S6_Reset

section S7_Extraction

/-! S7: the extraction algorithms (census:
`op.validate-and-normalize-high-water-mark`,
`op.make-size-algorithm-from-size-function`).

"If |strategy|["highWaterMark"] does not exist, return |defaultHWM|. Let
|highWaterMark| be |strategy|["highWaterMark"]. If |highWaterMark| is NaN or
|highWaterMark| < 0, throw a RangeError exception. Return |highWaterMark|." The
note beside it: "+∞ is explicitly allowed as a valid high water mark." -/

#check (@WhatwgStreams.Data.extractHighWaterMark_absent :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      strategy.highWaterMark = none ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.ok defaultHWM)
#check (@WhatwgStreams.Data.extractHighWaterMark_error_iff :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error WhatwgStreams.Data.RangeError.rangeError <->
        (exists highWaterMark, strategy.highWaterMark = some highWaterMark /\
          (sizes.isNaN highWaterMark = true \/ sizes.isNegative highWaterMark = true)))
#check (@WhatwgStreams.Data.extractHighWaterMark_refuses_nan :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      sizes.Classified -> strategy.highWaterMark = some sizes.nan ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error WhatwgStreams.Data.RangeError.rangeError)
#check (@WhatwgStreams.Data.extractHighWaterMark_refuses_negative :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM highWaterMark : Size),
      strategy.highWaterMark = some highWaterMark -> sizes.isNegative highWaterMark = true ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error WhatwgStreams.Data.RangeError.rangeError)
#check (@WhatwgStreams.Data.extractHighWaterMark_refuses_negInfinity :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      sizes.Classified -> strategy.highWaterMark = some sizes.negInfinity ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error WhatwgStreams.Data.RangeError.rangeError)

/-! "+∞ is explicitly allowed as a valid high water mark." The pinned WPT list
of high water marks that must throw is `[-1, -Infinity, NaN, 'foo', {}]`, and
`Infinity` is deliberately absent from it. -/
#check (@WhatwgStreams.Data.extractHighWaterMark_allows_posInfinity :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      sizes.Classified -> strategy.highWaterMark = some sizes.posInfinity ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.ok sizes.posInfinity)

/-! The algorithm at this pin normalizes nothing, despite the anchor id
`validate-and-normalize-high-water-mark`. `WS-DATA-CE-009` shows why the
identity law is frozen and an idempotence law is not: a clamping mutant is
idempotent too. -/
#check (@WhatwgStreams.Data.extractHighWaterMark_id_on_accepted :
  forall {σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size)
    (defaultHWM highWaterMark highWaterMark' : Size),
      strategy.highWaterMark = some highWaterMark ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
            Except.ok highWaterMark' ->
          highWaterMark' = highWaterMark)

/-! The two refusal sets differ on exactly one value. Frozen as a conjunction
so that a builder who shares one predicate between the two algorithms cannot
satisfy it under any carrier. `WS-DATA-CE-008` is the attack. -/
#check (@WhatwgStreams.Data.extractHighWaterMark_disagrees_with_enqueue_on_posInfinity :
  forall {α σ Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (defaultHWM : Size)
    (q : WhatwgStreams.Data.Queue α Size) (value : α),
      sizes.Classified -> strategy.highWaterMark = some sizes.posInfinity ->
        WhatwgStreams.Data.extractHighWaterMark sizes strategy defaultHWM =
            Except.ok sizes.posInfinity /\
          WhatwgStreams.Data.enqueueValueWithSize sizes q value sizes.posInfinity =
            Except.error WhatwgStreams.Data.RangeError.rangeError)

#check (@WhatwgStreams.Data.extractSizeAlgorithm_absent :
  forall {σ Size : Type u} (strategy : WhatwgStreams.Data.QueuingStrategy σ Size),
    strategy.size = none ->
      WhatwgStreams.Data.extractSizeAlgorithm strategy = WhatwgStreams.Data.SizeAlgorithm.one)
#check (@WhatwgStreams.Data.extractSizeAlgorithm_present :
  forall {σ Size : Type u} (strategy : WhatwgStreams.Data.QueuingStrategy σ Size) (name : σ),
    strategy.size = some name ->
      WhatwgStreams.Data.extractSizeAlgorithm strategy =
        WhatwgStreams.Data.SizeAlgorithm.foreign name)
#check (@WhatwgStreams.Data.SizeAlgorithm.invoke_one :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) (chunk : α),
      WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
          WhatwgStreams.Data.SizeAlgorithm.one chunk =
        WhatwgStreams.Data.SizeAnswer.value sizes.one)
#check (@WhatwgStreams.Data.SizeAlgorithm.invoke_foreign :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) (name : σ) (chunk : α),
      WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
          (WhatwgStreams.Data.SizeAlgorithm.foreign name) chunk =
        oracle name chunk)
#check (@WhatwgStreams.Data.extractSizeAlgorithm_absent_invoke :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size)
    (strategy : WhatwgStreams.Data.QueuingStrategy σ Size)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) (chunk : α),
      strategy.size = none ->
        WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
            (WhatwgStreams.Data.extractSizeAlgorithm strategy) chunk =
          WhatwgStreams.Data.SizeAnswer.value sizes.one)

end S7_Extraction

section S8_Strategies

/-! S8: the two built-in strategy classes and their foreign-boundary profiles
(census: `op.cqs-constructor`, `op.cqs-high-water-mark`, `op.cqs-size`,
`op.count-queuing-strategy-size-function`, `op.blqs-constructor`,
`op.blqs-high-water-mark`, `op.blqs-size`,
`op.byte-length-queuing-strategy-size-function`, `slot.high-water-mark`).

Each constructor "Set[s] [=this=].\[[highWaterMark]] to
|init|["highWaterMark"]" and does nothing else. The prose beside it is
explicit: "Note that the provided high water mark will not be validated ahead
of time." -/

#check (@WhatwgStreams.Data.CountQueuingStrategy.make_highWaterMark :
  forall {Size : Type u} (highWaterMark : Size),
    (WhatwgStreams.Data.CountQueuingStrategy.make highWaterMark :
      WhatwgStreams.Data.CountQueuingStrategy Size).highWaterMark = highWaterMark)
#check (@WhatwgStreams.Data.CountQueuingStrategy.make_does_not_validate :
  forall {Size : Type u} (highWaterMark : Size),
    (WhatwgStreams.Data.CountQueuingStrategy.make highWaterMark :
      WhatwgStreams.Data.CountQueuingStrategy Size).highWaterMark = highWaterMark)
#check (@WhatwgStreams.Data.CountQueuingStrategy.make_accepts_nan :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    (WhatwgStreams.Data.CountQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan)
#check (@WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm_eq :
  forall {σ : Type u} (countName : σ),
    WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName =
      WhatwgStreams.Data.SizeAlgorithm.foreign countName)
#check (@WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy_highWaterMark :
  forall {σ Size : Type u} (countName : σ)
    (self : WhatwgStreams.Data.CountQueuingStrategy Size),
      (WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy countName self).highWaterMark =
        some self.highWaterMark)
#check (@WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy_size :
  forall {σ Size : Type u} (countName : σ)
    (self : WhatwgStreams.Data.CountQueuingStrategy Size),
      (WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy countName self).size =
        some countName)
#check (@WhatwgStreams.Data.CountQueuingStrategy.extract_size_algorithm :
  forall {σ Size : Type u} (countName : σ)
    (self : WhatwgStreams.Data.CountQueuingStrategy Size),
      WhatwgStreams.Data.extractSizeAlgorithm
          (WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy countName self) =
        WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName)

/-! "Let |steps| be the following steps: Return 1." The pinned WPT observes the
count size function returning `1` for `undefined`, `null`, a string, `{}`, a
chunk, a getter, and a getter that throws: it never reads its argument, which
is the quantification over every chunk below. -/
#check (@WhatwgStreams.Data.CountQueuingStrategy.size_answers_one :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε),
      WhatwgStreams.Data.CountSizeProfile sizes countName oracle -> forall chunk : α,
        WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
            (WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk =
          WhatwgStreams.Data.SizeAnswer.value sizes.one)
#check (@WhatwgStreams.Data.CountQueuingStrategy.size_ignores_chunk :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε),
      WhatwgStreams.Data.CountSizeProfile sizes countName oracle -> forall left right : α,
        WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
            (WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName) left =
          WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
            (WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName) right)
#check (@WhatwgStreams.Data.CountQueuingStrategy.size_never_throws :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε),
      WhatwgStreams.Data.CountSizeProfile sizes countName oracle ->
        forall (chunk : α) (reason : ε),
          WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
              (WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk ≠
            WhatwgStreams.Data.SizeAnswer.thrown reason)
#check (@WhatwgStreams.Data.CountQueuingStrategy.enqueue_accepts :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) (chunk : α) (size : Size),
      WhatwgStreams.Data.CountSizeProfile sizes countName oracle -> sizes.Ordered ->
        WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
            (WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk =
          WhatwgStreams.Data.SizeAnswer.value size ->
            sizes.Admissible size)

#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.make_highWaterMark :
  forall {Size : Type u} (highWaterMark : Size),
    (WhatwgStreams.Data.ByteLengthQueuingStrategy.make highWaterMark :
      WhatwgStreams.Data.ByteLengthQueuingStrategy Size).highWaterMark = highWaterMark)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.make_accepts_nan :
  forall {Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    (WhatwgStreams.Data.ByteLengthQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq :
  forall {σ : Type u} (byteLengthName : σ),
    WhatwgStreams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName =
      WhatwgStreams.Data.SizeAlgorithm.foreign byteLengthName)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_highWaterMark :
  forall {σ Size : Type u} (byteLengthName : σ)
    (self : WhatwgStreams.Data.ByteLengthQueuingStrategy Size),
      (WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy
        byteLengthName self).highWaterMark = some self.highWaterMark)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size :
  forall {σ Size : Type u} (byteLengthName : σ)
    (self : WhatwgStreams.Data.ByteLengthQueuingStrategy Size),
      (WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).size =
        some byteLengthName)

/-! "Return ? GetV(|chunk|, "`byteLength`")". The `?` propagates an abrupt
completion, and the pinned WPT observes all three answers: `1024` for a chunk
with the property, `undefined` for a chunk without it, and a re-thrown error
for a throwing getter. A total `α -> Size` cannot express two of the three. -/
#check (@WhatwgStreams.Data.byteLengthSize_number :
  forall {ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (n : Size),
    WhatwgStreams.Data.byteLengthSize sizes
        (WhatwgStreams.Data.ByteLengthAnswer.number n : WhatwgStreams.Data.ByteLengthAnswer Size ε) =
      WhatwgStreams.Data.SizeAnswer.value n)
#check (@WhatwgStreams.Data.byteLengthSize_undefined :
  forall {ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size),
    WhatwgStreams.Data.byteLengthSize sizes
        (WhatwgStreams.Data.ByteLengthAnswer.undefined :
          WhatwgStreams.Data.ByteLengthAnswer Size ε) =
      WhatwgStreams.Data.SizeAnswer.value sizes.nan)
#check (@WhatwgStreams.Data.byteLengthSize_thrown :
  forall {ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (reason : ε),
    WhatwgStreams.Data.byteLengthSize sizes
        (WhatwgStreams.Data.ByteLengthAnswer.thrown reason :
          WhatwgStreams.Data.ByteLengthAnswer Size ε) =
      WhatwgStreams.Data.SizeAnswer.thrown reason)
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.size_eq_byteLength :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (byteLengthName : σ)
    (byteLength : α -> WhatwgStreams.Data.ByteLengthAnswer Size ε)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε),
      WhatwgStreams.Data.ByteLengthSizeProfile sizes byteLengthName byteLength oracle ->
        forall chunk : α,
          WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
              (WhatwgStreams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk =
            WhatwgStreams.Data.byteLengthSize sizes (byteLength chunk))

/-! The composite the pinned WPT forces: a chunk with no `byteLength` yields
`undefined`, the Web IDL conversion makes that `NaN`, and the enqueue that
follows refuses it with a `RangeError`. -/
#check (@WhatwgStreams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused :
  forall {α σ ε Size : Type u} (sizes : WhatwgStreams.Data.SizeClass Size) (byteLengthName : σ)
    (byteLength : α -> WhatwgStreams.Data.ByteLengthAnswer Size ε)
    (oracle : σ -> α -> WhatwgStreams.Data.SizeAnswer Size ε) (chunk : α)
    (q : WhatwgStreams.Data.Queue α Size) (value : α),
      WhatwgStreams.Data.ByteLengthSizeProfile sizes byteLengthName byteLength oracle ->
        sizes.Classified ->
          byteLength chunk = WhatwgStreams.Data.ByteLengthAnswer.undefined ->
            WhatwgStreams.Data.SizeAlgorithm.invoke sizes oracle
                (WhatwgStreams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName)
                chunk =
              WhatwgStreams.Data.SizeAnswer.value sizes.nan /\
            WhatwgStreams.Data.enqueueValueWithSize sizes q value sizes.nan =
              Except.error WhatwgStreams.Data.RangeError.rangeError)

/-! The theorem-shaped refusal of `DATA-FB-REALM`. The pinned WPT
`queuing-strategies-size-function-per-global.window.js` observes two realms
producing different size-function objects, whereas every Lean minting function
is a function of its argument. Realm distinctness is therefore the caller's
obligation, and every law above takes the name as an argument. -/
#check (@WhatwgStreams.Data.realm_identity_refused :
  forall {γ σ : Type u} (mint : γ -> σ) (left right : γ),
    left = right -> mint left = mint right)

end S8_Strategies

section ExecutableFalsifiers

/-! Executable finite checks on the frozen API.

The battery builds a concrete carrier locally, because the packet declares no
instance: which instance is right is ruling request `P3-R1`. `ProbeSize` is a
breaker-local extended integer with the three special points the `SizeClass`
fields demand. It is not a proposal for the answer to `P3-R1`; it exists so
that the frozen operations can be run on the pinned WPT inputs.

Every `#guard` below is a finite probe, not a theorem. -/

inductive ProbeSize
  | nan
  | posInf
  | negInf
  | fin (n : Int)
deriving DecidableEq, Repr

def ProbeSize.isNaN : ProbeSize -> Bool
  | .nan => true
  | _ => false

def ProbeSize.isNegative : ProbeSize -> Bool
  | .negInf => true
  | .fin n => decide (n < 0)
  | _ => false

def ProbeSize.isInfinite : ProbeSize -> Bool
  | .posInf => true
  | .negInf => true
  | _ => false

def ProbeSize.add : ProbeSize -> ProbeSize -> ProbeSize
  | .nan, _ => .nan
  | _, .nan => .nan
  | .posInf, .negInf => .nan
  | .negInf, .posInf => .nan
  | .posInf, _ => .posInf
  | _, .posInf => .posInf
  | .negInf, _ => .negInf
  | _, .negInf => .negInf
  | .fin a, .fin b => .fin (a + b)

def ProbeSize.sub : ProbeSize -> ProbeSize -> ProbeSize
  | a, b => ProbeSize.add a (match b with
      | .nan => .nan
      | .posInf => .negInf
      | .negInf => .posInf
      | .fin n => .fin (-n))

def probeSizes : WhatwgStreams.Data.SizeClass ProbeSize where
  zero := .fin 0
  one := .fin 1
  nan := .nan
  posInfinity := .posInf
  negInfinity := .negInf
  add := ProbeSize.add
  sub := ProbeSize.sub
  isNaN := ProbeSize.isNaN
  isNegative := ProbeSize.isNegative
  isInfinite := ProbeSize.isInfinite

abbrev ProbeQueue := WhatwgStreams.Data.Queue Nat ProbeSize

def probeEmpty : ProbeQueue := WhatwgStreams.Data.Queue.empty probeSizes

def probeEnqueue (q : ProbeQueue) (v : Nat) (s : ProbeSize) : Option ProbeQueue :=
  Except.toOption (WhatwgStreams.Data.enqueueValueWithSize probeSizes q v s)

/-! The four sizes the pinned WPT case "Readable stream: invalid strategy.size
return value" enumerates. Every one must be refused. -/
#guard (probeEnqueue probeEmpty 1 ProbeSize.nan).isNone
#guard (probeEnqueue probeEmpty 1 ProbeSize.posInf).isNone
#guard (probeEnqueue probeEmpty 1 ProbeSize.negInf).isNone
#guard (probeEnqueue probeEmpty 1 (ProbeSize.fin (-1))).isNone
#guard (probeEnqueue probeEmpty 1 (ProbeSize.fin 0)).isSome
#guard (probeEnqueue probeEmpty 1 (ProbeSize.fin 5)).isSome

/-! `+∞` passes `IsNonNegativeNumber` and is refused only by the second step. -/
#guard probeSizes.isNonNegativeNumber ProbeSize.posInf = true
#guard probeSizes.isNonNegativeNumber ProbeSize.negInf = false
#guard probeSizes.isNonNegativeNumber ProbeSize.nan = false
#guard probeSizes.isPositiveInfinity ProbeSize.posInf = true
#guard probeSizes.isPositiveInfinity ProbeSize.negInf = false

/-! Append, total, FIFO order, and the agreement of peek with dequeue. -/
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).map
    (fun q => q.entries.map WhatwgStreams.Data.QueueEntry.value)) = some [1, 2]
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).map WhatwgStreams.Data.Queue.totalSize) =
    some (ProbeSize.fin 8)
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).bind
    fun q => (WhatwgStreams.Data.dequeueValue probeSizes q).map Prod.fst) = some 1
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).bind
    fun q => WhatwgStreams.Data.peekQueueValue q) = some 1
#guard (WhatwgStreams.Data.dequeueValue probeSizes probeEmpty).isNone
#guard (WhatwgStreams.Data.peekQueueValue probeEmpty).isNone

/-! The clamp: a queue whose running total is below the head's size lands on
zero, never below it. -/
#guard ((WhatwgStreams.Data.dequeueValue probeSizes
  ({ entries := [{ value := 1, size := ProbeSize.fin 5 }], totalSize := ProbeSize.fin 2 } :
    ProbeQueue)).map (fun r => r.snd.totalSize)) = some (ProbeSize.fin 0)

/-! Reset writes zero outright. -/
#guard (WhatwgStreams.Data.resetQueue probeSizes
  ({ entries := [], totalSize := ProbeSize.fin 17 } : ProbeQueue)).totalSize =
    ProbeSize.fin 0

/-! The pinned WPT high-water-mark refusals, and the one value that separates
the two refusal sets. -/
def probeHWM (h : Option ProbeSize) : Option ProbeSize :=
  Except.toOption (WhatwgStreams.Data.extractHighWaterMark probeSizes
    ({ highWaterMark := h, size := (none : Option Nat) } :
      WhatwgStreams.Data.QueuingStrategy Nat ProbeSize) (ProbeSize.fin 1))

#guard (probeHWM (some ProbeSize.nan)).isNone
#guard (probeHWM (some ProbeSize.negInf)).isNone
#guard (probeHWM (some (ProbeSize.fin (-1)))).isNone
#guard probeHWM (some ProbeSize.posInf) = some ProbeSize.posInf
#guard probeHWM (some (ProbeSize.fin 7)) = some (ProbeSize.fin 7)
#guard probeHWM none = some (ProbeSize.fin 1)

/-! `ExtractSizeAlgorithm` defaults to the constant-one algorithm. -/
#guard (WhatwgStreams.Data.extractSizeAlgorithm
  ({ highWaterMark := (none : Option ProbeSize), size := (none : Option Nat) } :
    WhatwgStreams.Data.QueuingStrategy Nat ProbeSize)) =
      WhatwgStreams.Data.SizeAlgorithm.one
#guard (WhatwgStreams.Data.extractSizeAlgorithm
  ({ highWaterMark := (none : Option ProbeSize), size := some (9 : Nat) } :
    WhatwgStreams.Data.QueuingStrategy Nat ProbeSize)) =
      WhatwgStreams.Data.SizeAlgorithm.foreign 9

/-! `ByteLengthAnswer.undefined` becomes `NaN`, which the enqueue refuses. -/
#guard (WhatwgStreams.Data.byteLengthSize probeSizes
  (WhatwgStreams.Data.ByteLengthAnswer.undefined :
    WhatwgStreams.Data.ByteLengthAnswer ProbeSize Nat)) =
      WhatwgStreams.Data.SizeAnswer.value ProbeSize.nan

end ExecutableFalsifiers

end WhatwgStreamsTest.Data.QueueContract
