import Whatwg.Streams

/-
Contract packet: `test/contracts/queue-with-sizes.contract.md`

Breaker-owned red battery for P3, queue-with-sizes and the queuing
strategies. The implementation phase must not edit this file. It is red until
`Whatwg/Streams/Data/Queue.lean` and `Whatwg/Streams/Data/Strategy.lean` declare
the frozen surface and `Whatwg.Streams.lean` reaches them.

Every public declaration is frozen by an exact `#check (@name : proposition)`
ascription, so no weaker statement satisfies this contract. Names are written
fully qualified and this module deliberately does not `open Whatwg.Streams`, so
a locally shadowed spelling cannot silently satisfy an ascription.

The single production import is the library root, not the two fenced modules.
Section 8 of the contract records why: at the base commit the fenced modules
do not exist, and an unresolvable import is a build failure of a different
kind from the unknown-identifier failures a clean red phase is made of. The
module-closure gate in `WhatwgTest/Audit/AxiomGate.lean` guarantees the
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
--   lake env lean -DmaxErrors=10000 WhatwgTest/Streams/Data/QueueContract.lean
-- Section 12 of the contract packet records what that run must show.

namespace WhatwgTest.Streams.Data.QueueContract

universe u

section RefusalTag

/-! D0: the refusal tag. The `{{RangeError}}` of `op.enqueue-value-with-size`
and `op.validate-and-normalize-high-water-mark`. -/

#check (@Whatwg.Streams.Data.RangeError : Type)
#check (@Whatwg.Streams.Data.RangeError.rangeError : Whatwg.Streams.Data.RangeError)

example : DecidableEq Whatwg.Streams.Data.RangeError := inferInstance
example : Repr Whatwg.Streams.Data.RangeError := inferInstance

end RefusalTag

section SizeSurface

/-! D1 and D2: the size carrier interface and its three property predicates.

`[[queueTotalSize]]` is "a JavaScript Number, i.e. a double-precision floating
point number" (`slot.queue-total-size`). Which Lean carrier stands for that is
ruling request `P3-R1`; this surface is written so the ruling changes an
instance and no statement. The three special constants are fields rather than
derived predicates so that no instance can satisfy a refusal law for want of a
witness. -/

#check (@Whatwg.Streams.Data.SizeClass : Type u -> Type u)
#check (@Whatwg.Streams.Data.SizeClass.zero :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.one :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.nan :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.posInfinity :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.negInfinity :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.add :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.sub :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Size -> Size)
#check (@Whatwg.Streams.Data.SizeClass.isNaN :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Bool)
#check (@Whatwg.Streams.Data.SizeClass.isNegative :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Bool)
#check (@Whatwg.Streams.Data.SizeClass.isInfinite :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Bool)

#check (@Whatwg.Streams.Data.SizeClass.Admissible :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Prop)
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Bool)
#check (@Whatwg.Streams.Data.SizeClass.isPositiveInfinity :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Bool)
#check (@Whatwg.Streams.Data.SizeClass.clampNonNegative :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Size -> Size)

#check (@Whatwg.Streams.Data.SizeClass.Classified :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Prop)
#check (@Whatwg.Streams.Data.SizeClass.Ordered :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Prop)
#check (@Whatwg.Streams.Data.SizeClass.Exact :
  forall {Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> Prop)

/-! The `Exact` equations are guarded by `Admissible`. Unguarded they are false
of every carrier that has a `NaN`, so a builder who drops a guard freezes a
predicate no instance satisfies. -/
#check (@Whatwg.Streams.Data.SizeClass.Exact.sub_add_cancel :
  forall {Size : Type u} {sizes : Whatwg.Streams.Data.SizeClass Size},
    sizes.Exact -> forall a b : Size, sizes.Admissible a -> sizes.Admissible b ->
      sizes.sub (sizes.add a b) b = a)
#check (@Whatwg.Streams.Data.SizeClass.Exact.add_assoc :
  forall {Size : Type u} {sizes : Whatwg.Streams.Data.SizeClass Size},
    sizes.Exact -> forall a b c : Size,
      sizes.Admissible a -> sizes.Admissible b -> sizes.Admissible c ->
        sizes.add (sizes.add a b) c = sizes.add a (sizes.add b c))
#check (@Whatwg.Streams.Data.SizeClass.Exact.add_comm :
  forall {Size : Type u} {sizes : Whatwg.Streams.Data.SizeClass Size},
    sizes.Exact -> forall a b : Size, sizes.Admissible a -> sizes.Admissible b ->
      sizes.add a b = sizes.add b a)
#check (@Whatwg.Streams.Data.SizeClass.Exact.zero_add :
  forall {Size : Type u} {sizes : Whatwg.Streams.Data.SizeClass Size},
    sizes.Exact -> forall a : Size, sizes.Admissible a -> sizes.add sizes.zero a = a)
#check (@Whatwg.Streams.Data.SizeClass.Ordered.add_admissible :
  forall {Size : Type u} {sizes : Whatwg.Streams.Data.SizeClass Size},
    sizes.Ordered -> forall a b : Size, sizes.Admissible a -> sizes.Admissible b ->
      sizes.Admissible (sizes.add a b))
#check (@Whatwg.Streams.Data.SizeClass.Classified.nan_isolated :
  forall {Size : Type u} {sizes : Whatwg.Streams.Data.SizeClass Size},
    sizes.Classified -> forall v : Size, sizes.isNaN v = true ->
      sizes.isNegative v = false /\ sizes.isInfinite v = false)

end SizeSurface

section QueueSurface

/-! D3: the queue-with-sizes carrier (census: `slot.queue`,
`slot.queue-total-size`).

A `value-with-size` is "a struct with the two items value and size", and the
two paired slots are "always named \[[queue]] and \[[queueTotalSize]]". -/

#check (@Whatwg.Streams.Data.QueueEntry : Type u -> Type u -> Type u)
#check (@Whatwg.Streams.Data.QueueEntry.mk :
  forall {α Size : Type u}, α -> Size -> Whatwg.Streams.Data.QueueEntry α Size)
#check (@Whatwg.Streams.Data.QueueEntry.value :
  forall {α Size : Type u}, Whatwg.Streams.Data.QueueEntry α Size -> α)
#check (@Whatwg.Streams.Data.QueueEntry.size :
  forall {α Size : Type u}, Whatwg.Streams.Data.QueueEntry α Size -> Size)

#check (@Whatwg.Streams.Data.Queue : Type u -> Type u -> Type u)
#check (@Whatwg.Streams.Data.Queue.mk :
  forall {α Size : Type u},
    List (Whatwg.Streams.Data.QueueEntry α Size) -> Size -> Whatwg.Streams.Data.Queue α Size)
#check (@Whatwg.Streams.Data.Queue.entries :
  forall {α Size : Type u},
    Whatwg.Streams.Data.Queue α Size -> List (Whatwg.Streams.Data.QueueEntry α Size))
#check (@Whatwg.Streams.Data.Queue.totalSize :
  forall {α Size : Type u}, Whatwg.Streams.Data.Queue α Size -> Size)

example {α Size : Type u} [DecidableEq α] [DecidableEq Size] :
    DecidableEq (Whatwg.Streams.Data.QueueEntry α Size) := inferInstance
example {α Size : Type u} [DecidableEq α] [DecidableEq Size] :
    DecidableEq (Whatwg.Streams.Data.Queue α Size) := inferInstance

#check (@Whatwg.Streams.Data.Queue.empty :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.Queue α Size)
#check (@Whatwg.Streams.Data.sizeSum :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    List (Whatwg.Streams.Data.QueueEntry α Size) -> Size)
#check (@Whatwg.Streams.Data.Queue.WF :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.Queue α Size -> Prop)
#check (@Whatwg.Streams.Data.Queue.SizesAdmissible :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.Queue α Size -> Prop)

/-! `Queue.WF` is a separate decidable `Prop`, not a field invariant. The
pinned text says the running total "is *not* equivalent to adding up the size
of all chunks in \[[queue]]", so a structure that made the invariant
unconstructible-otherwise could not represent the specification's own
reachable states. -/
example {α Size : Type u} [DecidableEq Size]
    (sizes : Whatwg.Streams.Data.SizeClass Size) (q : Whatwg.Streams.Data.Queue α Size) :
    Decidable (Whatwg.Streams.Data.Queue.WF sizes q) := inferInstance

end QueueSurface

section OperationSurface

/-! D4 through D8: the four queue-with-sizes operations, the size algebra, the
strategy dictionary and the two built-in classes. -/

#check (@Whatwg.Streams.Data.enqueueValueWithSize :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.Queue α Size -> α -> Size ->
      Except Whatwg.Streams.Data.RangeError (Whatwg.Streams.Data.Queue α Size))
#check (@Whatwg.Streams.Data.dequeueValue :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.Queue α Size -> Option (α × Whatwg.Streams.Data.Queue α Size))
#check (@Whatwg.Streams.Data.peekQueueValue :
  forall {α Size : Type u}, Whatwg.Streams.Data.Queue α Size -> Option α)
#check (@Whatwg.Streams.Data.resetQueue :
  forall {α Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.Queue α Size -> Whatwg.Streams.Data.Queue α Size)

#check (@Whatwg.Streams.Data.SizeAlgorithm : Type u -> Type u)
#check (@Whatwg.Streams.Data.SizeAlgorithm.one :
  forall {σ : Type u}, Whatwg.Streams.Data.SizeAlgorithm σ)
#check (@Whatwg.Streams.Data.SizeAlgorithm.foreign :
  forall {σ : Type u}, σ -> Whatwg.Streams.Data.SizeAlgorithm σ)
#check (@Whatwg.Streams.Data.SizeAnswer : Type u -> Type u -> Type u)
#check (@Whatwg.Streams.Data.SizeAnswer.value :
  forall {Size ε : Type u}, Size -> Whatwg.Streams.Data.SizeAnswer Size ε)
#check (@Whatwg.Streams.Data.SizeAnswer.thrown :
  forall {Size ε : Type u}, ε -> Whatwg.Streams.Data.SizeAnswer Size ε)
#check (@Whatwg.Streams.Data.ByteLengthAnswer : Type u -> Type u -> Type u)
#check (@Whatwg.Streams.Data.ByteLengthAnswer.number :
  forall {Size ε : Type u}, Size -> Whatwg.Streams.Data.ByteLengthAnswer Size ε)
#check (@Whatwg.Streams.Data.ByteLengthAnswer.undefined :
  forall {Size ε : Type u}, Whatwg.Streams.Data.ByteLengthAnswer Size ε)
#check (@Whatwg.Streams.Data.ByteLengthAnswer.thrown :
  forall {Size ε : Type u}, ε -> Whatwg.Streams.Data.ByteLengthAnswer Size ε)

#check (@Whatwg.Streams.Data.SizeAlgorithm.invoke :
  forall {α σ ε Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    (σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) ->
      Whatwg.Streams.Data.SizeAlgorithm σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε)
#check (@Whatwg.Streams.Data.byteLengthSize :
  forall {ε Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.ByteLengthAnswer Size ε -> Whatwg.Streams.Data.SizeAnswer Size ε)

#check (@Whatwg.Streams.Data.QueuingStrategy : Type u -> Type u -> Type u)
#check (@Whatwg.Streams.Data.QueuingStrategy.mk :
  forall {σ Size : Type u}, Option Size -> Option σ ->
    Whatwg.Streams.Data.QueuingStrategy σ Size)
#check (@Whatwg.Streams.Data.QueuingStrategy.highWaterMark :
  forall {σ Size : Type u}, Whatwg.Streams.Data.QueuingStrategy σ Size -> Option Size)
#check (@Whatwg.Streams.Data.QueuingStrategy.size :
  forall {σ Size : Type u}, Whatwg.Streams.Data.QueuingStrategy σ Size -> Option σ)

#check (@Whatwg.Streams.Data.extractHighWaterMark :
  forall {σ Size : Type u}, Whatwg.Streams.Data.SizeClass Size ->
    Whatwg.Streams.Data.QueuingStrategy σ Size -> Size ->
      Except Whatwg.Streams.Data.RangeError Size)
#check (@Whatwg.Streams.Data.extractSizeAlgorithm :
  forall {σ Size : Type u}, Whatwg.Streams.Data.QueuingStrategy σ Size ->
    Whatwg.Streams.Data.SizeAlgorithm σ)

#check (@Whatwg.Streams.Data.CountQueuingStrategy : Type u -> Type u)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.highWaterMark :
  forall {Size : Type u}, Whatwg.Streams.Data.CountQueuingStrategy Size -> Size)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.make :
  forall {Size : Type u}, Size -> Whatwg.Streams.Data.CountQueuingStrategy Size)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm :
  forall {σ : Type u}, σ -> Whatwg.Streams.Data.SizeAlgorithm σ)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy :
  forall {σ Size : Type u}, σ -> Whatwg.Streams.Data.CountQueuingStrategy Size ->
    Whatwg.Streams.Data.QueuingStrategy σ Size)

#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy : Type u -> Type u)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.highWaterMark :
  forall {Size : Type u}, Whatwg.Streams.Data.ByteLengthQueuingStrategy Size -> Size)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.make :
  forall {Size : Type u}, Size -> Whatwg.Streams.Data.ByteLengthQueuingStrategy Size)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm :
  forall {σ : Type u}, σ -> Whatwg.Streams.Data.SizeAlgorithm σ)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy :
  forall {σ Size : Type u}, σ -> Whatwg.Streams.Data.ByteLengthQueuingStrategy Size ->
    Whatwg.Streams.Data.QueuingStrategy σ Size)

#check (@Whatwg.Streams.Data.CountSizeProfile :
  forall {α σ ε Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> σ ->
    (σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) -> Prop)
#check (@Whatwg.Streams.Data.ByteLengthSizeProfile :
  forall {α σ ε Size : Type u}, Whatwg.Streams.Data.SizeClass Size -> σ ->
    (α -> Whatwg.Streams.Data.ByteLengthAnswer Size ε) ->
      (σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) -> Prop)

end OperationSurface

section S1_Classification

/-! S1: classification and admission (census: `op.is-non-negative-number`).

"If |v| is not a Number, return false. If |v| is NaN, return false. If |v| < 0,
return false. Return true." The "is not a Number" step is a Web IDL boundary
and is `hostOnly`; the carrier's values are already Numbers. -/

#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (v : Size),
    sizes.isNonNegativeNumber v = (!sizes.isNaN v && !sizes.isNegative v))
#check (@Whatwg.Streams.Data.SizeClass.isPositiveInfinity_eq :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (v : Size),
    sizes.isPositiveInfinity v = (sizes.isInfinite v && !sizes.isNegative v))
#check (@Whatwg.Streams.Data.SizeClass.admissible_iff :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (v : Size),
    sizes.Admissible v <->
      (sizes.isNaN v = false /\ sizes.isNegative v = false /\ sizes.isInfinite v = false))
#check (@Whatwg.Streams.Data.SizeClass.not_admissible_nan :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Classified -> ¬ sizes.Admissible sizes.nan)
#check (@Whatwg.Streams.Data.SizeClass.not_admissible_posInfinity :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Classified -> ¬ sizes.Admissible sizes.posInfinity)
#check (@Whatwg.Streams.Data.SizeClass.not_admissible_negInfinity :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Classified -> ¬ sizes.Admissible sizes.negInfinity)
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_nan :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Classified -> sizes.isNonNegativeNumber sizes.nan = false)
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_negInfinity :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Classified -> sizes.isNonNegativeNumber sizes.negInfinity = false)

/-! The theorem that pins the two-step structure of `EnqueueValueWithSize`:
`+∞` passes `IsNonNegativeNumber` and is refused only by the second step. A
one-step model satisfies every other law in this battery. -/
#check (@Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_posInfinity :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Classified -> sizes.isNonNegativeNumber sizes.posInfinity = true)

#check (@Whatwg.Streams.Data.SizeClass.clampNonNegative_of_negative :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (v : Size),
    sizes.isNegative v = true -> sizes.clampNonNegative v = sizes.zero)
#check (@Whatwg.Streams.Data.SizeClass.clampNonNegative_of_nonneg :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (v : Size),
    sizes.isNegative v = false -> sizes.clampNonNegative v = v)
#check (@Whatwg.Streams.Data.SizeClass.clampNonNegative_not_negative :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    sizes.Ordered -> forall v : Size, sizes.isNegative (sizes.clampNonNegative v) = false)

end S1_Classification

section S2_Sum

/-! S2: the queue carrier and the sum (census: `slot.queue`,
`slot.queue-total-size`). -/

#check (@Whatwg.Streams.Data.Queue.empty_entries :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    (Whatwg.Streams.Data.Queue.empty sizes : Whatwg.Streams.Data.Queue α Size).entries = [])
#check (@Whatwg.Streams.Data.Queue.empty_totalSize :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    (Whatwg.Streams.Data.Queue.empty sizes : Whatwg.Streams.Data.Queue α Size).totalSize =
      sizes.zero)
#check (@Whatwg.Streams.Data.sizeSum_nil :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    Whatwg.Streams.Data.sizeSum sizes ([] : List (Whatwg.Streams.Data.QueueEntry α Size)) =
      sizes.zero)

/-! `sizeSum` folds left, from `zero`, in the order `EnqueueValueWithSize`
accumulates. `WS-DATA-CE-002` exhibits a carrier on which the two fold
directions differ, so the direction is not cosmetic. -/
#check (@Whatwg.Streams.Data.sizeSum_append_singleton :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (entries : List (Whatwg.Streams.Data.QueueEntry α Size))
    (entry : Whatwg.Streams.Data.QueueEntry α Size),
      Whatwg.Streams.Data.sizeSum sizes (entries ++ [entry]) =
        sizes.add (Whatwg.Streams.Data.sizeSum sizes entries) entry.size)
#check (@Whatwg.Streams.Data.sizeSum_cons :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (entries : List (Whatwg.Streams.Data.QueueEntry α Size)),
      sizes.Exact -> sizes.Ordered -> sizes.Admissible entry.size ->
        (forall e, e ∈ entries -> sizes.Admissible e.size) ->
          Whatwg.Streams.Data.sizeSum sizes (entry :: entries) =
            sizes.add entry.size (Whatwg.Streams.Data.sizeSum sizes entries))
#check (@Whatwg.Streams.Data.sizeSum_admissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (entries : List (Whatwg.Streams.Data.QueueEntry α Size)),
      sizes.Ordered -> (forall e, e ∈ entries -> sizes.Admissible e.size) ->
        sizes.Admissible (Whatwg.Streams.Data.sizeSum sizes entries))
#check (@Whatwg.Streams.Data.Queue.WF_iff :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.Queue.WF sizes q <->
        q.totalSize = Whatwg.Streams.Data.sizeSum sizes q.entries)
#check (@Whatwg.Streams.Data.Queue.WF_empty :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    Whatwg.Streams.Data.Queue.WF sizes
      (Whatwg.Streams.Data.Queue.empty sizes : Whatwg.Streams.Data.Queue α Size))
#check (@Whatwg.Streams.Data.Queue.SizesAdmissible_iff :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.Queue.SizesAdmissible sizes q <->
        forall entry, entry ∈ q.entries -> sizes.Admissible entry.size)
#check (@Whatwg.Streams.Data.Queue.SizesAdmissible_empty :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    Whatwg.Streams.Data.Queue.SizesAdmissible sizes
      (Whatwg.Streams.Data.Queue.empty sizes : Whatwg.Streams.Data.Queue α Size))

end S2_Sum

section S3_Enqueue

/-! S3: enqueue (census: `op.enqueue-value-with-size`).

"If ! IsNonNegativeNumber(|size|) is false, throw a RangeError exception. If
|size| is +∞, throw a RangeError exception. Append a new value-with-size ... Set
|container|.\[[queueTotalSize]] to |container|.\[[queueTotalSize]] + |size|." -/

#check (@Whatwg.Streams.Data.enqueueValueWithSize_error_iff :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.enqueueValueWithSize sizes q value size =
          Except.error Whatwg.Streams.Data.RangeError.rangeError <->
        (sizes.isNonNegativeNumber size = false \/ sizes.isPositiveInfinity size = true))
#check (@Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.enqueueValueWithSize sizes q value size =
          Except.error Whatwg.Streams.Data.RangeError.rangeError <->
        ¬ sizes.Admissible size)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_nan :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α),
      sizes.Classified ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.nan =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_negative :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      sizes.isNegative size = true ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_posInfinity :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α),
      sizes.Classified ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.posInfinity =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_refuses_negInfinity :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α),
      sizes.Classified ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.negInfinity =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_ok_iff :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      (exists q', Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q') <->
        sizes.Admissible size)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_eq_of_admissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      sizes.Admissible size ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size =
          Except.ok ({ entries := q.entries ++ [{ value := value, size := size }],
                       totalSize := sizes.add q.totalSize size } :
            Whatwg.Streams.Data.Queue α Size))

/-! The append. `WS-DATA-CE-010` attacks a model that prepends; it keeps the
total, the length and the multiset of entries, and is caught by nothing else
here. -/
#check (@Whatwg.Streams.Data.enqueueValueWithSize_entries :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
        q'.entries = q.entries ++
          [({ value := value, size := size } : Whatwg.Streams.Data.QueueEntry α Size)])
#check (@Whatwg.Streams.Data.enqueueValueWithSize_totalSize :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
        q'.totalSize = sizes.add q.totalSize size)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_length :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
        q'.entries.length = q.entries.length + 1)
#check (@Whatwg.Streams.Data.enqueueValueWithSize_sizesAdmissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.Queue.SizesAdmissible sizes q ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          Whatwg.Streams.Data.Queue.SizesAdmissible sizes q')
#check (@Whatwg.Streams.Data.enqueueValueWithSize_totalSize_admissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      sizes.Ordered -> sizes.Admissible q.totalSize ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          sizes.Admissible q'.totalSize)

/-! Enqueue never drifts: the running total and the fold take the same step,
by `sizeSum_append_singleton`. Dequeue does drift, which is `P3-R1`. -/
#check (@Whatwg.Streams.Data.enqueueValueWithSize_wf :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      Whatwg.Streams.Data.Queue.WF sizes q ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          Whatwg.Streams.Data.Queue.WF sizes q')

end S3_Enqueue

section S4_Dequeue

/-! S4: dequeue (census: `op.dequeue-value`).

"Assert: |container|.\[[queue]] is not empty. Let |valueWithSize| be
|container|.\[[queue]][0]. Remove |valueWithSize| ... Set
|container|.\[[queueTotalSize]] to |container|.\[[queueTotalSize]] −
|valueWithSize|'s size. If |container|.\[[queueTotalSize]] < 0, set
|container|.\[[queueTotalSize]] to 0. (This can occur due to rounding errors.)" -/

#check (@Whatwg.Streams.Data.dequeueValue_nil :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (total : Size),
    Whatwg.Streams.Data.dequeueValue sizes
        ({ entries := [], totalSize := total } : Whatwg.Streams.Data.Queue α Size) = none)
#check (@Whatwg.Streams.Data.dequeueValue_cons :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (total : Size)
    (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (rest : List (Whatwg.Streams.Data.QueueEntry α Size)),
      Whatwg.Streams.Data.dequeueValue sizes
          ({ entries := entry :: rest, totalSize := total } : Whatwg.Streams.Data.Queue α Size) =
        some (entry.value,
          ({ entries := rest,
             totalSize := sizes.clampNonNegative (sizes.sub total entry.size) } :
            Whatwg.Streams.Data.Queue α Size)))
#check (@Whatwg.Streams.Data.dequeueValue_isSome_iff :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      (Whatwg.Streams.Data.dequeueValue sizes q).isSome = true <-> q.entries ≠ [])
#check (@Whatwg.Streams.Data.dequeueValue_isNone_iff :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.dequeueValue sizes q = none <-> q.entries = [])
#check (@Whatwg.Streams.Data.dequeueValue_value_eq_head :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      (Whatwg.Streams.Data.dequeueValue sizes q).map Prod.fst =
        q.entries.head?.map Whatwg.Streams.Data.QueueEntry.value)
#check (@Whatwg.Streams.Data.dequeueValue_entries :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α),
      Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') ->
        q'.entries = q.entries.tail)
#check (@Whatwg.Streams.Data.dequeueValue_length :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α),
      Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') ->
        q.entries.length = q'.entries.length + 1)
#check (@Whatwg.Streams.Data.dequeueValue_totalSize :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α)
    (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (rest : List (Whatwg.Streams.Data.QueueEntry α Size)),
      q.entries = entry :: rest ->
        Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') ->
          q'.totalSize = sizes.clampNonNegative (sizes.sub q.totalSize entry.size))
#check (@Whatwg.Streams.Data.dequeueValue_totalSize_not_negative :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α),
      sizes.Ordered -> Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') ->
        sizes.isNegative q'.totalSize = false)
#check (@Whatwg.Streams.Data.dequeueValue_sizesAdmissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α),
      Whatwg.Streams.Data.Queue.SizesAdmissible sizes q ->
        Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') ->
          Whatwg.Streams.Data.Queue.SizesAdmissible sizes q')

/-! Preservation of the running-total invariant by dequeue is exactly what a
rounding carrier destroys. `WS-DATA-CE-001` is the pre-registered witness, and
the `Exact` hypothesis is where ruling `P3-R1` lands. -/
#check (@Whatwg.Streams.Data.dequeueValue_wf :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α),
      sizes.Classified -> sizes.Ordered -> sizes.Exact ->
        Whatwg.Streams.Data.Queue.WF sizes q ->
          Whatwg.Streams.Data.Queue.SizesAdmissible sizes q ->
            Whatwg.Streams.Data.dequeueValue sizes q = some (value, q') ->
              Whatwg.Streams.Data.Queue.WF sizes q')

/-! Under an exact carrier the clamp of step 6 is never taken. The step is
witnessed as vacuous rather than as a branch, which is the cost of ruling
`P3-R1` in favour of option (i), stated as a theorem in the tree. -/
#check (@Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size)
    (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (rest : List (Whatwg.Streams.Data.QueueEntry α Size)),
      sizes.Classified -> sizes.Ordered -> sizes.Exact ->
        Whatwg.Streams.Data.Queue.WF sizes q ->
          Whatwg.Streams.Data.Queue.SizesAdmissible sizes q ->
            q.entries = entry :: rest ->
              sizes.isNegative (sizes.sub q.totalSize entry.size) = false)

end S4_Dequeue

section S5_Fifo

/-! S5: FIFO and peek (census: `op.peek-queue-value`, `op.dequeue-value`).

`PeekQueueValue` takes no `SizeClass` and returns no queue. Both absences are
the packet's statement that it touches neither slot: the mutation
`WS-DATA-CE-005` attacks is not expressible in this result type. -/

#check (@Whatwg.Streams.Data.peekQueueValue_nil :
  forall {α Size : Type u} (total : Size),
    Whatwg.Streams.Data.peekQueueValue
      ({ entries := [], totalSize := total } : Whatwg.Streams.Data.Queue α Size) = none)
#check (@Whatwg.Streams.Data.peekQueueValue_cons :
  forall {α Size : Type u} (total : Size) (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (rest : List (Whatwg.Streams.Data.QueueEntry α Size)),
      Whatwg.Streams.Data.peekQueueValue
          ({ entries := entry :: rest, totalSize := total } : Whatwg.Streams.Data.Queue α Size) =
        some entry.value)
#check (@Whatwg.Streams.Data.peekQueueValue_eq_head :
  forall {α Size : Type u} (q : Whatwg.Streams.Data.Queue α Size),
    Whatwg.Streams.Data.peekQueueValue q =
      q.entries.head?.map Whatwg.Streams.Data.QueueEntry.value)
#check (@Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.peekQueueValue q =
        (Whatwg.Streams.Data.dequeueValue sizes q).map Prod.fst)
#check (@Whatwg.Streams.Data.peekQueueValue_isSome_iff :
  forall {α Size : Type u} (q : Whatwg.Streams.Data.Queue α Size),
    (Whatwg.Streams.Data.peekQueueValue q).isSome = true <-> q.entries ≠ [])
#check (@Whatwg.Streams.Data.dequeueValue_enqueueValueWithSize_empty :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size),
      q.entries = [] ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          (Whatwg.Streams.Data.dequeueValue sizes q').map Prod.fst = some value)

/-! The sharp FIFO statement: an enqueue onto a non-empty queue does not change
what the next dequeue answers. -/
#check (@Whatwg.Streams.Data.dequeueValue_enqueueValueWithSize_nonempty :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size)
    (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (rest : List (Whatwg.Streams.Data.QueueEntry α Size)),
      q.entries = entry :: rest ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          (Whatwg.Streams.Data.dequeueValue sizes q').map Prod.fst = some entry.value)
#check (@Whatwg.Streams.Data.peekQueueValue_enqueueValueWithSize_nonempty :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q q' : Whatwg.Streams.Data.Queue α Size) (value : α) (size : Size)
    (entry : Whatwg.Streams.Data.QueueEntry α Size)
    (rest : List (Whatwg.Streams.Data.QueueEntry α Size)),
      q.entries = entry :: rest ->
        Whatwg.Streams.Data.enqueueValueWithSize sizes q value size = Except.ok q' ->
          Whatwg.Streams.Data.peekQueueValue q' = some entry.value)

end S5_Fifo

section S6_Reset

/-! S6: reset (census: `op.reset-queue`).

"Set |container|.\[[queue]] to a new empty list. Set
|container|.\[[queueTotalSize]] to 0." Unconditionally, with no arithmetic, so
`resetQueue_wf` carries no carrier hypothesis. -/

#check (@Whatwg.Streams.Data.resetQueue_eq :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.resetQueue sizes q =
        ({ entries := [], totalSize := sizes.zero } : Whatwg.Streams.Data.Queue α Size))
#check (@Whatwg.Streams.Data.resetQueue_entries :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      (Whatwg.Streams.Data.resetQueue sizes q).entries = [])
#check (@Whatwg.Streams.Data.resetQueue_totalSize :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      (Whatwg.Streams.Data.resetQueue sizes q).totalSize = sizes.zero)
#check (@Whatwg.Streams.Data.resetQueue_wf :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.Queue.WF sizes (Whatwg.Streams.Data.resetQueue sizes q))
#check (@Whatwg.Streams.Data.resetQueue_sizesAdmissible :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.Queue.SizesAdmissible sizes (Whatwg.Streams.Data.resetQueue sizes q))
#check (@Whatwg.Streams.Data.resetQueue_idempotent :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.resetQueue sizes (Whatwg.Streams.Data.resetQueue sizes q) =
        Whatwg.Streams.Data.resetQueue sizes q)
#check (@Whatwg.Streams.Data.resetQueue_eq_empty :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.resetQueue sizes q = Whatwg.Streams.Data.Queue.empty sizes)
#check (@Whatwg.Streams.Data.resetQueue_dequeueValue :
  forall {α Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (q : Whatwg.Streams.Data.Queue α Size),
      Whatwg.Streams.Data.dequeueValue sizes (Whatwg.Streams.Data.resetQueue sizes q) = none)

end S6_Reset

section S7_Extraction

/-! S7: the extraction algorithms (census:
`op.validate-and-normalize-high-water-mark`,
`op.make-size-algorithm-from-size-function`).

"If |strategy|["highWaterMark"] does not exist, return |defaultHWM|. Let
|highWaterMark| be |strategy|["highWaterMark"]. If |highWaterMark| is NaN or
|highWaterMark| < 0, throw a RangeError exception. Return |highWaterMark|." The
note beside it: "+∞ is explicitly allowed as a valid high water mark." -/

#check (@Whatwg.Streams.Data.extractHighWaterMark_absent :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      strategy.highWaterMark = none ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.ok defaultHWM)
#check (@Whatwg.Streams.Data.extractHighWaterMark_error_iff :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error Whatwg.Streams.Data.RangeError.rangeError <->
        (exists highWaterMark, strategy.highWaterMark = some highWaterMark /\
          (sizes.isNaN highWaterMark = true \/ sizes.isNegative highWaterMark = true)))
#check (@Whatwg.Streams.Data.extractHighWaterMark_refuses_nan :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      sizes.Classified -> strategy.highWaterMark = some sizes.nan ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.extractHighWaterMark_refuses_negative :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM highWaterMark : Size),
      strategy.highWaterMark = some highWaterMark -> sizes.isNegative highWaterMark = true ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)
#check (@Whatwg.Streams.Data.extractHighWaterMark_refuses_negInfinity :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      sizes.Classified -> strategy.highWaterMark = some sizes.negInfinity ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.error Whatwg.Streams.Data.RangeError.rangeError)

/-! "+∞ is explicitly allowed as a valid high water mark." The pinned WPT list
of high water marks that must throw is `[-1, -Infinity, NaN, 'foo', {}]`, and
`Infinity` is deliberately absent from it. -/
#check (@Whatwg.Streams.Data.extractHighWaterMark_allows_posInfinity :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size),
      sizes.Classified -> strategy.highWaterMark = some sizes.posInfinity ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
          Except.ok sizes.posInfinity)

/-! The algorithm at this pin normalizes nothing, despite the anchor id
`validate-and-normalize-high-water-mark`. `WS-DATA-CE-009` shows why the
identity law is frozen and an idempotence law is not: a clamping mutant is
idempotent too. -/
#check (@Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted :
  forall {σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size)
    (defaultHWM highWaterMark highWaterMark' : Size),
      strategy.highWaterMark = some highWaterMark ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
            Except.ok highWaterMark' ->
          highWaterMark' = highWaterMark)

/-! The two refusal sets differ on exactly one value. Frozen as a conjunction
so that a builder who shares one predicate between the two algorithms cannot
satisfy it under any carrier. `WS-DATA-CE-008` is the attack. -/
#check (@Whatwg.Streams.Data.extractHighWaterMark_disagrees_with_enqueue_on_posInfinity :
  forall {α σ Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (defaultHWM : Size)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α),
      sizes.Classified -> strategy.highWaterMark = some sizes.posInfinity ->
        Whatwg.Streams.Data.extractHighWaterMark sizes strategy defaultHWM =
            Except.ok sizes.posInfinity /\
          Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.posInfinity =
            Except.error Whatwg.Streams.Data.RangeError.rangeError)

#check (@Whatwg.Streams.Data.extractSizeAlgorithm_absent :
  forall {σ Size : Type u} (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size),
    strategy.size = none ->
      Whatwg.Streams.Data.extractSizeAlgorithm strategy = Whatwg.Streams.Data.SizeAlgorithm.one)
#check (@Whatwg.Streams.Data.extractSizeAlgorithm_present :
  forall {σ Size : Type u} (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size) (name : σ),
    strategy.size = some name ->
      Whatwg.Streams.Data.extractSizeAlgorithm strategy =
        Whatwg.Streams.Data.SizeAlgorithm.foreign name)
#check (@Whatwg.Streams.Data.SizeAlgorithm.invoke_one :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α),
      Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
          Whatwg.Streams.Data.SizeAlgorithm.one chunk =
        Whatwg.Streams.Data.SizeAnswer.value sizes.one)
#check (@Whatwg.Streams.Data.SizeAlgorithm.invoke_foreign :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) (name : σ) (chunk : α),
      Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
          (Whatwg.Streams.Data.SizeAlgorithm.foreign name) chunk =
        oracle name chunk)
#check (@Whatwg.Streams.Data.extractSizeAlgorithm_absent_invoke :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size)
    (strategy : Whatwg.Streams.Data.QueuingStrategy σ Size)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α),
      strategy.size = none ->
        Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
            (Whatwg.Streams.Data.extractSizeAlgorithm strategy) chunk =
          Whatwg.Streams.Data.SizeAnswer.value sizes.one)

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

#check (@Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark :
  forall {Size : Type u} (highWaterMark : Size),
    (Whatwg.Streams.Data.CountQueuingStrategy.make highWaterMark :
      Whatwg.Streams.Data.CountQueuingStrategy Size).highWaterMark = highWaterMark)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.make_does_not_validate :
  forall {Size : Type u} (highWaterMark : Size),
    (Whatwg.Streams.Data.CountQueuingStrategy.make highWaterMark :
      Whatwg.Streams.Data.CountQueuingStrategy Size).highWaterMark = highWaterMark)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.make_accepts_nan :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    (Whatwg.Streams.Data.CountQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm_eq :
  forall {σ : Type u} (countName : σ),
    Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName =
      Whatwg.Streams.Data.SizeAlgorithm.foreign countName)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_highWaterMark :
  forall {σ Size : Type u} (countName : σ)
    (self : Whatwg.Streams.Data.CountQueuingStrategy Size),
      (Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy countName self).highWaterMark =
        some self.highWaterMark)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_size :
  forall {σ Size : Type u} (countName : σ)
    (self : Whatwg.Streams.Data.CountQueuingStrategy Size),
      (Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy countName self).size =
        some countName)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.extract_size_algorithm :
  forall {σ Size : Type u} (countName : σ)
    (self : Whatwg.Streams.Data.CountQueuingStrategy Size),
      Whatwg.Streams.Data.extractSizeAlgorithm
          (Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy countName self) =
        Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName)

/-! "Let |steps| be the following steps: Return 1." The pinned WPT observes the
count size function returning `1` for `undefined`, `null`, a string, `{}`, a
chunk, a getter, and a getter that throws: it never reads its argument, which
is the quantification over every chunk below. -/
#check (@Whatwg.Streams.Data.CountQueuingStrategy.size_answers_one :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε),
      Whatwg.Streams.Data.CountSizeProfile sizes countName oracle -> forall chunk : α,
        Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
            (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk =
          Whatwg.Streams.Data.SizeAnswer.value sizes.one)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.size_ignores_chunk :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε),
      Whatwg.Streams.Data.CountSizeProfile sizes countName oracle -> forall left right : α,
        Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
            (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) left =
          Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
            (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) right)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.size_never_throws :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε),
      Whatwg.Streams.Data.CountSizeProfile sizes countName oracle ->
        forall (chunk : α) (reason : ε),
          Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
              (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk ≠
            Whatwg.Streams.Data.SizeAnswer.thrown reason)
#check (@Whatwg.Streams.Data.CountQueuingStrategy.enqueue_accepts :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (countName : σ)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α) (size : Size),
      Whatwg.Streams.Data.CountSizeProfile sizes countName oracle -> sizes.Ordered ->
        Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
            (Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm countName) chunk =
          Whatwg.Streams.Data.SizeAnswer.value size ->
            sizes.Admissible size)

#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark :
  forall {Size : Type u} (highWaterMark : Size),
    (Whatwg.Streams.Data.ByteLengthQueuingStrategy.make highWaterMark :
      Whatwg.Streams.Data.ByteLengthQueuingStrategy Size).highWaterMark = highWaterMark)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_accepts_nan :
  forall {Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    (Whatwg.Streams.Data.ByteLengthQueuingStrategy.make sizes.nan).highWaterMark = sizes.nan)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq :
  forall {σ : Type u} (byteLengthName : σ),
    Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName =
      Whatwg.Streams.Data.SizeAlgorithm.foreign byteLengthName)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_highWaterMark :
  forall {σ Size : Type u} (byteLengthName : σ)
    (self : Whatwg.Streams.Data.ByteLengthQueuingStrategy Size),
      (Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy
        byteLengthName self).highWaterMark = some self.highWaterMark)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size :
  forall {σ Size : Type u} (byteLengthName : σ)
    (self : Whatwg.Streams.Data.ByteLengthQueuingStrategy Size),
      (Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy byteLengthName self).size =
        some byteLengthName)

/-! "Return ? GetV(|chunk|, "`byteLength`")". The `?` propagates an abrupt
completion, and the pinned WPT observes all three answers: `1024` for a chunk
with the property, `undefined` for a chunk without it, and a re-thrown error
for a throwing getter. A total `α -> Size` cannot express two of the three. -/
#check (@Whatwg.Streams.Data.byteLengthSize_number :
  forall {ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (n : Size),
    Whatwg.Streams.Data.byteLengthSize sizes
        (Whatwg.Streams.Data.ByteLengthAnswer.number n : Whatwg.Streams.Data.ByteLengthAnswer Size ε) =
      Whatwg.Streams.Data.SizeAnswer.value n)
#check (@Whatwg.Streams.Data.byteLengthSize_undefined :
  forall {ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size),
    Whatwg.Streams.Data.byteLengthSize sizes
        (Whatwg.Streams.Data.ByteLengthAnswer.undefined :
          Whatwg.Streams.Data.ByteLengthAnswer Size ε) =
      Whatwg.Streams.Data.SizeAnswer.value sizes.nan)
#check (@Whatwg.Streams.Data.byteLengthSize_thrown :
  forall {ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (reason : ε),
    Whatwg.Streams.Data.byteLengthSize sizes
        (Whatwg.Streams.Data.ByteLengthAnswer.thrown reason :
          Whatwg.Streams.Data.ByteLengthAnswer Size ε) =
      Whatwg.Streams.Data.SizeAnswer.thrown reason)
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.size_eq_byteLength :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (byteLengthName : σ)
    (byteLength : α -> Whatwg.Streams.Data.ByteLengthAnswer Size ε)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε),
      Whatwg.Streams.Data.ByteLengthSizeProfile sizes byteLengthName byteLength oracle ->
        forall chunk : α,
          Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
              (Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName) chunk =
            Whatwg.Streams.Data.byteLengthSize sizes (byteLength chunk))

/-! The composite the pinned WPT forces: a chunk with no `byteLength` yields
`undefined`, the Web IDL conversion makes that `NaN`, and the enqueue that
follows refuses it with a `RangeError`. -/
#check (@Whatwg.Streams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused :
  forall {α σ ε Size : Type u} (sizes : Whatwg.Streams.Data.SizeClass Size) (byteLengthName : σ)
    (byteLength : α -> Whatwg.Streams.Data.ByteLengthAnswer Size ε)
    (oracle : σ -> α -> Whatwg.Streams.Data.SizeAnswer Size ε) (chunk : α)
    (q : Whatwg.Streams.Data.Queue α Size) (value : α),
      Whatwg.Streams.Data.ByteLengthSizeProfile sizes byteLengthName byteLength oracle ->
        sizes.Classified ->
          byteLength chunk = Whatwg.Streams.Data.ByteLengthAnswer.undefined ->
            Whatwg.Streams.Data.SizeAlgorithm.invoke sizes oracle
                (Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm byteLengthName)
                chunk =
              Whatwg.Streams.Data.SizeAnswer.value sizes.nan /\
            Whatwg.Streams.Data.enqueueValueWithSize sizes q value sizes.nan =
              Except.error Whatwg.Streams.Data.RangeError.rangeError)

/-! The theorem-shaped refusal of `DATA-FB-REALM`. The pinned WPT
`queuing-strategies-size-function-per-global.window.js` observes two realms
producing different size-function objects, whereas every Lean minting function
is a function of its argument. Realm distinctness is therefore the caller's
obligation, and every law above takes the name as an argument. -/
#check (@Whatwg.Streams.Data.realm_identity_refused :
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

def probeSizes : Whatwg.Streams.Data.SizeClass ProbeSize where
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

abbrev ProbeQueue := Whatwg.Streams.Data.Queue Nat ProbeSize

def probeEmpty : ProbeQueue := Whatwg.Streams.Data.Queue.empty probeSizes

def probeEnqueue (q : ProbeQueue) (v : Nat) (s : ProbeSize) : Option ProbeQueue :=
  Except.toOption (Whatwg.Streams.Data.enqueueValueWithSize probeSizes q v s)

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
    (fun q => q.entries.map Whatwg.Streams.Data.QueueEntry.value)) = some [1, 2]
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).map Whatwg.Streams.Data.Queue.totalSize) =
    some (ProbeSize.fin 8)
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).bind
    fun q => (Whatwg.Streams.Data.dequeueValue probeSizes q).map Prod.fst) = some 1
#guard (((probeEnqueue probeEmpty 1 (ProbeSize.fin 3)).bind
  fun q => probeEnqueue q 2 (ProbeSize.fin 5)).bind
    fun q => Whatwg.Streams.Data.peekQueueValue q) = some 1
#guard (Whatwg.Streams.Data.dequeueValue probeSizes probeEmpty).isNone
#guard (Whatwg.Streams.Data.peekQueueValue probeEmpty).isNone

/-! The clamp: a queue whose running total is below the head's size lands on
zero, never below it. -/
#guard ((Whatwg.Streams.Data.dequeueValue probeSizes
  ({ entries := [{ value := 1, size := ProbeSize.fin 5 }], totalSize := ProbeSize.fin 2 } :
    ProbeQueue)).map (fun r => r.snd.totalSize)) = some (ProbeSize.fin 0)

/-! Reset writes zero outright. -/
#guard (Whatwg.Streams.Data.resetQueue probeSizes
  ({ entries := [], totalSize := ProbeSize.fin 17 } : ProbeQueue)).totalSize =
    ProbeSize.fin 0

/-! The pinned WPT high-water-mark refusals, and the one value that separates
the two refusal sets. -/
def probeHWM (h : Option ProbeSize) : Option ProbeSize :=
  Except.toOption (Whatwg.Streams.Data.extractHighWaterMark probeSizes
    ({ highWaterMark := h, size := (none : Option Nat) } :
      Whatwg.Streams.Data.QueuingStrategy Nat ProbeSize) (ProbeSize.fin 1))

#guard (probeHWM (some ProbeSize.nan)).isNone
#guard (probeHWM (some ProbeSize.negInf)).isNone
#guard (probeHWM (some (ProbeSize.fin (-1)))).isNone
#guard probeHWM (some ProbeSize.posInf) = some ProbeSize.posInf
#guard probeHWM (some (ProbeSize.fin 7)) = some (ProbeSize.fin 7)
#guard probeHWM none = some (ProbeSize.fin 1)

/-! `ExtractSizeAlgorithm` defaults to the constant-one algorithm. -/
#guard (Whatwg.Streams.Data.extractSizeAlgorithm
  ({ highWaterMark := (none : Option ProbeSize), size := (none : Option Nat) } :
    Whatwg.Streams.Data.QueuingStrategy Nat ProbeSize)) =
      Whatwg.Streams.Data.SizeAlgorithm.one
#guard (Whatwg.Streams.Data.extractSizeAlgorithm
  ({ highWaterMark := (none : Option ProbeSize), size := some (9 : Nat) } :
    Whatwg.Streams.Data.QueuingStrategy Nat ProbeSize)) =
      Whatwg.Streams.Data.SizeAlgorithm.foreign 9

/-! `ByteLengthAnswer.undefined` becomes `NaN`, which the enqueue refuses. -/
#guard (Whatwg.Streams.Data.byteLengthSize probeSizes
  (Whatwg.Streams.Data.ByteLengthAnswer.undefined :
    Whatwg.Streams.Data.ByteLengthAnswer ProbeSize Nat)) =
      Whatwg.Streams.Data.SizeAnswer.value ProbeSize.nan

end ExecutableFalsifiers

end WhatwgTest.Streams.Data.QueueContract
