import Whatwg.Streams

/-
Contract packet: `test/contracts/queue-with-sizes.contract.md`

Breaker-owned red axiom report for P3. The implementation phase must not edit
this file. It is red until `Whatwg/Streams/Data/Queue.lean` and
`Whatwg/Streams/Data/Strategy.lean` declare the frozen surface.

Every theorem named below must have a kernel receipt inside the semantic
ceiling: `none`, `propext`, `Quot.sound`, or `propext, Quot.sound`. Anything
else is a finding, not a note. `WhatwgTest/Audit/AxiomGate.lean` is the
exhaustive gate over the whole compiled environment; this module is the
per-packet human-readable receipt list, and the two are independent.

The list is the ninety-nine public theorems of the contract's section 9, in
battery order. A theorem that is here and not in the battery, or in the battery
and not here, is a defect in this packet.
-/

set_option autoImplicit false

-- See the same note in `QueueContract.lean`: the full red-phase diagnostic
-- list is obtained with `lake env lean -DmaxErrors=10000` on this file, not
-- with an in-file option, which the frontend's error counter does not read.

namespace WhatwgTest.Streams.Data.QueueAxiomReport

/-! ## S1 — classification and admission -/

#print axioms Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_eq
#print axioms Whatwg.Streams.Data.SizeClass.isPositiveInfinity_eq
#print axioms Whatwg.Streams.Data.SizeClass.admissible_iff
#print axioms Whatwg.Streams.Data.SizeClass.not_admissible_nan
#print axioms Whatwg.Streams.Data.SizeClass.not_admissible_posInfinity
#print axioms Whatwg.Streams.Data.SizeClass.not_admissible_negInfinity
#print axioms Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_nan
#print axioms Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_negInfinity
#print axioms Whatwg.Streams.Data.SizeClass.isNonNegativeNumber_posInfinity
#print axioms Whatwg.Streams.Data.SizeClass.clampNonNegative_of_negative
#print axioms Whatwg.Streams.Data.SizeClass.clampNonNegative_of_nonneg
#print axioms Whatwg.Streams.Data.SizeClass.clampNonNegative_not_negative

/-! ## S2 — the queue carrier and the sum -/

#print axioms Whatwg.Streams.Data.Queue.empty_entries
#print axioms Whatwg.Streams.Data.Queue.empty_totalSize
#print axioms Whatwg.Streams.Data.sizeSum_nil
#print axioms Whatwg.Streams.Data.sizeSum_append_singleton
#print axioms Whatwg.Streams.Data.sizeSum_cons
#print axioms Whatwg.Streams.Data.sizeSum_admissible
#print axioms Whatwg.Streams.Data.Queue.WF_iff
#print axioms Whatwg.Streams.Data.Queue.WF_empty
#print axioms Whatwg.Streams.Data.Queue.SizesAdmissible_iff
#print axioms Whatwg.Streams.Data.Queue.SizesAdmissible_empty

/-! ## S3 — enqueue -/

#print axioms Whatwg.Streams.Data.enqueueValueWithSize_error_iff
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_error_iff_not_admissible
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_refuses_nan
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_refuses_negative
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_refuses_posInfinity
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_refuses_negInfinity
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_ok_iff
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_eq_of_admissible
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_entries
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_totalSize
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_length
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_sizesAdmissible
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_totalSize_admissible
#print axioms Whatwg.Streams.Data.enqueueValueWithSize_wf

/-! ## S4 — dequeue -/

#print axioms Whatwg.Streams.Data.dequeueValue_nil
#print axioms Whatwg.Streams.Data.dequeueValue_cons
#print axioms Whatwg.Streams.Data.dequeueValue_isSome_iff
#print axioms Whatwg.Streams.Data.dequeueValue_isNone_iff
#print axioms Whatwg.Streams.Data.dequeueValue_value_eq_head
#print axioms Whatwg.Streams.Data.dequeueValue_entries
#print axioms Whatwg.Streams.Data.dequeueValue_length
#print axioms Whatwg.Streams.Data.dequeueValue_totalSize
#print axioms Whatwg.Streams.Data.dequeueValue_totalSize_not_negative
#print axioms Whatwg.Streams.Data.dequeueValue_sizesAdmissible
#print axioms Whatwg.Streams.Data.dequeueValue_wf
#print axioms Whatwg.Streams.Data.dequeueValue_clamp_unreachable_of_exact

/-! ## S5 — FIFO and peek -/

#print axioms Whatwg.Streams.Data.peekQueueValue_nil
#print axioms Whatwg.Streams.Data.peekQueueValue_cons
#print axioms Whatwg.Streams.Data.peekQueueValue_eq_head
#print axioms Whatwg.Streams.Data.peekQueueValue_agrees_dequeueValue
#print axioms Whatwg.Streams.Data.peekQueueValue_isSome_iff
#print axioms Whatwg.Streams.Data.dequeueValue_enqueueValueWithSize_empty
#print axioms Whatwg.Streams.Data.dequeueValue_enqueueValueWithSize_nonempty
#print axioms Whatwg.Streams.Data.peekQueueValue_enqueueValueWithSize_nonempty

/-! ## S6 — reset -/

#print axioms Whatwg.Streams.Data.resetQueue_eq
#print axioms Whatwg.Streams.Data.resetQueue_entries
#print axioms Whatwg.Streams.Data.resetQueue_totalSize
#print axioms Whatwg.Streams.Data.resetQueue_wf
#print axioms Whatwg.Streams.Data.resetQueue_sizesAdmissible
#print axioms Whatwg.Streams.Data.resetQueue_idempotent
#print axioms Whatwg.Streams.Data.resetQueue_eq_empty
#print axioms Whatwg.Streams.Data.resetQueue_dequeueValue

/-! ## S7 — the extraction algorithms -/

#print axioms Whatwg.Streams.Data.extractHighWaterMark_absent
#print axioms Whatwg.Streams.Data.extractHighWaterMark_error_iff
#print axioms Whatwg.Streams.Data.extractHighWaterMark_refuses_nan
#print axioms Whatwg.Streams.Data.extractHighWaterMark_refuses_negative
#print axioms Whatwg.Streams.Data.extractHighWaterMark_refuses_negInfinity
#print axioms Whatwg.Streams.Data.extractHighWaterMark_allows_posInfinity
#print axioms Whatwg.Streams.Data.extractHighWaterMark_id_on_accepted
#print axioms Whatwg.Streams.Data.extractHighWaterMark_disagrees_with_enqueue_on_posInfinity
#print axioms Whatwg.Streams.Data.extractSizeAlgorithm_absent
#print axioms Whatwg.Streams.Data.extractSizeAlgorithm_present
#print axioms Whatwg.Streams.Data.SizeAlgorithm.invoke_one
#print axioms Whatwg.Streams.Data.SizeAlgorithm.invoke_foreign
#print axioms Whatwg.Streams.Data.extractSizeAlgorithm_absent_invoke

/-! ## S8 — the built-in strategies and their profiles -/

#print axioms Whatwg.Streams.Data.CountQueuingStrategy.make_highWaterMark
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.make_does_not_validate
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.make_accepts_nan
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.sizeAlgorithm_eq
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_highWaterMark
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.toQueuingStrategy_size
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.extract_size_algorithm
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.size_answers_one
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.size_ignores_chunk
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.size_never_throws
#print axioms Whatwg.Streams.Data.CountQueuingStrategy.enqueue_accepts
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_highWaterMark
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.make_accepts_nan
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_highWaterMark
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size
#print axioms Whatwg.Streams.Data.byteLengthSize_number
#print axioms Whatwg.Streams.Data.byteLengthSize_undefined
#print axioms Whatwg.Streams.Data.byteLengthSize_thrown
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.size_eq_byteLength
#print axioms Whatwg.Streams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused
#print axioms Whatwg.Streams.Data.realm_identity_refused

end WhatwgTest.Streams.Data.QueueAxiomReport
