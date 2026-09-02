import WhatwgStreams

/-
Contract packet: `test/contracts/queue-with-sizes.contract.md`

Breaker-owned red axiom report for P3. The implementation phase must not edit
this file. It is red until `WhatwgStreams/Data/Queue.lean` and
`WhatwgStreams/Data/Strategy.lean` declare the frozen surface.

Every theorem named below must have a kernel receipt inside the semantic
ceiling: `none`, `propext`, `Quot.sound`, or `propext, Quot.sound`. Anything
else is a finding, not a note. `WhatwgStreamsTest/Audit/AxiomGate.lean` is the
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

namespace WhatwgStreamsTest.Data.QueueAxiomReport

/-! ## S1 — classification and admission -/

#print axioms WhatwgStreams.Data.SizeClass.isNonNegativeNumber_eq
#print axioms WhatwgStreams.Data.SizeClass.isPositiveInfinity_eq
#print axioms WhatwgStreams.Data.SizeClass.admissible_iff
#print axioms WhatwgStreams.Data.SizeClass.not_admissible_nan
#print axioms WhatwgStreams.Data.SizeClass.not_admissible_posInfinity
#print axioms WhatwgStreams.Data.SizeClass.not_admissible_negInfinity
#print axioms WhatwgStreams.Data.SizeClass.isNonNegativeNumber_nan
#print axioms WhatwgStreams.Data.SizeClass.isNonNegativeNumber_negInfinity
#print axioms WhatwgStreams.Data.SizeClass.isNonNegativeNumber_posInfinity
#print axioms WhatwgStreams.Data.SizeClass.clampNonNegative_of_negative
#print axioms WhatwgStreams.Data.SizeClass.clampNonNegative_of_nonneg
#print axioms WhatwgStreams.Data.SizeClass.clampNonNegative_not_negative

/-! ## S2 — the queue carrier and the sum -/

#print axioms WhatwgStreams.Data.Queue.empty_entries
#print axioms WhatwgStreams.Data.Queue.empty_totalSize
#print axioms WhatwgStreams.Data.sizeSum_nil
#print axioms WhatwgStreams.Data.sizeSum_append_singleton
#print axioms WhatwgStreams.Data.sizeSum_cons
#print axioms WhatwgStreams.Data.sizeSum_admissible
#print axioms WhatwgStreams.Data.Queue.WF_iff
#print axioms WhatwgStreams.Data.Queue.WF_empty
#print axioms WhatwgStreams.Data.Queue.SizesAdmissible_iff
#print axioms WhatwgStreams.Data.Queue.SizesAdmissible_empty

/-! ## S3 — enqueue -/

#print axioms WhatwgStreams.Data.enqueueValueWithSize_error_iff
#print axioms WhatwgStreams.Data.enqueueValueWithSize_error_iff_not_admissible
#print axioms WhatwgStreams.Data.enqueueValueWithSize_refuses_nan
#print axioms WhatwgStreams.Data.enqueueValueWithSize_refuses_negative
#print axioms WhatwgStreams.Data.enqueueValueWithSize_refuses_posInfinity
#print axioms WhatwgStreams.Data.enqueueValueWithSize_refuses_negInfinity
#print axioms WhatwgStreams.Data.enqueueValueWithSize_ok_iff
#print axioms WhatwgStreams.Data.enqueueValueWithSize_eq_of_admissible
#print axioms WhatwgStreams.Data.enqueueValueWithSize_entries
#print axioms WhatwgStreams.Data.enqueueValueWithSize_totalSize
#print axioms WhatwgStreams.Data.enqueueValueWithSize_length
#print axioms WhatwgStreams.Data.enqueueValueWithSize_sizesAdmissible
#print axioms WhatwgStreams.Data.enqueueValueWithSize_totalSize_admissible
#print axioms WhatwgStreams.Data.enqueueValueWithSize_wf

/-! ## S4 — dequeue -/

#print axioms WhatwgStreams.Data.dequeueValue_nil
#print axioms WhatwgStreams.Data.dequeueValue_cons
#print axioms WhatwgStreams.Data.dequeueValue_isSome_iff
#print axioms WhatwgStreams.Data.dequeueValue_isNone_iff
#print axioms WhatwgStreams.Data.dequeueValue_value_eq_head
#print axioms WhatwgStreams.Data.dequeueValue_entries
#print axioms WhatwgStreams.Data.dequeueValue_length
#print axioms WhatwgStreams.Data.dequeueValue_totalSize
#print axioms WhatwgStreams.Data.dequeueValue_totalSize_not_negative
#print axioms WhatwgStreams.Data.dequeueValue_sizesAdmissible
#print axioms WhatwgStreams.Data.dequeueValue_wf
#print axioms WhatwgStreams.Data.dequeueValue_clamp_unreachable_of_exact

/-! ## S5 — FIFO and peek -/

#print axioms WhatwgStreams.Data.peekQueueValue_nil
#print axioms WhatwgStreams.Data.peekQueueValue_cons
#print axioms WhatwgStreams.Data.peekQueueValue_eq_head
#print axioms WhatwgStreams.Data.peekQueueValue_agrees_dequeueValue
#print axioms WhatwgStreams.Data.peekQueueValue_isSome_iff
#print axioms WhatwgStreams.Data.dequeueValue_enqueueValueWithSize_empty
#print axioms WhatwgStreams.Data.dequeueValue_enqueueValueWithSize_nonempty
#print axioms WhatwgStreams.Data.peekQueueValue_enqueueValueWithSize_nonempty

/-! ## S6 — reset -/

#print axioms WhatwgStreams.Data.resetQueue_eq
#print axioms WhatwgStreams.Data.resetQueue_entries
#print axioms WhatwgStreams.Data.resetQueue_totalSize
#print axioms WhatwgStreams.Data.resetQueue_wf
#print axioms WhatwgStreams.Data.resetQueue_sizesAdmissible
#print axioms WhatwgStreams.Data.resetQueue_idempotent
#print axioms WhatwgStreams.Data.resetQueue_eq_empty
#print axioms WhatwgStreams.Data.resetQueue_dequeueValue

/-! ## S7 — the extraction algorithms -/

#print axioms WhatwgStreams.Data.extractHighWaterMark_absent
#print axioms WhatwgStreams.Data.extractHighWaterMark_error_iff
#print axioms WhatwgStreams.Data.extractHighWaterMark_refuses_nan
#print axioms WhatwgStreams.Data.extractHighWaterMark_refuses_negative
#print axioms WhatwgStreams.Data.extractHighWaterMark_refuses_negInfinity
#print axioms WhatwgStreams.Data.extractHighWaterMark_allows_posInfinity
#print axioms WhatwgStreams.Data.extractHighWaterMark_id_on_accepted
#print axioms WhatwgStreams.Data.extractHighWaterMark_disagrees_with_enqueue_on_posInfinity
#print axioms WhatwgStreams.Data.extractSizeAlgorithm_absent
#print axioms WhatwgStreams.Data.extractSizeAlgorithm_present
#print axioms WhatwgStreams.Data.SizeAlgorithm.invoke_one
#print axioms WhatwgStreams.Data.SizeAlgorithm.invoke_foreign
#print axioms WhatwgStreams.Data.extractSizeAlgorithm_absent_invoke

/-! ## S8 — the built-in strategies and their profiles -/

#print axioms WhatwgStreams.Data.CountQueuingStrategy.make_highWaterMark
#print axioms WhatwgStreams.Data.CountQueuingStrategy.make_does_not_validate
#print axioms WhatwgStreams.Data.CountQueuingStrategy.make_accepts_nan
#print axioms WhatwgStreams.Data.CountQueuingStrategy.sizeAlgorithm_eq
#print axioms WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy_highWaterMark
#print axioms WhatwgStreams.Data.CountQueuingStrategy.toQueuingStrategy_size
#print axioms WhatwgStreams.Data.CountQueuingStrategy.extract_size_algorithm
#print axioms WhatwgStreams.Data.CountQueuingStrategy.size_answers_one
#print axioms WhatwgStreams.Data.CountQueuingStrategy.size_ignores_chunk
#print axioms WhatwgStreams.Data.CountQueuingStrategy.size_never_throws
#print axioms WhatwgStreams.Data.CountQueuingStrategy.enqueue_accepts
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.make_highWaterMark
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.make_accepts_nan
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.sizeAlgorithm_eq
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_highWaterMark
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.toQueuingStrategy_size
#print axioms WhatwgStreams.Data.byteLengthSize_number
#print axioms WhatwgStreams.Data.byteLengthSize_undefined
#print axioms WhatwgStreams.Data.byteLengthSize_thrown
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.size_eq_byteLength
#print axioms WhatwgStreams.Data.ByteLengthQueuingStrategy.undefined_byteLength_refused
#print axioms WhatwgStreams.Data.realm_identity_refused

end WhatwgStreamsTest.Data.QueueAxiomReport
