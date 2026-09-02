# WhatwgStreams counterexample register

Stable IDs in this file are never reused. A row closes only when its witness
is retained and the repaired declaration or theorem mechanically rejects the
attack. Statuses are defined in `README.md` beside this file.

| ID | Status | Attacked statement | Witness / evidence | Forced repair |
| --- | --- | --- | --- | --- |
| `WS-SHA-CE-001` | `CLOSED` | `Sha256.Spec.H0` is FIPS 180-4 §5.3.3 and not §5.3.2 | `WhatwgStreamsTest/Counterexamples/Sha/Mutants.lean`, `ce001_sha224IV` with its control `ce001_control`; `Sha256.Bridge.sha256_ne_sha224_iv` on the constants | none: the shipped `H0` is §5.3.3, and the witness pins that the choice is load-bearing |
| `WS-SHA-CE-002` | `CLOSED` | `Sha256.Impl.padBytes` appends the 64-bit big-endian length of FIPS 180-4 §5.1.1 | same file, `ce002_noLengthField` on W2, with `ce002_padBytes_eq_on_empty` proving why W1 cannot discriminate | none to the implementation; the contract's claim that W1 catches this mutant is corrected in `test/counterexamples/sha/ATTACKS.md` |
| `WS-SHA-CE-003` | `CLOSED` | `Sha256.Impl.wordOfBytes` reads four bytes big-endian per FIPS 180-4 §3.1 | same file, `ce003_littleEndianWords` on W2 | none: the shipped reading is big-endian |
| `WS-SHA-CE-004` | `CLOSED` | `Sha256.Spec.bitsOfByte` is most-significant-bit-first per FIPS 180-4 §3.1, not FIPS 202 Appendix B.1's least-significant-first | same file, `ce004_lsbFirstBitOrder` on W1, with `ce004_padMarker` identifying the mutant's `0x01` padding byte | none: `Sha256.Spec` reproduces rather than imports foldlab's `formal/fips202` conversion, precisely because the conventions differ |
| `WS-SHA-CE-005` | `CLOSED` | `Sha256.Impl.sha224` keeps the **left-most** 28 bytes of the untruncated output, per FIPS 180-4 §6.3 exception 2 | same file, `ce005_rightmostTruncation` on the SHA-224 `Len = 0` vector, with its control `ce005_control` and the statement of the shipped truncation `ce005_truncation_is_leftmost` | none: the shipped truncation is the left-most, and the witness pins that the byte range is load-bearing |
| `WS-DATA-CE-001` | `CLOSED` | `[[queueTotalSize]]` equals the sum of the sizes in `[[queue]]`, for the specification's own carrier | `WhatwgStreamsTest/Counterexamples/Data/Queue.lean`, `ce001_wf_broken` with `ce001_exact_total`, `ce001_rounded_total`, `ce001_gap`, `ce001_carriers_disagree`; the M1 half is `ce001_desired_size_exact` and `ce001_desired_size_rounded`; the step-6 half is `ce001_clamp_reachable_rounded` and `ce001_clamp_unreachable_exact` | rule `P3-R1`; state every invariant law under a `SizeClass.Exact` hypothesis, so a rounding instance loses the law instead of falsifying it. Closes when the ruled instance lands and `dequeueValue_wf` is proved against it |
| `WS-DATA-CE-002` | `CLOSED` | the fold direction of `sizeSum` is a matter of taste | same file, `ce002_folds_differ_rounded` with `ce002_left_fold_rounded`, `ce002_right_fold_rounded`, and the agreeing exact case `ce002_folds_agree_exact` | fold left, from `zero`, in the order `EnqueueValueWithSize` accumulates |
| `WS-DATA-CE-003` | `CLOSED` | a negative size may be appended and subtracted back later | same file, `ce003_mutant_accepts` with `ce003_reference_refuses`, `ce003_mutant_total_negative`, `ce003_wpt_minus_one_refused` | refuse before the append, with a `RangeError`, per `op.enqueue-value-with-size` step 2 |
| `WS-DATA-CE-004` | `CLOSED` | `DequeueValue` may return a default on an empty queue, since the emptiness condition is an assertion | same file, `ce004_mutant_answers` with `ce004_reference_refuses` and `ce004_agree_when_nonempty`, which proves no non-empty case discriminates the two | `Option` result, with `dequeueValue_isNone_iff` pinning refusal to exactly the empty queue |
| `WS-DATA-CE-005` | `CLOSED` | `PeekQueueValue` may thread the container through its result | same file, `ce005_mutant_mutates` and `ce005_mutant_not_idempotent`, with `ce005_mutant_same_value` proving a value-only comparison is blind to it | freeze the result type as `Option α` with no `SizeClass` argument, so the mutation is not expressible |
| `WS-DATA-CE-006` | `CLOSED` | `ResetQueue` may preserve a running total it has been carrying | same file, `ce006_mutant_keeps` with `ce006_reference_zeroes`, `ce006_entries_agree`, `ce006_reset_restores_invariant` | write `zero` outright; `resetQueue_wf` is the one invariant law with no carrier hypothesis |
| `WS-DATA-CE-007` | `CLOSED` | the `NaN`, `+∞` and negative refusal laws are satisfiable on a carrier that has no `NaN` and no infinities | same file, `ce007_nan_refusal_is_vacuous`, with `ce007_wpt_sizes_all_refused` over the pinned WPT list `[NaN, -Infinity, Infinity, -1]` | make `nan`, `posInfinity` and `negInfinity` fields of `SizeClass` and classify each in `SizeClass.Classified`, so an instance must exhibit them |
| `WS-DATA-CE-008` | `CLOSED` | one refusal predicate serves both `EnqueueValueWithSize` and `ExtractHighWaterMark` | same file, `ce008_mutant_refuses_pos_inf` with `ce008_reference_allows_pos_inf`, `ce008_rules_agree_off_pos_inf`, `ce008_wpt_hwms_all_refused` | two predicates; `+∞` refused as a size and accepted as a high water mark, frozen together in `extractHighWaterMark_disagrees_with_enqueue_on_posInfinity` |
| `WS-DATA-CE-009` | `CLOSED` | `ExtractHighWaterMark` normalizes its input, as its anchor id `validate-and-normalize-high-water-mark` suggests | same file, `ce009_mutant_changes_pos_inf` with `ce009_reference_is_the_identity_on_accepted` and `ce009_mutant_is_still_idempotent`, which proves an idempotence law does not catch the mutant | freeze `extractHighWaterMark_id_on_accepted`; there is no normalization step and no such algorithm at this pin |
| `WS-DATA-CE-010` | `CLOSED` | the queue may be a stack | same file, `ce010_mutant_is_lifo` with `ce010_reference_is_fifo`, `ce010_totals_agree`, `ce010_lengths_agree`, `ce010_peek_dequeue_agree_reference` | append on enqueue, remove index `0` on dequeue; totals, lengths and multisets do not separate the two |

Every row's evidence command is `lake build WhatwgStreamsTest`, which
elaborates the witnesses. Each inequality is closed by `decide +kernel`, so it
is checked by the Lean kernel with no compiler in the trust path, and the
expected digests come from `Sha256.Kats`, produced mechanically from the sealed
`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp` and, for `WS-SHA-CE-005`,
`vendor/nist-cavp-sha224/SHA224ShortMsg.rsp`. The attack shapes are described in
`test/counterexamples/sha/ATTACKS.md`.

The `WS-DATA-*` rows were minted by the P3 queue-with-sizes breaker, 2026-09-02,
and are the first rows outside the `SHA` area. Their evidence command is
`lake build WhatwgStreamsTest.Counterexamples.Data.Queue`, which elaborates the
witnesses; each is closed by `decide`, so it is checked by the Lean kernel with
no compiler in the trust path, and every receipt is `none` or `propext`. The
attack shapes are described in `test/counterexamples/data/ATTACKS.md` and the
frozen surface they force is `test/contracts/queue-with-sizes.contract.md`.

The witnesses are breaker models in a `Breaker` namespace, not the production
declarations: they prove the attacks rather than the laws. The ten `WS-DATA-*`
rows closed 2026-09-02 when the P3 builder landed the frozen surface with all
99 theorems proved and the coordinator landed the ruled `P3-R1` instance
`WhatwgStreams.Data.DyadicSize`; each row's forced repair is now a theorem of
`WhatwgStreams.Data` with its receipt in `WhatwgStreamsTest/Data/QueueAxiomReport.lean`.
