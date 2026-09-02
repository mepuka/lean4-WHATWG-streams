# Queue-with-sizes proof graph (`DATA-PG-QUEUE`, phase P3)

Status: **breaker-authored 2026-09-02, awaiting the `P3-R1` ruling.** This
document owns the proof graph, the existing-type rows, and the per-row census
map for the queue-with-sizes and queuing-strategy family. It states no
coverage number: `WhatwgTest/Audit/SpecCoverage.lean` owns coverage
states and `docs/SPEC-COVERAGE.md` owns the rules.

Contract packet: `test/contracts/queue-with-sizes.contract.md`
Lean battery: `WhatwgTest/Streams/Data/QueueContract.lean`
Axiom report: `WhatwgTest/Streams/Data/QueueAxiomReport.lean`
Counterexamples: `WS-DATA-CE-001` .. `WS-DATA-CE-010`
Implementation fence: `Whatwg/Streams/Data/Queue.lean`,
`Whatwg/Streams/Data/Strategy.lean`

Pins: `vendor/whatwg-streams-b9ba9f49/index.bs` for the semantics,
`vendor/wpt-480fdfcd/streams/` for the host corpus. Rows are cited by census
row id from `generated/spec-algorithm-census.tsv` with the span digest that
file records.

## 1. Why this family gets a graph and not a leaf

`docs/AGENT-ROUTING.md` allows a leaf-receipt route only for a passive value
record with no checked invariant and no admission, judgment, or composition
law. This family fails that test on four independent counts, any one of which
would be enough:

- `EnqueueValueWithSize` and `ExtractHighWaterMark` each **admit or refuse**,
  with a `RangeError`, and their refusal sets differ;
- the relation between `[[queueTotalSize]]` and the sizes in `[[queue]]` is a
  **checked invariant** whose truth depends on the arithmetic carrier;
- the two built-in size functions are a **foreign boundary** entering as named
  decisions with profiles;
- the operations carry **composition laws** — FIFO order, the agreement of
  peek with dequeue, invariant preservation across an enqueue/dequeue run.

## 2. Ruling request `P3-R1` — which carrier is `Size`?

**Stated by the breaker, not decided.** The evidence, the three options and
what each can and cannot prove are in section 6 of the contract packet, which
is the authority. The summary here exists so a reader of this graph knows
which edges the ruling moves.

**Default: option (i)**, an exact carrier extended with `nan`, `posInfinity`
and `negInfinity`; the host's rounding becomes `DATA-FB-ROUNDING` below and
the four `floating-point-total-queue-size` WPT cases become host-only rows
under mask M1.

The disagreement is pinned to one case and one number: enqueue `1e-16`,
enqueue `1`, dequeue `1e-16`; binary64 lands on `9007199254740991 * 2^(-53)`
and exact arithmetic lands on `1`, a gap of exactly one ulp of `1.0`. The
witness is proved and green today in
`WhatwgTest/Streams/Counterexamples/Data/Queue.lean`.

Two secondary findings constrain the answer:

- option (iii), `Nat`-only sizes, is **refuted by the pinned text**, not merely
  costly: `+∞` is an explicitly allowed high water mark and `Nat` cannot
  represent it, and every refusal law is vacuous on a carrier with no `NaN`;
- option (ii) cannot be Lean's `Float`. `Float` operations are opaque `extern`
  constants, no equation between two of them reduces in the kernel, and the
  only tactic that decides one is `native_decide`, forbidden by
  `WhatwgTest/Audit/AxiomGate.lean`. Option (ii) means a **modelled**
  binary64 with rounding, subnormals and overflow.

If the ruling goes to option (ii), exactly three of the ninety-nine frozen
theorems become inapplicable, because they are the only three carrying a
`SizeClass.Exact` hypothesis: `sizeSum_cons`, `dequeueValue_wf`, and
`dequeueValue_clamp_unreachable_of_exact`. `enqueueValueWithSize_wf` and
`Queue.WF_empty` survive unchanged — enqueue's running total takes the same
step the left fold takes, so it cannot drift whatever the arithmetic. The
`laws` edge below then closes on the order, FIFO and refusal laws alone. No
signature and no other statement changes; that is the whole point of
parameterizing the carrier.

Two further questions the packet raises and does not decide, `P3-R2` (one
exception carrier or one per calculus) and `P3-R3` (whether `sizeSum` is
public), are in section 13 of the packet.

## 3. Existing-type rows

Every row records: stable public Lean name and owning module; role; the
specification anchor it models, by census row id and that row's span digest;
the contract that fixes its role; its `SPEC-MANIFEST.md` disposition; its
relationship to any canonical owner; and its assurance route. All rows below
are owned by `test/contracts/queue-with-sizes.contract.md` and route to
`DATA-PG-QUEUE` unless stated otherwise.

| # | Name and module | Role | Spec anchor (census row, span digest) | Disposition | Relationship |
| --- | --- | --- | --- | --- | --- |
| 1 | `Whatwg.Streams.Data.QueueEntry`, `Whatwg/Streams/Data/Queue.lean` | canonical carrier of the `value-with-size` struct | `slot.queue` (`9aaacc5116b7bb3286be79af6c3a0b7393f8b06f2a41e55c334036ace015e5b7`), whose section text defines "a value-with-size is a struct with the two items value and size" | `owned` | `canonical`; nothing else in the estate carries a sized chunk |
| 2 | `Whatwg.Streams.Data.Queue`, same module | canonical carrier of the paired `[[queue]]` / `[[queueTotalSize]]` slots | `slot.queue` and `slot.queue-total-size` (`f0d6bce926812e0c273583abd237b16959d31ab1169c6c2b30f0f0268f5b0659`) | `owned` | `canonical`. The two slots are one type because the pinned text calls them "two paired internal slots, always named" together and gives four operations that keep them synchronized |
| 3 | `Whatwg.Streams.Data.SizeClass`, same module | the arithmetic and classification interface of the ECMAScript Number that `[[queueTotalSize]]` is | `slot.queue-total-size`, "a JavaScript Number, i.e. a double-precision floating point number" | `owned`, with `DATA-FB-ROUNDING` naming what is dropped | `separate-calculus` from any concrete numeric type. It is an interface record, not a carrier: the carrier arrives with `P3-R1` |
| 4 | `Whatwg.Streams.Data.RangeError`, same module | the refusal tag of this calculus | the `{{RangeError}}` mentions inside `op.enqueue-value-with-size` (`bf25987f0b75df7b2f0a69b92b799663d0d94799db9e96beb6c28e63b9f5035c`) and `op.validate-and-normalize-high-water-mark` (`d9303084d19b298241323f639194c712749ed58918a76c12407a64ef58940c25`) | `owned` | `canonical` for this calculus only. `P3-R2` asks whether P4's `TypeError` widens it or embeds into it; the recommendation is an embedding theorem, not a widening |
| 5 | `Whatwg.Streams.Data.SizeAlgorithm`, `Whatwg/Streams/Data/Strategy.lean` | the two shapes `ExtractSizeAlgorithm` returns: the constant-one algorithm, and a named foreign callback | `op.make-size-algorithm-from-size-function` (`1a5e282855cfe10300f0c72ba41fe2fa9b6120e5a5d45d363c6b829d48b4f9f4`) | `owned` | `canonical`. It carries a **name**, never a stored Lean function, per DB-02 |
| 6 | `Whatwg.Streams.Data.SizeAnswer`, same module | the typed decision a size callback returns: a value or a throw | `idl.queuing-strategy-size` (`93b7680395a7353da0f07ca3596f991d9c6016671c27f1b363b774da407bfa01`), the callback type `unrestricted double (any chunk)`, read together with the pinned WPT throwing-callback cases | `hostOnly` at the IDL boundary; the answer alphabet is `owned` | `canonical` foreign-boundary answer type for this packet. P4 and P5 reuse it rather than minting a second |
| 7 | `Whatwg.Streams.Data.ByteLengthAnswer`, same module | the three answers `GetV(chunk, "byteLength")` can give: a number, `undefined`, or a throw | `op.byte-length-queuing-strategy-size-function` (span `325318..326376`) | `foreignBoundary` | `view` of `SizeAnswer` through the Web IDL unrestricted-double conversion; `byteLengthSize` is the conversion, and `undefined` maps to `nan` |
| 8 | `Whatwg.Streams.Data.QueuingStrategy`, same module | the `QueuingStrategy` dictionary as seen by the two extraction algorithms | `idl.queuing-strategy` (`57409b2926c5fb9209b87fcc5258a0f4142ec4c49383e99042700e4e97c2f0d1`), members `idl.queuingstrategy-high-water-mark` and `idl.queuingstrategy-size` | IDL members `hostOnly`; the dictionary as consumed by `qs-abstract-ops` is `owned` | `canonical`. Both fields are `Option` because the algorithms branch on "does not exist", which is not a present `undefined` |
| 9 | `Whatwg.Streams.Data.CountQueuingStrategy`, same module | the class's one internal slot | `op.cqs-constructor` (`de1004ef5fa453cafaa4d6547d7a897458724ad48615edf940ed2f607b5a4b99`) and `op.cqs-high-water-mark` (`8d27fa67d52c8bb2c3ce70f320396b0b810b3cba8bfd4a9a08a4b0d72b91a886`) | `owned`; its IDL members `hostOnly` | `canonical`. Not a `view` of `QueuingStrategy`: it is a class with one slot, and `toQueuingStrategy` is the named conversion |
| 10 | `Whatwg.Streams.Data.ByteLengthQueuingStrategy`, same module | the same, for the byte-length class | `op.blqs-constructor` (`41cc2f42f4c500b7d1dceac0206678d34c17760463fda3ca8a150fa004ad1831`), `op.blqs-high-water-mark` (`9a7624ba35a0d5801efd5b10a038f4a19d78db5d19bec4bc105facaeac07e981`), slot `slot.high-water-mark` (`031fc84bad2024528c52bc137f7b7deb0ffed9e3f20fc25ccae81b3eec82aabb`) | `owned`; IDL members `hostOnly` | `canonical`, deliberately **separate** from row 9. The two classes have the same shape and different size functions; identifying them would erase the one difference that matters |
| 11 | `Whatwg.Streams.Data.CountSizeProfile` and `Whatwg.Streams.Data.ByteLengthSizeProfile`, same module | foreign-boundary profiles: what the oracle must answer for each built-in size function | `op.count-queuing-strategy-size-function` (span `329962..330954`) and `op.byte-length-queuing-strategy-size-function` | `foreignBoundary` | `canonical` profiles. They are `Prop`s about a supplied oracle, never modelled bodies |

Rows 9 and 10 both claim `slot.high-water-mark`-shaped anchors. They do not
collide: the pinned bytes give `ByteLengthQueuingStrategy`'s slot its own
`<dfn for=…>` at `blqs-internal-slots` and `CountQueuingStrategy`'s at
`cqs-internal-slots`, and the census carries `slot.high-water-mark` for the
first only. Row 9's anchor is therefore its constructor and getter rows, not a
slot row. Whether the census should carry a second slot row for
`CountQueuingStrategy` is a P1.1 question and is recorded as such below.

## 4. Foreign-boundary rows

Each names exactly what this packet drops rather than models.

| Id | What is dropped | Why | How it re-enters |
| --- | --- | --- | --- |
| `DATA-FB-ROUNDING` | the ECMAScript Number carrier and the rounding of its arithmetic | the pinned text says `[[queueTotalSize]]` is a double and warns that the running total is not the sum of the sizes; under the default ruling the model is exact and cannot reproduce that | as host-profile rows in the harness ledger for the four `floating-point-total-queue-size` cases, under mask M1, with `WS-DATA-CE-001` as the pre-registered disagreement |
| `DATA-FB-IDL-DOUBLE` | the Web IDL conversion of a JavaScript value to `unrestricted double` | `'foo'` and `{}` become `NaN`, `true` becomes `1`, `'0'` becomes `0`; this is the IDL layer, `hostOnly` in `SPEC-MANIFEST.md` | the pinned WPT `highWaterMarkConversions` table is a host observation; the model receives the already-converted value |
| `DATA-FB-REALM` | realm identity of the two built-in size functions | the pinned WPT observes one function object per realm, different across realms; every Lean minting function is a function of its argument | `realm_identity_refused` is the theorem-shaped refusal; every law takes the function's name as an argument, so distinctness is the caller's obligation |
| `DATA-FB-CALLBACK` | the body of any user-supplied `size` callback | DB-02: host-supplied bodies are not computations in this model | as an oracle argument whose answers are `SizeAnswer` decisions, with `CountSizeProfile` and `ByteLengthSizeProfile` as the two profiles this packet needs |

## 5. The ten edges

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | every row in section 3 names its census row id and that row's span digest from `generated/spec-algorithm-census.tsv`, and every quoted algorithm in the contract's section 4 was read first-hand from the pinned `index.bs` bytes at the offsets the census records |
| construction | `required-open` | D0 through D8 are frozen by name and signature in `WhatwgTest/Streams/Data/QueueContract.lean`; the module that declares them does not exist yet. Closes when the builder lands the fence and the battery goes green |
| semantics | `required-open` | the four queue operations and the two extraction algorithms have frozen definitions in the contract's D4 and D6; the apex statements are `enqueueValueWithSize_error_iff_not_admissible`, `dequeueValue_cons`, `peekQueueValue_agrees_dequeueValue`, `resetQueue_eq`, `extractHighWaterMark_error_iff`, `extractSizeAlgorithm_present` |
| laws | `required-open`, and **gated on `P3-R1`** | the invariant spine is `enqueueValueWithSize_wf`, which needs no carrier hypothesis at all, together with `sizeSum_cons`, `dequeueValue_wf` and `dequeueValue_clamp_unreachable_of_exact`, which are the only three of the ninety-nine frozen theorems that carry `SizeClass.Exact`. Under option (ii) those three are not applicable and this edge closes on `enqueueValueWithSize_wf` and the remaining order, FIFO and refusal laws alone |
| representation | `required-open` | the four representation decisions are frozen and argued: `Queue.WF` as a separate decidable `Prop` rather than a field invariant; `sizeSum` as a left fold; `peekQueueValue` returning `Option α` with no `SizeClass`; the three special constants as `SizeClass` fields. Each has a counterexample row forcing it |
| counterexamples | `required-closed` | `WS-DATA-CE-001` .. `WS-DATA-CE-010`, all `SEEDED` with proved green witnesses in `WhatwgTest/Streams/Counterexamples/Data/Queue.lean`; forty-four theorems, receipts `none` or `propext`. They close when the ruled instance rejects each attack |
| bridges | `not-applicable` | this packet claims no relation to a host implementation. The pinned WPT observations constrain which statements may be written and are recorded as host observations in the contract's section 5; none is a bridge theorem. `DATA-FB-ROUNDING` is where a bridge would have to live, and it is refused for now |
| targets | `not-applicable` | no generated code. Lowering to TypeScript is `RS-5` in `docs/REIFICATION-STRATEGY.md` and is not opened by this packet |
| trust | `required-open` | the counterexample module's receipts are measured and inside the semantic ceiling; `lake exe trustselftest` passes with the declared red set matching the observed red set exactly. **Open:** the ninety-nine production receipts, which arrive with the builder in `WhatwgTest/Streams/Data/QueueAxiomReport.lean` |
| coverage | `required-open` | the per-row map in section 6 is a proposal. No coverage state changes until the builder's witnesses land and `WhatwgTest/Audit/SpecCoverage.lean` is edited under its own claim, as `docs/SPEC-COVERAGE.md` requires |

## 6. Census rows this packet targets

**This table is a proposal, not a coverage report.** It says which rows the
frozen theorem spine would witness and what each would still be short of. The
authority for coverage states is
`WhatwgTest/Audit/SpecCoverage.lean`; the authority for the numbers is
the block printed by the coverage report gate.

| Census row | Disposition | Witness theorems | Proposed state, and what is short of green |
| --- | --- | --- | --- |
| `op.enqueue-value-with-size` | `owned` | `enqueueValueWithSize_error_iff` (steps 2 and 3), `enqueueValueWithSize_entries` (step 4), `enqueueValueWithSize_totalSize` (step 5), plus the four refusal theorems | `green`. Step 1 is an assertion about slot presence, which the type makes unstatable and therefore vacuous; that is recorded in the row's comment, not proved |
| `op.dequeue-value` | `owned` | `dequeueValue_isNone_iff` (step 2), `dequeueValue_value_eq_head` (steps 3 and 7), `dequeueValue_entries` (step 4), `dequeueValue_totalSize` (steps 5 and 6) | `green` under either ruling, but the meaning differs: under option (i) step 6's branch is additionally proved unreachable by `dequeueValue_clamp_unreachable_of_exact`, so the step is witnessed as present-and-vacuous rather than as a taken branch. The row's comment must say so |
| `op.peek-queue-value` | `owned` | `peekQueueValue_isSome_iff`, `peekQueueValue_eq_head` | `green` |
| `op.reset-queue` | `owned` | `resetQueue_entries`, `resetQueue_totalSize` | `green` |
| `op.is-non-negative-number` | `owned` | `SizeClass.isNonNegativeNumber_eq` and the three constant theorems | `partial`. Step 1, "If |v| is not a Number, return false", is a Web IDL type test with no counterpart on a typed carrier; it is `DATA-FB-IDL-DOUBLE` |
| `op.validate-and-normalize-high-water-mark` | `owned` | `extractHighWaterMark_absent`, `extractHighWaterMark_error_iff`, `extractHighWaterMark_id_on_accepted`, `extractHighWaterMark_allows_posInfinity` | `green`. The name in the census anchor is stale; the algorithm at this pin is `ExtractHighWaterMark` and normalizes nothing |
| `op.make-size-algorithm-from-size-function` | `owned` | `extractSizeAlgorithm_absent`, `extractSizeAlgorithm_present`, `SizeAlgorithm.invoke_one`, `SizeAlgorithm.invoke_foreign` | `green`. The "invoking" of step 2.1 is the oracle application; the invocation machinery itself is `DATA-FB-CALLBACK` |
| `op.cqs-constructor` | `owned` | `CountQueuingStrategy.make_highWaterMark`, `make_does_not_validate`, `make_accepts_nan` | `green` |
| `op.cqs-high-water-mark` | `owned` | `CountQueuingStrategy.make_highWaterMark` | `green` |
| `op.cqs-size` | `owned` | `CountQueuingStrategy.sizeAlgorithm_eq`, `toQueuingStrategy_size` | `partial`. The getter returns "this's relevant global object's count queuing strategy size function"; relevant-global lookup is `DATA-FB-REALM` |
| `op.count-queuing-strategy-size-function` | `owned` | `CountQueuingStrategy.size_answers_one`, `size_ignores_chunk`, `size_never_throws` | `partial`. The `CreateBuiltinFunction` steps, the function's `length` and `name`, and the callback context are host construction, not modelled |
| `op.blqs-constructor` | `owned` | `ByteLengthQueuingStrategy.make_highWaterMark`, `make_accepts_nan` | `green` |
| `op.blqs-high-water-mark` | `owned` | `ByteLengthQueuingStrategy.make_highWaterMark` | `green` |
| `op.blqs-size` | `owned` | `ByteLengthQueuingStrategy.sizeAlgorithm_eq`, `toQueuingStrategy_size` | `partial`, for the same reason as `op.cqs-size` |
| `op.byte-length-queuing-strategy-size-function` | `owned` | `byteLengthSize_number`, `byteLengthSize_undefined`, `byteLengthSize_thrown`, `ByteLengthQueuingStrategy.size_eq_byteLength`, `undefined_byteLength_refused` | `partial`. `GetV` itself is `DATA-FB-CALLBACK`; the three answers and their consequences are witnessed |
| `slot.queue` | `owned` | `Queue.empty_entries`, `enqueueValueWithSize_entries`, `dequeueValue_entries`, `resetQueue_entries` | `green` |
| `slot.queue-total-size` | `owned` | `Queue.empty_totalSize`, `enqueueValueWithSize_totalSize`, `dequeueValue_totalSize`, `resetQueue_totalSize`, `Queue.WF_iff` | `partial` under either ruling. The slot is defined as a JavaScript Number and the model's carrier is not one; `DATA-FB-ROUNDING` names the gap and `WS-DATA-CE-001` measures it |
| `slot.high-water-mark` | `owned` | `ByteLengthQueuingStrategy.make_highWaterMark` | `green` |
| `idl.queuing-strategy`, `idl.queuingstrategy-high-water-mark`, `idl.queuingstrategy-size`, `idl.queuing-strategy-size`, `idl.queuing-strategy-init`, `idl.queuingstrategyinit-high-water-mark` | `hostOnly` | the shape is carried by `QueuingStrategy`; no witness is owed | unchanged. `hostOnly` rows count in the denominator and carry no must-witness rule |
| `idl.count-queuing-strategy`, `idl.countqueuingstrategy-*`, `idl.byte-length-queuing-strategy`, `idl.bytelengthqueuingstrategy-*` | `hostOnly` | as above | unchanged |

Rows this packet deliberately does **not** claim, though they mention the same
slots: `slot.strategy-hwm` and `slot.strategy-size-algorithm` belong to the
readable default controller and are P4's; every `*-desired-size` and
`*-enqueue` controller row is P4, P5 or P6. `desiredSize` is quoted in the
contract's section 6 only as evidence about what the carrier choice makes
observable.

## 7. Open pins raised by this packet

| Id | Question | Owner |
| --- | --- | --- |
| `P3-R1` | the size carrier; default option (i) | coordinator, before the builder starts |
| `P3-R2` | one exception carrier for the estate, or one per calculus | coordinator, may wait for P4 |
| `P3-R3` | whether `sizeSum` is public; recommendation: keep it public | coordinator |
| P1.1 follow-up | the census carries `slot.high-water-mark` for `ByteLengthQueuingStrategy` only, though `cqs-internal-slots` defines the same slot for `CountQueuingStrategy`. Either a second slot row is missing or the two `<dfn for=…>` forms are being collapsed by the generator | the P1 census seat |
| finding B1 | there is no `ValidateAndNormalizeHighWaterMark` algorithm at this pin, only `ExtractHighWaterMark` behind a stale anchor id. Any later document or brief that names the former is describing an older revision | recorded here; no action beyond not declaring it |

## Rulings (coordinator, 2026-09-02)

| Id | Ruling |
| --- | --- |
| `P3-R1` | **Option (i): an exact carrier.** Sizes are exact numbers extended with `nan`, `posInfinity`, and `negInfinity` as `SizeClass` constants; the builder supplies a concrete instance built from `Int`/`Nat` (a dyadic rational or a rational pair; the builder chooses and states why) satisfying `SizeClass.Classified`, `Ordered`, and `Exact`. The host's binary64 rounding is a foreign boundary (`DATA-FB-ROUNDING`): the four floating-point WPT cases are host-only under mask M1, and `WS-DATA-CE-001` stays the registered disagreement. `DequeueValue` step 6's clamp is modelled and proved unreachable under `Exact`, which is the honest statement of what the specification's rounding note means once rounding is outside the model. |
| `P3-R2` | One exception carrier per calculus is not minted; the queue packet's `RangeError` is embedded into the shared exception type when the readable and writable packets introduce it (P4/P5), by an explicit injection with a proved retraction. No widening of the frozen signatures. |
| `P3-R3` | `sizeSum` stays public; it is the statement of `WF` and the readable/writable controllers' desired-size laws cite it. |

The P3 builder may start against these rulings. The frozen statements do not
change; the rulings select the `SizeClass` instance and the disposition of the
four WPT files.
## Landing (coordinator, 2026-09-02)

The P3 builder landed the frozen surface with all 99 theorems proved and
zero edits to the battery: 447 declarations compiled from the two fenced
modules, 375 axiom-free, 70 at `[propext]`, 2 at `[propext, Quot.sound]`
(`sizeSum_append_singleton`, `enqueueValueWithSize_wf`, through core's
`List.foldl_append`). The trust self-test reports an empty declared red set.

Module allocation for the `P3-R1` instance: `Whatwg/Streams/Data/DyadicSize.lean`,
imported from the root. Twelfth existing-type row: `Whatwg.Streams.Data.DyadicSize`,
canonical carrier for `Size` at this pin, the dyadic rationals with the
exponent fixed at 1074 (`finite u` denotes `u · 2^(-1074)`; every finite
binary64 is representable; `nan`, `posInfinity`, `negInfinity` are
constructors), with `DyadicSize.classified`, `ordered`, `exact`, and
`admissible_iff`; disposition `owned`; assurance route: this graph's
representation edge. Two frozen statements carry a hypothesis their proofs do
not use (`dequeueValue_clamp_unreachable_of_exact` needs no `Classified`);
the statements are unweakened.

Edge states after landing: identity, construction, semantics, laws,
representation, counterexamples, trust, and coverage are `required-closed`
by the receipts above and the closed `WS-DATA-CE-001`..`010` rows; bridges
and targets remain `not-applicable` at this stratum. The census rows this
packet turns `green` (12) and `partial` (6) are the builder's proposal in §6
and land through the coverage numerator in a separate packet.

## Coverage landed (coordinator, 2026-09-02)

The §6 proposal landed as 12 `green` and 6 `partial`, reached step by step
from the pinned bytes by the coverage seat, with 55 witness theorems (27
axiom-free, 28 at `[propext]`). Two proposed witnesses were rejected:
`CountQueuingStrategy.make_does_not_validate` (statement identical to
`make_highWaterMark`; `make_accepts_nan` carries the content) and
`realm_identity_refused` (its statement is `congrArg` and witnesses no step;
`DATA-FB-REALM` alone carries those steps). The §3 row for `slot.queue`
attributed the value-with-size sentence to the slot span; that span is the
`[[queue]]` definition in the default controller's slot table, and the
sentence lives in the queue-with-sizes section; the state is unaffected.
The coverage edge closes. The block at this landing:
`denominator 410; owned-with-green 12/410; green 12, partial 6, absent 392;
census 450 rows, 40 excluded`.
