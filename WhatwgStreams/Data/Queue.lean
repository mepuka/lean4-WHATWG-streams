/-!
# Data.Queue.lean

Owner: the queue-with-sizes carrier, a chunk queue paired with its total
size, and the enqueue, dequeue and reset operations over it as total
functions with their size invariant.

Spec anchors: `queue-with-sizes`.

Opens in P3.

The public surface below is the one frozen by
`test/contracts/queue-with-sizes.contract.md` (D0 through D4) and ascribed by
`WhatwgStreamsTest/Data/QueueContract.lean`. Every definition is a
transcription of the census row named in its docstring, read from the pinned
bytes of `vendor/whatwg-streams-b9ba9f49/index.bs` at the span that
`generated/spec-algorithm-census.tsv` records for that row.

The size carrier is abstract: the operations take a `SizeClass` record rather
than a concrete numeric type, so ruling `P3-R1` selects an instance and never
a statement. The `Classified`, `Ordered` and `Exact` predicates are the three
carrier properties the laws are stated against; a concrete instance
satisfying all three is owed by `P3-R1` in a module this packet does not
fence.
-/

set_option autoImplicit false

universe u

namespace WhatwgStreams.Data

/-! ## D0 — the refusal tag -/

/-- The `{{RangeError}}` thrown by `EnqueueValueWithSize` (census row
`op.enqueue-value-with-size`, span digest
`bf25987f0b75df7b2f0a69b92b799663d0d94799db9e96beb6c28e63b9f5035c`) and by
`ExtractHighWaterMark` (census row
`op.validate-and-normalize-high-water-mark`, span digest
`d9303084d19b298241323f639194c712749ed58918a76c12407a64ef58940c25`). It is
the only exception this calculus raises; open question `P3-R2` owns how a
wider exception type relates to it. -/
inductive RangeError
  | rangeError
deriving DecidableEq, Repr

/-! ## D1 — the size carrier interface -/

/-- The arithmetic and classification interface of the ECMAScript Number that
`[[queueTotalSize]]` is: census row `slot.queue-total-size`, span digest
`f0d6bce926812e0c273583abd237b16959d31ab1169c6c2b30f0f0268f5b0659`, whose
pinned text reads "`[[queueTotalSize]]` is a JavaScript `Number`, i.e. a
double-precision floating point number".

This record is an interface, not a carrier. `nan`, `posInfinity` and
`negInfinity` are **fields** rather than derived predicates so that an
instance is forced to exhibit the three special values: on a carrier that
cannot represent them, every refusal law of this packet is satisfied by an
implementation that refuses nothing, which is counterexample
`WS-DATA-CE-007`.

What this interface deliberately does not carry is the rounding of the host's
binary64 arithmetic; that is foreign boundary `DATA-FB-ROUNDING`. -/
structure SizeClass (Size : Type u) : Type u where
  /-- The `0` that `ResetQueue` writes into `[[queueTotalSize]]`. -/
  zero : Size
  /-- The `1` that the count queuing strategy size function returns. -/
  one : Size
  /-- A `NaN`; refused as a size and as a high water mark. -/
  nan : Size
  /-- `+∞`; refused as a size and explicitly allowed as a high water mark. -/
  posInfinity : Size
  /-- `-∞`; refused as a size and as a high water mark. -/
  negInfinity : Size
  /-- The `+` of `EnqueueValueWithSize` step 5. -/
  add : Size → Size → Size
  /-- The `−` of `DequeueValue` step 5. -/
  sub : Size → Size → Size
  /-- "If `|v|` is NaN" of `IsNonNegativeNumber` step 2. -/
  isNaN : Size → Bool
  /-- "If `|v|` &lt; 0" of `IsNonNegativeNumber` step 3, and "`|highWaterMark|`
  &lt; 0" of `ExtractHighWaterMark` step 3. -/
  isNegative : Size → Bool
  /-- Infinitude, which `EnqueueValueWithSize` step 3 tests together with the
  sign to refuse `+∞`. -/
  isInfinite : Size → Bool

namespace SizeClass

variable {Size : Type u}

/-- `IsNonNegativeNumber(|v|)`, census row `op.is-non-negative-number`, span
digest `0ade3c3addef973af83f74d7af1f70a7f94227be7d5aa08c8c7c1833c2086d2d`:
"If `|v|` is not a Number, return false. If `|v|` is NaN, return false. If
`|v|` &lt; 0, return false. Return true."

Step 1 is a Web IDL type test with no counterpart on a typed carrier, and is
foreign boundary `DATA-FB-IDL-DOUBLE`; steps 2 and 3 are the two conjuncts
below. `+∞` passes this predicate, which is why `EnqueueValueWithSize` needs
its second refusal step. -/
def isNonNegativeNumber (sizes : SizeClass Size) (v : Size) : Bool :=
  !sizes.isNaN v && !sizes.isNegative v

/-- "If `|size|` is +∞" of `EnqueueValueWithSize` step 3: infinite and not
negative. It is a second predicate rather than a clause of
`isNonNegativeNumber` because the two refusal sets differ on exactly this
value — `+∞` is a legal high water mark — which is counterexample
`WS-DATA-CE-008`. -/
def isPositiveInfinity (sizes : SizeClass Size) (v : Size) : Bool :=
  sizes.isInfinite v && !sizes.isNegative v

/-- The set of sizes `EnqueueValueWithSize` appends: not `NaN`, not negative,
not infinite. It is the conjunction of the two refusal steps read positively,
and `enqueueValueWithSize_error_iff_not_admissible` is the theorem that the
reading is exact. -/
def Admissible (sizes : SizeClass Size) (v : Size) : Prop :=
  sizes.isNaN v = false ∧ sizes.isNegative v = false ∧ sizes.isInfinite v = false

/-- `DequeueValue` step 6, census row `op.dequeue-value`, span digest
`7f8c5cb491b0c61f2d3a56acd007e7ad2243a28c73eec1920682f87e8c9e8dc0`: "If
`|container|.[[queueTotalSize]]` &lt; 0, set `|container|.[[queueTotalSize]]`
to 0. (This can occur due to rounding errors.)"

The step is modelled under every answer to `P3-R1`. Under an exact carrier it
is additionally proved unreachable by
`dequeueValue_clamp_unreachable_of_exact`, which is the honest reading of the
specification's own parenthesis once rounding is outside the model. -/
def clampNonNegative (sizes : SizeClass Size) (v : Size) : Size :=
  if sizes.isNegative v = true then sizes.zero else v

/-! ## D2 — the three carrier property predicates -/

/-- The three special constants are classified as the pinned text classifies
them. Without this predicate an instance could declare `nan` to be an
ordinary non-negative number and satisfy every refusal law vacuously
(`WS-DATA-CE-007`). -/
structure Classified (sizes : SizeClass Size) : Prop where
  /-- `nan` is a `NaN`. -/
  nan_isNaN : sizes.isNaN sizes.nan = true
  /-- A `NaN` is not negative: `IsNonNegativeNumber` refuses it at step 2, not
  step 3. -/
  nan_not_negative : sizes.isNegative sizes.nan = false
  /-- A `NaN` is not infinite. -/
  nan_not_infinite : sizes.isInfinite sizes.nan = false
  /-- `+∞` is infinite. -/
  posInfinity_infinite : sizes.isInfinite sizes.posInfinity = true
  /-- `+∞` is not negative, so it passes `IsNonNegativeNumber`. -/
  posInfinity_not_negative : sizes.isNegative sizes.posInfinity = false
  /-- `+∞` is not a `NaN`. -/
  posInfinity_not_nan : sizes.isNaN sizes.posInfinity = false
  /-- `-∞` is infinite. -/
  negInfinity_infinite : sizes.isInfinite sizes.negInfinity = true
  /-- `-∞` is negative, so `IsNonNegativeNumber` refuses it at step 3. -/
  negInfinity_negative : sizes.isNegative sizes.negInfinity = true
  /-- `-∞` is not a `NaN`. -/
  negInfinity_not_nan : sizes.isNaN sizes.negInfinity = false
  /-- No value is both a `NaN` and signed or infinite. -/
  nan_isolated : ∀ v : Size, sizes.isNaN v = true →
    sizes.isNegative v = false ∧ sizes.isInfinite v = false

/-- The admissible sizes are closed under the arithmetic the queue performs.
`add_admissible` is where overflow lives: it holds of an unbounded carrier and
fails of a bounded one, which is a second, independent way ruling `P3-R1`
shows up in the statements. -/
structure Ordered (sizes : SizeClass Size) : Prop where
  /-- `0` is an admissible size. -/
  zero_admissible : sizes.Admissible sizes.zero
  /-- `1` is an admissible size; the count queuing strategy returns it. -/
  one_admissible : sizes.Admissible sizes.one
  /-- The running total of admissible sizes stays admissible. -/
  add_admissible : ∀ a b : Size, sizes.Admissible a → sizes.Admissible b →
    sizes.Admissible (sizes.add a b)

/-- Exactness of the carrier's arithmetic on admissible sizes. Every equation
is guarded by `Admissible`: unguarded they are false of any carrier that has a
`NaN`, since `sub_add_cancel a nan` would demand `nan = a`, and a predicate no
instance satisfies makes every law depending on it vacuous.

This is the predicate ruling `P3-R1` turns on. Option (i), the ruled answer,
has an instance that satisfies it; a rounding carrier does not, and
`WS-DATA-CE-001` is the pinned run that falsifies `sub_add_cancel` there. -/
structure Exact (sizes : SizeClass Size) : Prop where
  /-- Addition is associative on admissible sizes. -/
  add_assoc : ∀ a b c : Size, sizes.Admissible a → sizes.Admissible b → sizes.Admissible c →
    sizes.add (sizes.add a b) c = sizes.add a (sizes.add b c)
  /-- Addition is commutative on admissible sizes. -/
  add_comm : ∀ a b : Size, sizes.Admissible a → sizes.Admissible b →
    sizes.add a b = sizes.add b a
  /-- `0` is a left unit on admissible sizes. -/
  zero_add : ∀ a : Size, sizes.Admissible a → sizes.add sizes.zero a = a
  /-- Subtracting a summand recovers the other summand: the equation
  `DequeueValue` needs and a rounding carrier denies. -/
  sub_add_cancel : ∀ a b : Size, sizes.Admissible a → sizes.Admissible b →
    sizes.sub (sizes.add a b) b = a

end SizeClass

/-! ## D3 — the queue -/

/-- A `value-with-size`: census row `slot.queue`, span digest
`9aaacc5116b7bb3286be79af6c3a0b7393f8b06f2a41e55c334036ace015e5b7`, whose
section text reads "a `value-with-size` is a struct with the two items value
and size". The field order is the pinned order. -/
structure QueueEntry (α : Type u) (Size : Type u) : Type u where
  /-- The chunk. -/
  value : α
  /-- Its determined size. -/
  size : Size
deriving DecidableEq, Repr

/-- The queue-with-sizes: the paired internal slots `[[queue]]` (census row
`slot.queue`) and `[[queueTotalSize]]` (census row `slot.queue-total-size`,
span digest
`f0d6bce926812e0c273583abd237b16959d31ab1169c6c2b30f0f0268f5b0659`), which
the pinned text calls "two paired internal slots, always named `[[queue]]` and
`[[queueTotalSize]]`" and keeps synchronized through the four operations
below.

The synchronization is `Queue.WF`, a separate decidable `Prop` rather than a
field invariant, because the pinned text's own warning denies it: keeping a
running total "is *not* equivalent to adding up the size of all chunks in
`[[queue]]`". A structure that made the invariant unconstructible-otherwise
could not represent the specification's own reachable states. -/
structure Queue (α : Type u) (Size : Type u) : Type u where
  /-- `[[queue]]`, a list of value-with-sizes. -/
  entries : List (QueueEntry α Size)
  /-- `[[queueTotalSize]]`, the running total. -/
  totalSize : Size
deriving DecidableEq

/-- The state `ResetQueue` produces and the state a fresh container starts in:
an empty `[[queue]]` and a `[[queueTotalSize]]` of `0`. -/
def Queue.empty {α Size : Type u} (sizes : SizeClass Size) : Queue α Size :=
  { entries := [], totalSize := sizes.zero }

/-- The sum of the sizes of the queued value-with-sizes: the quantity the
pinned warning of the `queue-with-sizes` section is about.

It is a **left** fold from `zero`, in the order `EnqueueValueWithSize`
accumulates. The direction is not cosmetic: `WS-DATA-CE-002` exhibits a
carrier and a three-entry queue on which the two fold directions differ, and
the left fold is the one that makes `enqueueValueWithSize_wf` a one-step
argument. -/
def sizeSum {α Size : Type u} (sizes : SizeClass Size)
    (entries : List (QueueEntry α Size)) : Size :=
  entries.foldl (fun total entry => sizes.add total entry.size) sizes.zero

/-- The synchronization of the two paired slots: `[[queueTotalSize]]` is the
sum of the sizes in `[[queue]]`. Stated as a separate `Prop` because the
pinned text denies it for the carrier the specification uses; see the
`Queue` docstring and `WS-DATA-CE-001`. -/
def Queue.WF {α Size : Type u} (sizes : SizeClass Size) (q : Queue α Size) : Prop :=
  q.totalSize = sizeSum sizes q.entries

/-- Every queued size is one `EnqueueValueWithSize` would have accepted. It is
the hypothesis under which the running total is an exact sum. -/
def Queue.SizesAdmissible {α Size : Type u} (sizes : SizeClass Size) (q : Queue α Size) : Prop :=
  ∀ entry ∈ q.entries, sizes.Admissible entry.size

instance Queue.instDecidableWF {α Size : Type u} [DecidableEq Size]
    (sizes : SizeClass Size) (q : Queue α Size) : Decidable (Queue.WF sizes q) :=
  inferInstanceAs (Decidable (q.totalSize = sizeSum sizes q.entries))

/-! ## D4 — the four queue-with-sizes operations -/

/-- `EnqueueValueWithSize(|container|, |value|, |size|)`, census row
`op.enqueue-value-with-size`, span digest
`bf25987f0b75df7b2f0a69b92b799663d0d94799db9e96beb6c28e63b9f5035c`:

1. Assert: `|container|` has `[[queue]]` and `[[queueTotalSize]]` internal
   slots — vacuous here, since the type carries both.
2. "If ! `IsNonNegativeNumber(|size|)` is false, throw a `RangeError`
   exception."
3. "If `|size|` is +∞, throw a `RangeError` exception."
4. "Append a new value-with-size with value `|value|` and size `|size|` to
   `|container|.[[queue]]`."
5. "Set `|container|.[[queueTotalSize]]` to `|container|.[[queueTotalSize]]` +
   `|size|`."

The two refusals are two separate steps in a fixed order, and both precede the
append: a model that appends first lets the running total go negative while
the queue is non-empty (`WS-DATA-CE-003`). Step 4 appends;
`WS-DATA-CE-010` is the stack that prepends and keeps every other law. -/
def enqueueValueWithSize {α Size : Type u} (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (size : Size) : Except RangeError (Queue α Size) :=
  if sizes.isNonNegativeNumber size = false then .error .rangeError
  else if sizes.isPositiveInfinity size = true then .error .rangeError
  else
    .ok { entries := q.entries ++ [{ value := value, size := size }],
          totalSize := sizes.add q.totalSize size }

/-- `DequeueValue(|container|)`, census row `op.dequeue-value`, span digest
`7f8c5cb491b0c61f2d3a56acd007e7ad2243a28c73eec1920682f87e8c9e8dc0`:

1. Assert: the slots exist — vacuous here.
2. "Assert: `|container|.[[queue]]` is not empty."
3. "Let `|valueWithSize|` be `|container|.[[queue]][0]`."
4. "Remove `|valueWithSize|` from `|container|.[[queue]]`."
5. "Set `|container|.[[queueTotalSize]]` to `|container|.[[queueTotalSize]]` −
   `|valueWithSize|`'s size."
6. "If `|container|.[[queueTotalSize]]` &lt; 0, set it to 0. (This can occur
   due to rounding errors.)"
7. "Return `|valueWithSize|`'s value."

Step 2's assertion is modelled by the `Option`, and `dequeueValue_isNone_iff`
is the theorem that the refusing arm is reached on exactly the empty queue: an
assertion is not a runtime check, so a model is otherwise free to answer with
a default, which is `WS-DATA-CE-004`. -/
def dequeueValue {α Size : Type u} (sizes : SizeClass Size) (q : Queue α Size) :
    Option (α × Queue α Size) :=
  match q.entries with
  | [] => none
  | entry :: rest =>
      some (entry.value,
        { entries := rest,
          totalSize := sizes.clampNonNegative (sizes.sub q.totalSize entry.size) })

/-- `PeekQueueValue(|container|)`, census row `op.peek-queue-value`, span
digest `95ac1ea81b9e1ef48351e8e0f0b4f5619bb0b0322ad27c32a4d02368de10aca8`:
assert the slots, "Assert: `|container|.[[queue]]` is not empty", "Let
`|valueWithSize|` be `|container|.[[queue]][0]`", "Return `|valueWithSize|`'s
value".

It touches neither slot, and the signature says so: no `SizeClass` argument
and no queue in the result. `WS-DATA-CE-005` is the popping mutant, which
returns the right value and is caught only by the container it hands back —
a mutation this result type cannot express. -/
def peekQueueValue {α Size : Type u} (q : Queue α Size) : Option α :=
  match q.entries with
  | [] => none
  | entry :: _ => some entry.value

/-- `ResetQueue(|container|)`, census row `op.reset-queue`, span digest
`f6e02ee26429ac71ebac273cf9cf5f169abb3f65d882f09616ef0996609b0e72`: assert the
slots, "Set `|container|.[[queue]]` to a new empty list", "Set
`|container|.[[queueTotalSize]]` to 0".

Unconditionally, with no clamp and no arithmetic. Writing the literal `0`
rather than recomputing is why `resetQueue_wf` needs no carrier hypothesis;
`WS-DATA-CE-006` is the reset that keeps a drifted running total. -/
def resetQueue {α Size : Type u} (sizes : SizeClass Size) (_container : Queue α Size) :
    Queue α Size :=
  { entries := [], totalSize := sizes.zero }

/-! ## S1 — classification and admission

Census row `op.is-non-negative-number`. -/

namespace SizeClass

variable {Size : Type u}

theorem isNonNegativeNumber_eq (sizes : SizeClass Size) (v : Size) :
    sizes.isNonNegativeNumber v = (!sizes.isNaN v && !sizes.isNegative v) := rfl

theorem isPositiveInfinity_eq (sizes : SizeClass Size) (v : Size) :
    sizes.isPositiveInfinity v = (sizes.isInfinite v && !sizes.isNegative v) := rfl

theorem admissible_iff (sizes : SizeClass Size) (v : Size) :
    sizes.Admissible v ↔
      (sizes.isNaN v = false ∧ sizes.isNegative v = false ∧ sizes.isInfinite v = false) :=
  Iff.rfl

/-- The exact bridge between the two refusal steps of `EnqueueValueWithSize`
and the admissible set: a size is appended precisely when it passes
`IsNonNegativeNumber` and is not `+∞`. -/
private theorem admissible_iff_accepted (sizes : SizeClass Size) (v : Size) :
    sizes.Admissible v ↔
      (sizes.isNonNegativeNumber v = true ∧ sizes.isPositiveInfinity v = false) := by
  unfold Admissible isNonNegativeNumber isPositiveInfinity
  cases sizes.isNaN v <;> cases sizes.isNegative v <;> cases sizes.isInfinite v <;> simp

theorem not_admissible_nan (sizes : SizeClass Size) (classified : sizes.Classified) :
    ¬ sizes.Admissible sizes.nan := by
  intro h
  simp [Admissible, classified.nan_isNaN] at h

theorem not_admissible_posInfinity (sizes : SizeClass Size) (classified : sizes.Classified) :
    ¬ sizes.Admissible sizes.posInfinity := by
  intro h
  simp [Admissible, classified.posInfinity_infinite] at h

theorem not_admissible_negInfinity (sizes : SizeClass Size) (classified : sizes.Classified) :
    ¬ sizes.Admissible sizes.negInfinity := by
  intro h
  simp [Admissible, classified.negInfinity_infinite] at h

theorem isNonNegativeNumber_nan (sizes : SizeClass Size) (classified : sizes.Classified) :
    sizes.isNonNegativeNumber sizes.nan = false := by
  simp [isNonNegativeNumber, classified.nan_isNaN]

theorem isNonNegativeNumber_negInfinity (sizes : SizeClass Size) (classified : sizes.Classified) :
    sizes.isNonNegativeNumber sizes.negInfinity = false := by
  simp [isNonNegativeNumber, classified.negInfinity_negative]

/-- `+∞` passes `IsNonNegativeNumber` and is refused only by step 3 of
`EnqueueValueWithSize`. This is the theorem that pins the two-step structure:
a one-step model satisfies every other law of this packet. -/
theorem isNonNegativeNumber_posInfinity (sizes : SizeClass Size) (classified : sizes.Classified) :
    sizes.isNonNegativeNumber sizes.posInfinity = true := by
  simp [isNonNegativeNumber, classified.posInfinity_not_nan, classified.posInfinity_not_negative]

theorem clampNonNegative_of_negative (sizes : SizeClass Size) (v : Size)
    (h : sizes.isNegative v = true) : sizes.clampNonNegative v = sizes.zero := by
  simp [clampNonNegative, h]

theorem clampNonNegative_of_nonneg (sizes : SizeClass Size) (v : Size)
    (h : sizes.isNegative v = false) : sizes.clampNonNegative v = v := by
  simp [clampNonNegative, h]

theorem clampNonNegative_not_negative (sizes : SizeClass Size) (ordered : sizes.Ordered)
    (v : Size) : sizes.isNegative (sizes.clampNonNegative v) = false := by
  unfold clampNonNegative
  split
  · exact ordered.zero_admissible.2.1
  · next h => simpa using h

end SizeClass

/-! ## S2 — the queue carrier and the sum

Census rows `slot.queue` and `slot.queue-total-size`. -/

variable {α Size : Type u}

theorem Queue.empty_entries (sizes : SizeClass Size) :
    (Queue.empty sizes : Queue α Size).entries = [] := rfl

theorem Queue.empty_totalSize (sizes : SizeClass Size) :
    (Queue.empty sizes : Queue α Size).totalSize = sizes.zero := rfl

theorem sizeSum_nil (sizes : SizeClass Size) :
    sizeSum sizes ([] : List (QueueEntry α Size)) = sizes.zero := rfl

theorem sizeSum_append_singleton (sizes : SizeClass Size)
    (entries : List (QueueEntry α Size)) (entry : QueueEntry α Size) :
    sizeSum sizes (entries ++ [entry]) = sizes.add (sizeSum sizes entries) entry.size := by
  simp [sizeSum]

/-- Admissibility of a left fold over admissible sizes, from any admissible
accumulator. -/
private theorem foldl_admissible (sizes : SizeClass Size) (ordered : sizes.Ordered)
    (entries : List (QueueEntry α Size)) :
    ∀ acc : Size, sizes.Admissible acc → (∀ e ∈ entries, sizes.Admissible e.size) →
      sizes.Admissible (entries.foldl (fun total entry => sizes.add total entry.size) acc) := by
  induction entries with
  | nil => intro acc hacc _; exact hacc
  | cons e rest ih =>
      intro acc hacc hall
      simp only [List.foldl_cons]
      exact ih (sizes.add acc e.size)
        (ordered.add_admissible acc e.size hacc (hall e (List.mem_cons.mpr (Or.inl rfl))))
        (fun x hx => hall x (List.mem_cons.mpr (Or.inr hx)))

theorem sizeSum_admissible (sizes : SizeClass Size) (entries : List (QueueEntry α Size))
    (ordered : sizes.Ordered) (hall : ∀ e ∈ entries, sizes.Admissible e.size) :
    sizes.Admissible (sizeSum sizes entries) :=
  foldl_admissible sizes ordered entries sizes.zero ordered.zero_admissible hall

/-- A left fold from an admissible accumulator splits into the accumulator
plus the fold from `zero`. This is the only place the fold direction has to be
turned around, and it needs the whole of `Exact`. -/
private theorem foldl_shift (sizes : SizeClass Size) (hexact : sizes.Exact)
    (ordered : sizes.Ordered) (entries : List (QueueEntry α Size)) :
    ∀ acc : Size, sizes.Admissible acc → (∀ e ∈ entries, sizes.Admissible e.size) →
      entries.foldl (fun total entry => sizes.add total entry.size) acc =
        sizes.add acc (sizeSum sizes entries) := by
  induction entries with
  | nil =>
      intro acc hacc _
      show acc = sizes.add acc sizes.zero
      rw [hexact.add_comm acc sizes.zero hacc ordered.zero_admissible,
        hexact.zero_add acc hacc]
  | cons e rest ih =>
      intro acc hacc hall
      have he : sizes.Admissible e.size := hall e (List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ x ∈ rest, sizes.Admissible x.size :=
        fun x hx => hall x (List.mem_cons.mpr (Or.inr hx))
      have hsum : sizes.Admissible (sizeSum sizes rest) :=
        sizeSum_admissible sizes rest ordered hrest
      have hcons : sizeSum sizes (e :: rest) = sizes.add e.size (sizeSum sizes rest) := by
        unfold sizeSum
        simp only [List.foldl_cons]
        rw [hexact.zero_add e.size he]
        exact ih e.size he hrest
      simp only [List.foldl_cons]
      rw [ih (sizes.add acc e.size)
        (ordered.add_admissible acc e.size hacc he) hrest, hcons]
      exact hexact.add_assoc acc e.size (sizeSum sizes rest) hacc he hsum

/-- The left fold turned around. It carries `Exact` because it is false
without it: `WS-DATA-CE-002` exhibits a carrier and a three-entry queue on
which the two fold directions differ. It is exactly the lemma
`dequeueValue_wf` needs. -/
theorem sizeSum_cons (sizes : SizeClass Size) (entry : QueueEntry α Size)
    (entries : List (QueueEntry α Size)) (hexact : sizes.Exact) (ordered : sizes.Ordered)
    (hentry : sizes.Admissible entry.size) (hall : ∀ e ∈ entries, sizes.Admissible e.size) :
    sizeSum sizes (entry :: entries) = sizes.add entry.size (sizeSum sizes entries) := by
  unfold sizeSum
  simp only [List.foldl_cons]
  rw [hexact.zero_add entry.size hentry]
  exact foldl_shift sizes hexact ordered entries entry.size hentry hall

theorem Queue.WF_iff (sizes : SizeClass Size) (q : Queue α Size) :
    Queue.WF sizes q ↔ q.totalSize = sizeSum sizes q.entries := Iff.rfl

theorem Queue.WF_empty (sizes : SizeClass Size) :
    Queue.WF sizes (Queue.empty sizes : Queue α Size) := rfl

theorem Queue.SizesAdmissible_iff (sizes : SizeClass Size) (q : Queue α Size) :
    Queue.SizesAdmissible sizes q ↔ ∀ entry ∈ q.entries, sizes.Admissible entry.size :=
  Iff.rfl

theorem Queue.SizesAdmissible_empty (sizes : SizeClass Size) :
    Queue.SizesAdmissible sizes (Queue.empty sizes : Queue α Size) := by
  intro entry hentry
  simp [Queue.empty] at hentry

/-! ## S3 — enqueue

Census row `op.enqueue-value-with-size`. -/

theorem enqueueValueWithSize_error_iff (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (size : Size) :
    enqueueValueWithSize sizes q value size = Except.error RangeError.rangeError ↔
      (sizes.isNonNegativeNumber size = false ∨ sizes.isPositiveInfinity size = true) := by
  unfold enqueueValueWithSize
  cases hnn : sizes.isNonNegativeNumber size <;> cases hpi : sizes.isPositiveInfinity size <;>
    simp

theorem enqueueValueWithSize_error_iff_not_admissible (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (size : Size) :
    enqueueValueWithSize sizes q value size = Except.error RangeError.rangeError ↔
      ¬ sizes.Admissible size := by
  rw [enqueueValueWithSize_error_iff, SizeClass.admissible_iff_accepted]
  cases sizes.isNonNegativeNumber size <;> cases sizes.isPositiveInfinity size <;> simp

theorem enqueueValueWithSize_refuses_nan (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (classified : sizes.Classified) :
    enqueueValueWithSize sizes q value sizes.nan = Except.error RangeError.rangeError :=
  (enqueueValueWithSize_error_iff_not_admissible sizes q value sizes.nan).mpr
    (SizeClass.not_admissible_nan sizes classified)

theorem enqueueValueWithSize_refuses_negative (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (size : Size) (h : sizes.isNegative size = true) :
    enqueueValueWithSize sizes q value size = Except.error RangeError.rangeError :=
  (enqueueValueWithSize_error_iff_not_admissible sizes q value size).mpr
    (fun hadmissible => by rw [hadmissible.2.1] at h; exact Bool.noConfusion h)

theorem enqueueValueWithSize_refuses_posInfinity (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (classified : sizes.Classified) :
    enqueueValueWithSize sizes q value sizes.posInfinity = Except.error RangeError.rangeError :=
  (enqueueValueWithSize_error_iff_not_admissible sizes q value sizes.posInfinity).mpr
    (SizeClass.not_admissible_posInfinity sizes classified)

theorem enqueueValueWithSize_refuses_negInfinity (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (classified : sizes.Classified) :
    enqueueValueWithSize sizes q value sizes.negInfinity = Except.error RangeError.rangeError :=
  (enqueueValueWithSize_error_iff_not_admissible sizes q value sizes.negInfinity).mpr
    (SizeClass.not_admissible_negInfinity sizes classified)

theorem enqueueValueWithSize_eq_of_admissible (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (size : Size) (hadmissible : sizes.Admissible size) :
    enqueueValueWithSize sizes q value size =
      Except.ok ({ entries := q.entries ++ [{ value := value, size := size }],
                   totalSize := sizes.add q.totalSize size } : Queue α Size) := by
  have h := (SizeClass.admissible_iff_accepted sizes size).mp hadmissible
  unfold enqueueValueWithSize
  rw [if_neg (by simp [h.1]), if_neg (by simp [h.2])]

/-- A successful enqueue means both refusal steps were passed, which is the
admissible set. Proved by case analysis on the two decision bits rather than
by contradiction, so no classical reasoning enters the packet. -/
private theorem enqueueValueWithSize_admissible_of_ok (sizes : SizeClass Size)
    (q q' : Queue α Size) (value : α) (size : Size)
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') : sizes.Admissible size := by
  rw [SizeClass.admissible_iff_accepted]
  constructor
  · cases hnn : sizes.isNonNegativeNumber size with
    | true => rfl
    | false =>
        unfold enqueueValueWithSize at hok
        rw [hnn] at hok
        simp at hok
  · cases hpi : sizes.isPositiveInfinity size with
    | false => rfl
    | true =>
        unfold enqueueValueWithSize at hok
        rw [hpi] at hok
        cases hnn : sizes.isNonNegativeNumber size with
        | false => rw [hnn] at hok; simp at hok
        | true => rw [hnn] at hok; simp at hok

theorem enqueueValueWithSize_ok_iff (sizes : SizeClass Size) (q : Queue α Size)
    (value : α) (size : Size) :
    (∃ q', enqueueValueWithSize sizes q value size = Except.ok q') ↔ sizes.Admissible size := by
  constructor
  · intro h
    cases h with
    | intro q' hok => exact enqueueValueWithSize_admissible_of_ok sizes q q' value size hok
  · intro hadmissible
    exact ⟨_, enqueueValueWithSize_eq_of_admissible sizes q value size hadmissible⟩

/-- The successful result is the frozen record, so every projection law below
is a rewrite. -/
private theorem enqueueValueWithSize_ok_eq (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    q' = { entries := q.entries ++ [{ value := value, size := size }],
           totalSize := sizes.add q.totalSize size } := by
  have hadmissible : sizes.Admissible size :=
    (enqueueValueWithSize_ok_iff sizes q value size).mp ⟨q', hok⟩
  rw [enqueueValueWithSize_eq_of_admissible sizes q value size hadmissible] at hok
  exact (Except.ok.inj hok).symm

theorem enqueueValueWithSize_entries (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    q'.entries = q.entries ++ [({ value := value, size := size } : QueueEntry α Size)] := by
  rw [enqueueValueWithSize_ok_eq sizes q q' value size hok]

theorem enqueueValueWithSize_totalSize (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    q'.totalSize = sizes.add q.totalSize size := by
  rw [enqueueValueWithSize_ok_eq sizes q q' value size hok]

theorem enqueueValueWithSize_length (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    q'.entries.length = q.entries.length + 1 := by
  rw [enqueueValueWithSize_entries sizes q q' value size hok]
  simp

theorem enqueueValueWithSize_sizesAdmissible (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hq : Queue.SizesAdmissible sizes q)
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    Queue.SizesAdmissible sizes q' := by
  have hadmissible : sizes.Admissible size :=
    (enqueueValueWithSize_ok_iff sizes q value size).mp ⟨q', hok⟩
  intro entry hentry
  rw [enqueueValueWithSize_entries sizes q q' value size hok] at hentry
  cases List.mem_append.mp hentry with
  | inl hmem => exact hq entry hmem
  | inr hmem =>
      have heq : entry = ({ value := value, size := size } : QueueEntry α Size) := by
        simpa using hmem
      rw [heq]
      exact hadmissible

theorem enqueueValueWithSize_totalSize_admissible (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (ordered : sizes.Ordered)
    (htotal : sizes.Admissible q.totalSize)
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    sizes.Admissible q'.totalSize := by
  have hadmissible : sizes.Admissible size :=
    (enqueueValueWithSize_ok_iff sizes q value size).mp ⟨q', hok⟩
  rw [enqueueValueWithSize_totalSize sizes q q' value size hok]
  exact ordered.add_admissible q.totalSize size htotal hadmissible

/-- Enqueue never drifts, and needs no carrier hypothesis at all: the running
total and the fold take the same step, by `sizeSum_append_singleton`. Only
dequeue can drift, which is where ruling `P3-R1` lands. -/
theorem enqueueValueWithSize_wf (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hwf : Queue.WF sizes q)
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    Queue.WF sizes q' := by
  unfold Queue.WF
  rw [enqueueValueWithSize_entries sizes q q' value size hok,
    enqueueValueWithSize_totalSize sizes q q' value size hok,
    sizeSum_append_singleton sizes q.entries { value := value, size := size }, hwf]

/-! ## S4 — dequeue

Census row `op.dequeue-value`. -/

theorem dequeueValue_nil (sizes : SizeClass Size) (total : Size) :
    dequeueValue sizes ({ entries := [], totalSize := total } : Queue α Size) = none := rfl

theorem dequeueValue_cons (sizes : SizeClass Size) (total : Size) (entry : QueueEntry α Size)
    (rest : List (QueueEntry α Size)) :
    dequeueValue sizes ({ entries := entry :: rest, totalSize := total } : Queue α Size) =
      some (entry.value,
        ({ entries := rest,
           totalSize := sizes.clampNonNegative (sizes.sub total entry.size) } :
          Queue α Size)) := rfl

/-- The refusing arm, read off `[[queue]]` rather than off the container. -/
private theorem dequeueValue_of_nil (sizes : SizeClass Size) (q : Queue α Size)
    (hentries : q.entries = []) : dequeueValue sizes q = none := by
  unfold dequeueValue
  rw [hentries]

/-- The answering arm, read off `[[queue]]` rather than off the container. -/
private theorem dequeueValue_of_cons (sizes : SizeClass Size) (q : Queue α Size)
    (entry : QueueEntry α Size) (rest : List (QueueEntry α Size))
    (hentries : q.entries = entry :: rest) :
    dequeueValue sizes q =
      some (entry.value,
        ({ entries := rest,
           totalSize := sizes.clampNonNegative (sizes.sub q.totalSize entry.size) } :
          Queue α Size)) := by
  unfold dequeueValue
  rw [hentries]

theorem dequeueValue_isSome_iff (sizes : SizeClass Size) (q : Queue α Size) :
    (dequeueValue sizes q).isSome = true ↔ q.entries ≠ [] := by
  cases hentries : q.entries with
  | nil => rw [dequeueValue_of_nil sizes q hentries]; simp
  | cons entry rest =>
      rw [dequeueValue_of_cons sizes q entry rest hentries]; simp

theorem dequeueValue_isNone_iff (sizes : SizeClass Size) (q : Queue α Size) :
    dequeueValue sizes q = none ↔ q.entries = [] := by
  cases hentries : q.entries with
  | nil => rw [dequeueValue_of_nil sizes q hentries]; simp
  | cons entry rest =>
      rw [dequeueValue_of_cons sizes q entry rest hentries]; simp

theorem dequeueValue_value_eq_head (sizes : SizeClass Size) (q : Queue α Size) :
    (dequeueValue sizes q).map Prod.fst = q.entries.head?.map QueueEntry.value := by
  cases hentries : q.entries with
  | nil => rw [dequeueValue_of_nil sizes q hentries]; simp
  | cons entry rest =>
      rw [dequeueValue_of_cons sizes q entry rest hentries]; simp

theorem dequeueValue_entries (sizes : SizeClass Size) (q q' : Queue α Size) (value : α)
    (hsome : dequeueValue sizes q = some (value, q')) : q'.entries = q.entries.tail := by
  cases hentries : q.entries with
  | nil =>
      rw [dequeueValue_of_nil sizes q hentries] at hsome
      simp at hsome
  | cons entry rest =>
      rw [dequeueValue_of_cons sizes q entry rest hentries] at hsome
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      rw [← hsome.2]
      simp

theorem dequeueValue_length (sizes : SizeClass Size) (q q' : Queue α Size) (value : α)
    (hsome : dequeueValue sizes q = some (value, q')) :
    q.entries.length = q'.entries.length + 1 := by
  rw [dequeueValue_entries sizes q q' value hsome]
  cases hentries : q.entries with
  | nil =>
      rw [dequeueValue_of_nil sizes q hentries] at hsome
      simp at hsome
  | cons entry rest => simp

theorem dequeueValue_totalSize (sizes : SizeClass Size) (q q' : Queue α Size) (value : α)
    (entry : QueueEntry α Size) (rest : List (QueueEntry α Size))
    (hentries : q.entries = entry :: rest)
    (hsome : dequeueValue sizes q = some (value, q')) :
    q'.totalSize = sizes.clampNonNegative (sizes.sub q.totalSize entry.size) := by
  rw [dequeueValue_of_cons sizes q entry rest hentries] at hsome
  simp only [Option.some.injEq, Prod.mk.injEq] at hsome
  rw [← hsome.2]

theorem dequeueValue_totalSize_not_negative (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (ordered : sizes.Ordered)
    (hsome : dequeueValue sizes q = some (value, q')) :
    sizes.isNegative q'.totalSize = false := by
  cases hentries : q.entries with
  | nil =>
      rw [dequeueValue_of_nil sizes q hentries] at hsome
      simp at hsome
  | cons entry rest =>
      rw [dequeueValue_totalSize sizes q q' value entry rest hentries hsome]
      exact SizeClass.clampNonNegative_not_negative sizes ordered _

theorem dequeueValue_sizesAdmissible (sizes : SizeClass Size) (q q' : Queue α Size) (value : α)
    (hq : Queue.SizesAdmissible sizes q)
    (hsome : dequeueValue sizes q = some (value, q')) :
    Queue.SizesAdmissible sizes q' := by
  intro entry hentry
  rw [dequeueValue_entries sizes q q' value hsome] at hentry
  cases hentries : q.entries with
  | nil =>
      rw [hentries] at hentry
      simp at hentry
  | cons head rest =>
      rw [hentries] at hentry
      simp only [List.tail_cons] at hentry
      exact hq entry (by rw [hentries]; exact List.mem_cons.mpr (Or.inr hentry))

/-- The `DequeueValue` step-6 clamp is never taken on an exact carrier: the
running total of a well-formed queue is the head's size plus the sum of the
rest, so the subtraction lands on that admissible sum. This is the cost of
ruling `P3-R1` in favour of option (i), stated as a theorem in the tree: the
specification's step 6 is witnessed as present-and-vacuous rather than as a
taken branch, and a later ruling adopting a rounding carrier has an explicit
statement to supersede. -/
theorem dequeueValue_clamp_unreachable_of_exact (sizes : SizeClass Size) (q : Queue α Size)
    (entry : QueueEntry α Size) (rest : List (QueueEntry α Size))
    (_classified : sizes.Classified) (ordered : sizes.Ordered) (hexact : sizes.Exact)
    (hwf : Queue.WF sizes q) (hsizes : Queue.SizesAdmissible sizes q)
    (hentries : q.entries = entry :: rest) :
    sizes.isNegative (sizes.sub q.totalSize entry.size) = false := by
  have hentry : sizes.Admissible entry.size :=
    hsizes entry (by rw [hentries]; exact List.mem_cons.mpr (Or.inl rfl))
  have hrest : ∀ e ∈ rest, sizes.Admissible e.size := fun e he =>
    hsizes e (by rw [hentries]; exact List.mem_cons.mpr (Or.inr he))
  have hsum : sizes.Admissible (sizeSum sizes rest) :=
    sizeSum_admissible sizes rest ordered hrest
  have htotal : q.totalSize = sizes.add (sizeSum sizes rest) entry.size := by
    rw [hwf, hentries, sizeSum_cons sizes entry rest hexact ordered hentry hrest,
      hexact.add_comm entry.size (sizeSum sizes rest) hentry hsum]
  rw [htotal, hexact.sub_add_cancel (sizeSum sizes rest) entry.size hsum hentry]
  exact hsum.2.1

/-- Dequeue preserves the running-total invariant on an exact carrier. This is
exactly what a rounding carrier destroys; `WS-DATA-CE-001` is the pinned
witness, and the `Exact` hypothesis is where ruling `P3-R1` lands. -/
theorem dequeueValue_wf (sizes : SizeClass Size) (q q' : Queue α Size) (value : α)
    (classified : sizes.Classified) (ordered : sizes.Ordered) (hexact : sizes.Exact)
    (hwf : Queue.WF sizes q) (hsizes : Queue.SizesAdmissible sizes q)
    (hsome : dequeueValue sizes q = some (value, q')) :
    Queue.WF sizes q' := by
  cases hentries : q.entries with
  | nil =>
      rw [dequeueValue_of_nil sizes q hentries] at hsome
      simp at hsome
  | cons entry rest =>
      have hentry : sizes.Admissible entry.size :=
        hsizes entry (by rw [hentries]; exact List.mem_cons.mpr (Or.inl rfl))
      have hrest : ∀ e ∈ rest, sizes.Admissible e.size := fun e he =>
        hsizes e (by rw [hentries]; exact List.mem_cons.mpr (Or.inr he))
      have hsum : sizes.Admissible (sizeSum sizes rest) :=
        sizeSum_admissible sizes rest ordered hrest
      have hnotneg : sizes.isNegative (sizes.sub q.totalSize entry.size) = false :=
        dequeueValue_clamp_unreachable_of_exact sizes q entry rest classified ordered hexact
          hwf hsizes hentries
      have htotal : q.totalSize = sizes.add (sizeSum sizes rest) entry.size := by
        rw [hwf, hentries, sizeSum_cons sizes entry rest hexact ordered hentry hrest,
          hexact.add_comm entry.size (sizeSum sizes rest) hentry hsum]
      unfold Queue.WF
      rw [dequeueValue_totalSize sizes q q' value entry rest hentries hsome,
        dequeueValue_entries sizes q q' value hsome,
        SizeClass.clampNonNegative_of_nonneg sizes _ hnotneg, hentries, htotal,
        hexact.sub_add_cancel (sizeSum sizes rest) entry.size hsum hentry]
      simp

/-! ## S5 — FIFO and peek

Census rows `op.peek-queue-value` and `op.dequeue-value`. -/

theorem peekQueueValue_nil (total : Size) :
    peekQueueValue ({ entries := [], totalSize := total } : Queue α Size) = none := rfl

theorem peekQueueValue_cons (total : Size) (entry : QueueEntry α Size)
    (rest : List (QueueEntry α Size)) :
    peekQueueValue ({ entries := entry :: rest, totalSize := total } : Queue α Size) =
      some entry.value := rfl

/-- The empty arm, read off `[[queue]]`. -/
private theorem peekQueueValue_of_nil (q : Queue α Size) (hentries : q.entries = []) :
    peekQueueValue q = none := by
  unfold peekQueueValue
  rw [hentries]

/-- The answering arm, read off `[[queue]]`. -/
private theorem peekQueueValue_of_cons (q : Queue α Size) (entry : QueueEntry α Size)
    (rest : List (QueueEntry α Size)) (hentries : q.entries = entry :: rest) :
    peekQueueValue q = some entry.value := by
  unfold peekQueueValue
  rw [hentries]

theorem peekQueueValue_eq_head (q : Queue α Size) :
    peekQueueValue q = q.entries.head?.map QueueEntry.value := by
  cases hentries : q.entries with
  | nil => rw [peekQueueValue_of_nil q hentries]; simp
  | cons entry rest => rw [peekQueueValue_of_cons q entry rest hentries]; simp

theorem peekQueueValue_agrees_dequeueValue (sizes : SizeClass Size) (q : Queue α Size) :
    peekQueueValue q = (dequeueValue sizes q).map Prod.fst := by
  rw [peekQueueValue_eq_head, dequeueValue_value_eq_head]

theorem peekQueueValue_isSome_iff (q : Queue α Size) :
    (peekQueueValue q).isSome = true ↔ q.entries ≠ [] := by
  cases hentries : q.entries with
  | nil => rw [peekQueueValue_of_nil q hentries]; simp
  | cons entry rest => rw [peekQueueValue_of_cons q entry rest hentries]; simp

theorem dequeueValue_enqueueValueWithSize_empty (sizes : SizeClass Size) (q q' : Queue α Size)
    (value : α) (size : Size) (hempty : q.entries = [])
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    (dequeueValue sizes q').map Prod.fst = some value := by
  rw [dequeueValue_value_eq_head, enqueueValueWithSize_entries sizes q q' value size hok, hempty]
  simp

/-- The sharp FIFO statement: an enqueue onto a non-empty queue does not change
what the next dequeue answers. `WS-DATA-CE-010` is the stack that keeps the
total, the length and the multiset of entries and is caught only here. -/
theorem dequeueValue_enqueueValueWithSize_nonempty (sizes : SizeClass Size)
    (q q' : Queue α Size) (value : α) (size : Size) (entry : QueueEntry α Size)
    (rest : List (QueueEntry α Size)) (hentries : q.entries = entry :: rest)
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    (dequeueValue sizes q').map Prod.fst = some entry.value := by
  rw [dequeueValue_value_eq_head, enqueueValueWithSize_entries sizes q q' value size hok,
    hentries]
  simp

theorem peekQueueValue_enqueueValueWithSize_nonempty (sizes : SizeClass Size)
    (q q' : Queue α Size) (value : α) (size : Size) (entry : QueueEntry α Size)
    (rest : List (QueueEntry α Size)) (hentries : q.entries = entry :: rest)
    (hok : enqueueValueWithSize sizes q value size = Except.ok q') :
    peekQueueValue q' = some entry.value := by
  rw [peekQueueValue_eq_head, enqueueValueWithSize_entries sizes q q' value size hok, hentries]
  simp

/-! ## S6 — reset

Census row `op.reset-queue`. -/

theorem resetQueue_eq (sizes : SizeClass Size) (q : Queue α Size) :
    resetQueue sizes q = ({ entries := [], totalSize := sizes.zero } : Queue α Size) := rfl

theorem resetQueue_entries (sizes : SizeClass Size) (q : Queue α Size) :
    (resetQueue sizes q).entries = [] := rfl

theorem resetQueue_totalSize (sizes : SizeClass Size) (q : Queue α Size) :
    (resetQueue sizes q).totalSize = sizes.zero := rfl

/-- Reset carries no carrier hypothesis: it restores the invariant whatever
the arithmetic did before it, because it writes `0` rather than computing it.
`WS-DATA-CE-006` is the reset that keeps a drifted running total. -/
theorem resetQueue_wf (sizes : SizeClass Size) (q : Queue α Size) :
    Queue.WF sizes (resetQueue sizes q) := rfl

theorem resetQueue_sizesAdmissible (sizes : SizeClass Size) (q : Queue α Size) :
    Queue.SizesAdmissible sizes (resetQueue sizes q) := by
  intro entry hentry
  simp [resetQueue] at hentry

theorem resetQueue_idempotent (sizes : SizeClass Size) (q : Queue α Size) :
    resetQueue sizes (resetQueue sizes q) = resetQueue sizes q := rfl

theorem resetQueue_eq_empty (sizes : SizeClass Size) (q : Queue α Size) :
    resetQueue sizes q = Queue.empty sizes := rfl

theorem resetQueue_dequeueValue (sizes : SizeClass Size) (q : Queue α Size) :
    dequeueValue sizes (resetQueue sizes q) = none := rfl

end WhatwgStreams.Data
