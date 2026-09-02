import Init

/-
Counterexample witnesses for the P3 queue-with-sizes packet.

Contract packet: `test/contracts/queue-with-sizes.contract.md`
Attack shapes:   `test/counterexamples/data/ATTACKS.md`
Register rows:   `WS-DATA-CE-001` .. `WS-DATA-CE-010` in
                 `test/counterexamples/REGISTER.md`

This module is GREEN now and stays green after the builder lands. It is a
breaker-owned, self-contained model in the `Breaker` namespace: it shares no
name with the frozen surface, imports nothing from `Whatwg`, and
proves the attacks rather than the production laws. Its witnesses remain
executable after the repair so the repair stays testable.

Every proposition below is closed by `decide`, so the Lean kernel checks it
with no compiler in the trust path. The receipts are inside the semantic
ceiling; `WhatwgTest/Streams/Data/QueueAxiomReport.lean` records the frozen
surface's receipts once that surface exists.
-/

set_option autoImplicit false

-- `bitLen` below carries an explicit step budget so that it is structurally
-- recursive and the kernel can reduce it. Unfolding that budget during
-- elaboration of a ground `decide` exceeds the default frame limit, so the
-- limit is raised. This changes no trust boundary: it is an elaborator
-- resource bound, not an axiom, and every proposition here is still closed by
-- kernel reduction alone.
set_option maxRecDepth 8000

namespace WhatwgTest.Streams.Counterexamples.Data.Breaker

/-! ## The grid

Every number the pinned WPT floating-point cases mention is an exact multiple
of `2 ^ (-106)`, so a plain `Int` counting those units represents each of them
exactly. `U` is that count. Nothing here is a `Float`: Lean's `Float`
operations are opaque `extern` constants, so no equation between two of them
reduces in the kernel, and the only tactic that decides one is `native_decide`,
which this repository forbids. That fact is itself evidence for `P3-R1` and is
recorded in the contract, not worked around here.
-/

/-- A count of `2 ^ (-106)` units. -/
abbrev U := Int

/-- The binary64 value nearest the literal `1e-16`, in units of `2 ^ (-106)`:
its significand is `8112963841460668` and its exponent is `2 ^ (-106)`. Read
off the pinned WPT literal with `BitConverter.DoubleToInt64Bits`. -/
def eps : U := 8112963841460668

/-- The binary64 value `1.0`, in the same units. -/
def one : U := 2 ^ 106

/-- Bit length of `n`, i.e. the least `b` with `n < 2 ^ b`. Written with an
explicit step budget so it is structurally recursive and reduces in the
kernel; `Nat.log2` is well-founded and does not. The budget is never reached:
every value here is below `2 ^ 128`. -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, n => if n = 0 then 0 else bitLenAux fuel (n / 2) + 1

def bitLen (n : Nat) : Nat := bitLenAux 256 n

/-- Round `n` to the nearest multiple of `2 ^ k`, ties to even. -/
def roundAt (k : Nat) (n : Int) : Int :=
  let m : Int := 2 ^ k
  let q := n / m
  let r := n % m
  let twice := 2 * r
  if twice < m then q * m
  else if m < twice then (q + 1) * m
  else if q % 2 == 0 then q * m else (q + 1) * m

/-- Round to the nearest binary64, on this grid, by round-to-nearest-even at
53 significant bits. Subnormals and overflow are outside the range every value
here occupies, and the contract says so rather than this definition pretending
otherwise. -/
def roundDouble (n : Int) : Int :=
  let b := bitLen n.natAbs
  if b ≤ 53 then n else roundAt (b - 53) n

/-! ## Two arithmetic worlds

`Ops` is the breaker's mirror of the frozen `SizeClass` arithmetic, reduced to
the three fields the queue algorithms use. `exactOps` is option (i) of `P3-R1`;
`roundedOps` is option (ii). Every law the contract states under
`SizeClass.Exact` holds of the first and fails of the second.
-/

structure Ops where
  zero : U
  add : U → U → U
  sub : U → U → U

def exactOps : Ops := { zero := 0, add := (· + ·), sub := (· - ·) }

def roundedOps : Ops :=
  { zero := 0
    add := fun a b => roundDouble (a + b)
    sub := fun a b => roundDouble (a - b) }

/-! ## `WS-DATA-CE-001` — the running total drifts away from the sum of sizes

The pinned case is `vendor/wpt-480fdfcd/streams/readable-streams/`
`floating-point-total-queue-size.any.js`, the test named
"Floating point arithmetic must manifest near 0 (total ends up positive, but
clamped)". Its chunk sizes are `1e-16` and `1`, and its third assertion reads
`desiredSize === 0 - 1e-16 - 1 + 1e-16`, which in double arithmetic is
`-0.9999999999999999`, not `-1`.

The run below is that test's first three steps: enqueue `1e-16`, enqueue `1`,
dequeue `1e-16`.
-/

def runExact : U := exactOps.sub (exactOps.add (exactOps.add exactOps.zero eps) one) eps

def runRounded : U := roundedOps.sub (roundedOps.add (roundedOps.add roundedOps.zero eps) one) eps

/-- Under exact arithmetic the total returns to `1`, the sum of the one chunk
still queued. -/
theorem ce001_exact_total : runExact = one := by decide

/-- Under binary64 arithmetic it does not. `9007199254740991 * 2 ^ 53` units is
the double `0.9999999999999999`, which is exactly the value the pinned WPT
assertion demands of every conforming host. -/
theorem ce001_rounded_total : runRounded = 9007199254740991 * 2 ^ 53 := by decide

/-- The two carriers disagree on the pinned case. This is the disagreement
`P3-R1` rules on. -/
theorem ce001_carriers_disagree : runExact ≠ runRounded := by decide

/-- The gap is exactly one unit in the last place of `1.0`, `2 ^ (-53)`. -/
theorem ce001_gap : runExact - runRounded = 2 ^ 53 := by decide

/-- The specification's own warning, mechanized: with a rounding carrier the
`[[queueTotalSize]]` slot is not the sum of the sizes of the chunks in
`[[queue]]`. One chunk of size `1` remains queued, and the running total is not
`1`. Any `Queue.WF` obligation stated without an exactness hypothesis is
therefore false of the specification's own carrier. -/
theorem ce001_wf_broken : runRounded ≠ exactOps.add exactOps.zero one := by decide

/-- The same run under an exact carrier does satisfy the invariant. -/
theorem ce001_wf_holds_exact : runExact = exactOps.add exactOps.zero one := by decide

/-- The divergence reaches mask M1, not only M2. With a high water mark of `1`,
`desiredSize` is `highWaterMark - [[queueTotalSize]]`: exactly zero under the
exact carrier, so no pull is requested; strictly positive under the rounding
carrier, so the underlying source is pulled and the chunk sequence a consumer
observes can differ. -/
theorem ce001_desired_size_exact : one - runExact = 0 := by decide

theorem ce001_desired_size_rounded : 0 < one - runRounded := by decide

/-- The next dequeue drives the rounding carrier's total below zero, which is
the only reason the specification's `DequeueValue` step 6 clamp exists. -/
theorem ce001_clamp_reachable_rounded :
    roundedOps.sub runRounded one < 0 := by decide

/-- Under the exact carrier that same step lands on zero, so step 6 never
fires. A green witness for step 6 under an exact carrier is a vacuity theorem,
not a witness of the branch. -/
theorem ce001_clamp_unreachable_exact : exactOps.sub runExact one = 0 := by decide

/-! ## `WS-DATA-CE-002` — a fold-order choice is observable

`Queue.sizeSum` must be the left fold that mirrors the order `EnqueueValueWithSize`
accumulates in. Under a rounding carrier a right fold gives a different total
for the same queue, so the choice is not cosmetic.
-/

def sumL (ops : Ops) (sizes : List U) : U := sizes.foldl ops.add ops.zero

def sumR (ops : Ops) (sizes : List U) : U := sizes.foldr (fun s acc => ops.add s acc) ops.zero

def foldWitness : List U := [one, eps, eps]

theorem ce002_folds_agree_exact : sumL exactOps foldWitness = sumR exactOps foldWitness := by decide

theorem ce002_folds_differ_rounded :
    sumL roundedOps foldWitness ≠ sumR roundedOps foldWitness := by decide

theorem ce002_left_fold_rounded : sumL roundedOps foldWitness = one := by decide

theorem ce002_right_fold_rounded : sumR roundedOps foldWitness = one + 2 ^ 54 := by decide

/-! ## The queue model the remaining attacks run on

A minimal exact-arithmetic queue-with-sizes. `enqueue`, `dequeue`, `peek` and
`reset` are the breaker's reference readings of the four algorithms; each
mutant below changes exactly one of them.
-/

structure Entry where
  value : Nat
  size : U
deriving DecidableEq, Repr

structure Q where
  entries : List Entry
  total : U
deriving DecidableEq, Repr

def Q.empty : Q := { entries := [], total := 0 }

/-- `none` is the `RangeError`. -/
def enqueue (q : Q) (v : Nat) (s : U) : Option Q :=
  if s < 0 then none
  else some { entries := q.entries ++ [{ value := v, size := s }], total := q.total + s }

def clampNonNegative (t : U) : U := if t < 0 then 0 else t

def dequeue (q : Q) : Option (Nat × Q) :=
  match q.entries with
  | [] => none
  | e :: rest => some (e.value, { entries := rest, total := clampNonNegative (q.total - e.size) })

def peek (q : Q) : Option Nat :=
  match q.entries with
  | [] => none
  | e :: _ => some e.value

def reset (_q : Q) : Q := { entries := [], total := 0 }

def twoChunks : Q :=
  { entries := [{ value := 10, size := 3 }, { value := 20, size := 5 }], total := 8 }

/-! ## `WS-DATA-CE-003` — enqueue accepts a negative size -/

def enqueueNoGuard (q : Q) (v : Nat) (s : U) : Option Q :=
  some { entries := q.entries ++ [{ value := v, size := s }], total := q.total + s }

theorem ce003_reference_refuses : enqueue Q.empty 7 (-1) = none := by decide

theorem ce003_mutant_accepts : enqueueNoGuard Q.empty 7 (-1) ≠ none := by decide

/-- The cost of accepting it: the running total goes negative while the queue
is non-empty, a state no conforming host can reach. -/
theorem ce003_mutant_total_negative :
    (enqueueNoGuard Q.empty 7 (-1)).map Q.total = some (-1) := by decide

/-- Every size in the pinned WPT list `[NaN, -Infinity, Infinity, -1]` must be
refused. `-1` is the one of the four this exact-integer model can express; the
other three are refused by classification and are `WS-DATA-CE-007`. -/
theorem ce003_wpt_minus_one_refused : enqueue twoChunks 30 (-1) = none := by decide

/-! ## `WS-DATA-CE-004` — dequeue answers on an empty queue -/

def dequeueNoAssert (q : Q) : Option (Nat × Q) :=
  match q.entries with
  | [] => some (0, q)
  | e :: rest => some (e.value, { entries := rest, total := clampNonNegative (q.total - e.size) })

theorem ce004_reference_refuses : dequeue Q.empty = none := by decide

theorem ce004_mutant_answers : dequeueNoAssert Q.empty = some (0, Q.empty) := by decide

/-- The two agree everywhere the specification's assertion holds, so no
non-empty case discriminates them. -/
theorem ce004_agree_when_nonempty : dequeueNoAssert twoChunks = dequeue twoChunks := by decide

/-! ## `WS-DATA-CE-005` — peek mutates -/

def peekPopping (q : Q) : Option Nat × Q :=
  match q.entries with
  | [] => (none, q)
  | e :: rest => (some e.value, { entries := rest, total := clampNonNegative (q.total - e.size) })

theorem ce005_reference_value : peek twoChunks = some 10 := by decide

/-- The mutant returns the right value, so no value-only comparison catches it. -/
theorem ce005_mutant_same_value : (peekPopping twoChunks).fst = peek twoChunks := by decide

/-- It is caught only by comparing the container. A frozen `peekQueueValue`
whose result type is `Option α` cannot express the mutation at all, which is
why the contract freezes that result type rather than a pair. -/
theorem ce005_mutant_mutates : (peekPopping twoChunks).snd ≠ twoChunks := by decide

/-- Peeking twice must give the same answer. The mutant, threaded, does not. -/
theorem ce005_mutant_not_idempotent :
    (peekPopping (peekPopping twoChunks).snd).fst ≠ (peekPopping twoChunks).fst := by decide

/-! ## `WS-DATA-CE-006` — reset leaves a non-zero total

The queue below is one a rounding carrier can reach: empty of entries, with a
residue in the total. `ResetQueue` sets `[[queueTotalSize]]` to `0` outright,
so the residue cannot survive a reset.
-/

def drifted : Q := { entries := [], total := 17 }

def resetKeepingTotal (q : Q) : Q := { entries := [], total := q.total }

theorem ce006_reference_zeroes : (reset drifted).total = 0 := by decide

theorem ce006_mutant_keeps : (resetKeepingTotal drifted).total ≠ 0 := by decide

/-- The two mutants agree on the entries, so an entries-only law does not
separate them. -/
theorem ce006_entries_agree : (resetKeepingTotal drifted).entries = (reset drifted).entries := by
  decide

/-- Reset is the one operation whose result satisfies the sum invariant
whatever the carrier did before it, which is why the contract states
`reset_wf` with no exactness hypothesis. -/
theorem ce006_reset_restores_invariant : (reset drifted).total = sumL exactOps [] := by decide

/-! ## `WS-DATA-CE-007` — the classification refusals, and their vacuity trap

`EnqueueValueWithSize` refuses `NaN`, a negative size, and `+∞`;
`ExtractHighWaterMark` refuses `NaN` and a negative high water mark but
*allows* `+∞`. A carrier that cannot represent `NaN` or `+∞` satisfies every
one of those refusal laws vacuously.
-/

inductive Ext
  | nan
  | posInf
  | negInf
  | fin (n : U)
deriving DecidableEq, Repr

def Ext.isNaN : Ext → Bool
  | .nan => true
  | _ => false

def Ext.isNegative : Ext → Bool
  | .negInf => true
  | .fin n => decide (n < 0)
  | _ => false

def Ext.isInfinite : Ext → Bool
  | .posInf => true
  | .negInf => true
  | _ => false

/-- `IsNonNegativeNumber`, then the `+∞` step, as `EnqueueValueWithSize`
orders them. -/
def sizeAccepted (s : Ext) : Bool :=
  !s.isNaN && !s.isNegative && !s.isInfinite

/-- The four sizes the pinned WPT case "Readable stream: invalid strategy.size
return value" enumerates. Every one is refused. -/
theorem ce007_wpt_sizes_all_refused :
    (([Ext.nan, Ext.negInf, Ext.posInf, Ext.fin (-1)]).all
      (fun s => !sizeAccepted s)) = true := by decide

theorem ce007_finite_nonnegative_accepted : sizeAccepted (Ext.fin 5) = true := by decide

/-- A carrier with no `NaN`. -/
def NatSize := Nat

def natIsNaN (_s : NatSize) : Bool := false

def enqueueNeverRefuses (q : Q) (v : Nat) (_s : NatSize) : Option Q :=
  some { entries := q.entries ++ [{ value := v, size := 0 }], total := q.total }

/-- The vacuity trap, proved: on a carrier whose `isNaN` is constantly false,
an implementation that never refuses anything still satisfies the frozen
`NaN` refusal law. This is why the contract requires the `SizeClass` to carry
`nan`, `posInfinity` and `negInfinity` as fields and requires
`SizeClass.Classified` to classify them, rather than leaving the predicates
free. -/
theorem ce007_nan_refusal_is_vacuous (q : Q) (v : Nat) (s : NatSize) :
    natIsNaN s = true → enqueueNeverRefuses q v s = none := by
  intro h
  exact absurd h (by simp [natIsNaN])

/-! ## `WS-DATA-CE-008` — `ExtractHighWaterMark` refuses `+∞`

The specification note is explicit: "+∞ is explicitly allowed as a valid high
water mark. It causes backpressure to never be applied." The pinned WPT list of
high water marks that must throw is `[-1, -Infinity, NaN, 'foo', {}]`, and
`Infinity` is deliberately absent from it. A model that treated the size rule
and the high-water-mark rule as one rule would refuse `+∞` and contradict both.
-/

/-- `none` is the `RangeError`; the argument is the dictionary entry, absent
as `none`. -/
def extractHighWaterMark (entry : Option Ext) (defaultHWM : Ext) : Option Ext :=
  match entry with
  | none => some defaultHWM
  | some hwm => if hwm.isNaN || hwm.isNegative then none else some hwm

def extractHighWaterMarkSharingTheSizeRule (entry : Option Ext) (defaultHWM : Ext) : Option Ext :=
  match entry with
  | none => some defaultHWM
  | some hwm => if sizeAccepted hwm then some hwm else none

theorem ce008_reference_allows_pos_inf :
    extractHighWaterMark (some Ext.posInf) (Ext.fin 1) = some Ext.posInf := by decide

theorem ce008_mutant_refuses_pos_inf :
    extractHighWaterMarkSharingTheSizeRule (some Ext.posInf) (Ext.fin 1) = none := by decide

/-- The two rules agree on every other pinned input, so only `+∞` separates
them. -/
theorem ce008_rules_agree_off_pos_inf :
    (([Ext.nan, Ext.negInf, Ext.fin (-1), Ext.fin 0, Ext.fin 7]).all
      (fun h => extractHighWaterMark (some h) (Ext.fin 1) ==
        extractHighWaterMarkSharingTheSizeRule (some h) (Ext.fin 1))) = true := by decide

/-- The pinned WPT high-water-mark refusals. `'foo'` and `{}` reach the
algorithm as `NaN` after the Web IDL unrestricted-double conversion, which is a
host boundary and not modelled here. -/
theorem ce008_wpt_hwms_all_refused :
    (([Ext.fin (-1), Ext.negInf, Ext.nan]).all
      (fun h => extractHighWaterMark (some h) (Ext.fin 1) == none)) = true := by decide

/-! ## `WS-DATA-CE-009` — `ExtractHighWaterMark` normalizes its input

The algorithm at this pin returns the high water mark unchanged. Its anchor id
is still `validate-and-normalize-high-water-mark`, from an earlier revision that
had a normalizing step, and the name invites a model that clamps. A clamping
mutant is not idempotent on its own accepted output either.
-/

def extractHighWaterMarkClamping (entry : Option Ext) (defaultHWM : Ext) : Option Ext :=
  match entry with
  | none => some defaultHWM
  | some hwm =>
      if hwm.isNaN || hwm.isNegative then none
      else if hwm.isInfinite then some (Ext.fin 0) else some hwm

theorem ce009_reference_is_the_identity_on_accepted :
    (([Ext.posInf, Ext.fin 0, Ext.fin 7]).all
      (fun h => extractHighWaterMark (some h) (Ext.fin 1) == some h)) = true := by decide

theorem ce009_mutant_changes_pos_inf :
    extractHighWaterMarkClamping (some Ext.posInf) (Ext.fin 1) ≠ some Ext.posInf := by decide

/-- Idempotence does not separate them: the clamping mutant is idempotent too,
because `0` is a fixed point. Only the identity law above catches it, which is
why the contract freezes `extractHighWaterMark_id_on_accepted` and not an
idempotence law. -/
theorem ce009_mutant_is_still_idempotent :
    (extractHighWaterMarkClamping (some Ext.posInf) (Ext.fin 1)).bind
        (fun h => extractHighWaterMarkClamping (some h) (Ext.fin 1)) =
      extractHighWaterMarkClamping (some Ext.posInf) (Ext.fin 1) := by decide

/-! ## `WS-DATA-CE-010` — FIFO violated by a stack

`EnqueueValueWithSize` appends and `DequeueValue` removes index `0`. A model
that pushes onto the front keeps the same total, the same length, and the same
set of entries, and is caught only by the order.
-/

def enqueueFront (q : Q) (v : Nat) (s : U) : Option Q :=
  if s < 0 then none
  else some { entries := { value := v, size := s } :: q.entries, total := q.total + s }

def fifoRun (step : Q → Nat → U → Option Q) : Option Nat :=
  (step Q.empty 1 3).bind fun q1 =>
    (step q1 2 5).bind fun q2 =>
      (dequeue q2).map Prod.fst

theorem ce010_reference_is_fifo : fifoRun enqueue = some 1 := by decide

theorem ce010_mutant_is_lifo : fifoRun enqueueFront = some 2 := by decide

/-- The totals agree, so no total-size law separates them. -/
theorem ce010_totals_agree :
    ((enqueue Q.empty 1 3).bind fun q => enqueue q 2 5).map Q.total =
      ((enqueueFront Q.empty 1 3).bind fun q => enqueueFront q 2 5).map Q.total := by decide

/-- So do the lengths. -/
theorem ce010_lengths_agree :
    ((enqueue Q.empty 1 3).bind fun q => enqueue q 2 5).map (fun q => q.entries.length) =
      ((enqueueFront Q.empty 1 3).bind fun q => enqueueFront q 2 5).map
        (fun q => q.entries.length) := by decide

/-- `PeekQueueValue` and `DequeueValue` must answer with the same value; the
stack model breaks the pair together, which is the sharpest single statement of
the attack. -/
theorem ce010_peek_dequeue_agree_reference :
    ((enqueue Q.empty 1 3).bind fun q => enqueue q 2 5).bind (fun q => peek q) =
      some 1 := by decide

end WhatwgTest.Streams.Counterexamples.Data.Breaker
