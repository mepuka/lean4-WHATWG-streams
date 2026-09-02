import Whatwg.Streams.Data.Queue

/-!
# Data.DyadicSize.lean — the `P3-R1` instance (landed by the coordinator, 2026-09-02)

The `P3-R1` instance. Written by the P3 builder outside its fence and allocated to this module by the coordinator at landing. Section 3
item 7 of `test/contracts/queue-with-sizes.contract.md` says the packet
"declares no arithmetic instance ... the instance arrives with the `P3-R1`
ruling, in a module this contract does not fence", and the builder's fence is
exactly `Whatwg/Streams/Data/Queue.lean` and `Whatwg/Streams/Data/Strategy.lean`.
It is written here, compiled against the landed surface, and handed to the
coordinator with a module allocation request: a new `Whatwg/Streams/Data/`
module, an `import` line in `Whatwg.Streams.lean`, and a twelfth existing-type
row in `docs/DATA-DAG.md`, none of which the builder may write.

## The carrier, and why this one

`P3-R1` rules option (i): an exact carrier extended with `nan`, `posInfinity`
and `negInfinity`, built from `Int`/`Nat`, as either a dyadic rational with an
`Int × Nat` exponent or a normalized rational pair.

This is the dyadic rational with the exponent **fixed at 1074**: `finite u`
denotes `u * 2 ^ (-1074)`. It is the subgroup `2 ^ (-1074) · Z` of the
rationals. Three reasons, in order of weight:

1. **It contains every finite binary64 exactly.** The spacing of the subnormal
   doubles is `2 ^ (-1074)`, and every finite double — normal or subnormal —
   is an integer multiple of it. So the value a conforming host can put in
   `[[queueTotalSize]]` before rounding is always representable here, and the
   subgroup is closed under `+` and `−`, so every exact sum of such values
   stays in it. A carrier on the breaker's `2 ^ (-106)` grid
   (`WhatwgTest/Streams/Counterexamples/Data/Queue.lean`) reproduces the pinned
   WPT case and nothing smaller; this one reproduces every double.
2. **A per-value exponent would make the `Exact` equations unprovable as
   stated.** `SizeClass.Exact` is four equations *in the carrier*, i.e. Lean
   equalities. With a per-value exponent, `(1, 0)` and `(2, 1)` denote the same
   rational and are different terms, so `sub_add_cancel` returns a
   representative rather than the argument and the equation is false. Repairing
   that needs a canonical form, hence a proof-carrying normalization invariant
   and a homomorphism into a rational type that Lean core does not have. The
   fixed exponent makes representation equality *be* numeric equality, and the
   four equations become `Int` arithmetic.
3. **`Ordered.add_admissible` is where overflow lives**, and `Int` is
   unbounded, so it holds. The three special points are constructors, so
   `Classified` holds and no refusal law of the packet is vacuous
   (`WS-DATA-CE-007`).

What it does not do: represent a value below `2 ^ (-1074)` in magnitude. There
is no finite binary64 there, so nothing the model receives is lost; a future
calculus needing a finer grid raises the exponent and every proof below is
unchanged in shape. The host's *rounding* remains outside the model in either
case — that is `DATA-FB-ROUNDING`, and `WS-DATA-CE-001` is the registered
disagreement.
-/

set_option autoImplicit false

namespace Whatwg.Streams.Data

/-- A size on the fixed dyadic grid `2 ^ (-1074)`, extended with the three
special points an ECMAScript Number has. `finite u` denotes
`u * 2 ^ (-1074)`. -/
inductive DyadicSize
  /-- `NaN`. -/
  | nan
  /-- `+∞`. -/
  | posInfinity
  /-- `-∞`. -/
  | negInfinity
  /-- `units * 2 ^ (-1074)`. -/
  | finite (units : Int)
deriving DecidableEq, Repr

namespace DyadicSize

/-- `IsNonNegativeNumber` step 2. -/
def isNaN : DyadicSize → Bool
  | .nan => true
  | _ => false

/-- `IsNonNegativeNumber` step 3, and `ExtractHighWaterMark` step 3. -/
def isNegative : DyadicSize → Bool
  | .negInfinity => true
  | .finite units => decide (units < 0)
  | _ => false

/-- Infinitude, which `EnqueueValueWithSize` step 3 tests with the sign. -/
def isInfinite : DyadicSize → Bool
  | .posInfinity => true
  | .negInfinity => true
  | _ => false

/-- Negation, used to define subtraction, with the IEEE-754 signs on the
special points. -/
def neg : DyadicSize → DyadicSize
  | .nan => .nan
  | .posInfinity => .negInfinity
  | .negInfinity => .posInfinity
  | .finite units => .finite (-units)

/-- Exact addition on the grid, with `NaN` propagating and `+∞ + -∞` a `NaN`,
as IEEE-754 has it. On the finite values it is `Int` addition, which is where
"exact" lives: nothing rounds. -/
def add : DyadicSize → DyadicSize → DyadicSize
  | .nan, _ => .nan
  | _, .nan => .nan
  | .posInfinity, .negInfinity => .nan
  | .negInfinity, .posInfinity => .nan
  | .posInfinity, _ => .posInfinity
  | _, .posInfinity => .posInfinity
  | .negInfinity, _ => .negInfinity
  | _, .negInfinity => .negInfinity
  | .finite a, .finite b => .finite (a + b)

/-- Subtraction is addition of the negation, so `DequeueValue` step 5 is the
exact inverse of `EnqueueValueWithSize` step 5 on admissible sizes. -/
def sub (a b : DyadicSize) : DyadicSize := add a (neg b)

/-- `1.0` is exactly `2 ^ 1074` units of `2 ^ (-1074)`. Written as a `Nat`
cast so its non-negativity is structural rather than a 324-digit kernel
computation. -/
def oneUnits : Int := ((2 ^ 1074 : Nat) : Int)

/-- The `P3-R1` instance. -/
def sizes : SizeClass DyadicSize where
  zero := .finite 0
  one := .finite oneUnits
  nan := .nan
  posInfinity := .posInfinity
  negInfinity := .negInfinity
  add := add
  sub := sub
  isNaN := isNaN
  isNegative := isNegative
  isInfinite := isInfinite

/-- The admissible sizes are exactly the non-negative points of the grid. -/
theorem admissible_iff (v : DyadicSize) :
    sizes.Admissible v ↔ ∃ units : Int, v = .finite units ∧ 0 ≤ units := by
  cases v with
  | nan => simp [SizeClass.Admissible, sizes, isNaN, isNegative, isInfinite]
  | posInfinity => simp [SizeClass.Admissible, sizes, isNaN, isNegative, isInfinite]
  | negInfinity => simp [SizeClass.Admissible, sizes, isNaN, isNegative, isInfinite]
  | finite units =>
      constructor
      · intro hadmissible
        refine ⟨units, rfl, ?_⟩
        have hneg : sizes.isNegative (DyadicSize.finite units) = false := hadmissible.2.1
        simp only [sizes, isNegative, decide_eq_false_iff_not] at hneg
        omega
      · intro hexists
        cases hexists with
        | intro u hu =>
            have hunits : units = u := DyadicSize.finite.inj hu.1
            have hle : 0 ≤ u := hu.2
            subst hunits
            refine ⟨rfl, ?_, rfl⟩
            show sizes.isNegative (DyadicSize.finite units) = false
            simp only [sizes, isNegative, decide_eq_false_iff_not]
            omega

theorem classified : sizes.Classified where
  nan_isNaN := rfl
  nan_not_negative := rfl
  nan_not_infinite := rfl
  posInfinity_infinite := rfl
  posInfinity_not_negative := rfl
  posInfinity_not_nan := rfl
  negInfinity_infinite := rfl
  negInfinity_negative := rfl
  negInfinity_not_nan := rfl
  nan_isolated := by
    intro v hv
    cases v with
    | nan => exact ⟨rfl, rfl⟩
    | posInfinity => simp [sizes, isNaN] at hv
    | negInfinity => simp [sizes, isNaN] at hv
    | finite units => simp [sizes, isNaN] at hv

theorem ordered : sizes.Ordered where
  zero_admissible := by
    rw [admissible_iff]
    exact ⟨0, rfl, Int.le_refl 0⟩
  one_admissible := by
    rw [admissible_iff]
    refine ⟨oneUnits, rfl, ?_⟩
    unfold oneUnits
    omega
  add_admissible := by
    intro a b ha hb
    rw [admissible_iff] at ha hb
    cases ha with
    | intro ua hua =>
        cases hb with
        | intro ub hub =>
            rw [admissible_iff]
            refine ⟨ua + ub, ?_, ?_⟩
            · rw [hua.1, hub.1]; rfl
            · omega

theorem exact : sizes.Exact where
  add_assoc := by
    intro a b c ha hb hc
    rw [admissible_iff] at ha hb hc
    cases ha with
    | intro ua hua => cases hb with
      | intro ub hub => cases hc with
        | intro uc huc =>
            rw [hua.1, hub.1, huc.1]
            show DyadicSize.finite ((ua + ub) + uc) = DyadicSize.finite (ua + (ub + uc))
            rw [Int.add_assoc]
  add_comm := by
    intro a b ha hb
    rw [admissible_iff] at ha hb
    cases ha with
    | intro ua hua => cases hb with
      | intro ub hub =>
          rw [hua.1, hub.1]
          show DyadicSize.finite (ua + ub) = DyadicSize.finite (ub + ua)
          rw [Int.add_comm]
  zero_add := by
    intro a ha
    rw [admissible_iff] at ha
    cases ha with
    | intro ua hua =>
        rw [hua.1]
        show DyadicSize.finite (0 + ua) = DyadicSize.finite ua
        rw [Int.zero_add]
  sub_add_cancel := by
    intro a b ha hb
    rw [admissible_iff] at ha hb
    cases ha with
    | intro ua hua => cases hb with
      | intro ub hub =>
          rw [hua.1, hub.1]
          show DyadicSize.finite ((ua + ub) + -ub) = DyadicSize.finite ua
          congr 1
          omega

end DyadicSize

end Whatwg.Streams.Data
