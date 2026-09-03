# Better patterns for `Whatwg.Html`: a Lean 4.33.1 core/Std report

Research pass, 2026-09-03, by a read-only Opus agent at the operator's
request during slice H3 of `docs/HTML-PACKAGE-PLAN.md`. It establishes no
semantic claim. Every number below was measured on a synthetic model, not on
the repository's modules; every unverified statement is marked INFERRED.

**Method note, so you can discount correctly.** I read the repository files and the toolchain sources under
`/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`. I did **not** run `lake`. Where I give
a number, I measured it by piping a synthetic file to
`/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --stdin` from `cwd=/`, with a
**synthetic 115-constructor enum + 69 synthetic content sets** shaped like `Tag`/`ContentSet`, not with your
actual modules. So the numbers are *representative*, not *your* numbers; re-bisect against
`WhatwgTest/Html/DecideBenchmark.lean` before you freeze a bound. Everything I could not execute or read in
the toolchain source is marked **INFERRED**.

Since I started reading, another agent landed `Whatwg/Html/Node/{Typed,Combinators,Erasure}.lean` and rewrote
`WhatwgTest/Html/DecideBenchmark.lean` (now 106 lines, with whole-tree probes at 1200/1800 heartbeats). I read
the new `Typed.lean` and the head of `Combinators.lean` and this report is written against that state: several
things I would otherwise have recommended for section 3 are already done there, so section 3 is mostly about
what to change next rather than what to build.

---

## 0. Executive summary

| # | Question | Recommendation | Confidence |
| --- | --- | --- | --- |
| 1 | `Decidable (∀ t : Tag, p t)` | **Keep `forall_tag_of_all`, but change every `(by decide)` under it to `(by decide +kernel)`.** Measured 900 → 20 heartbeats on a representative subset lemma. Do *not* add a `Fintype`-like `Decidable (∀ t, p t)` instance; it is strictly worse (40 hb vs 20 hb kernel, 2000 hb vs 900 hb elaborator) and costs you a `decidable_of_iff` layer the kernel must chew through. | measured |
| 2 | Set representation | **Keep constructor dispatch for membership** — it is already O(1) `casesOn`, and a bitmask cannot beat it. **Add a parallel `Nat` bitmask projection for the *lattice lemmas only*.** A subset lemma becomes one `Nat.land` equation the kernel decides at ≤20 heartbeats instead of a 115-element `List.all` scan at 900. Elaboration of the generated module also drops (measured 1.56 s → 0.71 s wall for 69 sets). | measured |
| 3 | Typed tree | The landed design (`Element t inner`, `Child set`, computed index `childSet set t`, auto-param **last**) is right. Two changes: put `+kernel` on the auto-params, and add a `Child.weaken` coercion driven by `SubsetOf` so `Lattice`'s 27 inclusion theorems become usable at the call site. **Nested inductives are not an option** — I verified the kernel rejects `List (Node (childSet t set))`. | measured |
| 4 | `html!` diagnostics | `declare_syntax_cat` + a recursive `TermElabM` walker that carries the context as an **`Expr`**, uses `Meta.whnf` to evaluate `ContentSet.contains ctx t` and `childSet`, and `throwErrorAt` on the tag token. I built and ran a complete working skeleton; error text and position are exactly what you want. | measured (working skeleton) |
| 5 | Serializer proofs | **Escaping soundness must not be stated as "no `&amp;`"** — that statement is false and `decide` told me so. State it for `&lt;`, `&gt;`, `"` only, and get the `&amp;` half from a *local* `unescape` decoder with `unescape ∘ escape = id`, which also hands you `escape` injectivity for free. I compiled the whole chain in core; axioms `[propext]` only. Printer injectivity on the tree needs one prefix-determinacy lemma, which is real but bounded work. | measured for escaping; **INFERRED** for tree injectivity |
| 6 | Everything else | `deriving DecidableEq` on a 115-constructor **enum** already gave you `Tag.ctorIdx`, `Tag.ofNat`, and `Tag.ofNat_ctorIdx` for free, and the derived `DecidableEq` is *not* a 115×115 match — it is `Nat` equality on `ctorIdx`. Keep `Tag.all` a `List`. Do not `@[simp]` the 69 generated sets. `Tag.mem_all` is the single expensive declaration in `Lattice.lean` (4 000–20 000 hb); nothing I tried improves its order of magnitude, and it is a one-time cost. | measured |

---

## 1. Finite quantification over `Tag` without Mathlib

### 1.1 What the toolchain actually gives you

Facts I verified in the toolchain source (paths are under
`/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`):

- `Init/Data/List/Lemmas.lean:576` —
  `@[simp] theorem List.all_eq_true {l : List α} : l.all p = true ↔ ∀ x, x ∈ l → p x`.
  This is the lemma `forall_tag_of_all` is built on; it exists and is `simp`.
- `Lean/Meta/Constructions/CtorIdx.lean:25,29` — every inductive that eliminates into `Type` gets
  `T.ctorIdx : T → Nat` generated automatically (option `genCtorIdx`, default `true`, line 18–21).
  For **enum types** an additional deprecated alias `T.toCtorIdx` is emitted and marked deprecated
  since `2025-08-25` (lines 118–130). So write `Tag.ctorIdx`, not `Tag.toCtorIdx`; the latter still
  resolves but emits a deprecation warning, which under `warningAsError true` is a build failure.
  I confirmed this: `#check @T.toCtorIdx` on a derived 115-constructor enum printed
  ``warning: `T.toCtorIdx` has been deprecated: Use `T.ctorIdx` instead``.
- `Lean/Elab/Deriving/DecEq.lean:264–277` — `mkDecEqEnum`. For an *enum type* (all constructors
  nullary, which `Tag` and `ContentSet` both are), `deriving DecidableEq` generates

  ```lean
  instance : DecidableEq Tag := fun x y =>
    if h : x.ctorIdx = y.ctorIdx then isTrue (by ... ) else isFalse fun h => by subst h; contradiction
  ```

  So **`deriving DecidableEq` on your 115-constructor enum does not produce a quadratic match**; it produces
  one `Nat` equality, which the kernel does with GMP. This answers the question in the brief directly: no linear
  scan, and `t₁ == t₂` is O(1) in the kernel.
- `Lean/Elab/Deriving/DecEq.lean:220–262` — as a side effect of `mkDecEqEnum`, deriving `DecidableEq` on an
  enum **also** defines, and adds to the environment:
  - `Tag.ofNat : Nat → Tag`, built by `mkNatLookupTable` as a **balanced `bif ... Nat.ble` binary search tree**
    (I printed it: `bif n.ble 56 then bif n.ble 27 then ...`, depth ≈ ⌈log₂ 115⌉ = 7), with
    `ReducibilityHints.abbrev`;
  - `Tag.ofNat_ctorIdx : ∀ x, Tag.ofNat x.ctorIdx = x`, proved by `casesOn` with 115 `rfl`s.

  **You already have the `toCtorIdx`/`ofNat` round trip the brief asks about, for free, in
  `Whatwg/Html/Schema/Tags.lean`, because of the `deriving DecidableEq` on line 39.** Nothing in the
  repository uses it yet.

### 1.2 What `decide`, `decide +kernel` and `rfl` actually cost

Read `Lean/Elab/Tactic/Decide.lean`:

- `doElab` (lines 87–100): builds `of_decide_eq_true (rfl : decide p = true)` via
  `Lean.Meta.mkDecideProof` (`Lean/Meta/AppBuilder.lean:593`), then **reduces the instance in the elaborator
  with `whnf`** to check it is `isTrue`, then hands the term to the kernel, **which reduces it again**.
  Two full reductions; only the first is charged heartbeats.
- `doKernel` (lines 102–128): builds the same term but does **not** reduce it in the elaborator. It calls
  `mkAuxLemma` (`Lean/Meta/Tactic/AuxLemma.lean:43`) which, per the comment at lines 107–110, *caches the
  result in two ways: a `type`-indexed cache per module, and once the proof is in the environment the kernel
  need not check it again*. Only the kernel reduces, and kernel time is not heartbeat-charged.
- `preprocessPropToDecide` (lines 22–33) is where the two failure messages you will meet come from:
  `"Expected type must not contain metavariables"` (line 28) and `"Expected type must not contain free
  variables"` (line 30). Both matter for section 3.

Measured, on a synthetic 115-constructor enum `T` with two synthetic sets `SA` (86 members) and
`SB ⊇ SA` (100 members), goal `T.all.all (fun t => !SA t || SB t) = true`, bisecting `maxHeartbeats`
(largest failing value, then smallest passing value):

| Route | Fails at | Passes at |
| --- | --- | --- |
| `forall_T_of_all _ (by decide)` | 800 | 900 |
| `forall_T_of_all _ (by decide +kernel)` | — | **20** |
| `forall_T_of_all _ rfl` | 400 | (passes at 40 000; wall time 1.93 s vs 1.32 s) |
| `by decide` through a `Decidable (∀ t, p t)` instance | 1 000 | 2 000 |
| `by decide +kernel` through that instance | 20 | **40** |

Reading:

1. **`decide +kernel` is a 45× heartbeat saving on exactly the statements `Lattice.lean` is made of**, and it
   is already inside your ceiling: `#print axioms` on such a theorem gave `[propext]`, and on the bitmask
   variants `[propext, Quot.sound]`. `decide +kernel` mints **no** axiom (unlike `+native`, which routes
   through `elabNativeDecideCore` and `Lean.ofReduceBool`).
2. **A `Fintype`-like `Decidable (∀ t : Tag, p t)` instance is a regression, not an improvement.** Building it
   as `decidable_of_iff (∀ t ∈ Tag.all, p t) ⟨…⟩` costs the kernel an extra `decidable_of_iff` +
   `List.decidableBAll` layer: 40 hb instead of 20 under `+kernel`, 2 000 instead of 900 under plain `decide`.
   The only thing it buys is that you can write `by decide` on `∀ t : Tag, …` directly instead of
   `forall_tag_of_all _ (by decide)`. That is one line of ergonomics for a 2× kernel cost on every lemma in the
   module. **Do not add it.**
3. `rfl` is the worst of the three: it reduces in the elaborator at default transparency without the
   `decide`-specific fast path and without kernel caching.

`List.decidableBAll` does exist in core with the signature
`(p : α → Prop) → [DecidablePred p] → (l : List α) → Decidable (∀ x, x ∈ l → p x)` (verified by `#check`), so
the instance route *works*; it is just slower.

### 1.3 Recommendation

**Keep `forall_tag_of_all`. Change the tactic.** The change is mechanical and touches only proof scripts:

```lean
/-- `phrasing ⊆ flow5`. -/
theorem phrasing_subset_flow5 : SubsetOf Sets.phrasing Sets.flow5 :=
  subsetOf_of_all (by decide +kernel)   -- was: (by decide)
```

Two caveats to record in the module docstring before you do it:

- **`decide +kernel` ignores transparency.** The decide docstring (`Init/Tactics.lean:1416–1419`) is explicit:
  *"since it uses the kernel, it ignores transparency and can unfold everything"*. For your generated
  constructor-dispatch functions this is exactly what you want (there is nothing you are trying to keep
  irreducible). But it means a future `@[irreducible]` on a generated set silently stops protecting anything
  in these proofs.
- **`decide +kernel` adds an auxiliary lemma declaration per distinct proposition** (`mkAuxLemma`,
  `Decide.lean:113`). These are private `_auxLemma.N` constants in your module. Check
  `WhatwgTest/Audit/AxiomGate.lean` tolerates them: the gate is described as *"exhaustive over the compiled
  namespace rather than a hand-written theorem list"*, and it has a private-declaration allowlist keyed by
  *"exact owning module and original spelling, never by Lean's private-name counter"* — an aux lemma has no
  original spelling. **I did not verify that the gate currently covers `Whatwg/Html/` at all**: its docstring
  names `Whatwg/Streams/`, `WhatwgTest/Streams/` and `Gates/`. That is worth checking on its own terms; if
  `Whatwg/Html/` is outside the gate's tokenizer scope today, the HTML tree has no axiom gate.

One more thing worth stating as a theorem while you are in there, now that you know `Tag.ofNat` exists:

```lean
/-- `Tag.ctorIdx` and the derived `Tag.ofNat` are mutually inverse on the 115 indices, so a tag is
determined by its index. `Tag.ofNat_ctorIdx` is generated by `deriving DecidableEq`
(`Lean/Elab/Deriving/DecEq.lean` `mkEnumOfNatThm`). -/
theorem Tag.ctorIdx_injective {s t : Tag} (h : s.ctorIdx = t.ctorIdx) : s = t := by
  rw [← Tag.ofNat_ctorIdx s, ← Tag.ofNat_ctorIdx t, h]

theorem Tag.ctorIdx_lt (t : Tag) : t.ctorIdx < 115 := by cases t <;> decide
```

`Tag.ctorIdx_lt` costs about what `Tag.mem_all` costs (see §6.4) and is the bridge you need for §2.

---

## 2. Set representation: constructor dispatch vs bitmask

### 2.1 The claim to knock down first

The intuition "a 115-way `match` must be a linear scan" is wrong. A `match` on an enum compiles to
`Tag.casesOn`, and iota reduction of `casesOn` on a constructor is one step regardless of arity. The evidence
is in your own benchmark file — `Sets.flow5 .div = true := by decide` at `maxHeartbeats 20`, an 86-member set —
and I reproduced it: `CS.contains .s3 .c7` on a synthetic 69-set / 115-tag model reduces by `rfl` at
`maxHeartbeats 20`. So:

> **A bitmask cannot beat constructor dispatch on single-membership cost.** Both are ≤20 heartbeats. Anyone who
> proposes bitmasks "for speed at every node" is optimising something that is already O(1).

I confirmed the same for the mask side: with `M = 2^115 - 1` and `N = M ^^^ (1 <<< 40)` as literals,
`Nat.testBit M 114 = true`, `Nat.testBit N 40 = false` and `N &&& M = N` **all pass at `maxHeartbeats 20`**, in
both `decide` and `decide +kernel` mode. So the two representations tie at the node.

### 2.2 Where the bitmask does win: subset and disjointness

`SubsetOf a b` is currently a 115-element `List.all` scan: 900 heartbeats per lemma (§1.2). As a bitmask it is
**one `Nat.land` equation**, decided by the kernel's GMP path.

I verified the kernel really is GMP-accelerated for `Nat.land` and `Nat.shiftRight` (which `Nat.testBit`
reduces to — `Init/Data/Nat/Bitwise/Basic.lean:150`, `testBit m n := 1 &&& (m >>> n) != 0`): with
`maxHeartbeats 400`,

```lean
example : ((2^4000 - 1) &&& (2^4000 - 1) : Nat) = 2^4000 - 1 := by decide +kernel  -- passes
example : (Nat.testBit (2^4000-1) 3333) = true := by decide +kernel                -- passes
example : ((2^400 - 1) &&& 0 : Nat) = 1 := by decide +kernel
-- error: Tactic `decide` proved that the proposition ... is false   (so it really evaluated)
```

`Nat.land` is defined through `Nat.bitwise`, which is **well-founded recursion**
(`Init/Data/Nat/Bitwise/Basic.lean`, `decreasing_by apply bitwise_rec_lemma`). Without kernel acceleration a
4000-bit `land` would be hopeless. It is not. (I could not read the C++ kernel — this toolchain ships only
`src/lean` — so the *mechanism* is **INFERRED**; the *behaviour* is measured.)

The lemmas you need are in core. I compiled these:

```lean
/-- Membership as a bit of a mask. -/
@[inline] def Mem (m : Nat) (t : Tag) : Bool := m.testBit t.ctorIdx

/-- Subset from one `Nat.land` equation. No enumeration, no scan. -/
theorem subset_of_land {a b : Nat} (h : a &&& b = a) :
    ∀ t : Tag, Mem a t = true → Mem b t = true := by
  intro t ht
  have h2 : (a &&& b).testBit t.ctorIdx = true := by rw [h]; exact ht
  rw [Nat.testBit_and] at h2
  exact (Bool.and_eq_true _ _).mp h2 |>.2

/-- Disjointness from `a &&& b = 0`. -/
theorem disjoint_of_land_zero {a b : Nat} (h : a &&& b = 0) :
    ∀ t : Tag, Mem a t = true → Mem b t = false := by
  intro t ht
  unfold Mem at ht ⊢
  have h2 : (a &&& b).testBit t.ctorIdx = false := by rw [h]; simp
  rw [Nat.testBit_and, ht] at h2
  simpa using h2
```

Both compile. `#print axioms` gives `[propext, Quot.sound]` — inside your ceiling. `Nat.testBit_and` is
`Init/Data/Nat/Bitwise/Lemmas.lean:496`, `@[simp, grind =]`, exact statement
`(x &&& y).testBit i = (x.testBit i && y.testBit i)`. `Bool.and_eq_true` is core with signature
`((a && b) = true) = (a = true ∧ b = true)` (an `Eq` of `Prop`s, so `.mp` is `Eq.mp` — that works, I compiled it).

Then a call site is:

```lean
theorem phrasing_subset_flow5' :
    ∀ t : Tag, Mem Masks.phrasing t = true → Mem Masks.flow5 t = true :=
  subset_of_land (by decide +kernel)   -- one Nat.land on two 115-bit literals, ≤ 20 heartbeats
```

**20 heartbeats instead of 900, and the proof term is one equation instead of a 115-element list evaluation.**

### 2.3 The catch, and why I do not recommend replacing the representation

Three costs you must price in:

1. **The bridge is not free.** To turn `Mem Masks.flow5 t` back into `Sets.flow5 t` you need
   `∀ t, Sets.flow5 t = Masks.flow5.testBit t.ctorIdx`, which is exactly a 115-element reflection —
   one `forall_tag_of_all _ (by decide +kernel)` per set, 69 of them, at ≈20 hb each. That is a one-time
   cost, paid once, and it is what makes the two representations provably the same thing. Do that once and
   every lattice lemma afterwards is O(1).
2. **Set *equality* needs more than `land`.** `Masks.a = Masks.b → sets equal` is trivial. The converse
   ("equal as membership functions ⟹ equal masks") needs surjectivity of `ctorIdx` onto `Fin 115` *and*
   `mask < 2^115`, i.e. that no mask has junk bits above 114. If you generate the masks, that is an invariant
   of the emitter you can also state as `Masks.flow5 < 2^115 := by decide +kernel`. **INFERRED** that this is
   cheap; I did not measure `<` on 115-bit literals, but `Nat.ble` is on the same accelerated path as `land`.
3. **`UInt64` pairs and `Fin 115`-indexed bit vectors are worse than `Nat`.** `UInt64` arithmetic goes through
   `Fin (2^64)` with `Nat.mod` wrappers, and `BitVec` through `Fin`; both add a `Fin.val`/`mod` layer the
   kernel must reduce that a bare `Nat` literal does not have. `Nat` is the one type with direct GMP
   acceleration. **INFERRED**, from the definitions in `Init/Prelude.lean` (`UInt64.decEq` at line 2757 goes
   through `Nat` anyway) — I did not benchmark `UInt64`.
4. **Sorted lists are the worst option.** Membership becomes a scan with `Char`/`Nat` comparisons, subset
   becomes a merge; both are O(n) *in the kernel*, which is exactly what you avoided by using `casesOn`.

### 2.4 Elaboration cost of 69 large `match`es

Measured, wall clock, `lean --stdin`, single run each (so ±10%, and the numbers include the enum declarations
and `deriving`):

| Generated shape | Wall | User |
| --- | --- | --- |
| 115-ctor enum + `Tag.all` + 69 `Sets.sN : T → Bool` matches (1–90 members each) + 69-ctor `CS` + `CS.contains` dispatch | **1.56 s** | 2.50 s |
| 115-ctor enum + `Tag.all` + 69-ctor `CS` + `CS.mask : CS → Nat` with 69 literals + `contains c t := (mask c).testBit t.ctorIdx` | **0.71 s** | 0.82 s |

So the mask form roughly halves the elaboration time of the generated module, and its `.olean` is 69 numerals
instead of 69 matchers with their equation lemmas and `match_N` auxiliary definitions. That is a real but modest
win, and it is the *only* place bitmasks beat dispatch besides §2.2.

### 2.5 Recommendation

**Keep `Sets.* : Tag → Bool` as the canonical representation — it is what `Child`'s obligations and the
serializer read, it is O(1), and it is what the drift gate checks against TyXML.** Have the emitter
*additionally* produce a mask table and the 69 bridge theorems, and state the lattice in mask form:

```lean
namespace Whatwg.Html.Schema

/-- The bitmask projection of `Sets.flow5`: bit `t.ctorIdx` is set exactly when
`Sets.flow5 t = true`. GENERATED beside the membership function; `Masks.flow5_eq` is the
proof that the two agree, and it is the only place the two representations meet. -/
def Masks.flow5 : Nat := 0x…   -- 115-bit literal, emitted from the same parse

theorem Masks.flow5_eq : ∀ t : Tag, Sets.flow5 t = Masks.flow5.testBit t.ctorIdx :=
  forall_tag_of_all (fun t => Sets.flow5 t == Masks.flow5.testBit t.ctorIdx) (by decide +kernel)
    |> fun h t => eq_of_beq (h t)

end Whatwg.Html.Schema
```

This keeps one canonical carrier (satisfying `Whatwg/AGENTS.md`'s representation rule: a second representation
requires an explicit conversion theorem — `Masks.flow5_eq` *is* that theorem, and it names the canonical
owner), and it turns `Lattice.lean`'s 27 + 7 + 16 inclusion lemmas from 900-heartbeat scans into 20-heartbeat
`land` equations.

**Trade-off, stated plainly:** you are adding 69 generated constants and 69 bridge theorems to buy a 45×
reduction on ~50 lattice lemmas and half the elaboration time of `Families.lean`. If `Lattice.lean` is not
currently slow enough to hurt, `decide +kernel` alone (§1.3) buys you the same 45× with *zero* new
declarations, and you should do that first and only reach for masks if the H6 port-fidelity slice makes the
lattice much bigger.

---

## 3. Typed-tree ergonomics

### 3.1 What is already right in the landed `Typed.lean`

I read `Whatwg/Html/Node/Typed.lean` at its current state. The design is:

```lean
structure Element (t : Tag) (inner : ContentSet) where
  attrs : List (Attr × String)
  children : List RawNode

abbrev childSet (set : ContentSet) (t : Tag) : ContentSet :=
  (Content.resolveChildSet t set).getD .notag

structure Child (set : ContentSet) where
  tag : Tag
  admitted : Content.Admits set tag
  raw : RawNode

def Child.of {set : ContentSet} {t : Tag} (e : Element t (childSet set t))
    (h : Content.Admits set t := by decide) : Child set := ⟨t, h, e.toRaw⟩
```

This is the computed-index trick the brief asks about, and it is done correctly:

- `childSet set t` in the *argument* type of `Child.of` means the transparent element's `inner` index is
  assigned **by unification from the child position**, which is exactly TyXML's `('a attrib, 'a, [> 'a a]) star`.
  No `outParam` is needed, and `outParam` would in fact be wrong here — `outParam` is for typeclass resolution,
  and there is no class involved. The docstring's claim that the expected type propagates into the result type
  before the explicit arguments are elaborated matches Lean's application elaborator behaviour. **INFERRED**
  that this holds for *every* nesting depth; I verified it in a mini model to depth 3.
- `childSet` is an `abbrev` (i.e. `@[reducible]`), which is the right call: unification needs to unfold it at
  reducible transparency to see through `Child (childSet .flow5 .a)`. The obligations themselves reduce at
  default transparency either way, so `abbrev` costs nothing at the kernel.
- The proof is **stored** in `Child.admitted`, so a `Child set` is evidence rather than a promise. Because
  `Content.Admits` is a `Prop`, definitional proof irrelevance means two `Child`s with the same tag and raw
  form are definitionally equal regardless of how the proof was found — so erasure and the §5 injectivity
  argument never have to reason about `h`.

### 3.2 The one hard constraint: no nested inductives

I verified this and it is worth writing into the module docstring, because someone will try it:

```lean
inductive Node : CS → Type where
  | elem {set : CS} (t : Tag) (kids : List (Node (childSet t set)))
      (h : CS.contains set t = true := by decide) : Node set
-- error: (kernel) invalid nested inductive datatype 'List', nested inductive datatypes
--        parameters cannot contain local variables.
```

**A heterogeneous child list indexed by a content set cannot be `List (Node …)` when the index mentions a
constructor-bound variable.** Your two options are (a) the landed one — erase children to `List RawNode` and
keep the evidence in `Child` — or (b) a bespoke mutual inductive:

```lean
mutual
inductive Node : ContentSet → Type where
  | elem {set : ContentSet} (t : Tag) (kids : Nodes (childSet set t))
      (h : Content.Admits set t := by decide +kernel) : Node set
inductive Nodes : ContentSet → Type where
  | nil  {s : ContentSet} : Nodes s
  | cons {s : ContentSet} (n : Node s) (ns : Nodes s) : Nodes s
end
```

I compiled (b) and it works, including a `nodes[…]` list macro. **(a) is the better choice** and you already
took it: (b) gives you no `List` API (`map`, `append`, `length` all hand-rolled), makes the serializer a mutual
recursion, and forces every theorem about children into a mutual induction. (a)'s cost is that the typed layer
loses the children's evidence at the boundary — which is fine, because `Child.admitted` recorded it before
erasure.

### 3.3 The auto-param ordering rule — this is the metavariable question

The brief asks when auto-param metavariables are unassigned. I found the exact rule by breaking it:

```lean
| elem {set : CS} (t : Tag) (h : CS.contains set t = true := by decide)
    (kids : Nodes (childSet t set)) : Node set

def ex : Node .flow := .elem .div nodes[.elem .p nodes[.text "hi"]]
```

```
error: Application type mismatch: The argument
  Nodes.cons (Node.text "hi" ?m.6) Nodes.nil
has type  Nodes ?m.7
but is expected to have type  autoParam (CS.contains ?m.3 Tag.p = true) …
error: could not synthesize default value for parameter 'h' using tactics
error: Expected type must not contain metavariables
  CS.contains ?m.7 Tag.pcdata = true
```

Three distinct failures, all from one mistake. The rules:

1. **An auto-param cannot be skipped positionally.** If `h` precedes `kids`, the first positional argument
   after `t` is matched against `h`, not `kids`.
2. **`decide` refuses a goal with metavariables**, from `preprocessPropToDecide`
   (`Lean/Elab/Tactic/Decide.lean:28`): `if expectedType.hasMVar then throwError "Expected type must not
   contain metavariables"`. The tactic block of an auto-param is *not* postponed until the end of the
   definition — it runs when the application is elaborated, so the index must already be assigned.
3. Therefore: **auto-params go last, after every argument that determines the index.** The landed
   `Child.of (e) (h := by decide)` obeys this. Keep it as an invariant in the emitter that produces
   `Combinators.lean`, with a comment saying why, because it is not obvious and the failure mode is three
   confusing errors at once.

If you ever *do* need an obligation whose index is only known later, the escape hatch is
`Lean.Elab.Term.tryPostpone` / `tryPostponeIfMVar` / `tryPostponeIfHasMVars`
(`Lean/Elab/Term/TermElabM.lean:1370, 1379, 1406`) — but that means writing your own elaborator for the
constructor, i.e. §4, not an auto-param.

### 3.4 What I would add next

**(a) Put `+kernel` on the auto-params.** The new benchmark file records ≈22 heartbeats per node (deep) and
≈10 (wide) with plain `decide`. In my synthetic 30-child probe both modes needed ~200 heartbeats, so the win
is smaller here than in §1 — the per-node obligation is a single `casesOn`, which the elaborator does cheaply
anyway. But `decide +kernel` reduces once instead of twice, and `mkAuxLemma` caches per module by type
(`Decide.lean:107–110`), so a document with 400 `Admits .flow5 .div` obligations elaborates *one* aux lemma
and reuses it 400 times. **INFERRED** that this dominates at document scale; the 30-node probe is too small to
show it. It is a one-token change worth measuring against your real 61-node probe before you commit:

```lean
def Child.of {set : ContentSet} {t : Tag} (e : Element t (childSet set t))
    (h : Content.Admits set t := by decide +kernel) : Child set := ⟨t, h, e.toRaw⟩
```

The thing to watch is that `mkAuxLemma` adds declarations, and `Combinators.lean` has 111 combinators — so a
big document could mint a few hundred `_auxLemma.N` constants. If that is unwelcome, keep plain `decide`.

**(b) Make `Lattice.lean`'s inclusions usable.** You have 27 `x_without_y ⊆ x` theorems and 16 category
inclusions, and right now nothing at the tree level can consume them. Add:

```lean
/-- Weakening: a child admitted under a narrower set is admitted under a wider one. This is where
`Whatwg.Html.Content.Lattice`'s inclusion theorems become usable at a call site: a
`Child .phrasing` can be dropped into a `Child .flow5` position by `phrasing_subset_flow5`. -/
def Child.weaken {a b : ContentSet} (h : Content.SubsetOf a.contains b.contains)
    (c : Child a) : Child b :=
  ⟨c.tag, h c.tag c.admitted, c.raw⟩
```

Do **not** make this a `Coe` instance. A `Coe (Child a) (Child b)` would need `a` and `b` both free, so
instance search would have to *find* the subset proof, and `SubsetOf` is not a class. Making it one would
mean 69² potential instances. Explicit `Child.weaken h` reads fine and keeps the inclusion theorem visible in
the source, which is what a reader of a content-model library wants. This is the same reasoning that ruled out
`Fact` in HP-6.

**(c) Error-message readability.** The bare typed-tree failure is:

```
error: could not synthesize default value for parameter 'h' using tactics
error: Tactic `decide` proved that the proposition
  (childSet Tag.p CS.flow).contains Tag.div = true
is false
```

The position is right (it points at the offending child term), but the text names Lean constructors, not HTML.
There is no way to improve this from inside an auto-param — the message comes from `Decide.lean`'s `diagnose`.
This is precisely why H5 must be an `elab` and not `macro_rules`, and it is what §4 fixes. Until §4 lands, the
cheapest partial improvement is a custom tactic in the auto-param:

```lean
/-- The admission obligation, with a message that names the element and the content set instead of
the `Decidable` instance that failed to reduce. -/
syntax "admit_child" : tactic
macro_rules
  | `(tactic| admit_child) =>
    `(tactic| first
        | decide +kernel
        | fail "this element is not admitted in this position; \
                see `Whatwg.Html.Content.Admission` for the content set")
```

**INFERRED** — I did not compile this macro; the `first | … | fail` shape is standard but the interaction with
auto-param elaboration is worth a probe.

### 3.5 What is reusable from Verso and friends

I fetched `https://raw.githubusercontent.com/leanprover/verso/main/src/verso/Verso/Output/Html.lean` on
**2026-09-03**. Findings:

```lean
public inductive Html where
  | text (escape : Bool) (string : String)
  | tag (name : String) (attrs : Array (String × String)) (contents : Html)
  | seq (contents : Array Html)
```

- **Verso's HTML is entirely untyped**: tag names are `String`, attributes are `Array (String × String)`, there
  is no content model, and there are **no theorems**. It is a rendering library, not a model. So there is
  nothing in its *data type* to reuse; your `RawNode` already occupies that niche and is strictly better
  founded.
- **Its escaping is `String.replace` chains**: text is
  `str.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"` and attribute values additionally
  `replace "\"" "&quot;"`. Note the ordering discipline (`&` first) — get that wrong and you double-escape.
  This is *unprovable* in Lean 4.33.1 without heavy machinery: `String.replace` has grown a
  slice/`Pattern.ToForwardSearcher` signature (I `#check`ed it: it takes `{ρ σ}`, `Std.Iterator`,
  `String.Slice.Pattern.ToForwardSearcher` instances). See §5 — do not copy this.
- **Its `{{ … }}` syntax is worth copying structurally.** It declares `tag_name`, `html`, `attrib`,
  `attrib_val` as separate categories; supports `<tag attrs> … </tag>`, `<tag attrs />`, and `<!-- … -->`;
  antiquotes with `{{ term }}`; interpolates with `s!` and raw-strings with `r!`. `elabHtml` uses `withRef` to
  track source positions and `throwErrorAt` for diagnostics, e.g.
  ``"Mismatched closing tag, expected `{tag}` but got `{tag'}`"``, and special-cases void elements with a
  `"doesn't allow contents"` error. **That is the shape your H5 should have**, with the content-model check
  added.
- I found no `lean4-html`-style typed-content-model project. `Lean.Widget`/ProofWidgets encode HTML as a
  JSON-ish tree for the RPC boundary, which is a serialisation concern, not a content model. **INFERRED** —
  I searched but did not exhaustively survey.

---

## 4. `html!` surface syntax with diagnostics

### 4.1 A working skeleton

This is not a sketch. I typed this into `lean --stdin` against a mini schema and it produced both a clean term
and the error message you asked for, at the offending token.

```lean
import Lean

declare_syntax_cat htmlNode
syntax "<" ident ">" htmlNode* "</" ident ">" : htmlNode
syntax str : htmlNode
syntax "html!" "(" term ")" htmlNode : term

open Lean Elab Term Meta

/-- Markup name → `Tag` constructor. In the real library this is generated beside
`Tag.markupName` so there is one table, not two. -/
def tagOfName? (s : String) : Option Name := …

/-- Elaborate one node against a *closed* `Expr` of type `ContentSet`.
The context travels as an `Expr` and is reduced with `whnf`, so the payload table
(`ContentSet.transparentPayload`) is consulted by the same code the kernel will re-check —
there is no second copy of the schema in meta code. -/
partial def elabNode (ctx : Expr) (stx : Syntax) : TermElabM Expr := do
  match stx with
  | `(htmlNode| $s:str) => do
      let goal := mkApp2 (Lean.mkConst ``CS.contains) ctx (Lean.mkConst ``Tag.pcdata)
      unless (← whnf goal).isConstOf ``Bool.true do
        throwErrorAt stx "text is not admitted here"
      let pf ← mkDecideProof (← mkEq goal (Lean.mkConst ``Bool.true))
      return mkApp3 (Lean.mkConst ``Node.text) ctx (mkStrLit s.getString) pf
  | `(htmlNode| < $t:ident > $kids* </ $t2:ident >) => do
      unless t.getId == t2.getId do throwErrorAt t2 "closing tag mismatch"
      let some tn := tagOfName? t.getId.toString | throwErrorAt t "unknown element"
      let tagE := Lean.mkConst tn
      let goal := mkApp2 (Lean.mkConst ``CS.contains) ctx tagE
      unless (← whnf goal).isConstOf ``Bool.true do
        let ctxN ← whnf (mkApp (Lean.mkConst ``CS.name) ctx)
        throwErrorAt t
          m!"element <{t.getId}> is not admitted here; this position takes {ctxN}"
      let inner ← whnf (mkApp2 (Lean.mkConst ``childSet) tagE ctx)
      let mut acc := mkApp (Lean.mkConst ``Nodes.nil) inner
      for k in kids.reverse do
        acc := mkApp3 (Lean.mkConst ``Nodes.cons) inner (← elabNode inner k) acc
      let pf ← mkDecideProof (← mkEq goal (Lean.mkConst ``Bool.true))
      return mkApp4 (Lean.mkConst ``Node.elem) ctx tagE acc pf
  | _ => throwErrorAt stx "unsupported html node"

elab_rules : term
  | `(html! ($ctx) $n) => do
      let ctxE ← elabTerm ctx (some (Lean.mkConst ``CS))
      elabNode (← instantiateMVars ctxE) n
```

(Note for this repository: the skeleton's `partial def` must become a fuel-bounded or structurally recursive
walker; `partial` is forbidden under the trust gate.)

Results:

```
def good : Node CS.flow := html! (CS.flow) <div><p>"hello"</p></div>
-- elaborates to:
--   Node.elem Tag.div (Nodes.cons (Node.elem Tag.p (Nodes.cons (Node.text "hello" _) …) _) …) _

def bad : Node CS.flow := html! (CS.flow) <p><div>"x"</div></p>
-- <stdin>:65:44: error: element <div> is not admitted here; this position takes "phrasing content"
```

Column 44 is the `div` identifier. **The diagnostic lands on the offending token, names the element, and names
the content set in prose**, which is exactly the H5 requirement.

### 4.2 Design notes that matter

- **Carry the context as an `Expr`, never as a meta-level `ContentSet` value.** If you `evalExpr` the context
  into a real `ContentSet` you have to trust the compiler (and `evalExpr` is `unsafe`, which your ceiling
  forbids). Keeping it as an `Expr` and using `Meta.whnf` means the elaborator consults *the same definitions
  the kernel will re-check*, so the diagnostic can never disagree with the proof obligation. This is the single
  most important structural decision in the elaborator.
- **How to evaluate a closed `Bool` at elaboration time**: `Meta.whnf e` then `e.isConstOf ``Bool.true`. That is
  what I used and it works on `ContentSet.contains` (constructor dispatch, one delta + one iota). Do **not**
  reach for `Meta.evalNat` (`Lean/Meta/Offset.lean:28`) — it is `partial` and only handles `Nat` offset
  arithmetic. Do **not** reach for `Meta.isDefEq` against `Bool.true` — it works but gives you no way to
  distinguish "false" from "stuck", so your error messages degrade. `whnf` + explicit `isConstOf` on both
  `Bool.true` and `Bool.false` lets you say "not admitted" vs "the schema is stuck here, this is a bug".
- **Getting the prose right.** `whnf (mkApp (mkConst ``CS.name) ctx)` evaluates a `ContentSet → String`
  naming function at elaboration time and gives you a `String` literal `Expr` to splat into the message. For the
  real library that function should be generated beside `ContentSet.tyxmlName` — call it
  `ContentSet.phrasingName`, mapping `.flow5 ↦ "flow content"`, `.phrasing_without_interactive ↦ "phrasing
  content that is not interactive"`, etc. It is 69 rows, it is authored (not generated from TyXML, because
  TyXML has no prose), and it is the whole difference between a usable and an unusable error message.
- **Producing the proof.** `Lean.Meta.mkDecideProof p` (`Lean/Meta/AppBuilder.lean:593`) builds
  `of_decide_eq_true (rfl : decide p = true)`. The kernel re-reduces it. If you would rather pay kernel-only
  cost with caching, mirror `Decide.lean`'s `doKernel`: build the same term and hand it to
  `Lean.Meta.mkAuxLemma` (`Lean/Meta/Tactic/AuxLemma.lean:43`), which caches by type per module. That is what
  turns "one proof per node" into "one proof per distinct obligation per document".
- **`tryPostpone`.** You will need it only if `html!` can appear where the expected type is not yet known
  (e.g. `let x := html! …`). The signature is `Lean.Elab.Term.tryPostpone : TermElabM Unit`
  (`Lean/Elab/Term/TermElabM.lean:1370`); the idiomatic use is
  `tryPostponeIfHasMVars? expectedType?` (line 1393) at the top of the `elab_rules`, then fall back to a clear
  error ("`html!` needs its content set; annotate the expected type or write `html! (.flow5) …`") rather than
  postponing forever.
- **Void elements.** Reuse Verso's discipline: a `<br>…</br>` with contents should say
  *"`br` is a void element and takes no children"*, not *"`notag` admits nothing"*. You have
  `Tag.isVoid` and `Content.not_admits_notag` to justify it; the elaborator should check `Tag.isVoid` *first*
  so the message is about voidness rather than about the empty set.
- **Attributes.** Same pattern: `whnf (AttrSet.contains attrsetE attrE)`, error at the attribute token,
  message naming the element. The `AttrsAdmitted` abbrev in `Typed.lean` is a `List.all`, so the elaborator
  can check attributes one at a time and blame the exact one, which the single `by decide` on `_ha` cannot.
  **This is the largest diagnostic win available and it is invisible today**, because `_ha`'s failure names a
  binder called `_ha`.

---

## 5. Serializer proofs

### 5.1 The `String` situation in v4.33.1 changed, and it changed in your favour

`Init/Prelude.lean:3537`:

```lean
structure String where ofByteArray ::
  toByteArray : ByteArray
  isValidUTF8 : ByteArray.IsValidUTF8 toByteArray
```

`String` is now a UTF-8 `ByteArray` with a validity proof, not `⟨data : List Char⟩`. Reasoning about `String`
*directly* is now much worse. But core added the bridge you need, all in `Init/Data/String/Basic.lean` and all
verified by `#check`:

| Lemma | Statement | Line |
| --- | --- | --- |
| `String.toList_append` | `(s ++ t).toList = s.toList ++ t.toList` (`@[simp]`) | 385 |
| `String.toList_injective` | `s₁.toList = s₂.toList → s₁ = s₂` | 370 |
| `String.toList_inj` | `s₁.toList = s₂.toList ↔ s₁ = s₂` | 377 |
| `String.ofList_toList` | `String.ofList s.toList = s` (`@[simp]`) | — |
| `String.toList_ofList` | `(String.ofList l).toList = l` (`@[simp]`) | 334 |
| `String.toList_empty` | `"".toList = []` (`@[simp]`) | 260 |
| `String.toList_eq_nil_iff` | `b.toList = [] ↔ b = ""` (`@[simp]`) | — |
| `String.toList_singleton` | `(String.singleton c).toList = [c]` | — |
| `String.toList_push` | `(s.push c).toList = s.toList ++ [c]` | — |
| `String.length_append` | `(s ++ t).length = s.length + t.length` | — |

**Recommendation: define the serializer at `List Char` and lift with `String.ofList` at the boundary.**

```lean
/-- The renderer, at `List Char`, so that every proof is a `List` proof. -/
def renderChars : RawNode → List Char := …

/-- The public serializer. `String.ofList` is the only `String` operation in the module, and
`String.toList_ofList` turns every statement about `render` back into a statement about
`renderChars`. -/
def render (n : RawNode) : String := String.ofList (renderChars n)

theorem toList_render (n : RawNode) : (render n).toList = renderChars n := by
  simp [render]
```

Everything after that is `List Char`, where core is rich. Note `String.append` injectivity is *not* directly in
core, but you do not need it: `String.toList_append` + `String.toList_injective` + `List.append_inj`
(`s₁ ++ t₁ = s₂ ++ t₂ → s₁.length = s₂.length → s₁ = s₂ ∧ t₁ = t₂`, verified by `#check`) and
`List.append_cancel_left` give you every `String` cancellation fact you will actually want.

**Do not build the serializer on `String.replace`.** Its signature in this version is
`{ρ σ} → [Std.Iterator …] → [String.Slice.Pattern.ToForwardSearcher …] → String → ρ → α → String` — a
slice/pattern machine. Proving anything about it is a research project. This is where Verso's implementation
is a bad model for you.

### 5.2 Escaping soundness: the statement you want is *not* the statement in the brief

The brief says "no unescaped `<`, `>`, `&`, `"` in output". I wrote that statement and Lean refuted it:

```
error: Tactic `decide` proved that the proposition
  ¬'&' ∈ ['&', 'l', 't', ';']
is false
```

Of course: `&` starts every entity. **The soundness theorem splits in two.**

**Part A — the three delimiters never survive.** Compiled, in core, axioms `[propext]`:

```lean
def escapeChar (c : Char) : List Char :=
  if c = '<' then ['&','l','t',';']
  else if c = '>' then ['&','g','t',';']
  else if c = '&' then ['&','a','m','p',';']
  else if c = '"' then ['&','q','u','o','t',';']
  else [c]

def escape (l : List Char) : List Char := l.flatMap escapeChar

/-- The characters whose appearance in a text run would change the parse. -/
def isDelim (c : Char) : Bool := c == '<' || c == '>' || c == '"'

theorem escapeChar_no_delim (c d : Char) (hd : isDelim d = true) : d ∉ escapeChar c := by
  simp only [isDelim, Bool.or_eq_true, beq_iff_eq] at hd
  unfold escapeChar
  split
  · rcases hd with (rfl|rfl)|rfl <;> decide
  split
  · rcases hd with (rfl|rfl)|rfl <;> decide
  split
  · rcases hd with (rfl|rfl)|rfl <;> decide
  split
  · rcases hd with (rfl|rfl)|rfl <;> decide
  · rename_i h1 h2 _ h4
    simp only [List.mem_singleton]
    rcases hd with (rfl|rfl)|rfl
    exact Ne.symm h1; exact Ne.symm h2; exact Ne.symm h4

theorem escape_no_delim (l : List Char) (d : Char) (hd : isDelim d = true) : d ∉ escape l := by
  induction l with
  | nil => simp [escape]
  | cons c cs ih =>
    simp only [escape, List.flatMap_cons, List.mem_append, not_or]
    exact ⟨escapeChar_no_delim c d hd, ih⟩
```

Three notes from having actually written this. `escapeChar` **must** be `if`-chained, not a literal-pattern
`match`: `split` on the `if`s gives you clean `¬c = '<'` hypotheses in the default branch, while `split` on the
match gives you goals `simp` cannot close because it will not decide `Char`-literal disequality (I hit this:
`simp` left `False`; `decide` closed it). Second, `simp_all [eq_comm]` loops (max recursion depth) — finish the
default branch with explicit `Ne.symm`. Third, `exacts [...]` is not in core here; use `;`-separated `exact`s
or bullets.

**Part B — `&` occurs only as a well-formed entity, via a local decoder.** This is the pattern I most want to
recommend, because it is cheap, it is provable, and it is *not* a parser:

```lean
/-- The inverse of `escape` on the four entities it produces. This is a decoder for one
alphabet, not an HTML parser: it never looks at tags, and HP-8's refusal of a parse round trip
is untouched. -/
def unescape : List Char → List Char
  | [] => []
  | '&'::'l'::'t'::';'::rest => '<' :: unescape rest
  | '&'::'g'::'t'::';'::rest => '>' :: unescape rest
  | '&'::'a'::'m'::'p'::';'::rest => '&' :: unescape rest
  | '&'::'q'::'u'::'o'::'t'::';'::rest => '"' :: unescape rest
  | c::rest => c :: unescape rest

theorem unescape_escape (l : List Char) : unescape (escape l) = l := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    show unescape (escapeChar c ++ escape cs) = c :: cs
    unfold escapeChar
    split
    · subst_eqs; simp [unescape, ih]
    split
    · subst_eqs; simp [unescape, ih]
    split
    · subst_eqs; simp [unescape, ih]
    split
    · subst_eqs; simp [unescape, ih]
    · rename_i _ _ h3 _
      simp only [List.cons_append, List.nil_append]
      rw [unescape]
      case _ => simp [ih]
      all_goals exact fun _ hc => absurd hc h3

theorem escape_injective {l₁ l₂ : List Char} (h : escape l₁ = escape l₂) : l₁ = l₂ := by
  have := congrArg unescape h
  rwa [unescape_escape, unescape_escape] at this
```

All of this compiles. `#print axioms escape_injective` → **`[propext]`**.

The one non-obvious step, and the one that will cost you an hour if nobody warns you: `unescape`'s patterns
**overlap** (`'&'::rest` matches both the entity cases and the fallback), so the equation lemma for the
fallback carries side conditions of the form `∀ rest, c = '&' → escape cs ≠ 'l'::'t'::';'::rest`. `rw [unescape]`
leaves them as goals. They all discharge from `c ≠ '&'` — hence `all_goals exact fun _ hc => absurd hc h3`.
Structural recursion is accepted without a `termination_by` because `rest` is a proper subterm in every branch.

**Recommendation: state escaping soundness as the conjunction of Part A (for `<`, `>`, `"` in text; add `&` and
`"` for attribute values with a separate `escapeAttr`) and Part B (`unescape_escape`).** Part B is the honest
form of "no *unescaped* `&`": the output decodes back to the input, so every `&` in it is the start of an
entity. That is stronger than any "no bare `&`" statement, and it is *shorter to prove*.

### 5.3 Printer injectivity on the tree

You have `escape_injective` for free from §5.2. For the whole printer, the two routes:

**Route 1 — decoder, the same trick one level up.** Write `parseNode? : List Char → Option (RawNode × List Char)`
for your own output format only (fully bracketed `<tag …>…</tag>`, void tags `<tag …/>`), and prove
`parseNode? (renderChars n ++ rest) = some (n, rest)` by structural induction on `n` with a mutual lemma for
child lists. Then injectivity is `congrArg` twice, exactly as above. This is **not** an HTML parser and does
not violate HP-8: it accepts only the sublanguage your printer emits, and you should say so in the docstring
and state the refusal theorem (HP-8) beside it so the distinction is on the record. **INFERRED** — I compiled
this shape for `escape` but not for a tree.

**Route 2 — direct prefix determinacy.** Prove

```lean
theorem renderChars_prefix_inj :
    ∀ (a b : RawNode) (r s : List Char),
      renderChars a ++ r = renderChars b ++ s → a = b ∧ r = s
```

by mutual induction with the children-list version. The key facts are `List.append_inj` /
`List.append_cancel_left` (both verified present in core) plus the observation that the first character
determines the constructor (`'<'` for element, otherwise text) and the tag name is delimited. This is doable
but genuinely fiddly: you need "a tag name contains no `>`/space", "escaped text contains no `<`" (which is
Part A above), and a length-or-delimiter argument to split the two halves.

**Recommendation: Route 1.** It is less proof per theorem, it reuses the §5.2 pattern you have already
validated, and its statement (`decode ∘ encode = id`) is the one a reviewer can check by eye. Route 2 is what
you fall back to if the decoder's overlapping-pattern side conditions get out of hand at tree scale.

**What is realistically out of reach in core:** anything requiring `String` measure theory, `String.length`
arithmetic over UTF-8 byte offsets, or reasoning about `String.replace`/`String.Slice`. Stay at `List Char` and
none of it comes up.

---

## 6. Things a Lean expert would do differently

### 6.1 `deriving` choices in `Tags.lean` / `Families.lean`

`deriving DecidableEq, Repr, Inhabited` on `Tag` (115 ctors) and `ContentSet` (69 ctors):

- **`DecidableEq` — keep.** As shown in §1.1 it is the enum path: one `Nat` comparison on `ctorIdx`, plus you
  get `Tag.ofNat` and `Tag.ofNat_ctorIdx` free. Excellent value.
- **`Repr` — reconsider.** `deriving Repr` on a 115-constructor enum generates a 115-arm matcher plus a
  `ReprAtom`-ish instance, and it is used nowhere in `Whatwg/Html/` that I can find. You already have
  `Tag.variantName` and `Tag.markupName`, which are better `Repr`s for this domain. If nothing calls `repr` on a
  `Tag`, dropping `Repr` removes 115 arms × 2 types from elaboration and from the `.olean`. If something does
  (error messages, `#eval` in tests), keep it. **INFERRED** — I did not grep every usage.
- **`Inhabited` — keep**, it costs one constant and `Option`/`getD` code paths tend to want it.
- **Consider adding `deriving Hashable`** *only* if the H6 fidelity slice needs a `Std.HashMap Tag _`. It is
  cheap on enums (hashes `ctorIdx`), but do not add it speculatively.

### 6.2 `@[simp]` and `@[reducible]` on the generated sets

- **Do not `@[simp]` the 69 `Sets.*` functions or their equation lemmas.** Sixty-nine functions × ~80 arms is
  ~5 500 rewrite rules in the default simp set, which would slow every `simp` call in the package and in any
  downstream user. The lemmas you actually want in `simp` are the *bridge* theorems
  (`admits_eq_contains`, `Masks.flow5_eq` if you take §2.5), not the raw dispatch.
- **Do not `@[reducible]`/`abbrev` the `Sets.*` functions.** Reducible transparency affects the *elaborator's*
  unifier, and you do not want the unifier unfolding an 86-arm matcher speculatively during every `Child.of`
  application. The kernel unfolds at default transparency regardless, which is where the reduction happens.
  `def` is correct. The one place `abbrev` *is* correct is `childSet`, and `Typed.lean` already gets that
  right and documents why.
- `Content.admits` / `Content.Admits` being plain `def`s with `admits_iff : … ↔ … := Iff.rfl` is exactly right —
  definitional bridges cost nothing and keep `decide` reducing.
- Note `Content.AttrsAdmitted` is an `abbrev` in `Typed.lean` while `Content.Admits` is a `def` in
  `Admission.lean`. That asymmetry is probably unintentional. `abbrev` on `AttrsAdmitted` means the unifier
  will unfold `attrs.all (fun p => set.contains p.1) = true` eagerly; that is harmless but inconsistent. Pick
  one and say why in the docstring.

### 6.3 `Tag.all` as `List` vs `Array`

**Keep it a `List`.** `List.all` reduces by structural recursion — one `casesOn` per element, no arithmetic.
`Array.all` goes through `Array.anyM`/`Array.size`/`Fin` bounds and `Nat` index arithmetic, so the kernel has to
reduce an index counter and a bound proof at every step. For a *kernel* reduction (which is what `decide` does)
`List` is strictly cheaper. `Array` wins at *runtime*, and nothing in `Lattice.lean` runs. The `List` also gives
you `List.Nodup`, `List.all_eq_true`, `List.mem_of_getElem?` directly (all verified present).

### 6.4 `Tag.mem_all` is the expensive declaration, and that is fine

Measured, on the synthetic 115-constructor enum, bisecting `maxHeartbeats`:

| Proof of `t ∈ T.all` | Fails at | Passes at |
| --- | --- | --- |
| `by cases t <;> decide` (what `Lattice.lean` does) | 4 000 | 20 000 |
| `by cases t <;> decide +kernel` | 4 000 | 20 000 |
| via `T.all[t.ctorIdx]? = some t` + `List.mem_of_getElem?` | 4 000 | 20 000 |
| `by decide +kernel` (no `cases`) | — | never (free variable `t`) |

This is quadratic by nature: 115 goals, each a scan of a 115-element list. **None of the three routes changes
the order of magnitude**, and `+kernel` does not help because the cost is in producing 115 separate goals in the
elaborator, not in reducing any one of them. It is paid once per module and it is nothing next to a document.
I would leave it exactly as it is and add one sentence to the docstring saying it is the module's one expensive
declaration and why no cheaper route exists — otherwise someone will "optimise" it three times.

The same is true of `Tag.all_nodup : Tag.all.Nodup := by decide`, which is O(115²) pair comparisons; it is
also a one-time cost and it is a genuinely valuable theorem (it is what makes `Tag.all` an enumeration rather
than a list).

### 6.5 `List.eraseDups` in the emitter

`Gates/TyxmlSchemaEmit.lean` uses `eraseDups` at lines 520, 526, 540, 546. `List.eraseDups` is O(n²) with
`BEq`. At your sizes (115 tags, 69 sets, 216 attributes) that is at most ~47 000 comparisons — irrelevant, and
it runs in the gate binary, not in the kernel. The reason to change it is not speed:

**`eraseDups` keeps the first occurrence, so the output order depends on discovery order.** Lines 526 and 546
then `qsort` anyway, so those two are fine. Lines 520 and 540 (`contentSeeds`, `attrSeeds`) do **not** sort,
which means the seed order — and therefore any downstream ordering that depends on it — is a function of the
order `elements` happens to be in. If `elements` order ever changes, the projection changes for a reason that
has nothing to do with TyXML, and the drift gate will fire. Sorting the seeds (or documenting that seed order
is deliberately `html_sigs.mli` order and is part of the projection contract) removes a class of spurious drift.
This is a small robustness point, not a bug.

### 6.6 Docstring conventions

Two observations on the generated modules:

- The generated `Sets.*` docstrings carry the `html_types.mli` line number *and* the member count
  (`` `flow5` (`html_types.mli` line 926): 74 of 115 tags ``). That is good — the count is a cheap invariant a
  reader can check against the theorem. Consider also emitting the count as a theorem
  (`theorem Sets.flow5_card : (Tag.all.filter Sets.flow5).length = 86 := by decide +kernel`), because a
  docstring is not checked and a theorem is. **INFERRED** cost; a `filter` + `length` over 115 elements should
  be in the same class as `List.all`, i.e. ~20 hb under `+kernel`.
- `Lattice.lean`'s module docstring lists the seven observed departures from the family names in prose. That
  is exemplary and I would not change it — it is the kind of thing that stops a future reader from "fixing" a
  theorem that is true to the data. The one thing I would add is a pointer from each departure bullet to the
  *theorem name* that witnesses it, so the prose and the code cannot drift apart.

### 6.7 One correctness-adjacent observation

`WhatwgTest/Audit/AxiomGate.lean`'s docstring says it *"tokenizes every authored source under
`Whatwg/Streams/`, `WhatwgTest/Streams/`, and `Gates/`"*. `Whatwg/Html/` is not named. If the tokenizer's file
set is literally those three prefixes, then **the HTML tree currently has no axiom gate**, and the ceiling
claim in `Whatwg/AGENTS.md` ("Every declaration in this tree is bound by the ceiling…, `sorry`,
`native_decide`, `bv_decide`, `partial`, `unsafe`, and new axioms are rejected by
`WhatwgTest/Audit/AxiomGate.lean`") would be unsupported for `Whatwg/Html/`. I read only the first 80 lines of
the gate, so I could not confirm the file-set logic — **this is a flag to check, not a finding**. It matters
more than usual right now, because §1.3 and §3.4 both propose `decide +kernel`, which mints aux-lemma
declarations the gate would have to see.

> Coordinator's note (2026-09-03): checked. `auditedSources` walks every `.lean` under `Whatwg/`,
> `WhatwgTest/`, and `Gates/`, and `belongsToAuditedTree` matches the module prefixes `Whatwg`, `WhatwgTest`,
> `Gates`; the HTML tree is inside the gate. Only the docstring is stale.

---

## Appendix: exact provenance

**Toolchain source, all under `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/`:**

| File:line | Fact |
| --- | --- |
| `Init/Prelude.lean:3537` | `String` is `ofByteArray :: (toByteArray : ByteArray) (isValidUTF8 : …)` |
| `Init/Prelude.lean:1870` | `Nat.decEq` via `Nat.beq` |
| `Init/Data/String/Basic.lean:241,260,334,370,377,385` | `String.toList` and its lemmas |
| `Init/Data/List/Lemmas.lean:576` | `List.all_eq_true` |
| `Init/Data/Nat/Bitwise/Basic.lean:99,150` | `AndOp Nat := Nat.land`; `Nat.testBit m n := 1 &&& (m >>> n) != 0` |
| `Init/Data/Nat/Bitwise/Lemmas.lean:496` | `Nat.testBit_and`, `@[simp, grind =]` |
| `Init/Tactics.lean:1382–1428` | `DecideConfig`; `+kernel` reduces once and ignores transparency |
| `Lean/Elab/Tactic/Decide.lean:22–33` | `preprocessPropToDecide`: no metavariables, no free variables |
| `Lean/Elab/Tactic/Decide.lean:87–128` | `doElab` reduces twice; `doKernel` uses `mkAuxLemma` and caches by type per module |
| `Lean/Meta/AppBuilder.lean:589,593` | `mkDecide`, `mkDecideProof` |
| `Lean/Meta/Tactic/AuxLemma.lean:43` | `mkAuxLemma` |
| `Lean/Meta/Constructions/CtorIdx.lean:18,25,29,118–130` | `genCtorIdx`; `T.ctorIdx`; `T.toCtorIdx` deprecated since 2025-08-25 |
| `Lean/Elab/Deriving/DecEq.lean:220–277` | enum path: `ofNat` binary-search table, `ofNat_ctorIdx`, `DecidableEq` via `ctorIdx` |
| `Lean/Elab/Term/TermElabM.lean:1370,1379,1393,1406` | `tryPostpone`, `tryPostponeIfMVar`, `tryPostponeIfHasMVars?`, `tryPostponeIfHasMVars` |
| `Lean/Exception.lean:84` | `throwErrorAt` |
| `Lean/Meta/Offset.lean:28` | `Meta.evalNat` is `partial`, `Nat`-offset only |

**Web, fetched 2026-09-03:**
[Verso `Verso/Output/Html.lean` (raw)](https://raw.githubusercontent.com/leanprover/verso/main/src/verso/Verso/Output/Html.lean) — untyped `Html` inductive, `String.replace`-chain escaping, no theorems; `{{ … }}` syntax categories `tag_name`/`html`/`attrib`/`attrib_val`, `elabHtml` with `withRef` and `throwErrorAt`.
Background searches: [Verso on Reservoir](https://reservoir.lean-lang.org/@leanprover/verso), [Embedding DSLs By Elaboration](https://leanprover-community.github.io/lean4-metaprogramming-book/main/08_dsls.html), [Lean reference: Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/). No typed-content-model HTML DSL for Lean 4 surfaced.

**Repository files read:** `AGENTS.md`, `Whatwg/AGENTS.md`, `docs/HTML-PACKAGE-PLAN.md`,
`Whatwg/Html/Schema/{Tags,Families,ContentModel}.lean`, `Whatwg/Html/Content/{Lattice,Transparent,Admission}.lean`,
`Whatwg/Html/Node/Typed.lean`, head of `Whatwg/Html/Node/Combinators.lean`, `WhatwgTest/Html/DecideBenchmark.lean`
(current state, post-rewrite), head of `WhatwgTest/Audit/AxiomGate.lean`, `Whatwg/Html.lean`, `Whatwg/Html/Schema.lean`.

**No file in the repository was modified, and `lake` was not invoked.** All measurements were made by piping
synthetic Lean source to `bin/lean --stdin` with `cwd=/`; `--stdin` writes no artifacts.
