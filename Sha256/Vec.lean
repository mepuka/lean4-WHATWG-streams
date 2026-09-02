/-!
# `Sha256.Vec` — a `Vector.ofFn` that stays inside the axiom ceiling

`Vector.ofFn` is the shape `docs/SHA256-DAG.md` §3.2 prescribes for a bounded
loop in a definition, and the rest of core's `Vector` API is inside this lane's
semantic ceiling: `Vector.ext`, `getElem_set_self`, `getElem_set_ne`,
`getElem_map`, `getElem_replicate`, `Nat.fold_zero` and `Nat.fold_succ` all
report `[propext, Quot.sound]` or less.

**`Vector.ofFn` is the exception.** Under v4.33.1, measured with
`#print axioms`:

```text
Vector.getElem_ofFn   [propext, Classical.choice, Quot.sound]
Array.getElem_ofFn    [propext, Classical.choice, Quot.sound]
Array.toList_ofFn     [propext, Classical.choice, Quot.sound]
Vector.toList_ofFn    [propext, Classical.choice, Quot.sound]
```

Every route from core's `Vector.ofFn` to its elements therefore leaves the
ceiling of §3.1, and there is no core lemma that re-enters it. `List.ofFn` is
clean (`List.length_ofFn` and `List.getElem_ofFn` are both `[propext]`), so this
module builds the same vector through the list and states the one lemma the
proofs need. Nothing else about `ofFn` is used anywhere in `Sha256/`.

This is a finding about `Sha256/`'s stricter-than-usual ceiling, not a defect in
core: `Classical.choice` is ordinary in Lean's own library.
-/

namespace Sha256.Vec

/-- The vector whose `i`-th entry is `f i`, built through `List.ofFn`. -/
def ofFn {α : Type} {n : Nat} (f : Fin n → α) : Vector α n :=
  ⟨⟨List.ofFn f⟩, List.length_ofFn⟩

@[simp] theorem getElem_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (h : i < n) :
    (ofFn f)[i] = f ⟨i, h⟩ :=
  List.getElem_ofFn (by rw [List.length_ofFn]; exact h)

end Sha256.Vec
