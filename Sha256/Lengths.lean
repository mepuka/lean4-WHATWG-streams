import Sha256.Impl

/-!
# `Sha256.Lengths` — the length and padding facts of the byte-level reference

The `Sha256.Impl` length theorems of `docs/SHA256-DAG.md` §4 A1.S1, kept out of
`Sha256/Impl.lean` so that the definitions read as a transcription.

`length_padBytes_eq` is the one that matters downstream: it pins the zero-count
formula, so `Fast.padBytes_eq` and `Bridge.padBytes_bridge` are data-flow proofs
over a fixed arithmetic shape rather than rederivations of it.
-/

namespace Sha256.Impl

@[simp] theorem length_lengthBytes (n : Nat) : (lengthBytes n).length = 8 := rfl

@[simp] theorem length_bytesOfWord (w : Word) : (bytesOfWord w).length = 4 := rfl

/-- The padded length in closed form. `(119 - ℓ % 64) % 64` is the zero count:
`119 ≡ 55 (mod 64)`, and `119 - ℓ % 64 ≥ 56`, so the truncating `Nat`
subtraction never fires and the count is the FIPS 180-4 §5.1.1 `k` at byte
granularity. -/
theorem length_padBytes_eq (msg : List UInt8) :
    (padBytes msg).length = msg.length + 1 + (119 - msg.length % 64) % 64 + 8 := by
  simp only [padBytes, List.length_append, List.length_cons, List.length_replicate,
    length_lengthBytes]
  omega

theorem length_padBytes (msg : List UInt8) : (padBytes msg).length % 64 = 0 := by
  rw [length_padBytes_eq]
  omega

theorem length_padBytes_pos (msg : List UInt8) : msg.length < (padBytes msg).length := by
  rw [length_padBytes_eq]
  omega

theorem padBytes_prefix (msg : List UInt8) : (padBytes msg).take msg.length = msg :=
  List.take_left

theorem length_sha256 (msg : List UInt8) : (sha256 msg).length = 32 := by
  rw [sha256, Spec.length_flatMap_const _ _ 4 fun i => length_bytesOfWord _]
  simp

end Sha256.Impl
