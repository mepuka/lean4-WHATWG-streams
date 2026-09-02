import Sha256.Spec

/-!
# `Sha256.Impl` — the byte-level reference

SHA-256 on byte strings, over `BitVec 32` words. This is the layer the
known-answer tests of `Sha256.Kats` run on, and the layer `Sha256.Fast` is
proved equal to.

It is kernel-reducible on purpose. `docs/SHA256-DAG.md` §2 records the measured
reason for the split: identical rotate/xor/shift/add work over `10⁷` iterations
costs 6572.78 ms on `BitVec 32` against 8.90 ms on `UInt32` at runtime, while in
the kernel the `BitVec 32` form is about an order of magnitude *cheaper*. So the
kernel known-answer test lives here and the throughput lives in `Sha256.Fast`.

`Impl` does not restate the word functions. `Ch`, `Maj`, `Σ0`, `Σ1`, `σ0`, `σ1`,
`K`, `H0`, `schedule` and `compress` are `Sha256.Spec`'s, shared rather than
copied, so `Bridge.schedule_bridge` and `Bridge.compress_bridge` are `rfl` and
the bridge is a data-flow proof rather than an arithmetic one
(`docs/SHA256-DAG.md` §4 A1.S1).

No `Id.run do`, no `for`/`mut`, no `xs[i]!`: every loop is `Nat.fold`,
`Vec.ofFn`, `List.foldl`, or structural, and every index carries a proof or
goes through `List.getD` (`docs/SHA256-DAG.md` §3.3).
-/

namespace Sha256.Impl

/-- FIPS 180-4 §3.1, as carried by `Sha256.Spec`. -/
abbrev Word := BitVec 32

/-- The eight-word hash state of FIPS 180-4 §6.2.2. -/
abbrev St := Vector Word 8

/-- FIPS 180-4 §5.1.1: the message bit length as eight bytes, big-endian. -/
def lengthBytes (bitLength : Nat) : List UInt8 :=
  [UInt8.ofNat (bitLength >>> 56), UInt8.ofNat (bitLength >>> 48),
   UInt8.ofNat (bitLength >>> 40), UInt8.ofNat (bitLength >>> 32),
   UInt8.ofNat (bitLength >>> 24), UInt8.ofNat (bitLength >>> 16),
   UInt8.ofNat (bitLength >>> 8), UInt8.ofNat bitLength]

/-- FIPS 180-4 §5.1.1 at byte granularity: the byte `0x80` (the `1` bit
followed by seven zeros), zeros until the length is `56 mod 64`, then the
message bit length as eight big-endian bytes.

The zero count is `(119 - ℓ % 64) % 64`. `119 ≡ 55 (mod 64)` and
`119 - ℓ % 64 ≥ 56`, so the truncating `Nat` subtraction never fires. This is
the formula `Lengths.length_padBytes_eq` pins. -/
def padBytes (msg : List UInt8) : List UInt8 :=
  msg ++ ((0x80 :: List.replicate ((119 - msg.length % 64) % 64) 0) ++
    lengthBytes (8 * msg.length))

/-- FIPS 180-4 §3.1: four bytes read as one word, big-endian. -/
def wordOfBytes (b0 b1 b2 b3 : UInt8) : Word :=
  (BitVec.ofNat 32 b0.toNat <<< 24) |||
    ((BitVec.ofNat 32 b1.toNat <<< 16) |||
      ((BitVec.ofNat 32 b2.toNat <<< 8) ||| BitVec.ofNat 32 b3.toNat))

/-- FIPS 180-4 §5.2.1 at byte granularity: a 64-byte block read as sixteen
big-endian words. Absent bytes read as zero, so the function is total. -/
def wordsOfBlock (block : List UInt8) : Vector Word 16 :=
  Vec.ofFn fun i : Fin 16 =>
    wordOfBytes (block.getD (4 * i.1) 0) (block.getD (4 * i.1 + 1) 0)
      (block.getD (4 * i.1 + 2) 0) (block.getD (4 * i.1 + 3) 0)

/-- FIPS 180-4 §6.2.2 step 1, shared with `Sha256.Spec`. -/
def schedule (w : Vector Word 16) : Vector Word 64 := Spec.schedule w

/-- FIPS 180-4 §6.2.2 steps 2–4, shared with `Sha256.Spec`. -/
def compress (H : St) (w : Vector Word 16) : St := Spec.compress H w

set_option linter.unusedVariables false in
/-- The padded message cut into 64-byte blocks. Total extension: a trailing run
shorter than a block is dropped, which never happens on `padBytes` output. -/
def blocks (P : List UInt8) : List (List UInt8) :=
  if h : P.length < 64 then [] else P.take 64 :: blocks (P.drop 64)
termination_by P.length
decreasing_by simp only [List.length_drop]; omega

theorem blocks_nil_of_lt (P : List UInt8) (h : P.length < 64) : blocks P = [] := by
  rw [blocks, dif_pos h]

theorem blocks_cons (P : List UInt8) (h : ¬ (P.length < 64)) :
    blocks P = P.take 64 :: blocks (P.drop 64) := by
  rw [blocks, dif_neg h]

/-- FIPS 180-4 §6.2 on an already-padded byte string. -/
def hash' (P : List UInt8) : St := ((blocks P).map wordsOfBlock).foldl compress Spec.H0

/-- FIPS 180-4 §6.2: pad, parse, compress. -/
def hash (msg : List UInt8) : St := hash' (padBytes msg)

/-- FIPS 180-4 §3.1: one word as four bytes, big-endian. -/
def bytesOfWord (w : Word) : List UInt8 :=
  [UInt8.ofNat (w >>> 24).toNat, UInt8.ofNat (w >>> 16).toNat,
   UInt8.ofNat (w >>> 8).toNat, UInt8.ofNat w.toNat]

/-- The 32-byte SHA-256 digest of a byte string.

Meaning: `Sha256.Bridge.sha256_bridge`, which proves this equals
`Sha256.Spec.sha256_bytes`, the FIPS 180-4 function, on every byte string. -/
def sha256 (msg : List UInt8) : List UInt8 :=
  (List.finRange 8).flatMap fun i => bytesOfWord (hash msg)[i]

end Sha256.Impl
