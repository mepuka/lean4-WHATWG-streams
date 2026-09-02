import Sha256.Vec

/-!
# `Sha256.Spec` — the FIPS 180-4 transcription

The bit-level transcription of SHA-256 from NIST FIPS 180-4, *Secure Hash
Standard*, August 2015, vendored at `vendor/nist-fips-180-4/NIST.FIPS.180-4.pdf`
and sealed by `generated/vendor-manifest.tsv`. Every definition carries the
section it transcribes.

This layer says what SHA-256 *means*. It is not executed: `Sha256.Impl` is the
byte-level reference the known-answer tests run on, `Sha256.Fast` is the native
layer, and `Sha256.Bridge` proves `Impl` computes this function on byte-aligned
messages.

Two domain facts are load-bearing and easy to get wrong.

* FIPS 180-4 §3.1 is **most significant bit first** within a word *and* within
  a byte. FIPS 202 Appendix B.1 is least significant bit first within a byte,
  so foldlab's `formal/fips202` `bitsOfBytes` is the opposite convention and is
  not reusable here (`test/contracts/sha256.contract.md`, E4). Both round-trip
  theorems below hold for either convention; only a known-answer vector
  separates them.
* `parse` and `hash` are total extensions. They carry FIPS 180-4 meaning only
  on padded input; elsewhere they are defined and meaningless.

Transcription fidelity of this file to an English-and-pseudocode standard is a
named human trust step, not a theorem (`test/contracts/sha256.contract.md`, C2).

The `natOfBits`/`bitsOfNat` round-trip technique reproduces, for the MSB-first
convention, the `Classical.choice`-free route the operator supplied for
foldlab's `formal/fips202` stage S0.2. It is reproduced, not imported.
-/

namespace Sha256.Spec

/-! ## §3.1 — bit strings, integers, words -/

/-- FIPS 180-4 §3.1: a *word* is a 32-bit string; within a word the most
significant bit is stored in the left-most bit position. -/
abbrev Word := BitVec 32

/-- FIPS 180-4 §3.1: the integer denoted by a bit string written most
significant bit first. -/
def natOfBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + natOfBits bs

/-- FIPS 180-4 §3.1: the `k`-bit spelling of `n`, most significant bit first. -/
def bitsOfNat : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, n => n.testBit k :: bitsOfNat k n

@[simp] theorem length_bitsOfNat (k n : Nat) : (bitsOfNat k n).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [bitsOfNat, List.length_cons, ih]

theorem natOfBits_lt (bits : List Bool) : natOfBits bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [natOfBits]
  | cons b bs ih =>
      have hb : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
      have hle := Nat.mul_le_mul_right (2 ^ bs.length) hb
      simp only [natOfBits, List.length_cons, Nat.pow_succ]
      omega

theorem natOfBits_append (xs ys : List Bool) :
    natOfBits (xs ++ ys) = natOfBits xs * 2 ^ ys.length + natOfBits ys := by
  induction xs with
  | nil => simp [natOfBits]
  | cons b bs ih =>
      simp only [List.cons_append, natOfBits, List.length_append, ih, Nat.pow_add,
        Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-! One step of the big-endian reading, at the level of `Nat`: the bit at
position `k` contributes `2 ^ k` and the rest is the low `k`-bit remainder.

The route is `Nat.eq_of_testBit_eq` throughout, and never `Nat.div`. The
arithmetic identity `n % 2 ^ (k+1) / 2 ^ k = n / 2 ^ k % 2` is available in core
as `Nat.mod_mul_right_div_self`, but **that lemma itself reaches
`Classical.choice`** (measured with `#print axioms` under v4.33.1), which the
ceiling of `docs/SHA256-DAG.md` §3.1 forbids here. `Nat.testBit_mod_two_pow`,
`Nat.testBit_or`, `Nat.testBit_two_pow` and `Nat.or_two_pow_eq_add_of_lt` are
all inside the ceiling, and they are the operator's `lowBits` route for
FIPS 202 stage S0.2 in a shorter form. -/

private theorem mod_two_pow_succ_of_false (n k : Nat) (hb : n.testBit k = false) :
    n % 2 ^ (k + 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  rcases Nat.lt_trichotomy i k with h | h | h
  · rw [decide_eq_true h, decide_eq_true (Nat.lt_succ_of_lt h)]
  · subst h
    rw [hb, Bool.and_false, Bool.and_false]
  · rw [decide_eq_false (Nat.not_lt_of_gt h), decide_eq_false (by omega : ¬ (i < k + 1))]

private theorem mod_two_pow_succ_of_true (n k : Nat) (hb : n.testBit k = true) :
    n % 2 ^ (k + 1) = 2 ^ k + n % 2 ^ k := by
  have hm : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  rw [Nat.add_comm (2 ^ k) (n % 2 ^ k), ← Nat.or_two_pow_eq_add_of_lt hm]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i k with h | h | h
  · rw [decide_eq_true h, decide_eq_true (Nat.lt_succ_of_lt h),
      decide_eq_false (by omega : ¬ (k = i)), Bool.or_false]
  · subst h
    rw [hb, decide_eq_true (Nat.lt_succ_self _), decide_eq_false (Nat.lt_irrefl _)]
    simp
  · rw [decide_eq_false (Nat.not_lt_of_gt h), decide_eq_false (by omega : ¬ (i < k + 1)),
      decide_eq_false (by omega : ¬ (k = i)), Bool.or_false]

private theorem mod_two_pow_succ (n k : Nat) :
    n % 2 ^ (k + 1) = (if n.testBit k then 1 else 0) * 2 ^ k + n % 2 ^ k := by
  cases hb : n.testBit k with
  | false => rw [mod_two_pow_succ_of_false n k hb]; simp
  | true => rw [mod_two_pow_succ_of_true n k hb]; simp

theorem natOfBits_bitsOfNat (k n : Nat) : natOfBits (bitsOfNat k n) = n % 2 ^ k := by
  induction k with
  | zero => simp [bitsOfNat, natOfBits, Nat.mod_one]
  | succ k ih =>
      simp only [bitsOfNat, natOfBits, length_bitsOfNat, ih]
      exact (mod_two_pow_succ n k).symm

theorem bitsOfNat_congr {m n : Nat} (k : Nat) (h : ∀ j, j < k → m.testBit j = n.testBit j) :
    bitsOfNat k m = bitsOfNat k n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [bitsOfNat]
      rw [h k (Nat.lt_succ_self k), ih fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem bitsOfNat_natOfBits (bits : List Bool) :
    bitsOfNat bits.length (natOfBits bits) = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
      have hlt : natOfBits bs < 2 ^ bs.length := natOfBits_lt bs
      have hval : natOfBits (b :: bs)
          = 2 ^ bs.length * (if b then 1 else 0) + natOfBits bs := by
        simp only [natOfBits]
        cases b <;> simp
      have h1 : (2 ^ bs.length * (if b then 1 else 0) + natOfBits bs).testBit bs.length = b := by
        rw [Nat.testBit_two_pow_mul_add _ hlt]
        cases b <;> simp
      have h2 : bitsOfNat bs.length (2 ^ bs.length * (if b then 1 else 0) + natOfBits bs)
          = bitsOfNat bs.length (natOfBits bs) := by
        refine bitsOfNat_congr _ fun j hj => ?_
        rw [Nat.testBit_two_pow_mul_add _ hlt, if_pos hj]
      simp only [List.length_cons, bitsOfNat, hval, h1, h2, ih]

/-- Splitting a big-endian spelling: the top `a` bits are the spelling of the
value shifted down by `b`, and the bottom `b` bits are the spelling of the
value itself. -/
theorem bitsOfNat_add (a b n : Nat) :
    bitsOfNat (a + b) n = bitsOfNat a (n >>> b) ++ bitsOfNat b n := by
  induction a with
  | zero => simp [bitsOfNat]
  | succ a ih =>
      have hshape : a + 1 + b = a + b + 1 := by omega
      have hbit : (n >>> b).testBit a = n.testBit (a + b) := by
        rw [Nat.testBit_shiftRight, Nat.add_comm]
      rw [hshape]
      simp only [bitsOfNat, List.cons_append, ih, hbit]

/-! ## §3.1 — bytes and bit strings

FIPS 180-4 §3.1 fixes the most-significant-bit-first reading of both a byte and
a word. This is the convention `bitsOfByte` transcribes. -/

/-- FIPS 180-4 §3.1: the eight bits of a byte, most significant bit first. -/
def bitsOfByte (b : UInt8) : List Bool := bitsOfNat 8 b.toNat

/-- FIPS 180-4 §3.1: the thirty-two bits of a word, most significant bit first. -/
def bitsOfWord (w : Word) : List Bool := bitsOfNat 32 w.toNat

/-- The byte denoted by a bit string read most significant bit first. -/
def byteOfBits (bits : List Bool) : UInt8 := UInt8.ofNat (natOfBits bits)

/-- The word denoted by a bit string read most significant bit first. -/
def wordOfBits (bits : List Bool) : Word := BitVec.ofNat 32 (natOfBits bits)

/-- FIPS 180-4 §3.1: a byte string read as a bit string, most significant bit
of each byte first. -/
def bitsOfBytes (bs : List UInt8) : List Bool := bs.flatMap bitsOfByte

set_option linter.unusedVariables false in
/-- Inverse of `bitsOfBytes` on whole-byte strings. A trailing partial byte is
dropped, which is exactly why `bitsOfBytes_bytesOfBits` carries its `% 8`
premise. -/
def bytesOfBits (bits : List Bool) : List UInt8 :=
  if h : bits.length < 8 then []
  else byteOfBits (bits.take 8) :: bytesOfBits (bits.drop 8)
termination_by bits.length
decreasing_by simp only [List.length_drop]; omega

/-- A `flatMap` whose step has constant length has that length times the count. -/
theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (n : Nat)
    (hf : ∀ a, (f a).length = n) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.flatMap_cons, List.length_append, hf a, ih, List.length_cons, Nat.mul_succ]
      omega

@[simp] theorem length_bitsOfByte (b : UInt8) : (bitsOfByte b).length = 8 := by
  simp [bitsOfByte]

@[simp] theorem length_bitsOfWord (w : Word) : (bitsOfWord w).length = 32 := by
  simp [bitsOfWord]

theorem length_bitsOfBytes (bs : List UInt8) : (bitsOfBytes bs).length = 8 * bs.length :=
  length_flatMap_const bs bitsOfByte 8 length_bitsOfByte

theorem natOfBits_bitsOfByte (b : UInt8) : natOfBits (bitsOfByte b) = b.toNat := by
  have h : b.toNat < 2 ^ 8 := Nat.lt_of_lt_of_le b.toNat_lt (by decide)
  rw [bitsOfByte, natOfBits_bitsOfNat, Nat.mod_eq_of_lt h]

theorem byteOfBits_bitsOfByte (b : UInt8) : byteOfBits (bitsOfByte b) = b := by
  rw [byteOfBits, natOfBits_bitsOfByte, UInt8.ofNat_toNat]

theorem bitsOfByte_byteOfBits (l : List Bool) (h : l.length = 8) :
    bitsOfByte (byteOfBits l) = l := by
  have hlt : natOfBits l < 2 ^ 8 := h ▸ natOfBits_lt l
  have hsize : natOfBits l < UInt8.size := Nat.lt_of_lt_of_le hlt (by decide)
  have hb := bitsOfNat_natOfBits l
  rw [h] at hb
  rw [bitsOfByte, byteOfBits, UInt8.toNat_ofNat_of_lt' hsize]
  exact hb

/-- The truncation in `UInt8.ofNat` is invisible to the eight bits it keeps. -/
theorem bitsOfByte_ofNat (x : Nat) : bitsOfByte (UInt8.ofNat x) = bitsOfNat 8 x := by
  rw [bitsOfByte, UInt8.toNat_ofNat']
  refine bitsOfNat_congr _ fun j hj => ?_
  rw [Nat.testBit_mod_two_pow]
  simp [hj]

/-- The truncation in `BitVec.ofNat 32` is invisible to the thirty-two bits it
keeps. -/
theorem bitsOfWord_ofNat (x : Nat) : bitsOfWord (BitVec.ofNat 32 x) = bitsOfNat 32 x := by
  rw [bitsOfWord, BitVec.toNat_ofNat]
  refine bitsOfNat_congr _ fun j hj => ?_
  rw [Nat.testBit_mod_two_pow]
  simp [hj]

theorem bitsOfBytes_cons (b : UInt8) (bs : List UInt8) :
    bitsOfBytes (b :: bs) = bitsOfByte b ++ bitsOfBytes bs := rfl

theorem bytesOfBits_nil : bytesOfBits [] = [] := by
  rw [bytesOfBits]; simp

/-- Peeling one byte off the front: the conversion is a head/tail recursion. -/
theorem bytesOfBits_append8 (b8 rest : List Bool) (h : b8.length = 8) :
    bytesOfBits (b8 ++ rest) = byteOfBits b8 :: bytesOfBits rest := by
  have hnot : ¬ ((b8 ++ rest).length < 8) := by
    simp only [List.length_append, h]; omega
  rw [bytesOfBits, dif_neg hnot, List.take_left' h, List.drop_left' h]

/-! ## §4.1.2 — the SHA-224 and SHA-256 logical functions -/

/-- FIPS 180-4 §4.1.2, equation (4.2): `Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def Ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)

/-- FIPS 180-4 §4.1.2, equation (4.3): `Maj(x,y,z) = (x∧y) ⊕ (x∧z) ⊕ (y∧z)`. -/
def Maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 §4.1.2, equation (4.4): `Σ₀ = ROTR² ⊕ ROTR¹³ ⊕ ROTR²²`. -/
def «Σ0» (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22

/-- FIPS 180-4 §4.1.2, equation (4.5): `Σ₁ = ROTR⁶ ⊕ ROTR¹¹ ⊕ ROTR²⁵`. -/
def «Σ1» (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25

/-- FIPS 180-4 §4.1.2, equation (4.6): `σ₀ = ROTR⁷ ⊕ ROTR¹⁸ ⊕ SHR³`. -/
def σ0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)

/-- FIPS 180-4 §4.1.2, equation (4.7): `σ₁ = ROTR¹⁷ ⊕ ROTR¹⁹ ⊕ SHR¹⁰`. -/
def σ1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-! ## §4.2.2 — the SHA-224 and SHA-256 constants -/

/-- FIPS 180-4 §4.2.2: the first thirty-two bits of the fractional parts of the
cube roots of the first sixty-four prime numbers. -/
def K : Vector Word 64 :=
  #v[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
     0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
     0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
     0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
     0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
     0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
     0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
     0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-! ## §5.3.3 — the SHA-256 initial hash value -/

/-- FIPS 180-4 §5.3.3: the first thirty-two bits of the fractional parts of the
*square* roots of the first eight prime numbers. The SHA-224 initial value of
§5.3.2 differs in all eight words and is the discriminating negative
(`test/contracts/sha256.contract.md`). -/
def H0 : Vector Word 8 :=
  #v[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
     0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-! ## §5.1.1 — padding the message -/

/-- FIPS 180-4 §5.1.1: append the bit `1`, then `k` zero bits where `k` is the
smallest non-negative solution of `ℓ + 1 + k ≡ 448 (mod 512)`, then the 64-bit
big-endian representation of the message length `ℓ`.

`(959 - ℓ % 512) % 512` is that `k`: `959 ≡ 447 (mod 512)`, and `959 - ℓ % 512`
is at least `448`, so the truncating `Nat` subtraction never fires. -/
def pad (M : List Bool) : List Bool :=
  M ++ ((true :: List.replicate ((959 - M.length % 512) % 512) false) ++
    bitsOfNat 64 M.length)

/-! ## §5.2.1 — parsing the padded message -/

/-- FIPS 180-4 §5.2.1: a 512-bit block read as sixteen 32-bit words, the first
32 bits of the block being word 0. -/
def blockOfBits (bits : List Bool) : Vector Word 16 :=
  Vec.ofFn fun i : Fin 16 => wordOfBits ((bits.drop (32 * i.1)).take 32)

set_option linter.unusedVariables false in
/-- FIPS 180-4 §5.2.1: the padded message is parsed into 512-bit blocks. Total
extension: a trailing run shorter than a block is dropped, so this carries FIPS
180-4 meaning only on padded input. -/
def parse (P : List Bool) : List (Vector Word 16) :=
  if h : P.length < 512 then []
  else blockOfBits (P.take 512) :: parse (P.drop 512)
termination_by P.length
decreasing_by simp only [List.length_drop]; omega

theorem parse_nil_of_lt (P : List Bool) (h : P.length < 512) : parse P = [] := by
  rw [parse, dif_pos h]

theorem parse_cons (P : List Bool) (h : ¬ (P.length < 512)) :
    parse P = blockOfBits (P.take 512) :: parse (P.drop 512) := by
  rw [parse, dif_neg h]

/-! ## §6.2.2 — the SHA-256 hash computation -/

/-- FIPS 180-4 §6.2.2 step 1, the initial sixteen words: `Wt = Mt` for
`0 ≤ t ≤ 15`. -/
def scheduleInit (block : Vector Word 16) : Vector Word 64 :=
  Vec.ofFn fun i : Fin 64 => if h : i.val < 16 then block[i.val] else 0

/-- FIPS 180-4 §6.2.2 step 1, the recurrence:
`Wt = σ₁(W t−2) + W t−7 + σ₀(W t−15) + W t−16` for `16 ≤ t ≤ 63`, with addition
modulo `2³²`. -/
def scheduleStep (i : Nat) (hi : i < 48) (acc : Vector Word 64) : Vector Word 64 :=
  have h2 : i + 16 - 2 < 64 := by omega
  have h7 : i + 16 - 7 < 64 := by omega
  have h15 : i + 16 - 15 < 64 := by omega
  have h16 : i + 16 - 16 < 64 := by omega
  acc.set (i + 16)
    (σ1 acc[i + 16 - 2] + acc[i + 16 - 7] + σ0 acc[i + 16 - 15] + acc[i + 16 - 16])
    (by omega)

/-- FIPS 180-4 §6.2.2 step 1: the sixty-four-word message schedule. -/
def schedule (block : Vector Word 16) : Vector Word 64 :=
  Nat.fold 48 scheduleStep (scheduleInit block)

/-- FIPS 180-4 §6.2.2 step 3, one round on the working variables
`⟨a, b, c, d, e, f, g, h⟩`. -/
def round (sched : Vector Word 64) (t : Nat) (ht : t < 64) (st : Vector Word 8) :
    Vector Word 8 :=
  let a := st[0]
  let b := st[1]
  let c := st[2]
  let d := st[3]
  let e := st[4]
  let f := st[5]
  let g := st[6]
  let h := st[7]
  let T1 := h + «Σ1» e + Ch e f g + K[t] + sched[t]
  let T2 := «Σ0» a + Maj a b c
  #v[T1 + T2, a, b, c, d + T1, e, f, g]

/-- FIPS 180-4 §6.2.2 steps 2–4: initialise the working variables from `H`, run
the sixty-four rounds, then add the working variables into `H`. -/
def compress (H : Vector Word 8) (block : Vector Word 16) : Vector Word 8 :=
  let final := Nat.fold 64 (round (schedule block)) H
  Vec.ofFn fun i : Fin 8 =>
    have hi : i.1 < 8 := i.2
    H[i.1] + final[i.1]

/-- FIPS 180-4 §6.2: the hash value after every block of the padded message. -/
def hash (M : List Bool) : Vector Word 8 := (parse (pad M)).foldl compress H0

/-- FIPS 180-4 §3.1: the final hash value as a 256-bit string, words in order,
most significant bit of each word first. -/
def bitsOfWords (H : Vector Word 8) : List Bool :=
  (List.finRange 8).flatMap fun i => bitsOfWord H[i]

/-- SHA-256 as FIPS 180-4 defines it: a bit string to a 256-bit string. -/
def sha256 (M : List Bool) : List Bool := bitsOfWords (hash M)

/-- SHA-256 on byte-aligned messages, the only domain this lane claims. -/
def sha256_bytes (msg : List UInt8) : List UInt8 :=
  bytesOfBits (sha256 (bitsOfBytes msg))

/-! ## The frozen `Spec` theorems (`docs/SHA256-DAG.md` §4 A1.S1) -/

theorem length_pad (M : List Bool) : (pad M).length % 512 = 0 := by
  simp only [pad, List.length_append, List.length_cons, List.length_replicate,
    length_bitsOfNat]
  omega

theorem pad_prefix (M : List Bool) : (pad M).take M.length = M := List.take_left

theorem length_bitsOfWords (H : Vector Word 8) : (bitsOfWords H).length = 256 := by
  rw [bitsOfWords, length_flatMap_const _ _ 32 fun i => length_bitsOfWord H[i]]
  simp

theorem length_sha256 (M : List Bool) : (sha256 M).length = 256 :=
  length_bitsOfWords (hash M)

theorem bytesOfBits_bitsOfBytes (bs : List UInt8) : bytesOfBits (bitsOfBytes bs) = bs := by
  induction bs with
  | nil =>
      rw [show bitsOfBytes ([] : List UInt8) = [] from rfl, bytesOfBits_nil]
  | cons b t ih =>
      rw [bitsOfBytes_cons, bytesOfBits_append8 _ _ (length_bitsOfByte b),
        byteOfBits_bitsOfByte, ih]

theorem bitsOfBytes_bytesOfBits (bits : List Bool) (h : bits.length % 8 = 0) :
    bitsOfBytes (bytesOfBits bits) = bits := by
  rcases Nat.eq_zero_or_pos bits.length with h0 | hpos
  · rw [List.eq_nil_of_length_eq_zero h0, bytesOfBits_nil]
    rfl
  · have h8 : 8 ≤ bits.length := by omega
    have htake : (bits.take 8).length = 8 := by rw [List.length_take]; omega
    have hdrop : (bits.drop 8).length % 8 = 0 := by rw [List.length_drop]; omega
    calc bitsOfBytes (bytesOfBits bits)
        = bitsOfBytes (bytesOfBits (bits.take 8 ++ bits.drop 8)) := by
          rw [List.take_append_drop]
      _ = bitsOfBytes (byteOfBits (bits.take 8) :: bytesOfBits (bits.drop 8)) := by
          rw [bytesOfBits_append8 _ _ htake]
      _ = bitsOfByte (byteOfBits (bits.take 8)) ++ bitsOfBytes (bytesOfBits (bits.drop 8)) :=
          bitsOfBytes_cons _ _
      _ = bits.take 8 ++ bits.drop 8 := by
          rw [bitsOfByte_byteOfBits _ htake,
            bitsOfBytes_bytesOfBits (bits.drop 8) hdrop]
      _ = bits := List.take_append_drop 8 bits
termination_by bits.length
decreasing_by simp only [List.length_drop]; omega

end Sha256.Spec
