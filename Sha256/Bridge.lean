import Sha256.Lengths

/-!
# `Sha256.Bridge` — the byte-level reference computes the FIPS 180-4 function

The apex is `sha256_bridge`: `Impl.sha256 msg = Spec.sha256_bytes msg` for every
byte string. `docs/SHA256-DAG.md` §4 A1.S2 fixes the decomposition; this file
proves it.

The whole proof is data flow. `Impl` shares `Spec`'s word functions and
constants outright, so `schedule_bridge` and `compress_bridge` are `rfl`;
everything else is about how bytes become bits, how bits become words, and how
a byte string is cut into blocks.

Domain of validity, inherited from foldlab `formal/fips202` REV2:
`Spec.parse` and `Spec.hash` are total extensions that carry FIPS 180-4 meaning
only on padded input, `Spec.bitsOfBytes_bytesOfBits` carries its `% 8` premise,
and `sha256_bridge` is stated on byte-aligned messages only. No unrestricted
bijection is claimed.
-/

namespace Sha256.Bridge

open Sha256

/-! ## Byte-string plumbing -/

theorem bitsOfBytes_append (xs ys : List UInt8) :
    Spec.bitsOfBytes (xs ++ ys) = Spec.bitsOfBytes xs ++ Spec.bitsOfBytes ys :=
  List.flatMap_append

theorem bitsOfBytes_flatMap {α : Type} (l : List α) (f : α → List UInt8) :
    Spec.bitsOfBytes (l.flatMap f) = l.flatMap fun a => Spec.bitsOfBytes (f a) := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, bitsOfBytes_append, ih, List.flatMap_cons]

theorem bitsOfBytes_take (bs : List UInt8) (k : Nat) :
    Spec.bitsOfBytes (bs.take k) = (Spec.bitsOfBytes bs).take (8 * k) := by
  induction bs generalizing k with
  | nil => simp [Spec.bitsOfBytes]
  | cons b bs ih =>
      cases k with
      | zero => rfl
      | succ k =>
          rw [List.take_succ_cons, Spec.bitsOfBytes_cons, Spec.bitsOfBytes_cons, ih,
            List.take_append,
            List.take_of_length_le (show (Spec.bitsOfByte b).length ≤ 8 * (k + 1) by
              rw [Spec.length_bitsOfByte]; omega),
            Spec.length_bitsOfByte, show 8 * (k + 1) - 8 = 8 * k by omega]

theorem bitsOfBytes_drop (bs : List UInt8) (k : Nat) :
    Spec.bitsOfBytes (bs.drop k) = (Spec.bitsOfBytes bs).drop (8 * k) := by
  induction bs generalizing k with
  | nil => simp [Spec.bitsOfBytes]
  | cons b bs ih =>
      cases k with
      | zero => rfl
      | succ k =>
          rw [List.drop_succ_cons, Spec.bitsOfBytes_cons, ih, List.drop_append,
            List.drop_eq_nil_of_le (show (Spec.bitsOfByte b).length ≤ 8 * (k + 1) by
              rw [Spec.length_bitsOfByte]; omega),
            List.nil_append, Spec.length_bitsOfByte, show 8 * (k + 1) - 8 = 8 * k by omega]

theorem bitsOfBytes_replicate (n : Nat) :
    Spec.bitsOfBytes (List.replicate n 0) = List.replicate (8 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, Spec.bitsOfBytes_cons, ih,
        show Spec.bitsOfByte 0 = List.replicate 8 false from rfl,
        List.replicate_append_replicate, show 8 + 8 * n = 8 * (n + 1) by omega]

/-! ## Splitting a big-endian spelling into bytes -/

private theorem bitsOfNat_split8 (a b n : Nat) (h : a = 8 + b) :
    Spec.bitsOfNat a n = Spec.bitsOfNat 8 (n >>> b) ++ Spec.bitsOfNat b n := by
  subst h
  exact Spec.bitsOfNat_add 8 b n

/-- FIPS 180-4 §5.1.1: the eight big-endian length bytes are the 64-bit
big-endian spelling of the length. -/
theorem bitsOfBytes_lengthBytes (m : Nat) :
    Spec.bitsOfBytes (Impl.lengthBytes m) = Spec.bitsOfNat 64 m := by
  rw [Impl.lengthBytes]
  simp only [Spec.bitsOfBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Spec.bitsOfByte_ofNat]
  rw [bitsOfNat_split8 64 56 m rfl, bitsOfNat_split8 56 48 m rfl,
    bitsOfNat_split8 48 40 m rfl, bitsOfNat_split8 40 32 m rfl,
    bitsOfNat_split8 32 24 m rfl, bitsOfNat_split8 24 16 m rfl,
    bitsOfNat_split8 16 8 m rfl]

/-- FIPS 180-4 §3.1: the four big-endian bytes of a word are its 32-bit
big-endian spelling. -/
theorem bitsOfBytes_bytesOfWord (w : Impl.Word) :
    Spec.bitsOfBytes (Impl.bytesOfWord w) = Spec.bitsOfWord w := by
  rw [Impl.bytesOfWord]
  simp only [Spec.bitsOfBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Spec.bitsOfByte_ofNat, BitVec.toNat_ushiftRight]
  rw [Spec.bitsOfWord, bitsOfNat_split8 32 24 w.toNat rfl,
    bitsOfNat_split8 24 16 w.toNat rfl, bitsOfNat_split8 16 8 w.toNat rfl]

/-! ## §5.1.1 — padding -/

/-- The byte-level padding of `Impl` is the bit-level padding of `Spec`. The
zero counts agree: `7 + 8 * ((119 - ℓ % 64) % 64) = (959 - 8ℓ % 512) % 512`. -/
theorem padBytes_bridge (msg : List UInt8) :
    Spec.bitsOfBytes (Impl.padBytes msg) = Spec.pad (Spec.bitsOfBytes msg) := by
  have hzero : 7 + 8 * ((119 - msg.length % 64) % 64)
      = (959 - 8 * msg.length % 512) % 512 := by omega
  rw [Impl.padBytes, Spec.pad, bitsOfBytes_append, bitsOfBytes_append,
    Spec.bitsOfBytes_cons, bitsOfBytes_replicate, bitsOfBytes_lengthBytes,
    Spec.length_bitsOfBytes,
    show Spec.bitsOfByte 0x80 = true :: List.replicate 7 false from rfl,
    List.cons_append, List.replicate_append_replicate, hzero]

/-! ## §5.2.1 — words, blocks, parsing -/

private theorem getD_drop (l : List UInt8) (m j : Nat) :
    (l.drop m).getD j 0 = l.getD (m + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem take4_of_ge (l : List UInt8) (h : 4 ≤ l.length) :
    l.take 4 = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0] := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | [_, _, _] => simp at h
  | _ :: _ :: _ :: _ :: _ => rfl

private theorem take4_drop (l : List UInt8) (m : Nat) (h : m + 4 ≤ l.length) :
    (l.drop m).take 4 =
      [l.getD m 0, l.getD (m + 1) 0, l.getD (m + 2) 0, l.getD (m + 3) 0] := by
  have hlen : 4 ≤ (l.drop m).length := by rw [List.length_drop]; omega
  rw [take4_of_ge _ hlen, getD_drop, getD_drop, getD_drop, getD_drop, Nat.add_zero]

/-- Four disjoint byte-wide fields packed into a word: the `|||` of the shifted
pieces is their sum, so the big-endian reading of the four bytes is the word. -/
private theorem pack4 (A B C D : Nat) (hA : A < 256) (hB : B < 256) (hC : C < 256)
    (hD : D < 256) :
    BitVec.ofNat 32 (A * 2 ^ 24 + (B * 2 ^ 16 + (C * 2 ^ 8 + D)))
      = (BitVec.ofNat 32 A <<< 24) ||| ((BitVec.ofNat 32 B <<< 16) |||
        ((BitVec.ofNat 32 C <<< 8) ||| BitVec.ofNat 32 D)) := by
  have step : ∀ i a b : Nat, b < 2 ^ i → a * 2 ^ i ||| b = a * 2 ^ i + b := fun i a b hb => by
    rw [Nat.mul_comm]
    exact (Nat.two_pow_add_eq_or_of_lt hb a).symm
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega : A < 2 ^ 32), Nat.mod_eq_of_lt (by omega : B < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : C < 2 ^ 32), Nat.mod_eq_of_lt (by omega : D < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : A * 2 ^ 24 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : B * 2 ^ 16 < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : C * 2 ^ 8 < 2 ^ 32),
    step 8 C D (by omega), step 16 B (C * 2 ^ 8 + D) (by omega),
    step 24 A (B * 2 ^ 16 + (C * 2 ^ 8 + D)) (by omega),
    Nat.mod_eq_of_lt (by omega : A * 2 ^ 24 + (B * 2 ^ 16 + (C * 2 ^ 8 + D)) < 2 ^ 32)]

/-- FIPS 180-4 §3.1: the big-endian word denoted by four bytes' bits is the
word `Impl` packs from those bytes. -/
theorem wordOfBits_bitsOfBytes4 (a b c d : UInt8) :
    Spec.wordOfBits (Spec.bitsOfBytes [a, b, c, d]) = Impl.wordOfBytes a b c d := by
  have hb : ∀ x : UInt8, x.toNat < 256 := fun x =>
    Nat.lt_of_lt_of_le x.toNat_lt (by decide)
  rw [Spec.wordOfBits]
  simp only [Spec.bitsOfBytes, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Spec.natOfBits_append, Spec.length_bitsOfByte, List.length_append,
    Spec.natOfBits_bitsOfByte]
  rw [Impl.wordOfBytes]
  exact pack4 a.toNat b.toNat c.toNat d.toNat (hb a) (hb b) (hb c) (hb d)

/-- The sixteen words `Impl` reads out of a 64-byte block are the sixteen words
FIPS 180-4 §5.2.1 reads out of the corresponding 512 bits. -/
theorem wordsOfBlock_eq_blockOfBits (block : List UInt8) (h : block.length = 64) :
    Impl.wordsOfBlock block = Spec.blockOfBits (Spec.bitsOfBytes block) := by
  rw [Impl.wordsOfBlock, Spec.blockOfBits]
  apply Vector.ext
  intro i hi
  simp only [Vec.getElem_ofFn]
  have h4 : 4 * i + 4 ≤ block.length := by omega
  have hchunk : ((Spec.bitsOfBytes block).drop (32 * i)).take 32
      = Spec.bitsOfBytes [block.getD (4 * i) 0, block.getD (4 * i + 1) 0,
          block.getD (4 * i + 2) 0, block.getD (4 * i + 3) 0] := by
    rw [show (32 : Nat) * i = 8 * (4 * i) by omega, ← bitsOfBytes_drop,
      show (32 : Nat) = 8 * 4 from rfl, ← bitsOfBytes_take, take4_drop _ _ h4]
  rw [hchunk, wordOfBits_bitsOfBytes4]

/-! ## §5.2.1 — parsing agrees with cutting into blocks -/

theorem blocks_bridge (P : List UInt8) (h : P.length % 64 = 0) :
    (Impl.blocks P).map Impl.wordsOfBlock = Spec.parse (Spec.bitsOfBytes P) := by
  by_cases hsmall : P.length < 64
  · have hzero : P.length = 0 := by omega
    rw [Impl.blocks_nil_of_lt P hsmall, List.map_nil,
      Spec.parse_nil_of_lt _ (by rw [Spec.length_bitsOfBytes]; omega)]
  · have hbig : ¬ ((Spec.bitsOfBytes P).length < 512) := by
      rw [Spec.length_bitsOfBytes]; omega
    have htake : (P.take 64).length = 64 := by rw [List.length_take]; omega
    have hdrop : (P.drop 64).length % 64 = 0 := by rw [List.length_drop]; omega
    have hrec : ((Impl.blocks (P.drop 64)).map Impl.wordsOfBlock)
        = Spec.parse (Spec.bitsOfBytes (P.drop 64)) := blocks_bridge (P.drop 64) hdrop
    rw [Impl.blocks_cons P hsmall, List.map_cons, hrec, Spec.parse_cons _ hbig,
      wordsOfBlock_eq_blockOfBits _ htake,
      show (512 : Nat) = 8 * 64 from rfl, ← bitsOfBytes_take, ← bitsOfBytes_drop]
termination_by P.length
decreasing_by simp only [List.length_drop]; omega

/-- The frozen A1.S2 shape of `wordsOfBlock_bridge`: on a 64-byte block the
parse produces exactly one block of words, and it is `Impl`'s. -/
theorem wordsOfBlock_bridge (block : List UInt8) (h : block.length = 64) :
    Impl.wordsOfBlock block = (Spec.parse (Spec.bitsOfBytes block)).head! := by
  have hlen : (Spec.bitsOfBytes block).length = 512 := by
    rw [Spec.length_bitsOfBytes, h]
  have hbig : ¬ ((Spec.bitsOfBytes block).length < 512) := by omega
  have hrest : ((Spec.bitsOfBytes block).drop 512).length < 512 := by
    rw [List.length_drop, hlen]; omega
  rw [Spec.parse_cons _ hbig, Spec.parse_nil_of_lt _ hrest,
    wordsOfBlock_eq_blockOfBits _ h,
    List.take_of_length_le (Nat.le_of_eq hlen)]
  rfl

/-! ## §6.2.2 — the shared round functions -/

theorem schedule_bridge (w : Vector Impl.Word 16) : Impl.schedule w = Spec.schedule w := rfl

theorem compress_bridge (H : Impl.St) (w : Vector Impl.Word 16) :
    Impl.compress H w = Spec.compress H w := rfl

/-! ## §6.2 — the hash computation -/

theorem hash_bridge (msg : List UInt8) : Impl.hash msg = Spec.hash (Spec.bitsOfBytes msg) := by
  rw [Impl.hash, Impl.hash', Spec.hash, ← padBytes_bridge,
    blocks_bridge _ (Impl.length_padBytes msg)]
  rfl

/-! ## §3.1 — the output -/

theorem output_bridge (H : Impl.St) :
    Spec.bitsOfBytes ((List.finRange 8).flatMap fun i => Impl.bytesOfWord H[i])
      = Spec.bitsOfWords H := by
  rw [bitsOfBytes_flatMap, Spec.bitsOfWords]
  simp only [bitsOfBytes_bytesOfWord]

/-! ## The apex -/

/-- The byte-level reference computes the FIPS 180-4 function on every byte
string. This is the theorem that gives `Sha256.sha256` its meaning; the
known-answer tests of `Sha256.Kats` are finite evidence beside it, never a
substitute for it. -/
theorem sha256_bridge (msg : List UInt8) : Impl.sha256 msg = Spec.sha256_bytes msg := by
  rw [Spec.sha256_bytes, Spec.sha256, ← hash_bridge, ← output_bridge]
  exact (Spec.bytesOfBits_bitsOfBytes (Impl.sha256 msg)).symm

/-! ## The discriminating negative

FIPS 180-4 §6.3: SHA-224 is defined in the exact same manner as SHA-256 with
exactly two exceptions, the §5.3.2 initial value and truncation to the
left-most 224 bits. So the initial value is load-bearing and nothing else in
the algorithm reveals a mistake in it: a transcription seeded from §5.3.2 would
satisfy every structural theorem above and produce a wrong digest for every
input. Injectivity of `compress` is not claimed and is not needed: this is a
statement about two named constants. -/

/-- FIPS 180-4 §5.3.2: the SHA-224 initial hash value. Present only as the
negative's other half; SHA-224 itself is stage S1.6. -/
def sha224IV : Vector Spec.Word 8 :=
  #v[0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
     0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4]

/-- The S1.2 form of the negative (`docs/SHA256-DAG.md` §4 A1.S2): the two
initial values are different constants. -/
theorem sha256_ne_sha224_iv : Spec.H0 ≠ sha224IV := by decide

end Sha256.Bridge
