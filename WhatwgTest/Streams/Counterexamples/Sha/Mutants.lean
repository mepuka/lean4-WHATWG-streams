import Sha256
import Sha256.Kats

/-!
# `WS-SHA-CE-001` … `WS-SHA-CE-004` — SHA-256 transcription mutants

Four plausible wrong transcriptions of FIPS 180-4, each defined here in full
and each proved to produce a digest different from the pinned NIST CAVP answer.
They are the executable witnesses for the rows of the same names in
`test/counterexamples/REGISTER.md`; `test/counterexamples/sha/ATTACKS.md`
describes the attack shapes in prose.

Every mutant reuses the shipped `Sha256.Impl` for everything except the one
thing it gets wrong, so each theorem isolates exactly that mistake. The
expected digests are `Sha256.Kats`'s, which were produced mechanically from the
sealed `vendor/nist-cavp-sha256/SHA256ShortMsg.rsp`; no literal is retyped here.

Each inequality is closed by `decide +kernel`: kernel reduction, no compiler in
the trust path, no axiom beyond the semantic ceiling. Plain `decide` and `rfl`
exhaust `maxRecDepth` on a full digest (`docs/SHA256-DAG.md` §2, measured).

**What these witnesses do and do not show.** Each shows that one specific wrong
transcription is rejected by one pinned vector. None of them shows that the
shipped transcription is right; that is `Sha256.Bridge.sha256_bridge` for the
`Impl` = `Spec` step and the named human trust step of
`test/contracts/sha256.contract.md` C2 for `Spec` = FIPS 180-4.
-/

namespace WhatwgTest.Streams.Counterexamples.Sha

open Sha256

/-- The digest a transcription would produce from an arbitrary initial hash
value, everything else being `Sha256.Impl`. -/
def digestWithIV (iv : Impl.St) (msg : List UInt8) : List UInt8 :=
  let final := ((Impl.blocks (Impl.padBytes msg)).map Impl.wordsOfBlock).foldl Impl.compress iv
  (List.finRange 8).flatMap fun i => Impl.bytesOfWord final[i]

/-! ## WS-SHA-CE-001 — the SHA-224 initial hash value

FIPS 180-4 §5.3.2 against §5.3.3. The initial value is load-bearing and nothing
else in the algorithm reveals a mistake in it: a transcription seeded from
§5.3.2 satisfies every length lemma, every padding lemma and every round
identity in `docs/SHA256-DAG.md` §4 A1.S1, and produces a wrong digest for
every input. `Sha256.Bridge.sha256_ne_sha224_iv` states it on the constants;
this states it on a digest. -/

theorem ce001_sha224IV : digestWithIV Bridge.sha224IV [] ≠ Kats.w1Digest := by
  decide +kernel

/-- Control: with the §5.3.3 value the same pipeline reproduces the pinned
digest, so `ce001_sha224IV` is about the initial value and nothing else. -/
theorem ce001_control : digestWithIV Spec.H0 [] = Kats.w1Digest := by
  decide +kernel

/-! ## WS-SHA-CE-002 — padding without the 64-bit length field

FIPS 180-4 §5.1.1 appends the message length as a 64-bit big-endian integer.
This mutant appends the `1` bit and zeros only, padding to a whole number of
blocks, and is otherwise `Sha256.Impl`.

**W1 cannot catch this mutant, and `padBytes_eq_on_empty` proves why.** The
empty message's length field is eight zero bytes, and the correct padding of
the empty message is `0x80` followed by fifty-five zeros and then those eight
zeros — which is `0x80` followed by sixty-three zeros, exactly what this mutant
produces. The two paddings are not merely digest-equal on W1; they are the same
list of bytes. `test/contracts/sha256.contract.md` §4 lists this mutant as
"caught by W1, W2"; the W1 half of that claim is false, and this is the finding
that says so. `W2` is the shortest pinned witness that does catch it. -/

/-- `0x80` then zeros to a multiple of 64 bytes, with no length field. -/
def padNoLength (msg : List UInt8) : List UInt8 :=
  msg ++ (0x80 :: List.replicate ((63 - msg.length % 64) % 64) 0)

def digestNoLength (msg : List UInt8) : List UInt8 :=
  let final := ((Impl.blocks (padNoLength msg)).map Impl.wordsOfBlock).foldl
    Impl.compress Spec.H0
  (List.finRange 8).flatMap fun i => Impl.bytesOfWord final[i]

/-- Why W1 is blind to a missing length field: on the empty message the two
paddings are the same bytes. -/
theorem ce002_padBytes_eq_on_empty : Impl.padBytes [] = padNoLength [] := by decide

theorem ce002_noLengthField : digestNoLength Kats.w2Msg ≠ Kats.w2Digest := by
  decide +kernel

/-! ## WS-SHA-CE-003 — little-endian word loading

FIPS 180-4 §3.1 stores the most significant bit of a word in the left-most
position, so the four bytes of a word are read big-endian. This mutant reads
them little-endian and is otherwise `Sha256.Impl`. `W2` is the first witness
with message words, which is why the contract names it for this row. -/

def wordsOfBlockLE (block : List UInt8) : Vector Impl.Word 16 :=
  Vec.ofFn fun i : Fin 16 =>
    Impl.wordOfBytes (block.getD (4 * i.1 + 3) 0) (block.getD (4 * i.1 + 2) 0)
      (block.getD (4 * i.1 + 1) 0) (block.getD (4 * i.1) 0)

def digestLE (msg : List UInt8) : List UInt8 :=
  let final := ((Impl.blocks (Impl.padBytes msg)).map wordsOfBlockLE).foldl
    Impl.compress Spec.H0
  (List.finRange 8).flatMap fun i => Impl.bytesOfWord final[i]

theorem ce003_littleEndianWords : digestLE Kats.w2Msg ≠ Kats.w2Digest := by
  decide +kernel

/-! ## WS-SHA-CE-004 — the FIPS 202 bit order

FIPS 180-4 §3.1 is most significant bit first within a byte; FIPS 202 Appendix
B.1 is least significant bit first. Reading bytes into bits by the FIPS 202
convention and then packing words most significant bit first, as §5.2.1 says,
is exactly bit-reversal of every byte; the `1` padding bit becomes `0x01`
rather than `0x80` for the same reason, and the output bytes come back
reversed too.

This is the trap that experience with foldlab's `formal/fips202` makes *more*
likely, not less. Both round-trip theorems of §4 A1.S1 hold for either
convention, so no structural theorem catches it; only a known-answer vector
does (`test/contracts/sha256.contract.md`, E4). -/

/-- Reverse the eight bits of a byte. -/
def revBits (b : UInt8) : UInt8 :=
  UInt8.ofNat ((List.range 8).foldl (fun acc j => acc + if b.toNat.testBit j then 2 ^ (7 - j) else 0) 0)

def digestLsbFirst (msg : List UInt8) : List UInt8 :=
  let padded := (Impl.padBytes msg).map revBits
  let final := ((Impl.blocks padded).map Impl.wordsOfBlock).foldl Impl.compress Spec.H0
  ((List.finRange 8).flatMap fun i => Impl.bytesOfWord final[i]).map revBits

theorem ce004_lsbFirstBitOrder : digestLsbFirst [] ≠ Kats.w1Digest := by
  decide +kernel

/-- The bit-order mutant really is the FIPS 202 reading and not a typo: the
padding byte it produces is `0x01`, the least-significant-bit-first spelling of
a `1` bit followed by seven zeros, where FIPS 180-4 §5.1.1 writes `0x80`. -/
theorem ce004_padMarker : revBits 0x80 = 0x01 := by decide

/-! ## WS-SHA-CE-005 — the SHA-224 truncation

FIPS 180-4 §6.3, exception 2: the 224-bit message digest is the final hash
value truncated to its **left-most** 224 bits, written there as
`H₀ ‖ H₁ ‖ H₂ ‖ H₃ ‖ H₄ ‖ H₅ ‖ H₆` — the first seven of the eight words. The
plausible mistake is keeping the wrong end: the last seven words instead of the
first. That mutant produces 28 bytes, satisfies `Sha256.Impl.length_sha224` and
every bridge theorem above it, and differs from the standard on every input.

Nothing structural separates the two truncations, because both are `take 28` of
a permutation of the same 32 bytes. A vector is what fixes the choice, exactly
as for the four shapes above. -/

/-- The shipped truncation, stated against the untruncated output: SHA-224 is
the first 28 bytes of the digest bytes of the run from the §5.3.2 initial
value. This is the statement `ce005_rightmostTruncation` attacks. -/
theorem ce005_truncation_is_leftmost (msg : List UInt8) :
    Impl.sha224 msg = (Impl.hashBytes (Impl.hashWith Spec.H0_224 msg)).take 28 := rfl

/-- The mutant: the right-most 28 bytes, that is, dropping word `H₀`'s four
bytes where FIPS 180-4 drops word `H₇`'s. -/
def sha224Rightmost (msg : List UInt8) : List UInt8 :=
  (Impl.hashBytes (Impl.hashWith Spec.H0_224 msg)).drop 4

theorem ce005_rightmostTruncation : sha224Rightmost [] ≠ Kats.sha224W1Digest := by
  decide +kernel

/-- Control: the shipped left-most truncation reproduces the pinned SHA-224
vector on the same input, so `ce005_rightmostTruncation` is about the byte
range and nothing else. -/
theorem ce005_control : Impl.sha224 [] = Kats.sha224W1Digest := by decide +kernel

end WhatwgTest.Streams.Counterexamples.Sha
