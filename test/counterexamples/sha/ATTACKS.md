# SHA-256 attack shapes (area `SHA`)

The attacks the SHA-256 lane defends against are transcription mistakes, not
cryptanalysis. Nothing in this area is a security claim
(`test/contracts/sha256.contract.md`, "OUT, explicitly").

Each shape below is a complete, plausible reading of FIPS 180-4 that a careful
person could arrive at, that satisfies every structural theorem of
`docs/SHA256-DAG.md` §4 A1.S1, and that produces a wrong digest. The witnesses
are in `WhatwgTest/Streams/Counterexamples/Sha/Mutants.lean`; each is a Lean
theorem closed by `decide +kernel`, so the evidence is kernel reduction with no
compiler in the trust path.

The expected digests are `Sha256.Kats`'s, produced mechanically from the sealed
`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp`.

## Why known-answer vectors are the only defence here

The round-trip lemmas `Spec.bytesOfBits_bitsOfBytes` and
`Spec.bitsOfBytes_bytesOfBits`, the padding-length lemmas, and every round
identity hold for **all four** mutants below. They are statements about the
internal consistency of a transcription, not about which transcription it is.
A vector is what fixes the choice.

## The shapes

### The initial hash value (`WS-SHA-CE-001`)

FIPS 180-4 §5.3.3 gives SHA-256's initial hash value as the first thirty-two
bits of the fractional parts of the *square* roots of the first eight primes;
§5.3.2 gives SHA-224's from a different derivation, and §4.2.2's `K` comes from
the *cube* roots of the first sixty-four primes. Three tables on adjacent pages,
all eight or sixty-four words of hex. Seeding `H0` from the wrong one changes
every digest and nothing else.

Discriminated by W1. Injectivity of `compress` is not claimed and is not needed:
the witness is a statement about two named constants and the digests they
produce on one named input.

### Padding without the length field (`WS-SHA-CE-002`)

FIPS 180-4 §5.1.1 appends `1`, then `k` zero bits, then the message length as a
64-bit big-endian integer. Dropping the last part still yields a whole number
of blocks and still satisfies every length lemma.

**W1 is blind to this mutant, and the witness proves it.** The empty message's
length field is eight zero bytes, so its correct padding — `0x80`, fifty-five
zeros, eight zeros — is byte-for-byte the mutant's `0x80` followed by
sixty-three zeros. `ce002_padBytes_eq_on_empty` states that equality directly.
`test/contracts/sha256.contract.md` §4 lists this mutant as "caught by W1, W2";
the W1 half of that claim is false and is corrected here. W2 is the shortest
pinned witness that discriminates.

### Little-endian word loading (`WS-SHA-CE-003`)

FIPS 180-4 §3.1 stores the most significant bit of a word in the left-most
position, so a word is read from its four bytes big-endian. Reading them
little-endian is the single most common way to get a hash wrong on a
little-endian host, because the host's own integer loads are the wrong ones.

Discriminated by W2, the first witness with message words; W1 also
discriminates it, through the padding bytes.

### The FIPS 202 bit order (`WS-SHA-CE-004`)

FIPS 180-4 §3.1 is most significant bit first within a byte. FIPS 202 Appendix
B.1 is least significant bit first. Composing the FIPS 202 byte-to-bit map with
§5.2.1's most-significant-first word packing is exactly bit-reversal of every
byte; the padding `1` bit becomes `0x01` rather than `0x80` for the same reason,
and the output bytes come back reversed.

This is the shape that experience makes *more* likely rather than less: foldlab's
`formal/fips202` is the process precedent for this whole lane, and its
`bitsOfBytes` is the opposite convention. It is why that file is reproduced
rather than imported.

Discriminated by W1.

### The SHA-224 truncation (`WS-SHA-CE-005`)

FIPS 180-4 §6.3 says SHA-224 is SHA-256 with two exceptions: the §5.3.2 initial
value, and truncation of the final hash value "to its left-most 224 bits",
spelled out on the same page as `H₀ ‖ H₁ ‖ H₂ ‖ H₃ ‖ H₄ ‖ H₅ ‖ H₆` — the first
seven of eight words. Keeping the last seven instead produces 28 bytes, keeps
`Sha256.Impl.length_sha224` true, and keeps every bridge theorem above it true,
because both truncations are `take 28` of the same 32 bytes in a different
order.

The initial value is already covered by `WS-SHA-CE-001`; this row covers the
second exception on its own, against the SHA-224 `Len = 0` vector of
`vendor/nist-cavp-sha224/SHA224ShortMsg.rsp`. The control
`ce005_control` shows the shipped left-most truncation reproduces that vector,
so the inequality is about the byte range and nothing else.

Discriminated by the SHA-224 `Len = 0` vector.
