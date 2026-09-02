# WhatwgStreams counterexample register

Stable IDs in this file are never reused. A row closes only when its witness
is retained and the repaired declaration or theorem mechanically rejects the
attack. Statuses are defined in `README.md` beside this file.

| ID | Status | Attacked statement | Witness / evidence | Forced repair |
| --- | --- | --- | --- | --- |
| `WS-SHA-CE-001` | `CLOSED` | `Sha256.Spec.H0` is FIPS 180-4 §5.3.3 and not §5.3.2 | `WhatwgStreamsTest/Counterexamples/Sha/Mutants.lean`, `ce001_sha224IV` with its control `ce001_control`; `Sha256.Bridge.sha256_ne_sha224_iv` on the constants | none: the shipped `H0` is §5.3.3, and the witness pins that the choice is load-bearing |
| `WS-SHA-CE-002` | `CLOSED` | `Sha256.Impl.padBytes` appends the 64-bit big-endian length of FIPS 180-4 §5.1.1 | same file, `ce002_noLengthField` on W2, with `ce002_padBytes_eq_on_empty` proving why W1 cannot discriminate | none to the implementation; the contract's claim that W1 catches this mutant is corrected in `test/counterexamples/sha/ATTACKS.md` |
| `WS-SHA-CE-003` | `CLOSED` | `Sha256.Impl.wordOfBytes` reads four bytes big-endian per FIPS 180-4 §3.1 | same file, `ce003_littleEndianWords` on W2 | none: the shipped reading is big-endian |
| `WS-SHA-CE-004` | `CLOSED` | `Sha256.Spec.bitsOfByte` is most-significant-bit-first per FIPS 180-4 §3.1, not FIPS 202 Appendix B.1's least-significant-first | same file, `ce004_lsbFirstBitOrder` on W1, with `ce004_padMarker` identifying the mutant's `0x01` padding byte | none: `Sha256.Spec` reproduces rather than imports foldlab's `formal/fips202` conversion, precisely because the conventions differ |

Every row's evidence command is `lake build WhatwgStreamsTest`, which
elaborates the witnesses. Each inequality is closed by `decide +kernel`, so it
is checked by the Lean kernel with no compiler in the trust path, and the
expected digests come from `Sha256.Kats`, produced mechanically from the sealed
`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp`. The attack shapes are described in
`test/counterexamples/sha/ATTACKS.md`.

The P3 queue-with-sizes breaker mints the first rows outside the `SHA` area.
