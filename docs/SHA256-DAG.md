# SHA-256 proof graph

Status: graph opened at P0, every edge `required-open`, 2026-09-01. Lane S1
in `PLAN.md`.

The graph-bearing owner is `SHA256-PG-IMPL-EQ-SPEC`. Its subject is the
SHA-256 in `Gates/Sha256.lean`, which every digest in this repository depends
on: the vendor seal, the future span digests of the specification census, and
the provenance cross-checks. Until this graph closes, that implementation is
tooling with finite executable evidence, and every document that quotes a
digest says so.

## Why this is not trivial

The precedent is foldlab's `formal/fips202` SHA3-512 artifact, whose
`Impl = Spec` apex took a Pass A contract, a Pass B frozen snapshot, a
model-invariants ruling, and a six-part refinement decomposition before the
first bridge theorem was attempted. Four of its findings transfer directly:

1. **A bit-level specification carrier is not kernel-executable.** fips202
   measured a lane-level known-answer test at 17 s of kernel `rfl` and
   abandoned bit-level kernel KATs after two runs of over 40 minutes did not
   finish. Known-answer tests therefore live on the executable layer, and the
   specification connects to them only through a proved refinement bridge.
2. **The bridge decomposes or it does not close.** fips202's B2 apex was
   provable only after it was split into padding correspondence, block
   loading, abstraction commutation, one-block absorption, fold induction,
   and output conversion. SHA-256 needs the same shape.
3. **`omega` and `decide` carry the arithmetic; nothing native does.** The
   fips202 sources use `omega` 166 times and `by decide` 16 times and never
   `native_decide`. This repository's axiom gate forbids `Lean.ofReduceBool`,
   which rules out both `native_decide` and `bv_decide`. Word-level
   identities cannot be discharged by SAT; they must be avoided by sharing
   definitions or proved by rewriting.
4. **Panicking accessors do not survive a proof.** An implementation written
   with `arr[i]!` returns a default value out of range, so every theorem about
   it carries bound obligations the current `for`-loop code does not expose.

## Carriers

| Layer | Carrier | Status |
| --- | --- | --- |
| specification (`Sha256.Spec`) | message as `List Bool`; padded message as `List Bool` with the FIPS 180-4 §5.1.1 padding; blocks as `List (Vector (BitVec 32) 16)`; schedule as a `BitVec 32`-valued function of `Fin 64`; compression as `Nat.fold` over 64 rounds on an 8-tuple of `BitVec 32`; digest as `List Bool` of length 256; byte conversion by FIPS 180-4 §3.1 big-endian order | to be written at S1 Pass B; never executed by the kernel beyond tiny probes |
| executable (`Sha256.Impl`) | `ByteArray` message; `Vector UInt32 64` schedule; `Vector UInt32 8` state; structural recursion or `Nat.fold`, not `for` loops, over blocks and rounds; bounded indexing through `Vector` | replaces the current `Gates/Sha256.lean` body at S1; the current body is retained as `Sha256.Tooling` until the replacement's KATs match |
| abstraction | `UInt32.toBitVec` per word; `bitsOfBytes` big-endian per byte | S1 |

The word functions Σ0, Σ1, σ0, σ1, Ch, Maj are **shared definitions** written
once over `BitVec 32` and instantiated at `UInt32` through `toBitVec`, so the
bridge never has to prove a bit-level identity. FIPS 180-4 itself defines
them on 32-bit words; transcribing them at word level is faithful.

## Decomposition

| Node | Statement (meaning frozen here; exact form fixed in the S1 battery) |
| --- | --- |
| `S-A` padding | for a byte-aligned message, `bitsOfBytes (Impl.pad m) = Spec.pad (bitsOfBytes m)`; `(Impl.pad m).size % 64 = 0`; `(Impl.pad m).size = m.size + 1 + zeros m + 8` with `zeros` the §5.1.1 count |
| `S-B` word loading | the `i`-th 32-bit word of a 64-byte block equals the big-endian `BitVec 32` of the corresponding 32 bits of the padded bit string |
| `S-C` schedule | the executable 64-word schedule equals the specification's `W_t` recurrence for every `t < 64`, by induction on `t` |
| `S-D` compression | 64 rounds of the executable round function on `UInt32` equal 64 rounds of the specification round on `BitVec 32` under `toBitVec`, by induction on the round index |
| `S-E` block fold | folding compression over the block list equals the specification's `H^(i)` sequence, by induction on the list |
| `S-F` output | the 32 output bytes are the big-endian serialization of the final eight words |
| `S-KAT` known answers | at the executable layer only: the FIPS 180-4 examples for `abc` and the two-block message, and the CAVP short-message vectors, each by kernel `decide` or `rfl` if within budget, otherwise recorded as executable evidence and never as a theorem |
| `S-NEG` discriminating negative | SHA-224 shares the compression function and differs only in initial state and truncation; `Impl.sha256 [] ≠ Impl.sha224Padded []` witnesses that the initial-state constants are load-bearing |
| apex | `∀ m : ByteArray, bitsOfBytes (Impl.digest m) = Spec.sha256 (bitsOfBytes m)` |

`S-KAT` kernel budget: measure before claiming. fips202's 17 s lane-level
budget is the reference; a `decide` over `ByteArray` and `UInt32` arithmetic
in the kernel may not fit. If it does not, the KATs stay executable evidence
and the apex theorem is what carries trust, exactly as in fips202.

## Edge ledger

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-open` | FIPS 180-4 PDF pinned by digest in `docs/PROVENANCE.md`; CAVP vectors not yet fetched |
| construction | `required-open` | `Spec` and `Impl` declarations frozen by the S1 Pass B snapshot |
| semantics | `required-open` | the apex refinement above |
| laws | `required-open` | `S-A` through `S-F` |
| representation | `required-open` | `Vector`-indexed executable carrier replaces `!`-indexed `for` loops; `Sha256.Tooling` retired only after byte-identical digests on the vendor tree |
| counterexamples | `required-open` | `S-NEG`; an `Impl.pad` mutant that pads to 56 mod 64 without the length field; a big-endian/little-endian word-loading mutant; each registered as `WS-SHA-CE-nnn` |
| bridges | `not-applicable` | the SHA-256 lane has no host target |
| targets | `not-applicable` | no generated code |
| trust | `required-open` | axiom receipts inside `propext`/`Quot.sound` for every S1 theorem; external replay with `leanchecker`; dual-host build (Windows and macOS) as in fips202 |
| coverage | `required-open` | every FIPS 180-4 section the transcription cites is listed in the Pass A contract with the citation verified against the pinned PDF |

## Trust statement until closure

`lake exe sha256 --self-test` is finite evidence against seven vectors: the
FIPS 180-4 examples for the empty message, `abc`, and the 56-byte two-block
message; three padding-boundary lengths; and the one-million-`a` vector.
Every pinned digest is additionally cross-checked against PowerShell's
`Get-FileHash`. Neither is a theorem, and no document in this repository may
describe the in-tree SHA-256 as verified while this ledger has an open edge.

## Route to close

1. S1 Pass A: domain contract over FIPS 180-4, fetched and pinned CAVP
   vectors, witness digests transcribed from the pinned `.rsp` files rather
   than from memory, the discriminating negative, and the claim-domain table.
2. S1 Pass B: frozen signature snapshot for `Sha256.Spec`, `Sha256.Impl`, and
   the bridge; kernel-budget measurement for `S-KAT`.
3. Breaker freezes the battery red; builder closes `S-A` through `S-F`, then
   the apex.
4. Retire `Sha256.Tooling` after the vendor manifest regenerates
   byte-identically under `Sha256.Impl`.
5. Record receipts, dual-host build, `leanchecker` replay; close the ledger.
