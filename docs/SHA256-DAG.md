# SHA-256 proof graph and implementation spec (lane S1)

Status: **S1.1–S1.4 LANDED 2026-09-02 (commit `a8f08d0`)** under ruling
R-10, reviewed first-hand and re-gated on a clean build by the coordinator.
`Sha256.Bridge.sha256_bridge` (`Impl.sha256 msg = Spec.sha256_bytes msg`)
and `Sha256.Fast.sha256_eq_impl` are proved at `[propext, Quot.sound]`; 280
declarations audited with 0 offenders and an empty R-3 list; the kernel KAT
for the empty message closes by `decide +kernel` in about 1 s; the vendor
manifest regenerates byte-identically through the proved library;
`leanchecker --fresh Sha256.Verified` exits 0. The edge ledger in §10 records
what is closed and what remains (S1.5 streaming, S1.6 SHA-224, S1.7 assurance
record, dual-host). Earlier history: R-1 approved 2026-09-01 with the §9
defaults; §4 frozen; S1.0 landed 2026-09-02. Author: coordinator, from a first-hand read of
foldlab's `formal/fips202` at commit `8d36195970b83a1439ec705b9a504617554b8062`,
its library specification `.staging/fips202-library/SPEC.md` (decision 45,
R-1 approved 2026-09-01), the prior art at
`.reference/clones/lean-crypto-hash` commit `54e6068abd4658fd91203cae1c2316188ffa0e89`,
and the pinned Lean `v4.33.1` sources.

Audience: the operator (rulings in §9) and the implementing seats (everything
else). A seat receives this document plus the name of ONE stage in §6 and
nothing more.

## 0. How to use this document

**Roles.** The coordinator owns statements and this document. The operator
owns rulings. A breaker freezes each stage's battery red; a builder
implements the stage: definitions, proofs, gates, the report. A seat never
changes a frozen statement, never mints a ruling, never commits, never pushes.

**Reading order for a seat.** `AGENTS.md` at the repository root whole;
`Gates/AGENTS.md` and `Whatwg/AGENTS.md`; then this document §1–§5,
the seat's stage in §6, and §7–§8. Then the files named in the stage's edit
region and nothing else.

**Stop conditions (report and stop, do not work around).**

1. The stage cannot be completed without changing the body of any frozen
   definition or the statement of any theorem in §4.
2. A proof needs an axiom outside the ceiling in §3.1, or a tactic in §3.3's
   forbidden list.
3. A known-answer check fails. The literal is never adjusted; the failure is
   the finding.
4. A dependency (Mathlib, Batteries, any `[[require]]`) would be needed.
5. The per-stage budget in §6 is exceeded by more than half.
6. Regenerating `generated/vendor-manifest.tsv` through the new
   implementation produces different bytes from the committed manifest. That
   is a finding about one of the two implementations, never a reason to
   rewrite the manifest.

**Report shape (mandatory).** Every command run, verbatim; every log written
to a file and the path given; the exact pass line quoted from the file, never
from the console; the timing table the stage asks for; the audit summary
line; the list of every new declaration with its statement; anything left
out, named. Exit codes are read from the file, never from a piped console
(foldlab `formal/fips202/TOOLING-NOTES.md` items 3–5).

## 1. Goals and non-goals

**Goal.** A Lean 4 library `Sha256` that a consumer imports for a SHA-256
digest over `ByteArray`, at native speed, with the refinement theorem to the
FIPS 180-4 transcription as the documentation of what the digest means. The
first consumer is `Gates/`: the vendor seal and the P1 specification census
compute every digest this repository trusts through it. Later stages add a
streaming interface and SHA-224.

**Why this lane exists.** Digests decide which bytes this repository trusts.
Two agreeing digests of the same wrong bytes were already observed at P0
(`docs/PROVENANCE.md`, "Why the blob-hash check exists"). An unproved hash
is one more place where agreement can be hollow.

**Non-goals.** Security claims of any kind; injectivity of the hash;
conformance beyond the pinned vectors; performance claims as theorems
(measurements are recorded, never proved); bit-level (non-byte-aligned)
messages at the executable layer; SHA-384, SHA-512, HMAC.

**What is preserved untouched.** `Gates/Sha256.lean` as shipped at P0, until
stage S1.4 retires it behind the API. `generated/vendor-manifest.tsv` bytes.
Every statement in §4 once R-1 freezes it.

## 2. Measured baseline (2026-09-01, Windows 11 x86-64, AMD Ryzen 7 8700F, toolchain v4.33.1)

The P0 tooling, `Gates/Sha256.lean`: `UInt32` words, `ByteArray` messages,
`Id.run do` loops with `for` and `mut`, `xs[i]!` indexing, an `Array UInt32`
message schedule built by `push`.

| Measurement | Value | Note |
| --- | --- | --- |
| `Gates.Sha256` fresh module build | 0.7 s | from the P0 build log |
| `lake exe sha256 --self-test`, seven vectors including one million `a` | 0.058 s wall | |
| 1 MiB pseudo-random file, median of 3 | 0.045 s | digest agrees with PowerShell `Get-FileHash` |
| 16 MiB pseudo-random file, median of 3 | 0.363 s | digest agrees with PowerShell `Get-FileHash` |
| `vendorseal --write` over 177 files, 1.35 MB | 2.2 s | dominated by file I/O and 177 process-level reads |

Contrast with fips202's baseline: 20.7 s per MiB, because `BitVec 64` is a
`Nat` at runtime and lanes with the top bit set are bignums. SHA-256 words
are 32 bits, so a `BitVec 32` implementation stays inside Lean's scalar
`Nat` range. The coordinator's P0 prediction that `Impl` over `BitVec 32`
would therefore run "within one order of magnitude of `Fast`" is
**REFUTED** by R0-A (`docs/research/2026-09-01-lean-stdlib-strategy-and-performance.md`,
section 4): identical rotate/xor/shift/add over 10^7 iterations measured
6572.78 ms on `BitVec 32` against 8.90 ms on `UInt32`, a factor of 738. The
gap is allocation and `%`-wrapping through `Fin`, not bignums, and it is two
orders larger than predicted. The prohibition in §3.3 stands; the three-layer
split is not optional.

The same document inverts the picture in the kernel: a 64-round `BitVec 32`
loop reduces in about 3 ms above baseline where the `UInt32` form costs
about 35 ms, and under the default `maxRecDepth` every plain `decide` and
`rfl` in its battery failed with "maximum recursion depth has been reached"
while `decide +kernel` passed. So `Impl` stays on `BitVec 32` for the
kernel's sake, every known-answer test on `Impl` uses `decide +kernel`, and
R-4's 30 s budget is expected to hold comfortably. S1.1 records the actual
numbers.

The performance question that fips202 had to solve is therefore not this
lane's problem. This lane's problem is that the P0 tooling is written in
exactly the style that cannot be reasoned about (§3.3), so the `Fast` layer
is a rewrite for proof shape, and the measurements above are the floor it
must not fall below by more than 2×.

## 3. Standing constraints

### 3.1 Estate law that binds every stage

- Toolchain `leanprover/lean4:v4.33.1` exactly. No change.
- Zero Lake dependencies (`lake-manifest.json` packages stay `[]`).
- Axiom ceiling for `Sha256/`: originally `propext` and `Quot.sound` with
  R-3 exact admissions; **relaxed by operator ruling R-11 (2026-09-02) to
  Lean's standard three axioms, `Classical.choice` included**, matching
  fips202. The lane landed choice-free anyway (0 admissions), which is
  recorded as a fact, not a requirement. `sorryAx`, `Lean.ofReduceBool`,
  `Lean.ofReduceNat`, and `Lean.trustCompiler` are forbidden.
- Every `Sha256.*` module is free of `unsafe`, `opaque`, `partial`,
  `implemented_by`, `extern`, and `IO`. The repository axiom gate scans the
  first two by token and by declaration; the others are checked by the S1.0
  audit command.
- `lake --wfail build` is the build. Warnings are errors.
- Commit minting is a gated step performed by the coordinator, never by a
  seat.
- The breaker/builder order of `AGENTS.md` applies to every stage: the
  battery is frozen red and declared in `test/fixtures/trust-gate/known-red.txt`
  before the builder starts.

### 3.2 Built-ins to use (the API sweep, pinned to the v4.33.1 sources)

Paths are under foldlab `.reference/clones/lean4-v4.33.1/src/`; line numbers
were read on 2026-09-01.

| Need | Use | Where | Why this one |
| --- | --- | --- | --- |
| Native word | `UInt32` with `^^^ &&& ||| ~~~ <<< >>> +` | `Init/Data/UInt/Basic.lean` | unboxed at runtime. The macro `declare_bitwise_uint_theorems UInt32 32` in `Init/Data/UInt/Bitwise.lean` (macro body lines 30–35, instantiated for `UInt32` at line 52) gives `UInt32.toBitVec_not/and/or/xor/shiftLeft/shiftRight` by `rfl`; `UInt32.toBitVec_add` is the `rfl` lemma at `Init/Data/UInt/Lemmas.lean:207`. `Fast = Impl` is pointwise `simp` with this set |
| Word rotate | own `rotr (x : UInt32) (n : Nat) : UInt32 := (x >>> n.toUInt32) \|\|\| (x <<< (32 - n).toUInt32)` | core has no `UInt32.rotateRight`; `BitVec.rotateRight` is `Init/Data/BitVec/Basic.lean:665` | one lemma `toBitVec_rotr (h : n < 32)` is owed. **`BitVec.rotateRight_def` (`Init/Data/BitVec/Lemmas.lean:5122`) already states `x.rotateRight r = (x >>> (r % w)) \|\|\| (x <<< (w - r % w))`, the exact shape of `rotr`**, so the lemma is `rotateRight_def` plus the shift lemmas' `% 32` bookkeeping; the bit-by-bit route through `eq_of_getLsbD_eq_iff` (Lemmas 221), `getLsbD_or` (1375), `getLsbD_shiftLeft` (1881), `getLsbD_ushiftRight` (2083) is the fallback |
| Σ0, Σ1, σ0, σ1, Ch, Maj | shared definitions over `BitVec 32` in `Spec`, instantiated at `UInt32` in `Fast` through `toBitVec` | FIPS 180-4 §4.1.2 defines them on 32-bit words | the bridge never proves a bit-level identity; it proves that `toBitVec` commutes with each operator, which is `rfl` |
| Byte↔word arithmetic | `UInt32.toUInt8`, `UInt8.toUInt32`, `UInt32.toNat_toUInt8` (`rfl`, `UInt/Lemmas.lean:218` macro), `UInt8.toUInt8_toUInt32` (`Lemmas.lean:714`), `UInt8.toUInt32_mod_256` (`Lemmas.lean:406`) | | pair with `Nat.testBit_mod_two_pow` (`Nat/Bitwise/Lemmas.lean:301`) and `BitVec.testBit_toNat` for big-endian word loading |
| Fixed-size state | `Vector UInt32 8` (state), `Vector UInt32 64` (schedule), `Vector UInt32 16` (block words) | `Init/Data/Vector/Basic.lean` | `Vector.ofFn` + `getElem_ofFn` (`Vector/OfFn.lean:27`), `Vector.ext` (`Vector/Lemmas.lean:514`), `getElem_set_self/ne` (1304/1309), `getElem_map` (1490), `getElem_replicate` (2139), `getElem_zipWith` (3008), `getElem_mapFinIdx` (`MapIdx.lean:23`) |
| Byte carrier | `ByteArray` | `Init/Data/ByteArray/Basic.lean` | reason through `bs.data` and `bs.data.toList`, NOT through `ByteArray.toList`. Lemmas at `ByteArray/Lemmas.lean`: `data_append` (62), `size_append` (98), `getElem_eq_getElem_data` (107), `getElem_append_left/right` (111/116), `size_extract` (132), `getElem_extract` (224), `ext_getElem` (306) |
| List ↔ ByteArray | `List.toByteArray`, `List.toList_data_toByteArray` (`ByteArray/Bootstrap.lean:42`), `List.toByteArray_append'` (Bootstrap 54), `List.size_toByteArray`, `List.getElem_toByteArray` | | the correspondence the `Fast = Impl` bridge is stated on |
| Total byte read | own `byteAt (bs : ByteArray) (i : Nat) : UInt8 := if h : i < bs.size then bs[i] else 0` | | no `!`, no panic path; it is exactly `List.getD _ 0` on `bs.data.toList` |
| Bounded loops in definitions | `Nat.fold n (fun i h acc => …)` | `Init/Data/Nat/Fold.lean:30`; `fold_zero` (268), `fold_succ` (271), `fold_eq_finRange_foldl` (274) | index with proof and an induction principle. Structural recursion on a block list is also fine; do not mix styles inside one stage |
| Round trip of 8 bits | `Nat.eq_of_testBit_eq` (`Nat/Bitwise/Lemmas.lean:189`), `testBit_lt_two_pow` (229), `testBit_shiftRight` (782), `testBit_mod_two_pow` (301) | | replaces any 256-case `decide` |
| Hex | own two-char table over `Fin 16` | | `Nat.toDigits 16` has no padding and no lemmas; `BitVec.toHex` uses `String.Internal` and says not to prove about it |
| UTF-8 convenience | `String.toUTF8` | | wrapper only; no theorem is stated about it |
| Kernel-side decision | `decide +kernel` | `Init/Tactics.lean:1416` | kernel reduction, no new axiom; allowed where a finite check is wanted and `rfl` is awkward |
| Axiom audit | `Lean.collectAxioms` | `Lean/Util/CollectAxioms.lean` | already what `WhatwgTest/Audit/AxiomGate.lean` calls; the S1.0 per-library audit reuses it |
| Lake metadata | `description`, `keywords`, `license`, `readmeFile`, `version`, `testDriver`, `leanOptions` | `lake/Lake/Config/PackageConfig.lean`, `LeanConfig.lean` | see §5.2 |

### 3.3 Built-ins and idioms NOT to use, with the reason

| Do not | Because |
| --- | --- |
| `bv_decide`, `native_decide`, `decide +native` | they close through `Lean.ofReduceBool`; the repository gate forbids it and additionally rejects the `_native` auxiliary axiom by name |
| `BitVec 32` in any definition `Fast` calls | boxed `Nat` arithmetic at runtime (§2) |
| `xs[i]!` in new code | forces panic-path plumbing into every lemma; index with a proof, or through `byteAt` |
| `Id.run do` with `for`/`mut` in a definition a theorem is stated about | the P0 tooling's and the prior art's style; unfoldable only through `forIn` lemmas; use `Vector.ofFn`, `Nat.fold`, or structural recursion |
| `ByteArray.toList`, `ByteArray.foldl`, `ByteArray.toUInt64LE!` | thin or no lemma support; the last one panics |
| `#print axioms` inside library modules | info lines into every consumer's build log; the S1.0 audit module emits one typed verdict |
| A `rfl`/`decide` KAT on the `Fast` layer | the kernel never runs `Fast`; KATs stay on `Impl`, `Fast` is proved equal to it |
| A digest literal typed from memory | every witness is transcribed from the pinned `.rsp` file or the pinned FIPS example file; §3.4 |
| Adding `[[require]]` | zero-dependency is a property of this artifact's trust statement |
| Lean's `module` system (`module`, `public import`, `@[expose]`) | `requiresModuleSystem` forces every downstream package to adopt module headers; ruling R-6, default not adopted |
| `Classical.choice` anywhere in `Spec`, `Impl`, `Bridge`, `Fast` | the semantic ceiling; only the R-3 string declarations may reach it |

### 3.4 Pinned sources for this lane

| Source | Pin | Role |
| --- | --- | --- |
| NIST FIPS 180-4, *Secure Hash Standard*, August 2015 | PDF SHA-256 `0455b406d89648d20cbde375561e19c245b9815e894164c2670772e3d54deb82`, 833,315 bytes (`docs/PROVENANCE.md`) | transcription source; every `Spec` definition cites its section inline |
| NIST CAVP `SHA256ShortMsg.rsp`, CAVS 11.0, generated 2011-03-15 | SHA-256 `294ecec26959357405a621121bbfb01db4d45b9e834624b2d71aedd94ffde019`, 10,031 bytes, as vendored in lean-crypto-hash `validation/vectors/nist/` at commit `54e6068a` | known-answer vectors; vendored into this repository at S1.0 under `vendor/nist-cavp-sha256/` and sealed by the manifest |
| NIST SHA-256 example values (`abc`, the two-block message) | not yet fetched; pinned at S1.7 | additional witnesses only |
| foldlab `formal/fips202` | commit `8d36195970b83a1439ec705b9a504617554b8062`; `.staging/fips202-library/SPEC.md` decision 45 | the refinement decomposition, the three-layer architecture, the stage discipline |
| kim-em/lean-crypto-hash | commit `54e6068abd4658fd91203cae1c2316188ffa0e89`, Apache-2.0, toolchain v4.33.0 | prior art, §3.5 |

Witnesses transcribed from the pinned `.rsp` on 2026-09-01 (the S1.0 seat
re-transcribes them from the vendored copy; these are the coordinator's
reading, not the frozen literals):

| Witness | Len (bits) | Msg | MD |
| --- | --- | --- | --- |
| W1 | 0 | (empty) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| W2 | 24 | `b4190e` | `dff2e73091f6c05e528896c4c831b9448653dc2ff043528f6769437bc7b975c2` |
| E1 | 440 (55 bytes; the last length whose padding fits one block) | as in the file | `6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4` |
| E2 | 448 (56 bytes; padding spills into a second block) | as in the file | `cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360` |
| E3 | 512 (64 bytes; exactly one block of message) | as in the file | `42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa` |

The seven literals in the P0 self-test (`abc`, the 56-byte two-block message,
55/56/64 copies of `a`, one million `a`) were typed from memory. They pass
against an implementation that agrees with `Get-FileHash` on real files, so
they are almost certainly right, but they have no pinned provenance and are
replaced by the table above at S1.1. They may return as additional witnesses
only after the NIST example file is pinned (S1.7).

### 3.5 Prior-art ledger

| Source | Guarantee offered | Mismatch with this lane | Class |
| --- | --- | --- | --- |
| foldlab `formal/fips202` (SHA3-512, fully proved `Impl = Spec`, dual-host, leanchecker) | the Pass A / Pass B contract shape; B2a–B2f decomposition; kernel-KAT cost data (59 s / 6 GB for two SHA3-512 digests); the `Spec`/`Impl`/`Fast` split and every rule in §3.2–§3.3 | 64-bit lanes and a sponge; tolerates `Classical.choice`; FIPS 202 B.1 is LSB-first within a byte, FIPS 180-4 §3.1 is MSB-first, so `bitsOfBytes` is **not** reusable and E3-style bit-order errors are the discriminating risk here too | process precedent |
| kim-em/lean-crypto-hash `Crypto/SHA2/*` | SHA-256/224/384/512 over `UInt32`/`UInt64` with `Vector` and proof-indexed `for h : i in` loops; `ByteVector n` with a size proof; `Context.update_append` streaming law; strict hex; CAVP vectors; conformance against OpenSSL and coreutils | its README states the theorems "are not a formal end-to-end proof of each compression function"; `validation/CryptoValidation/Proofs.lean` imports `Std.Tactic.BVDecide` (`Lean.ofReduceBool`, forbidden here); `Id.run do` bodies are outside §3.3; Lean `module` system; toolchain v4.33.0 | reference for API shape, streaming technique (credited at S1.5), and vectors; no code imported |
| fips202 S0.2 Route A, operator-supplied 2026-09-01 | a `Classical.choice`-free byte round trip: `lowBits n k := (List.range k).foldl (fun acc j => acc + if n.testBit j then 2^j else 0) 0`; `lowBits_spec` by induction on `k` with `Nat.or_two_pow_eq_add_of_lt`, `Nat.testBit_or`, `Nat.testBit_two_pow`; `lowBits_eq_mod : lowBits n k = n % 2^k` by `Nat.eq_of_testBit_eq` and `Nat.testBit_mod_two_pow`; `byte_roundtrip_fin` by `UInt8.toNat_inj` and `simpa` with `List.range 8` unfolded by `rfl` | FIPS 202 B.1 is LSB-first; SHA-256's `bitsOfByte` is MSB-first, so the fold index is `7 - j` and the `testBit` argument follows | the technique for `Spec.bytesOfBits_bitsOfBytes`; reproduced, not imported |

## 4. Statement addendum A1 (FROZEN 2026-09-01, ruling R-1)

Names are final once frozen; a seat that needs a different shape stops.
`Spec` means `Sha256.Spec`, `Impl` means `Sha256.Impl`, `Bridge` means
`Sha256.Bridge`, `Fast` means `Sha256.Fast`.

### A1.S1 — specification, reference implementation, lengths

```lean
namespace Sha256.Spec          -- bit-level FIPS 180-4 transcription; never executed by the kernel beyond probes

abbrev Word := BitVec 32
def Ch (x y z : Word) : Word            -- §4.1.2 (4.2)
def Maj (x y z : Word) : Word           -- §4.1.2 (4.3)
def Σ0 (x : Word) : Word                -- §4.1.2 (4.4)   rotr 2 ^ rotr 13 ^ rotr 22
def Σ1 (x : Word) : Word                -- §4.1.2 (4.5)   rotr 6 ^ rotr 11 ^ rotr 25
def σ0 (x : Word) : Word                -- §4.1.2 (4.6)   rotr 7 ^ rotr 18 ^ shr 3
def σ1 (x : Word) : Word                -- §4.1.2 (4.7)   rotr 17 ^ rotr 19 ^ shr 10
def K : Vector Word 64                  -- §4.2.2
def H0 : Vector Word 8                  -- §5.3.3
def pad (M : List Bool) : List Bool     -- §5.1.1: M ++ [true] ++ zeros ++ 64-bit big-endian length
def parse (P : List Bool) : List (Vector Word 16)          -- §5.2.1; total, junk on unpadded input
def schedule (block : Vector Word 16) : Vector Word 64     -- §6.2.2 step 1
def compress (H : Vector Word 8) (block : Vector Word 16) : Vector Word 8   -- §6.2.2 steps 2–4
def hash (M : List Bool) : Vector Word 8                   -- foldl compress H0 (parse (pad M))
def bitsOfWords (H : Vector Word 8) : List Bool            -- §3.1 big-endian, MSB first
def sha256 (M : List Bool) : List Bool                     -- 256 bits
def bitsOfBytes (bs : List UInt8) : List Bool              -- §3.1 MSB-first within each byte
def bytesOfBits (bits : List Bool) : List UInt8
def sha256_bytes (msg : List UInt8) : List UInt8 := bytesOfBits (sha256 (bitsOfBytes msg))

theorem length_pad (M : List Bool) : (pad M).length % 512 = 0
theorem pad_prefix (M : List Bool) : (pad M).take M.length = M
theorem length_sha256 (M : List Bool) : (sha256 M).length = 256
theorem bytesOfBits_bitsOfBytes (bs : List UInt8) : bytesOfBits (bitsOfBytes bs) = bs
theorem bitsOfBytes_bytesOfBits (bits : List Bool) (h : bits.length % 8 = 0) :
    bitsOfBytes (bytesOfBits bits) = bits

end Sha256.Spec

namespace Sha256.Impl          -- byte-level reference; kernel-reducible; the layer KATs live on

abbrev Word := BitVec 32
abbrev St := Vector Word 8
def padBytes (msg : List UInt8) : List UInt8               -- 0x80, zeros to 56 mod 64, 8-byte big-endian bit length
def wordOfBytes (b0 b1 b2 b3 : UInt8) : Word              -- big-endian
def wordsOfBlock (block : List UInt8) : Vector Word 16     -- block.getD, absent = 0
def schedule (w : Vector Word 16) : Vector Word 64         -- Vector.ofFn / Nat.fold, shared Spec.σ0/σ1
def compress (H : St) (w : Vector Word 16) : St            -- Nat.fold over 64 rounds, shared Spec.Ch/Maj/Σ0/Σ1/K
def blocks (P : List UInt8) : List (List UInt8)            -- chunks of 64
def hash (msg : List UInt8) : St                           -- foldl compress Spec.H0 (blocks (padBytes msg))
def bytesOfWord (w : Word) : List UInt8                    -- big-endian, 4 bytes
def sha256 (msg : List UInt8) : List UInt8                 -- 32 bytes

theorem length_sha256 (msg : List UInt8) : (sha256 msg).length = 32
theorem padBytes_prefix (msg : List UInt8) : (padBytes msg).take msg.length = msg
theorem length_padBytes (msg : List UInt8) : (padBytes msg).length % 64 = 0
theorem length_padBytes_pos (msg : List UInt8) : msg.length < (padBytes msg).length
theorem length_padBytes_eq (msg : List UInt8) :
    (padBytes msg).length = msg.length + 1 + (119 - (msg.length % 64)) % 64 + 8

end Sha256.Impl
```

`Impl.schedule` and `Impl.compress` use `Spec`'s `Ch`, `Maj`, `Σ0`, `Σ1`,
`σ0`, `σ1`, `K`, `H0` directly: the two layers share the word functions and
differ only in how bytes become words and how blocks are cut. That is what
makes `Bridge` a data-flow proof rather than an arithmetic one.

The two `Impl` length theorems and the padding lemmas live in
`Sha256/Lengths.lean`, not in `Impl.lean`.

Known-answer tests on `Impl`, in `Sha256/Kats.lean`, reached only from
`Sha256.Verified`: compiled `#guard` for W1, W2, E1, E2, E3; kernel
`decide +kernel` for W1 only, subject to ruling R-4 and its measured cost.

### A1.S2 — the bridge (the apex)

```lean
namespace Sha256.Bridge

theorem padBytes_bridge (msg : List UInt8) :
    Spec.bitsOfBytes (Impl.padBytes msg) = Spec.pad (Spec.bitsOfBytes msg)
theorem wordsOfBlock_bridge (block : List UInt8) (h : block.length = 64) :
    Impl.wordsOfBlock block = (Spec.parse (Spec.bitsOfBytes block)).head!   -- exact shape fixed at proof time within this meaning
theorem blocks_bridge (P : List UInt8) (h : P.length % 64 = 0) :
    (Impl.blocks P).map Impl.wordsOfBlock = Spec.parse (Spec.bitsOfBytes P)
theorem schedule_bridge (w : Vector Impl.Word 16) : Impl.schedule w = Spec.schedule w
theorem compress_bridge (H : Impl.St) (w : Vector Impl.Word 16) : Impl.compress H w = Spec.compress H w
theorem hash_bridge (msg : List UInt8) : Impl.hash msg = Spec.hash (Spec.bitsOfBytes msg)
theorem output_bridge (H : Impl.St) :
    Spec.bitsOfBytes ((List.range 8).flatMap fun i => Impl.bytesOfWord H[i]) = Spec.bitsOfWords H

/-- The apex: the byte-level reference computes the FIPS 180-4 function on byte-aligned messages. -/
theorem sha256_bridge (msg : List UInt8) : Impl.sha256 msg = Spec.sha256_bytes msg

/-- The discriminating negative: the initial hash value is load-bearing. -/
theorem sha256_ne_sha224_iv : Impl.sha256 [] ≠ Impl.hashWith sha224IV [] |>.toBytes   -- exact form fixed at S1.6 when `hashWith` exists; until then stated on `Spec.H0 ≠ sha224IV` and `compress` injectivity is NOT claimed

end Sha256.Bridge
```

`schedule_bridge` and `compress_bridge` are `rfl` or near-`rfl` if `Impl`
and `Spec` share the definitions as required; if a seat finds they are not,
the definitions have diverged and the stop condition 1 applies.

Domain-of-validity ruling, inherited from fips202 REV2: `Spec.parse` and
`Spec.hash` are total extensions, carrying FIPS 180-4 meaning only on padded
input. `bitsOfBytes_bytesOfBits` carries its `% 8` premise. `sha256_bridge`
and every KAT are stated on byte-aligned messages only. No unrestricted
bijection is claimed anywhere.

### A1.S3 — API

```lean
namespace Sha256

/-- A byte string whose length is carried by its type. -/
structure Digest (n : Nat) where
  bytes : ByteArray
  size_eq : bytes.size = n

namespace Digest
def toByteArray (d : Digest n) : ByteArray := d.bytes
def toList (d : Digest n) : List UInt8 := d.bytes.data.toList
def toHex (d : Digest n) : String
def ofHex? (n : Nat) (s : String) : Option (Digest n)
theorem ext {a b : Digest n} (h : a.bytes = b.bytes) : a = b
theorem size_toByteArray (d : Digest n) : d.toByteArray.size = n
theorem length_toList (d : Digest n) : d.toList.length = n
theorem length_toHex (d : Digest n) : d.toHex.length = 2 * n
theorem ofHex?_toHex (d : Digest n) : ofHex? n d.toHex = some d
instance : BEq (Digest n)
instance : DecidableEq (Digest n)
end Digest

namespace Hex
def encode (bs : ByteArray) : String          -- lowercase, two chars per byte, no separators
def decode? (s : String) : Option ByteArray   -- lowercase digits only; none on odd length or bad char
theorem length_encode (bs : ByteArray) : (encode bs).length = 2 * bs.size
theorem decode?_encode (bs : ByteArray) : decode? (encode bs) = some bs
theorem encode_lower (bs : ByteArray) : ∀ c ∈ (encode bs).toList, c.toLower = c
end Hex

/-- SHA-256 of a byte string. Meaning: `sha256_spec`. Trust base: the FIPS 180-4
transcription in `Sha256.Spec` and the v4.33.1 kernel. -/
def sha256 (msg : ByteArray) : Digest 32
def sha256String (s : String) : Digest 32 := sha256 s.toUTF8

theorem sha256_impl (msg : ByteArray) : (sha256 msg).toList = Impl.sha256 msg.data.toList
theorem sha256_spec (msg : ByteArray) : (sha256 msg).toList = Spec.sha256_bytes msg.data.toList
theorem sha256_ofList (l : List UInt8) : (sha256 l.toByteArray).toList = Impl.sha256 l

end Sha256
```

`Digest` and `Hex` are the same shapes as fips202 A1.S1, copied rather than
imported (zero dependencies), with the file header crediting the source.
Whether `Digest.toHex`, `Digest.ofHex?`, `Hex.encode`, and `Hex.decode?` may
reach `Classical.choice` through `String` lemmas is ruling R-3; the seat
measures it and reports the receipt before any admission is written.

**Measured 2026-09-01 (coordinator, `#print axioms` under v4.33.1):**
`String.toUTF8`, `String.ofList`, `List.toByteArray`, `ByteArray.extract`,
`ByteArray.get!`, and `Nat.toDigits` are axiom-free; `String.length`,
`String.splitOn`, `String.extract`, `String.Pos.next`, `String.Pos.get`,
`Substring.toString`, and `String.fromUTF8!` reach `Classical.choice`. So:
implement `Hex.encode` as a `List Char` producer wrapped by `String.ofList`,
implement `Hex.decode?` over `s.toList` only if `String.toList` is measured
axiom-free (else over a `List Char` input with a `String` wrapper), and state
`length_encode` on the `List Char` form, because a theorem whose statement
mentions `String.length` inherits `Classical.choice` from the statement
itself. The R-3 exact list is then expected to be empty; if a `String`-typed
convenience wrapper still reaches choice, it alone is admitted.

### A1.S4 — the native layer

```lean
namespace Sha256.Fast

abbrev Word := UInt32
abbrev St := Vector Word 8

def rotr (x : Word) (n : Nat) : Word
def Ch Maj Σ0 Σ1 σ0 σ1 : …                       -- over UInt32, mirroring Spec line for line
def K : Vector Word 64                            -- the same 64 literals as Spec.K
def H0 : Vector Word 8                            -- the same 8 literals as Spec.H0
def byteAt (bs : ByteArray) (i : Nat) : UInt8
def wordAt (bs : ByteArray) (off i : Nat) : Word  -- bytes off+4i … off+4i+3, big-endian, absent = 0
def wordsAt (bs : ByteArray) (off : Nat) : Vector Word 16
def schedule (w : Vector Word 16) : Vector Word 64
def compress (H : St) (w : Vector Word 16) : St
def padBytes (msg : ByteArray) : ByteArray
def hashAll (P : ByteArray) : St                  -- Nat.fold over P.size / 64 blocks at offset 64*i
def squeeze (H : St) : ByteArray                  -- 32 bytes, big-endian words
def sha256 (msg : ByteArray) : ByteArray

/-- Abstraction to the proved layer. -/
def abs (s : St) : Impl.St := s.map UInt32.toBitVec

theorem toBitVec_rotr (x : Word) (n : Nat) (h : n < 32) : (rotr x n).toBitVec = x.toBitVec.rotateRight n
theorem K_eq (i : Fin 64) : (K[i]).toBitVec = Spec.K[i]
theorem H0_eq : abs H0 = Spec.H0
theorem Ch_abs Maj_abs Σ0_abs Σ1_abs σ0_abs σ1_abs : …    -- toBitVec commutes, by simp with the §3.2 set
theorem schedule_abs (w : Vector Word 16) : (schedule w).map UInt32.toBitVec = Impl.schedule (w.map UInt32.toBitVec)
theorem compress_abs (H : St) (w : Vector Word 16) : abs (compress H w) = Impl.compress (abs H) (w.map UInt32.toBitVec)
theorem byteAt_eq (bs : ByteArray) (i : Nat) : byteAt bs i = bs.data.toList.getD i 0
theorem wordsAt_eq (bs : ByteArray) (off : Nat) :
    (wordsAt bs off).map UInt32.toBitVec = Impl.wordsOfBlock ((bs.data.toList.drop off).take 64)
theorem padBytes_eq (msg : ByteArray) : (padBytes msg).data.toList = Impl.padBytes msg.data.toList
theorem hashAll_abs (P : ByteArray) : abs (hashAll P) = Impl.hash' P.data.toList   -- Impl.hash' = hash on already-padded input; exact name fixed at S1.1
theorem squeeze_eq (H : St) : (squeeze H).data.toList = (List.range 8).flatMap fun i => Impl.bytesOfWord (abs H)[i]
theorem size_squeeze (H : St) : (squeeze H).size = 32

/-- The apex of the native layer. -/
theorem sha256_eq_impl (msg : ByteArray) : (sha256 msg).data.toList = Impl.sha256 msg.data.toList
theorem size_sha256 (msg : ByteArray) : (sha256 msg).size = 32

end Sha256.Fast
```

On S1.4 landing, `Sha256.sha256` (A1.S3) is redefined to call
`Fast.sha256`; the statements `sha256_impl`, `sha256_spec`, `sha256_ofList`
do not change and are re-proved through `Fast.sha256_eq_impl`.

### A1.S5 — streaming (FROZEN 2026-09-02, elaborated by the coordinator after S1.4)

```lean
namespace Sha256

/-- An incremental SHA-256 computation: the chaining state after every
complete 64-byte block absorbed so far, the pending partial block, and the
total byte count. -/
structure Context where
  state : Fast.St
  buffer : ByteArray
  absorbedBlocks : Nat                       -- number of complete blocks folded into `state`
  buffer_lt : buffer.size < 64

namespace Context
def init : Context
def update (c : Context) (chunk : ByteArray) : Context
def finalize (c : Context) : Digest 32
/-- The bytes fed so far, as a model; not stored, derived. -/
def absorbed (c : Context) : List UInt8       -- exists only through `Absorbs` below

/-- `Absorbs c bs`: `c` is the context reached from `init` by feeding exactly `bs`. -/
inductive Absorbs : Context → List UInt8 → Prop

theorem absorbs_init : Absorbs init []
theorem absorbs_update {c bs} (h : Absorbs c bs) (chunk : ByteArray) :
    Absorbs (c.update chunk) (bs ++ chunk.data.toList)
theorem update_empty (c : Context) : c.update ByteArray.empty = c
theorem update_append (c : Context) (a b : ByteArray) :
    (c.update a).update b = c.update (a ++ b)
theorem finalize_absorbs {c bs} (h : Absorbs c bs) :
    c.finalize.toList = Impl.sha256 bs
theorem finalize_init_update (m : ByteArray) :
    (init.update m).finalize = sha256 m
theorem size_buffer (c : Context) : c.buffer.size < 64
end Context

end Sha256
```

The state invariant behind these: `state = Fast.hashAll (first
`64 * absorbedBlocks` bytes of the absorbed input)` and `buffer` is the
remainder; `update` absorbs whole blocks from `buffer ++ chunk` and keeps
the tail. `update_append` is the buffered-update law; the technique is
lean-crypto-hash's `updateBuffered_append`, credited in the file header and
reproved here. `Absorbs` is stated as an inductive relation rather than a
stored list so the context carries no unbounded data. Names are final.

### A1.S6 — SHA-224 (FROZEN 2026-09-02, elaborated by the coordinator after S1.4)

```lean
namespace Sha256.Spec
def H0_224 : Vector Word 8                    -- FIPS 180-4 §5.3.2
def hashWith (iv : Vector Word 8) (M : List Bool) : Vector Word 8   -- §6.2.2 with a supplied initial value
theorem hash_eq_hashWith (M : List Bool) : hash M = hashWith H0 M
def sha224 (M : List Bool) : List Bool := (bitsOfWords (hashWith H0_224 M)).take 224   -- §6.3
def sha224_bytes (msg : List UInt8) : List UInt8 := bytesOfBits (sha224 (bitsOfBytes msg))
theorem length_sha224 (M : List Bool) : (sha224 M).length = 224
end Sha256.Spec

namespace Sha256.Impl
def hashWith (iv : St) (msg : List UInt8) : St
theorem hash_eq_hashWith (msg : List UInt8) : hash msg = hashWith Spec.H0 msg
def sha224 (msg : List UInt8) : List UInt8     -- 28 bytes: first seven words big-endian
theorem length_sha224 (msg : List UInt8) : (sha224 msg).length = 28
end Sha256.Impl

namespace Sha256.Bridge
theorem hashWith_bridge (iv : Impl.St) (msg : List UInt8) :
    Impl.hashWith iv msg = Spec.hashWith iv (Spec.bitsOfBytes msg)
theorem sha224_bridge (msg : List UInt8) : Impl.sha224 msg = Spec.sha224_bytes msg
/-- Final form of the discriminating negative: the untruncated digest under
the SHA-224 initial value differs from SHA-256 on the empty message. -/
theorem sha256_ne_hashWith_sha224IV :
    Impl.sha256 [] ≠ (List.finRange 8).flatMap (fun i => Impl.bytesOfWord (Impl.hashWith Spec.H0_224 [])[i])
end Sha256.Bridge

namespace Sha256.Fast
def hashWith (iv : St) (P : ByteArray) : St    -- over already-padded bytes, as hashAll
def sha224 (msg : ByteArray) : ByteArray
theorem sha224_eq_impl (msg : ByteArray) : (sha224 msg).data.toList = Impl.sha224 msg.data.toList
theorem size_sha224 (msg : ByteArray) : (sha224 msg).size = 28
end Sha256.Fast

namespace Sha256
inductive Algorithm | sha256 | sha224
  deriving DecidableEq, Repr
def Algorithm.outputBytes : Algorithm → Nat   -- 32, 28
def digest (alg : Algorithm) (msg : ByteArray) : Digest alg.outputBytes
def sha224 (msg : ByteArray) : Digest 28
theorem digest_sha256 (msg : ByteArray) : digest .sha256 msg = sha256 msg
theorem sha224_impl (msg : ByteArray) : (sha224 msg).toList = Impl.sha224 msg.data.toList
theorem sha224_spec (msg : ByteArray) : (sha224 msg).toList = Spec.sha224_bytes msg.data.toList
end Sha256
```

Vectors: `SHA224ShortMsg.rsp` from the same prior-art clone, extracted by
git object and sealed at S1.6 with its digest recorded in
`docs/PROVENANCE.md`; compiled `#guard`s for its `Len = 0`, `24`, and the
padding-boundary lengths on `Impl.sha224`, restated on the API; the
self-test reproduces every record of both files. Names are final.

## 5. Target layout

### 5.1 Modules

```text
Sha256.lean               -- API root: imports Spec, Impl, Lengths, Bridge, Hex, Digest, Api, Fast
Sha256/Spec.lean          -- A1.S1; frozen after S1.1 review
Sha256/Impl.lean          -- A1.S1; frozen after S1.1 review
Sha256/Lengths.lean       -- A1.S1 length and padding theorems
Sha256/Bridge.lean        -- A1.S2
Sha256/Hex.lean           -- A1.S3
Sha256/Digest.lean        -- A1.S3
Sha256/Api.lean           -- A1.S3 public functions and their theorems; ends with the compiled CAVP #guards restated on the API
Sha256/Fast.lean          -- A1.S4
Sha256/Context.lean       -- A1.S5
Sha256/Sha224.lean        -- A1.S6
Sha256/Verified.lean      -- imports Sha256, Kats, Audit; runs the audit under a #guard_msgs pin
Sha256/Kats.lean          -- Impl-level known-answer tests; reached only from Sha256.Verified
Sha256/Audit.lean         -- S1.0 axiom audit elaborator for the Sha256 namespace
bin/Sha256.lean           -- unchanged entry point; after S1.4 it calls Sha256.sha256 through Gates.Sha256.cli
```

Deviation accepted at S1.0: the executable's Lake root is `bin.Sha256` with
the default source directory, not root `Sha256` under `srcDir = "bin"`,
because Lake keys modules on the bare name and the library root `Sha256`
would otherwise share one build key and one `.olean` with the executable
root (observed as an `undefined symbol: WinMain` link failure). The file
`bin/Sha256.lean` is unchanged.

`Sha256/` is a fourth library at the semantic ceiling. The repository axiom
gate audits it with the `Whatwg` prefix rule extended to `Sha256`,
and the module-closure gate requires every `Sha256/*.lean` to be reachable
from the test root, which imports `Sha256.Verified`.

### 5.2 `lakefile.toml` additions (target)

```toml
[[lean_lib]]
name = "Sha256"

[[lean_lib]]
name = "Sha256Verified"
roots = ["Sha256.Verified"]
```

with `leanOptions = { autoImplicit = false, relaxedAutoImplicit = false,
warningAsError = true }` at package level (ruling R-6) and `testDriver =
"Sha256Verified"` until the P1 census gate becomes the package test driver.
`lake build` still builds the default targets; `lake build Sha256Verified`
builds the KATs and audit; a consumer that imports `Sha256` never pays for
them.

### 5.3 CI additions

```text
lake --wfail build Sha256Verified
lake env leanchecker --fresh Sha256.Verified
```

## 6. Stages

Each stage: purpose, edit region, work, acceptance, budget. Budgets are
wall-clock for one seat on one host, excluding waiting on rulings. Stages are
sequential except where noted; a stage may start once the previous one is
reviewed.

### S1.0 — Pass A contract, Pass B snapshot, pins, audit scaffold (no proofs)

**Landed 2026-09-02 after coordinator review.** Both pins vendored from
git objects and sealed; contract drafted with every FIPS citation verified
against the vendored PDF (tables from page images); `Sha256/Audit.lean` and
the `#guard_msgs`-pinned audit line; R-6 options package-wide with a
warning-free clean build in 13.6 s; `leanchecker --fresh Sha256.Verified`
exit 0 with evidence it ran. Measured: a full empty-message `decide +kernel`
digest costs about 2.2 s and 450 MB net, so R-4's W1 kernel KAT is
affordable; under the interpreter the `Impl` shape is 17.3x slower than the
P0 `UInt32` tooling on 1 MiB, corroborating the §2 refutation end to end
(compiled `Impl` versus compiled `Fast` remains for S1.1/S1.4). The seat's
probe reproduced the CAVP `Len = 0` digest from the §4 A1.S1 shape. One
gate interaction surfaced and was fixed by the coordinator: with R-6's
`warningAsError`, a planted `sorry` is rejected at elaboration before the
axiom gate can name `sorryAx`, so the trust self-test now accepts either
diagnostic for that plant. Package metadata and `testDriver` were added by
the coordinator at landing.

**Purpose.** The question is frozen before any code: what is transcribed,
from which bytes, with which witnesses and which negative; and the seat
tooling exists.

**Edit region.** New `test/contracts/sha256.contract.md` (Pass A: objects,
operations, observables, scope, W1/W2, E1–E3, the SHA-224 negative,
assumptions versus facts-to-prove versus deployment facts, claim-domain
table); `docs/SHA256-DAG.md` §4 promoted from PROPOSED to FROZEN on R-1;
`vendor/nist-cavp-sha256/SHA256ShortMsg.rsp` and, on R-4, the FIPS 180-4
PDF, sealed by `lake exe vendorseal --write`; `docs/PROVENANCE.md` rows;
`Sha256/Audit.lean`; `Sha256/Verified.lean` (audit only); `lakefile.toml`
§5.2; `WhatwgTest/Audit/AxiomGate.lean` prefix list; CI.

**Work.** S1.0.1 Vendor and seal the `.rsp` (and PDF); record the fetch
commands and blob-hash verification. S1.0.2 Write the Pass A contract in the
fips202 PASSA shape; every FIPS section cited is verified against the pinned
PDF's text (the liteparse workflow from foldlab; tables read from page
images, never from extracted text). S1.0.3 `Sha256/Audit.lean`: `elab
"#sha256_axiom_audit" : command` walking `env.constants` for the `Sha256`
prefix excluding `Sha256.Audit`, calling `Lean.collectAxioms`, throwing on
any axiom outside `[propext, Quot.sound]` except the R-3 exact list, and
logging exactly one line: `sha256 axiom audit: <N> declarations across <M>
modules; ceiling [propext, Quot.sound]; <k> admitted string declarations;
0 offenders`. Pinned with `#guard_msgs` in `Sha256/Verified.lean`. S1.0.4
Measure and record: kernel cost of `decide +kernel` on a 64-byte `BitVec 32`
compression probe, to size R-4.

**Acceptance.** Contract reviewed and R-1 ruled; `lake --wfail build` green
with the empty libraries; audit line pinned with `N = 0`; seal green;
citations green; the measurement table in the report.

**Budget.** 1 day.

### S1.1 — Spec, Impl, Lengths, KATs

**Purpose.** The transcription and the byte-level reference exist, the
reference passes the pinned vectors, and its shape obeys §3.3.

**Edit region.** `Sha256/Spec.lean`, `Sha256/Impl.lean`, `Sha256/Lengths.lean`,
`Sha256/Kats.lean`, `Sha256/Verified.lean` imports, `Sha256.lean`.

**Work.** Implement A1.S1 exactly. `Spec` definitions carry their FIPS 180-4
section in a docstring. `Impl` shares `Spec`'s word functions and constants.
No `!`, no `Id.run do`. Compiled `#guard`s for W1, W2, E1, E2, E3 with
literals copied from the vendored `.rsp` by the seat, never retyped from
this document. Kernel KAT for W1 by `decide +kernel` if S1.0.4's measurement
allows (R-4), else recorded as a finding. Length theorems by `omega` over
`List.length` lemmas; `length_padBytes_eq` pins the zero-count formula the
P0 tooling uses, so the eventual `Fast.padBytes_eq` is a data-flow proof.

**Acceptance.** Build, seal, citations, trust self-test green; the audit line
updated; a timing table for `Sha256.Impl`, `Sha256.Kats`, and the
`decide +kernel` KAT if attempted; `Impl.sha256` run through a probe on the 1
MiB file from §2 with its wall time (the §2 prediction is confirmed or
refuted here).

**Budget.** 1.5 days.

### S1.2 — Bridge

**Purpose.** `Impl.sha256 = Spec.sha256_bytes` on byte-aligned messages.

**Edit region.** `Sha256/Bridge.lean` only; `Sha256/Lengths.lean` to remove
`private` from helpers a bridge proof needs.

**Work.** Proof order: `bytesOfBits_bitsOfBytes` and its converse through
`Nat.eq_of_testBit_eq` (never a 256-case `decide`); `padBytes_bridge` from
`length_padBytes_eq` and the big-endian length encoding; `wordsOfBlock_bridge`
by unfolding both four-term big-endian folds; `blocks_bridge` by induction on
the block count; `schedule_bridge` and `compress_bridge` by `rfl` or `simp`
if the definitions are shared as required, else stop; `hash_bridge` by list
induction; `output_bridge`; `sha256_bridge` composes. The negative is stated
in its S1.2 form on `Spec.H0 ≠ sha224IV` by `decide`.

**Acceptance.** Every A1.S2 theorem elaborated with a receipt inside the
ceiling; `leanchecker --fresh Sha256.Verified` exit 0 with empty output and
evidence it ran; dual-host build (Windows here, macOS at the foldlab
coordinator) with axiom reports parsed as `(declaration, axiom-set)` pairs.

**Budget.** 4 days. This is the stage that fips202 found hardest; the budget
is the largest for that reason.

### S1.3 — API

**Purpose.** A consumer imports `Sha256` and gets `ByteArray → Digest 32`
whose docstring names the theorem that gives it meaning, plus hex and length
facts.

**Edit region.** `Sha256/Hex.lean`, `Sha256/Digest.lean`, `Sha256/Api.lean`,
`Sha256.lean`; `Gates/Sha256.lean` untouched.

**Work.** Implement A1.S3 over `Impl`. `sha256 msg := ⟨(Impl.sha256
msg.data.toList).toByteArray, by rw [List.size_toByteArray,
Impl.length_sha256]⟩`. `Sha256/Api.lean` ends with the five CAVP `#guard`s
restated on the API. Measure whether any string declaration reaches
`Classical.choice`; if so, report the exact receipts for R-3 before writing
any admission.

**Acceptance.** Build and gates green; `#check` of every A1.S3 name in the
report; R-3 evidence attached.

**Budget.** 1 day.

### S1.4 — Fast, and the cutover of Gates

**Purpose.** Native throughput with no change to what is proved, and every
digest in the repository computed through the proved library.

**Edit region.** `Sha256/Fast.lean`; `Sha256/Api.lean` (retarget); `Gates/Sha256.lean`
(becomes a thin wrapper over `Sha256.sha256` and `Sha256.Hex.encode`);
`Gates/VendorSeal.lean` (calls the API); `Gates/AGENTS.md`.

**Work.** Implement A1.S4. Definitions mirror `Impl` line for line with
`UInt32` for `BitVec 32`, `rotr` for `rotateRight`, `byteAt` for `getD`,
`Nat.fold` and `Vector.ofFn` for every loop. Proof order: `toBitVec_rotr` via
`BitVec.rotateRight_def`; the table lemmas by `decide` over 64 and 8 literals;
the six word-function lemmas by `simp` with the `UInt32.toBitVec_*` set;
`schedule_abs` and `compress_abs` by `Vector.ext` + `getElem_ofFn` +
`Nat.fold` induction; `byteAt_eq`, `wordsAt_eq`, `padBytes_eq` through
`bs.data.toList` and `List.getD` on `take`/`drop`; `hashAll_abs` by induction
on the block count with `Nat.fold_succ`; `squeeze_eq` by `ByteArray.ext_getElem`;
`sha256_eq_impl` composes. Then the cutover: `lake exe vendorseal --write`
into a clean tree must reproduce `generated/vendor-manifest.tsv`
byte-identically (stop condition 6), and `lake exe sha256` on the §2 files
must reproduce the recorded digests.

**Acceptance.** Build and all five gates green; `Sha256.Fast` fresh build ≤
30 s; throughput protocol: the §2 1 MiB and 16 MiB files, three runs each,
medians reported; target: within 2× of §2 (1 MiB ≤ 0.09 s, 16 MiB ≤ 0.73 s);
manifest reproduced byte-identically; the P0 self-test's memory-typed
literals deleted.

**Budget.** 3 days.

### S1.5 — Streaming (after S1.4)

`Sha256.Context` per A1.S5 with the buffered-update law. Budget 2 days.

### S1.6 — SHA-224 (after S1.4; may run beside S1.5)

Per A1.S6, with `SHA224ShortMsg.rsp` pinned first. Budget 2 days.

### S1.7 — Assurance record

Run lean4lean against `Sha256.Verified` and record it in `docs/PROVENANCE.md`;
dual-host axiom parse (Windows and macOS) as `(declaration, axiom-set)`
pairs, never raw lines; fetch and pin the NIST example-values file and add
`abc` and the two-block message as compiled guards; close the edge ledger.
Budget 1 day.

## 7. Verification commands (from the repository root)

```text
lake --wfail build                        2>&1 | Tee-Object -FilePath <log-root>.txt
lake --wfail build Sha256Verified         2>&1 | Tee-Object -FilePath <log-verified>.txt
lake env leanchecker --fresh Sha256.Verified 2>&1 | Tee-Object -FilePath <log-checker>.txt ; $LASTEXITCODE
lake exe sha256 --self-test
lake exe vendorseal
lake exe citations
lake exe trustselftest
```

The exit code of every command is captured to its log file on its own line
by the seat's script; a report that quotes a console tail is returned to the
seat.

## 8. Consumer migration (Gates), part of S1.4

- `Gates/Sha256.lean`: `hexDigest bs := (Sha256.sha256 bs).toHex`;
  `hexDigestOfFile` unchanged in signature; the seven-vector self-test is
  replaced by the API `#guard`s plus a runtime re-check of W1, W2, E1–E3
  read from the vendored `.rsp` at run time (so the self-test can never drift
  from the pin).
- `Gates/VendorSeal.lean`: `Row.digest` computed through the API; no other
  change; the regenerated manifest must be byte-identical.
- The P1 census generator, when it lands, computes span digests through the
  API from the start.

## 9. Rulings (R-1 approved 2026-09-01; R-2–R-9 ratified at their defaults the same day)

| Id | Question | Ruling (was: default if silent) |
| --- | --- | --- |
| R-1 | Approve §4 A1.S1–A1.S4 as the frozen statement addendum and open S1.0 | approve |
| R-2 | Route B (`decide +kernel`) acceptable as a landing for a bridge lemma if the structural route exceeds its budget | acceptable as a finding, not a completion |
| R-3 | `Classical.choice` admission for `Digest.toHex`, `Digest.ofHex?`, `Hex.encode`, `Hex.decode?` if and only if their receipts reach it | admit by exact declaration on the trust edge; never a module-wide exemption; none if the receipts are clean |
| R-4 | Kernel KAT policy for `Impl`: W1 only, budget 30 s and the memory figure recorded | W1 only if within budget; otherwise compiled guards only, as fips202 R-8 |
| R-5 | Hex decoding: lowercase-only or case-insensitive | lowercase-only (fips202 R-5; the manifest and every pin already use lowercase) |
| R-6 | Adopt `leanOptions = { autoImplicit = false, relaxedAutoImplicit = false, warningAsError = true }` for the whole package, not only `Sha256` | adopt package-wide at S1.0, as a separate commit, after confirming `Gates/` and `WhatwgTest/Streams/` build warning-free |
| R-7 | Repository license. **This repository currently has no `LICENSE` file.** | Apache-2.0, matching fips202 R-7 and the prior art, at S1.0 |
| R-8 | Vendor the FIPS 180-4 PDF (US Government work) beside the `.rsp`, or keep digest-only | vendor it at S1.0, sealed |
| R-9 | Toolchain policy for consumers | exact pin, stated in `README.md` |
| R-10 | **One-shot mode (operator, 2026-09-01: "jump the gun and one shot this thing").** S1.1–S1.4 are built by one seat in one pass against the frozen §4 statements, without a separate breaker freezing a red battery first; S1.5 and S1.6 are stretch in the same pass. The coordinator's first-hand review of the delivery is the check the breaker would have supplied. Any statement the seat cannot close is left out of the green build and parked in a module declared in `known-red.txt`, never closed with `sorry`. | ruled; applies to lane S1 only and sets no precedent for the streams calculi |

## 10. Edge ledger

| Edge | State | Evidence or remaining work |
| --- | --- | --- |
| identity | `required-closed` | FIPS 180-4 PDF and CAVP `.rsp` vendored from git objects and sealed at S1.0 (`docs/PROVENANCE.md`) |
| construction | `required-closed` | A1.S1–A1.S4 landed under their frozen names; the seven deviations are recorded in the S1 landing note below and none changes a meaning |
| semantics | `required-closed` | `Bridge.sha256_bridge` and `Fast.sha256_eq_impl`, both `[propext, Quot.sound]`; the API theorems `sha256_impl`, `sha256_spec`, `sha256_ofList` compose them |
| laws | `required-closed` | the A1.S2 decomposition (`padBytes_bridge`, `blocks_bridge`, `schedule_bridge`, `compress_bridge`, `hash_bridge`, `output_bridge`) and the A1.S4 pointwise lemmas, all landed |
| representation | `required-closed` | `Vector`/`Nat.fold`/`byteAt` throughout; the P0 `Id.run do` tooling deleted; `Gates/Sha256.lean` is a wrapper over `Sha256.sha256` |
| counterexamples | `required-closed` | `WS-SHA-CE-001`..`004` closed with `decide +kernel` witnesses in `WhatwgTest/Streams/Counterexamples/Sha/Mutants.lean`; the contract's claim that W1 detects a missing length field is refuted by `ce002_padBytes_eq_on_empty` and corrected |
| bridges | `not-applicable` | no host target |
| targets | `not-applicable` | no generated code |
| trust | `required-open` | audit line pinned (`422 declarations across 12 modules; 0 admitted string declarations; 0 offenders` after S1.5/S1.6); `leanchecker --fresh` exit 0 on Windows x86-64 (this host) and on Ubuntu x86-64 (CI); **open:** the macOS arm64 leg, and lean4lean, which S1.7 stopped at its toolchain gate: no commit on any lean4lean ref targets v4.33.1 (nearest `v4.33.0-rc2` at `5518bf83`, 2026-08-04); no mismatched checker was run |
| coverage | `required-closed` | every FIPS 180-4 section cited was verified against the pinned PDF in the Pass A contract; all 65 CAVP records reproduced by the runtime self-test |

### S1.5–S1.6 landing note (2026-09-02, merge `a1383bc`)

Streaming (`Sha256/Context.lean`) and SHA-224 (`Sha256/Sha224.lean`) landed
fully proved; the audit line moved to 422 declarations, 0 offenders, R-3
list still empty. Accepted deviations: `Context.absorbed` is not a function
(a context cannot recover its input; the `Absorbs` relation carries the
notion as the frozen prose directed); `Absorbs` constructors are `.empty`
and `.feed` with `absorbs_init`/`absorbs_update` as theorems; `Impl.sha224`
is `take 28` of all eight words' bytes, equal by `rfl` to the seven-word
form (`WS-SHA-CE-005` attacks the byte range); `hashWith_bridge` sits beside
`hash_bridge` because the layout puts A1.S6 above `Bridge.lean`;
`Bridge.sha224IV` and `Spec.H0_224` coexist pinned equal by
`sha224IV_eq`; helper declarations beyond the frozen lists are listed in the
seat's report. Throughput unregressed: 0.0598 s per MiB, 0.6888 s per 16 MiB.

### S1 landing note (2026-09-02)

Deviations from the frozen text, each recorded by the builder and accepted
at review because none changes a meaning: `Σ0`/`Σ1` are spelled `«Σ0»`/`«Σ1»`
because U+03A3 is not letter-like to Lean; `output_bridge` and `squeeze_eq`
index with `List.finRange 8` and `i : Fin 8` because `List.range 8` gives no
bound in scope; the `String`-typed hex theorems are stated on the `List
Char` form (`length_encodeChars`, `decodeChars?_encodeChars`,
`encodeChars_lower`, `length_toHexChars`, `ofHexChars?_toHexChars`) because
`String.length` and `String.toList` reach `Classical.choice` from the
statement itself; `Sha256/Vec.lean` re-proves `Vector.ofFn` access because
`Vector.getElem_ofFn`, `Array.toList_ofFn`, `List.drop_take`, and
`Nat.mod_mul_right_div_self` reach `Classical.choice` in v4.33.1 core;
`Spec.schedule`/`compress` are factored into named steps so `Fast`'s
`Nat.fold` transport matches syntactically. The cost stated plainly: no
theorem relates `Hex.decode? (Hex.encode bs)` to `bs` at the `String` layer;
`decodeChars?_encodeChars` carries the round trip one layer down.
Throughput: 0.058 s per MiB and 0.680 s per 16 MiB, within the 2x targets,
the 1.87x on 16 MiB coming from a fresh 8-word `Vector` per round.

## 11. Trust statement until closure

`lake exe sha256 --self-test` is finite evidence against seven vectors whose
literals were typed from memory, on an implementation that agrees with
PowerShell's `Get-FileHash` on every file checked. Every pinned digest is
cross-checked that way and, for vendored trees, against upstream git blob
hashes. None of this is a theorem, and no document in this repository may
describe the in-tree SHA-256 as verified while this ledger has an open edge.
