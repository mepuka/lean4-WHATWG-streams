# Plan: strictness parity for the shared hash library (step 9)

Status: **PLAN, 2026-09-02.** Nothing here has been executed. This document
plans step 9 of `docs/HASH-PACKAGE-PLAN.md`: bringing the SHA3-512 family to
the same axiom ceiling as the SHA-256 family, unifying the two `Digest n` and
`Hex` copies into one, and restating every `String`-typed theorem on the
`List Char` form.

Owner: the coordinator. Executing seats: one breaker, one builder, per §8.

Every number below was produced by a command run for this document. The
commands and their logs are named at each number. Claims are labelled
**MEASURED** (a command was run here), **READ** (a file was read), or
**INFERRED** (a conclusion drawn from the two).

## 0. Pins

| Thing | Pin | How checked |
| --- | --- | --- |
| foldlab | `64be4b2c8182f92997bffb3d47f7598d6a558ed4`, working tree clean | MEASURED, `git -C C:\Users\kokok\Dev\foldlab log -1` and `git status --porcelain -- formal/fips202` (empty) |
| this repository | `698d91ec288c40871c485949e6bdb3169eaba024`, working tree clean | MEASURED, same commands |
| `Sha256/` at `a1383bc` vs at `698d91ec` | identical | MEASURED, `git diff --stat a1383bc..HEAD -- Sha256 Sha256.lean` printed nothing |
| Toolchain | `leanprover/lean4:v4.33.1` in both packages | READ, `formal/fips202/lean-toolchain`, `lean-toolchain` |
| Core sources | `C:\Users\kokok\Dev\foldlab\.reference\clones\lean4-v4.33.1\src` | READ |

Probe copies (read-only work on throwaway trees; `lake` was never run in this
repository or in foldlab):

```text
<probe> = C:\Users\kokok\AppData\Local\Temp\claude\C--Users-kokok-Dev-foldlab\
          a218249a-b983-4635-ae4f-dea3a573ad60\scratchpad\parity-probe
<logs>  = ...\scratchpad\parity-logs
```

`<probe>\fips202` is a copy of `formal/fips202`. `<probe>\sha256pkg` is
`Sha256/` plus `Sha256.lean` under a minimal `lakefile.toml` carrying the same
`leanOptions`; the SHA-256 tree imports only `Sha256.*` and `Lean`, so it
builds standalone (MEASURED: `lake build`, exit 0, `<logs>\sha256-build.log`).

## 1. The two baselines

**MEASURED.** A `Lean.collectAxioms` sweep over every declaration whose owning
module lies under the tree prefix, skipping `Name.isInternal` names.

Command (in each probe copy): `lake env lean .\Probe.lean`.
Logs: `<logs>\sha3-probe.log`, `<logs>\sha256-probe.log`.
Data: `<logs>\sha3-offenders.tsv`, `<logs>\sha256-offenders.tsv`.

| Family | Public declarations | Modules | Reaching `Classical.choice` |
| --- | --- | --- | --- |
| `Sha256.*` | 422 | 12 | **0** |
| `Sha3.*` | 213 | 14 | **33** |

The `Sha3` figure includes `Sha3.BridgeEvidence`; the first sweep omitted that
module and reported 212 / 13 / 32 (`<logs>\sha3-probe.log`). The final count is
from `lake env lean .\Probe5.lean`, `<logs>\sha3-candidates.log`:
`public 213, all 583, modules 14, choice-offenders 33`.

Two counting conventions exist and they differ. `Sha3/Audit.lean` maps private
names back to user names before filtering, so its pinned line reads
`571 declarations across 14 modules` (READ, `formal/fips202/Sha3/Verified.lean`
line 7). This document counts only names that survive `Name.isInternal`, the
convention `Sha256/Audit.lean` uses (READ, `Sha256/Audit.lean:97`). The debt
list is unaffected: private offenders are a further 12, all inside the same
cones (MEASURED, `<logs>\sha3-offenders.tsv`, `# INTERNAL` section).

Per module (MEASURED, `lake env lean .\Probe9.lean`,
`<logs>\sha3-per-module.log`):

| Module | Public | Reaching `Classical.choice` |
| --- | --- | --- |
| `Sha3.Bridge` | 21 | 11 |
| `Sha3.Fast` | 51 | 8 |
| `Sha3.Hex` | 7 | 5 |
| `Sha3.Digest` | 30 | 4 |
| `Sha3.Api` | 5 | 3 |
| `Sha3.Impl` | 20 | 1 |
| `Sha3.BridgeEvidence` | 1 | 1 |
| `Sha3.Spec` | 32 | 0 |
| `Sha3.KeccakProbe` | 12 | 0 |
| `Sha3.Roundtrips` | 11 | 0 |
| `Sha3.Structural` | 10 | 0 |
| `Sha3.Lengths` | 7 | 0 |
| `Sha3.Kats` | 4 | 0 |
| `Sha3.Theorems` | 2 | 0 |

Seven of fourteen modules are already at the SHA-256 ceiling, including the
whole of `Spec` and both known-answer modules. `Sha3.Roundtrips` is clean
because it already carries the choice-free `lowBits` technique the SHA-256 lane
later reproduced (READ, `formal/fips202/Sha3/Roundtrips.lean:19-91`;
`docs/SHA256-DAG.md` §3.5 credits it).

## 2. The first reason for each debt item

**MEASURED.** For every offending declaration, a walk down the dependency graph
that always steps to a dependency which also reaches `Classical.choice`, until
it leaves the `Sha3` tree. The constant it leaves on is the first reason.

Command: `lake env lean .\Probe4.lean`.
Log: `<logs>\sha3-attribution-final.log`. Data: `<logs>\sha3-attribution.tsv`.
Result line: `attributed 33 public offenders to 5 distinct first reasons`.

| First reason | Core module | Offenders |
| --- | --- | --- |
| `Vector.getElem_ofFn` | `Init.Data.Vector.OfFn` | 14 |
| `String.toList` | `Init.Data.String.Basic` | 8 |
| `Nat.and_two_pow_sub_one_eq_mod` | `Init.Data.Nat.Bitwise.Lemmas` | 5 |
| `Nat.testBit_two_pow_sub_one` | `Init.Data.Nat.Bitwise.Lemmas` | 4 |
| `String.length` | `Init.Data.String.Length` | 2 |

Receipts for the five, and for the alternatives, MEASURED by `#print axioms`
(`lake env lean .\Probe3.lean` and `.\Probe5.lean`; logs `<logs>\sha3-why.log`,
`<logs>\sha3-candidates.log`):

| Constant | Receipt |
| --- | --- |
| `String.length` | `[propext, Classical.choice, Quot.sound]` |
| `String.toList` | `[propext, Classical.choice, Quot.sound]` |
| `String.length_ofList` | `[propext, Classical.choice, Quot.sound]` |
| `String.toList_ofList` | `[propext, Classical.choice, Quot.sound]` |
| `String.ofList` | no axioms |
| `String.toUTF8` | no axioms |
| `Char.ofNat` | no axioms |
| `Vector.getElem_ofFn` | `[propext, Classical.choice, Quot.sound]` |
| `Vector.toList_ofFn` | `[propext, Classical.choice, Quot.sound]` |
| `Array.toList_ofFn` | `[propext, Classical.choice, Quot.sound]` |
| `List.getElem_ofFn` | `[propext]` |
| `List.length_ofFn` | `[propext]` |
| `Nat.testBit_two_pow_sub_one` | `[propext, Classical.choice, Quot.sound]` |
| `Nat.testBit_two_pow_sub_succ` | `[propext, Classical.choice, Quot.sound]` |
| `Nat.and_two_pow_sub_one_eq_mod` | `[propext, Classical.choice, Quot.sound]` |
| `Nat.testBit_mod_two_pow` | `[propext, Quot.sound]` |
| `Nat.testBit_and` | `[propext, Quot.sound]` |
| `Nat.eq_of_testBit_eq` | `[propext, Quot.sound]` |
| `Nat.testBit_succ` | `[propext, Quot.sound]` |
| `Vector.getElem_mapFinIdx` | `[propext, Quot.sound]` |
| `Vector.getElem_replicate` | `[propext, Quot.sound]` |
| `Vector.replicate` | `[propext]` |
| `ByteArray.toList` | `[propext]` |
| `List.toList_data_toByteArray` | `[propext]` |

Two of these correct the standing lists. `docs/SHA256-DAG.md` §3.3 tells this
lane not to use `ByteArray.toList` for thin lemma support; that is still good
advice, but it is **not** an axiom offender (MEASURED, `[propext]`). And the
S1 landing note names `List.drop_take`, `Array.toList_ofFn`,
`Vector.getElem_ofFn` and `Nat.mod_mul_right_div_self` as the SHA-256 lane's
four dirty core lemmas; only `Vector.getElem_ofFn` also appears in the SHA3
debt. The two `Nat.Bitwise` roots are new and were not on any list.

Chains, for the record (MEASURED, `<logs>\sha3-why2.log`):

```text
Sha3.Bridge.theta_bridge → Vector.getElem_ofFn → Array.getElem_ofFn
  → Array.getElem_ofFn_go → Classical.byContradiction → Classical.propDecidable
  → Classical.choice

Sha3.Fast.squeeze_eq → Fast.squeeze_byte → Nat.and_two_pow_sub_one_eq_mod
  → Nat.testBit_two_pow_sub_one → Nat.testBit_two_pow_sub_succ
  → (its _proof_1_3) → Classical.propDecidable → Classical.choice

Sha3.Impl.toHex → String.toList → String.Internal.toArray
  → ByteArray.utf8Decode? → … → ByteArray.utf8DecodeChar?.assemble₁._proof_3
```

### The full debt list

**MEASURED**, `<logs>\sha3-attribution.tsv`. Every receipt is
`[propext, Classical.choice, Quot.sound]`; only the first reason varies.

| # | Declaration | First reason | Repair |
| --- | --- | --- | --- |
| 1 | `Sha3.Bridge.absorbBlock_bridge` | `Vector.getElem_ofFn` | R1 |
| 2 | `Sha3.Bridge.absorbBlocks_bridge` | `Vector.getElem_ofFn` | R1 |
| 3 | `Sha3.Bridge.chi_bridge` | `Vector.getElem_ofFn` | R1 |
| 4 | `Sha3.Bridge.keccakF_bridge` | `Vector.getElem_ofFn` | R1 |
| 5 | `Sha3.Bridge.rhoPi_bridge` | `Vector.getElem_ofFn` | R1 |
| 6 | `Sha3.Bridge.rnd_bridge` | `Vector.getElem_ofFn` | R1 |
| 7 | `Sha3.Bridge.theta_bridge` | `Vector.getElem_ofFn` | R1 |
| 8 | `Sha3.Bridge.xor_abs_bridge` | `Vector.getElem_ofFn` | R1 |
| 9 | `Sha3.Fast.absorbAll_abs` | `Vector.getElem_ofFn` | R1 |
| 10 | `Sha3.Fast.chi_abs` | `Vector.getElem_ofFn` | R1 |
| 11 | `Sha3.Fast.keccakF_abs` | `Vector.getElem_ofFn` | R1 |
| 12 | `Sha3.Fast.rhoPi_abs` | `Vector.getElem_ofFn` | R1 |
| 13 | `Sha3.Fast.rnd_abs` | `Vector.getElem_ofFn` | R1 |
| 14 | `Sha3.Fast.theta_abs` | `Vector.getElem_ofFn` | R1 |
| 15 | `Sha3.Bridge.keccak512_prefips_bridge` | `Nat.testBit_two_pow_sub_one` | R2 |
| 16 | `Sha3.Bridge.sha3_512_bridge` | `Nat.testBit_two_pow_sub_one` | R2 |
| 17 | `Sha3.Bridge.squeeze_bridge` | `Nat.testBit_two_pow_sub_one` | R2 |
| 18 | `Sha3.Bridge.sha3_ne_prefips_spec` (in `BridgeEvidence`) | `Nat.testBit_two_pow_sub_one` | R2 |
| 19 | `Sha3.Fast.sha3_512_eq_impl` | `Nat.and_two_pow_sub_one_eq_mod` | R2 |
| 20 | `Sha3.Fast.squeeze_eq` | `Nat.and_two_pow_sub_one_eq_mod` | R2 |
| 21 | `Sha3.sha3_512_impl` | `Nat.and_two_pow_sub_one_eq_mod` | R2 |
| 22 | `Sha3.sha3_512_ofList` | `Nat.and_two_pow_sub_one_eq_mod` | R2 |
| 23 | `Sha3.sha3_512_spec` | `Nat.and_two_pow_sub_one_eq_mod` | R2 |
| 24 | `Sha3.Impl.toHex` | `String.toList` | R3 |
| 25 | `Sha3.Hex.decode?` | `String.toList` | R4 |
| 26 | `Sha3.Hex.decode?.eq_1` | `String.toList` | R4 |
| 27 | `Sha3.Digest.ofHex?` | `String.toList` | R4 |
| 28 | `Sha3.Digest.ofHex?.eq_1` | `String.toList` | R4 |
| 29 | `Sha3.Hex.length_encode` | `String.length` | R5 |
| 30 | `Sha3.Hex.decode?_encode` | `String.toList` | R5 |
| 31 | `Sha3.Hex.encode_lower` | `String.toList` | R5 |
| 32 | `Sha3.Digest.length_toHex` | `String.length` | R5 |
| 33 | `Sha3.Digest.ofHex?_toHex` | `String.toList` | R5 |

Items 21–23 are the three public API theorems. They are downstream of item 19
and close for free when it closes: `sha3_512_impl` *is*
`Fast.sha3_512_eq_impl` (READ, `formal/fips202/Sha3/Api.lean:18-20`), and the
other two rewrite through it.

## 3. The repairs

### R1 — `Vector.ofFn` (14 items, the largest cone)

The problem. Core's `Vector.ofFn` is the only shape `docs/SHA256-DAG.md` §3.2
and foldlab's `SPEC.md` §3.2 both prescribe for a bounded loop in a definition,
and every route from it to its elements leaves the ceiling.

**The definitions must change.** Re-proving core's lemma locally, which would
leave every definition untouched, was tried and is blocked: the auxiliary
`Array.ofFn.go` is not nameable outside its own core module under v4.33.1
(MEASURED, `lake env lean .\Probe6.lean`, `<logs>\vec-feasibility.log`:
`error(lean.unknownIdentifier): Unknown constant 'Array.ofFn.go'`, and the
elaborated goal shows it as `Array.ofFn.go✝`). There is no clean core lemma
relating `Array.ofFn` to `List.ofFn` either: `Array.toList_ofFn` and
`Vector.toList_ofFn` both reach `Classical.choice` (MEASURED, §2). So the
`ofFn` used in `Sha3.Impl`, `Sha3.Fast` and `Sha3.KeccakProbe` has to become a
local one. **INFERRED** from those two measurements.

Two local `ofFn`s were built and measured (`lake env lean .\Probe7.lean`,
`<logs>\vec-alt.log`):

| Candidate | Definition | Receipt of the access lemma |
| --- | --- | --- |
| List-backed (`Sha256/Vec.lean`'s route) | `⟨⟨List.ofFn f⟩, List.length_ofFn⟩` | `[propext]` |
| Array-backed | `(Vector.replicate n default).mapFinIdx (fun i _ h => f ⟨i, h⟩)` | `[propext, Quot.sound]` |

Both are inside the ceiling. The Array-backed one needs `[Inhabited α]` and its
lemma is one `simp only [ofFnR, Vector.getElem_mapFinIdx]`.

Recommendation: **the List-backed route, exactly as `Sha256/Vec.lean`**, for a
single shared `Hash.Vec.ofFn`; the Array-backed one is the fallback if the
runtime check below fails. The reason to prefer it is that it is already
landed, reviewed and dual-host green in the SHA-256 family, which uses it in
`Spec`, `Impl` *and* the hot `Fast` layer (READ, `Sha256/Fast.lean:149,203,272`;
`Sha256/Impl.lean:62`; `Sha256/Spec.lean:323,347,385`), at a measured 0.058 s
per MiB (READ, `docs/SHA256-DAG.md` S1 landing note).

The reason it is nonetheless a risk here, stated plainly: SHA3-512's hot loop
is 24 rounds over a 25-lane state, and each round would allocate a 25-element
`List` before the `Array`. The published fips202 throughput is 0.635 s per MiB
(READ, `docs/HASH-PACKAGE-PLAN.md` §1 header) and 0.823 s per MiB on this host
(READ, same document, step 0 row) — an order of magnitude slower than SHA-256
already. **INFERRED:** this is where a regression would show, and no
measurement can be made before the edit exists.

Edit sites, all `Vector.ofFn` occurrences (READ, ripgrep over
`formal/fips202/Sha3/*.lean`):

| File | Lines |
| --- | --- |
| `Sha3/Impl.lean` | 44, 47, 55, 77 |
| `Sha3/Fast.lean` | 46, 49, 60, 177 |
| `Sha3/KeccakProbe.lean` | 38, 41, 49 |
| `Sha3/Bridge.lean` | 405, 414 (inside statements of two bridge lemmas) |

`Sha3/KeccakProbe.lean` has no offenders today, but its definitions mirror
`Impl`'s and must move with them or the probe stops mirroring what it probes.

Then every `rw`/`simp only [Vector.getElem_ofFn]` becomes the local lemma:
`Sha3/Bridge.lean` lines 39, 59, 87, 409, 419, 434 and `Sha3/Fast.lean` lines
112, 122, 131, 256 (READ).

Statement effect: **none of the public API, and two lemmas.**
`Bridge.xor_abs_bridge` (public, `Sha3/Bridge.lean:404-405`) and
`Bridge.loadBlock_bridge` (private, `Sha3/Bridge.lean:413-414`) name
`Vector.ofFn` in their statements, so those two change spelling — the symbol,
not the meaning. Every other statement is byte-identical. This is a
definition-body change, which `docs/HASH-PACKAGE-PLAN.md` §4 forbids *during
the move*; step 9 is the step that is allowed to make it, and ruling P-3 below
asks for that to be said out loud.

### R2 — the two `Nat.Bitwise` roots (9 items, the best leverage)

Both roots enter through exactly one line each (READ):

- `Sha3/Bridge.lean:467`: `rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]`
- `Sha3/Fast.lean:288`: `simp only [show 0xFF = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]`

Core's `Nat.testBit_two_pow_sub_one` goes through
`Nat.testBit_two_pow_sub_succ`, whose generated proof term reaches
`Classical.propDecidable` (READ, core `Init/Data/Nat/Bitwise/Lemmas.lean:334-357`;
MEASURED chain in §2). Core's `Nat.and_two_pow_sub_one_eq_mod` is a four-line
`eq_of_testBit_eq` proof whose only dirty ingredient is that simp lemma (READ,
same file, lines 537-541).

**Both were re-proved choice-free, and the proofs are already written**
(MEASURED, `lake env lean .\Probe8.lean`, `<logs>\nat-feasibility.log`, exit 0):

```text
Probe.testBit_two_pow_sub_one'  [propext, Quot.sound]
Probe.and_two_pow_sub_one_eq_mod'  [propext, Quot.sound]
```

The technique. `testBit_two_pow_sub_one'` is induction on `n`, with
`2 ^ (n+1) - 1 = 2 * (2 ^ n - 1) + 1` by `omega` over `Nat.two_pow_pos`, then
`Nat.testBit_succ` (`[propext, Quot.sound]`) to step the index down.
`and_two_pow_sub_one_eq_mod'` is core's own proof with the local lemma
substituted: `Nat.eq_of_testBit_eq`, then `Nat.testBit_and` and
`Nat.testBit_mod_two_pow`, all three clean. Source:
`<probe>\fips202\Probe8.lean`, 22 lines including both statements.

Home: a new `Sha3/Nat.lean` (shared package: `Hash/Nat.lean`), imported by
`Bridge` and `Fast`. No statement anywhere changes. **This is the cheapest nine
receipts in the plan.**

### R3 — `Sha3.Impl.toHex` (1 item)

`Sha3/Impl.lean:124-128` renders hex through `"0123456789abcdef".toList`
(READ). The literal's `.toList` is the whole debt. Replacing the string literal
with a `List Char` literal — the shape `Sha256/Hex.lean:41-42` already uses
(READ) — closes it. Body-only; the four `#guard` KATs at `Sha3/Impl.lean:137,
140, 146, 154` re-evaluate unchanged.

`Impl.toHex` is documented in its own docstring as "sanity-check plumbing
only". Ruling P-4 asks whether it survives the unification at all.

### R4 — `decode?` and `ofHex?` (4 items)

`Sha3.Hex.decode?` reads its characters with `String.toList`
(`Sha3/Hex.lean:58`, READ). `Sha3.Digest.ofHex?` calls it
(`Sha3/Digest.lean:22-25`, READ). Both are definitions, and both keep their
name and their type after the repair; only the body changes.

The repair is `Sha256/Hex.lean:93-98` verbatim (READ): a private
`asciiChars (bs : ByteArray) : List Char := bs.data.toList.map (Char.ofNat ·.toNat)`,
and `decode? s := decodeChars? (asciiChars s.toUTF8)`. `String.toUTF8` and
`Char.ofNat` are both axiom-free (MEASURED, §2).

Behaviour. **INFERRED, and a proof obligation the builder should discharge or
the reviewer should accept as an argument:** the two routes agree on every
input. On a string of lowercase ASCII hex the UTF-8 bytes are the characters.
On anything else, every byte at or above `0x80` maps to a `Char` that
`digitValue?` rejects, so both routes return `none`. The one shape worth a
counterexample witness is a string whose character count is even but whose
UTF-8 byte count is odd, or the reverse; both routes still return `none`
because a non-ASCII character can never be a hex digit. A witness in the
package's counterexample register is cheaper than an argument and is asked for
in packet Q3.

### R5 — the five `String`-typed theorems (5 items)

These are the only items whose **statements** change. Each moves to the
`List Char` form the SHA-256 family already carries (READ, `Sha256/Hex.lean`
and `Sha256/Digest.lean`):

| fips202 today | Statement | Becomes | Precedent |
| --- | --- | --- | --- |
| `Sha3.Hex.length_encode` | `(encode bs).length = 2 * bs.size` | `Hex.length_encodeChars : (encodeChars bs).length = 2 * bs.size` | `Sha256/Hex.lean:118` |
| `Sha3.Hex.decode?_encode` | `decode? (encode bs) = some bs` | `Hex.decodeChars?_encodeChars : decodeChars? (encodeChars bs) = some bs` | `Sha256/Hex.lean:141` |
| `Sha3.Hex.encode_lower` | `∀ c ∈ (encode bs).toList, c.toLower = c` | `Hex.encodeChars_lower : ∀ c ∈ encodeChars bs, c.toLower = c` | `Sha256/Hex.lean:147` |
| `Sha3.Digest.length_toHex` | `d.toHex.length = 2 * n` | `Digest.length_toHexChars : d.toHexChars.length = 2 * n` | `Sha256/Digest.lean:62` |
| `Sha3.Digest.ofHex?_toHex` | `ofHex? n d.toHex = some d` | `Digest.ofHexChars?_toHexChars : ofHexChars? n d.toHexChars = some d` | `Sha256/Digest.lean:66` |

Two new definitions come with them, both already in the SHA-256 copy:
`Hex.encodeChars : ByteArray → List Char` with `encode := String.ofList ∘ encodeChars`,
and `Digest.toHexChars`/`Digest.ofHexChars?`.

Proof technique: the existing fips202 proofs transfer almost unchanged, because
fips202 already proves everything on a private `encodeList`/`decodeList?` pair
over `List Char` and only wraps at the end (READ, `Sha3/Hex.lean:42-95`). The
private lemmas `length_encodeList`, `decodeList?_encodeList`,
`encodeList_lower` become the public `*Chars` theorems by dropping the
`String.ofList` wrapper from the statement. The only proof steps that
disappear are the `String.length_ofList` and `String.toList_ofList`
rewrites at `Sha3/Hex.lean:98,102,108` — which are precisely the dirty steps.
**INFERRED:** this repair removes work rather than adding it.

**The cost, stated and not hidden.** After R5 there is no theorem relating
`decode? (encode bs)` to `bs` at the `String` layer, in either family. The
SHA-256 lane recorded the same loss in its S1 landing note. The round trip
lives one layer down, on `List Char`.

## 4. The old `String`-typed forms cannot be kept

`docs/HASH-PACKAGE-PLAN.md` step 9 asks for "every statement byte-identical
except the five restated theorems, each with its old form kept under a
`String`-suffixed name", and in the same row for an "audit admission list
empty". **INFERRED: those two cannot both hold.** A theorem whose statement
mentions `String.length` or `String.toList` inherits `Classical.choice` from
the statement itself (MEASURED, §2). Keeping `length_encode_String` under any
name keeps a declaration on the offender list, which forces an admission entry.

Three ways out, for ruling P-1:

| Option | What it costs |
| --- | --- |
| **(a) Delete the five** — the SHA-256 lane's choice | Nothing measurable. No consumer uses them (§5). The loss is documentation: a reader must follow `encode = String.ofList ∘ encodeChars` themselves |
| (b) Keep them in a second library root outside the audited tree | The package then has two ceilings, which is the state step 9 exists to end |
| (c) Keep them with an admission list of exactly five | The acceptance criterion "empty admission list" fails by construction |

Recommended: **(a)**, with the five old statements recorded verbatim in the
package's DAG document as retired statements and the reason. That preserves the
record without preserving a declaration.

## 5. What the unification breaks in foldlab's consumer: nothing

The brief expected `experiments/entity-store-shell` to consume
`Sha3.sha3_512`, `Sha3.Hex.encode/decode?` and `Sha3.Digest.*`. **MEASURED**
(ripgrep for `Sha3` over every `.lean` file under
`C:\Users\kokok\Dev\foldlab\experiments\entity-store-shell`): it consumes none
of them. The complete list of names it uses is:

| Name | Where | Kind |
| --- | --- | --- |
| `Sha3.Impl.sha3_512` | `Shell/Hash.lean:24,27` | the reference implementation, `List UInt8 → List UInt8` |
| `` `Sha3 ``, `` `Sha3.Impl ``, `` `Sha3.Spec `` | `Shell/Gate.lean:145` | namespace **names**, in the gate's `coreNamespaces` list |
| `import Sha3` | `Shell/Hash.lean:16` | the library root |

The shell carries its own hex (`Shell/Hex.lean`: `hexOfByte`, `hexOfBytes`,
`hexVal`, `bytesOfHex`, `hexOfAddr`, `addrOfHex`) and its own address carrier
(READ). It never touches `Sha3.Digest` or `Sha3.Hex`.

Consequences, all **INFERRED** from that measurement:

1. Unifying `Digest`/`Hex` breaks nothing in the consumer. The compatibility
   shim the brief asked for is not needed for `Digest` or `Hex`.
2. What *does* break is the **namespace rename** at step 3 of the package plan,
   not step 9: `Shell/Gate.lean:145` is a list of `Name` literals, and
   `Sha3.Impl.sha3_512` would become `Hash.Sha3.Impl.sha3_512`. That is a
   three-token edit in a gate, and it belongs to package-plan step 7.
3. R1 changes `Sha3.Impl`'s definition bodies, so the shell's kernel-evaluated
   address theorems re-reduce. `Shell/VectorTheorems.lean:47-48` records that
   one kernel evaluation of `Sha3.Impl.sha3_512` costs about 8.7 s and peaks
   near 3.9 GB (READ). Eleven such theorems exist. **This, not the API, is the
   consumer's real exposure to step 9**, and it is a cost risk, not a
   correctness risk.
4. `Shell/VectorTheorems.lean:334` states the shell's own axiom posture as
   "the same three `Sha3.Bridge` reports", i.e. it *expects*
   `Classical.choice`. After step 9 the shell's reports narrow. That is a prose
   correction owed in foldlab, listed in packet Q5.

Shim, if one is wanted anyway (ruling P-2): `abbrev Sha3.Digest := Hash.Digest`
and `abbrev Sha3.Hex.encode := Hash.Hex.encode` in a `Hash/Compat.lean` outside
the audited roots. Retirement condition: the first release in which no
in-repository or foldlab consumer names anything under `Sha3.` — which,
measured today, is already true for `Digest` and `Hex`, so the honest
recommendation is **no shim at all**.

## 6. Which `Digest`/`Hex` is canonical

`docs/HASH-PACKAGE-PLAN.md` HP-2 already rules this: the SHA-256 copy, because
it is choice-free. The measurements support it and add detail.

| Member | fips202 | this repository | After unification |
| --- | --- | --- | --- |
| `bytes`, `size_eq`, `toByteArray`, `toList` | identical | identical | unchanged |
| `ext`, `size_toByteArray`, `length_toList` | identical statements | identical statements | unchanged |
| `toHex` | `Hex.encode d.bytes` | same | unchanged, and already clean in both |
| `toHexChars`, `ofHexChars?` | absent | present | adopted from SHA-256 |
| `length_toHex`, `ofHex?_toHex` | present, dirty | absent | retired (§4) |
| `DecidableEq` | via `ext` on `bytes` (`Sha3/Digest.lean:47-49`) | via `data.toList` and `byteArray_eq_of_data` (`Sha256/Digest.lean:72-76`) | SHA-256's; fips202's is also clean, so this is a style choice |
| `BEq` | hand-written `beq` (`Sha3/Digest.lean:44-45`) | `instBEqOfDecidableEq` | SHA-256's, so that `BEq` and `DecidableEq` agree by construction |

The `Sha3` API theorems need nothing. `sha3_512_impl`, `sha3_512_spec` and
`sha3_512_ofList` are all stated on `(sha3_512 msg).toList`, and `toList` is
`d.bytes.data.toList` in both copies (READ, `Sha3/Digest.lean:18`,
`Sha256/Digest.lean:28`) — the same definition, already clean. **INFERRED:**
the API theorem statements survive the unification byte-identically; only the
`Digest` they are stated about is renamed.

The `#guard` KATs at `Sha3/Api.lean:33-53` render through `.toHex`, which
stays. They re-evaluate unchanged.

## 7. Proof-graph edges, and acceptance

Edges this touches:

| Graph | Edge | Change |
| --- | --- | --- |
| `docs/SHA256-DAG.md` §10 | `trust` (`required-open`) | its pinned audit line changes: the shared package's audit reports both families, so the pinned declaration count and module count are re-pinned once |
| `docs/SHA256-DAG.md` §10 | `construction` | R1's shared `Hash.Vec` replaces `Sha256.Vec`; the module's own justification text is rewritten to cite both families' measurements |
| fips202 `README.md` §"axiom profile" (READ, lines 101-102) | the tree ceiling | `[propext, Classical.choice, Quot.sound]` becomes `[propext, Quot.sound]` |
| fips202 `Sha3/Verified.lean` (READ, line 7) | the pinned `#guard_msgs` audit line | re-pinned: the allowlist text and the declaration count both change |
| fips202 `PASSB-SNAPSHOT.md` | the frozen statement snapshot | five statements retired, five added; R1's two `Vector.ofFn` statement spellings updated |
| foldlab `Shell/VectorTheorems.lean:334` | the shell's stated axiom posture | narrows |

Acceptance for step 9, all of it mechanical:

1. The shared package's audit gate runs with `allowedAxioms = [propext, Quot.sound]`
   and `admittedStringDeclarations = []` — an **empty exact-declaration
   admission list** — and reports `0 offenders` over both families.
2. Every theorem in both families has a receipt inside `[propext, Quot.sound]`.
   Check: the sweep of §1, re-run over `Hash.*`, reporting `0`.
3. Both self-tests unchanged: `sha3_512sum` on its four CAVP guards and
   `lake exe sha256 --self-test` over all 65 records.
4. `lake env leanchecker --fresh` exit 0 on the package's verified root.
5. foldlab's consumer green: its gate, its eleven kernel address theorems, and
   `mise run check`.
6. Runtime unchanged within tolerance: `sha3_512sum` on 1 MiB within 1.25× of
   the 0.823 s recorded on this host, and `sha256` within 1.25× of 0.058 s per
   MiB. This is R1's exit check and the reason the Array-backed `ofFn` is kept
   as a fallback.

Costs on this host, for planning (MEASURED, `<probe>\fips202-clean`, a copy
with no `.lake`):

| Command | Time | Log |
| --- | --- | --- |
| `lake build` (library, 14 jobs) | 9.8 s | `<logs>\fips202-clean-build.log` |
| `lake build Sha3Verified` (adds the kernel KATs) | 56.5 s further, of which `Sha3.Kats` is 53 s | `<logs>\fips202-verified-build.log` |

So a full red-to-green cycle on the SHA3 side is about 70 s. The expensive
checks are `leanchecker --fresh` (138 s, READ, `docs/HASH-PACKAGE-PLAN.md`
step 0 row) and the consumer's kernel theorems (about 8.7 s each, READ).

## 8. Packets

Two seats, breaker then builder, per the estate's rule that the statements are
frozen by a different process than the one that proves them.

| Packet | Seat | Act | Exit check | Budget |
| --- | --- | --- | --- | --- |
| Q0 | breaker | Flip the audit's `allowedAxioms` to `[propext, Quot.sound]` and `admittedStringDeclarations` to `[]`. Freeze the R5 statements and the R1/R2 local-lemma statements as text. Record the 33-item list of §2 as the battery's expected failure | `lake build Sha3Verified` fails, naming exactly the 33 declarations of §2 and no others. That list is the red battery | 0.5 seat-day |
| Q1 | builder | R2: add `Hash/Nat.lean` with the two lemmas of `<probe>\fips202\Probe8.lean`; retarget `Bridge.lean:467` and `Fast.lean:288` | 9 of 33 close; no statement changed; `lake build` green | 0.5 seat-day — the proofs exist and are measured |
| Q2 | builder | R3 + R4 + R5: the hex and digest work. `Impl.toHex` literal; `decode?` through `String.toUTF8`; the five restatements; `encodeChars`/`toHexChars`/`ofHexChars?` adopted from `Sha256/Hex.lean` and `Sha256/Digest.lean` | 10 of 33 close; the `#guard` KATs of `Impl.lean` and `Api.lean` re-evaluate unchanged; one counterexample witness for the `decode?` re-route (§R4) | 1 seat-day |
| Q3 | builder | R1: `Hash/Vec.lean`; the 11 definition sites and 10 proof sites of §R1 | 14 of 33 close, so **0 offenders**; `lake build Sha3Verified` green; `sha3_512sum` 1 MiB within 1.25× of 0.823 s; kernel KAT within 1.5× of 53 s. If either budget fails, switch to the Array-backed `ofFn` and re-measure | 1.5 seat-days, the riskiest packet |
| Q4 | builder | Unification: one `Hash.Digest`, one `Hash.Hex`, per §6. Delete the SHA3 copies | both families build against the single copy; every API theorem statement byte-identical modulo the type's name | 1 seat-day |
| Q5 | builder | Documents and consumer: the six edges of §7; foldlab's shell gate namespace list; its stated axiom posture | consumer gate green; `mise run check` green; `leanchecker --fresh` exit 0; dual host | 1 seat-day |

Q1 and Q2 are independent and may run in parallel after Q0. Q3 must follow
Q0 alone. Q4 must follow Q2. Q5 is last.

Order by leverage, if the packets must be cut short: **Q1 (9 receipts, proofs
already written), Q2 (10 receipts, and it is the only packet that changes a
statement), Q3 (14 receipts, and the only packet that can regress runtime).**

## 9. Rulings owed

| Id | Question | Recommended default |
| --- | --- | --- |
| P-1 | The five `String`-typed statements: delete, exile to an unaudited root, or admit five entries? §4 shows the package plan's step-9 row asks for two incompatible things | **delete**, recording the retired statements verbatim in the DAG document. The SHA-256 family already lives without them and no consumer names them |
| P-2 | A `Sha3.Digest`/`Sha3.Hex` compatibility shim at all? | **no shim.** Measured: foldlab's only consumer uses neither |
| P-3 | May step 9 change `Impl`, `Fast` and `KeccakProbe` definition bodies? `docs/HASH-PACKAGE-PLAN.md` §4 forbids it during the move, and R1 is impossible without it | **yes, and only in step 9**, with the ban restated for every later step. Without this ruling the 14-item cone cannot close |
| P-4 | Does `Sha3.Impl.toHex` survive the unification, or is it deleted in favour of `Hash.Hex.encode`? | **delete it**, after moving its four `#guard` KATs onto `Hex.encodeChars`. It is documented as sanity-check plumbing and duplicates the shared encoder |
| P-5 | Does the shell consumer move to `List Char`, or keep its own hex? | **keep its own.** It never imported the library's hex; making it depend on one now adds coupling step 9 does not need |
| P-6 | `Vector.ofFn` route: List-backed (SHA-256's, landed) or Array-backed (measured clean here)? | **List-backed**, with the Array-backed one as the named fallback if Q3's runtime check fails |
| P-7 | Is the `decode?` re-route's behavioural equality a proof obligation or an accepted argument? | **a counterexample witness plus the argument of §R4.** A theorem would need the String-layer round trip that §3 R5 shows does not exist |

## 10. What this document does not claim

No proof was landed. Six probe files were elaborated against a copy of the
fips202 tree, and their receipts are quoted above; two of them
(`Probe8.lean`, `Probe7.lean`) contain complete choice-free proofs of lemmas
this plan proposes, and those are the strongest evidence here. Everything else
is measurement of the existing trees and inference from it. The runtime
question in R1 is open and cannot be closed before the edit exists.

## Rulings (coordinator, 2026-09-02, at the recommended defaults)

| Id | Ruling |
| --- | --- |
| P-1 | The five `String`-typed theorem forms are deleted in step 9, not exiled and not admitted; a statement that mentions `String.length` or `String.toList` inherits `Classical.choice` from itself, so keeping it under any name is incompatible with an empty admission list. The `String`-typed definitions (`encode`, `decode?`, `toHex`, `ofHex?`) stay as definitions with their bodies re-routed through axiom-free primitives. |
| P-2 | No compatibility shim: foldlab's consumer uses only `Sha3.Impl.sha3_512` and three namespace literals in its gate, none of the hex or digest API. |
| P-3 | Step 9 may change `Impl` and `Fast` definition bodies where the parity repair requires it (the `Vector.ofFn` route), provided every bridge and KAT statement stays byte-identical, every KAT still passes, and `sha3_512_eq_impl` and `sha3_512_spec` are re-proved unchanged. `docs/HASH-PACKAGE-PLAN.md` §4 is amended to say so for step 9 only. |
| P-4 | `Sha3.Impl.toHex` is retired in favour of the shared `Hash.Hex.encode`; the consumer keeps its own hex and is unaffected. |
| P-5 | The shell consumer does not move; it needs nothing from the hex layer. Its exposure is the re-reduction of its eleven kernel address theorems, which is a measured cost, not a statement change. |
| P-6 | List-backed `ofFn` (the route `Sha256/Vec.lean` already ships) unless the 24-round permutation's throughput regresses beyond 2x of the S2 baseline, in which case the Array-backed `replicate` + `mapFinIdx` route is taken; both are measured in the packet, not assumed. |
| P-7 | The `decode?` re-route is a proof obligation: `decodeChars?_encodeChars` on `List Char` as the SHA-256 copy has it, plus a stated theorem that the `String` definition agrees with the `List Char` one on `toUTF8`-decoded input. |

The parity work is step 9 of `docs/HASH-PACKAGE-PLAN.md` and opens after
the extraction lands and is tagged; its packets and budgets are above.