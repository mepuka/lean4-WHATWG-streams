# Lean 4.33.1 standard-library strategy and performance (R0-A)

Status: R0-A, MEASURED on Windows 11 x86-64 / AMD Ryzen 7 8700F, 2026-09-01.
Author: the R0-A research seat. This document is research input for P1 and the
S1 SHA-256 lane. It rules nothing and freezes nothing.

## 0. Host, toolchain, and how to read this

| Fact | Value | How obtained |
| --- | --- | --- |
| OS | `Microsoft Windows NT 10.0.26200.0` | `[Environment]::OSVersion.VersionString` |
| CPU | `AMD Ryzen 7 8700F 8-Core Processor`, 16 logical processors | `(Get-CimInstance Win32_Processor).Name`, `.NumberOfLogicalProcessors` |
| RAM | 16,771,702,784 bytes | `(Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory` |
| Lean | `Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)` | `lake env lean --version` in the scratch package |
| Repository HEAD when written | `432f1b8` | `git rev-parse --short HEAD` |
| Pinned Lean sources read | `C:\Users\kokok\Dev\foldlab\.reference\clones\lean4-v4.33.1\src` | read-only |

**Where the work lives.** Every measurement in this document was produced by a
throwaway Lake package outside this repository. No `lake` command was run
inside this checkout.

```
$BENCH = C:\Users\kokok\AppData\Local\Temp\claude\C--Users-kokok-Dev-foldlab\a218249a-b983-4635-ae4f-dea3a573ad60\scratchpad\r0-stdlib-bench
$LOGS  = $BENCH\logs
```

`$BENCH\lean-toolchain` is `leanprover/lean4:v4.33.1`; `$BENCH\lake-manifest.json`
has no packages. `$BENCH\index.bs` is a byte copy of
`vendor/whatwg-streams-b9ba9f49/index.bs`, 417,076 bytes, SHA-256
`24360b4f8446e6c80e185c5021fcca9b67a7e0bb62490a00109080ebc04c6440`
(`Get-FileHash`). The in-tree `Gates.Sha256` port in the scratch package computes
the same digest (row `H0-wholeFile`), which is the cross-check that the scratch
copy is the pinned bytes.

**Tags.** Every row is tagged.

- **MEASURED** — a number produced by a command named in the row.
- **READ** — a fact read from a pinned Lean source line, quoted or paraphrased,
  with `File.lean:line`. Line numbers are relative to the pinned source root
  above. Every cited line was opened and read; the reading log is
  `$LOGS\verify-cites.txt`.
- **INFERRED** — a conclusion drawn from MEASURED and READ rows. The rows it
  rests on are named.

**Timing method.** Each case is its own process invocation, run three times,
median reported. `wall_ms` is `Measure-Command` around the whole process.
`inner_ms` is `IO.monoNanosNow` around the operation only, with the pure
computation forced inside the timed region by `IO.lazyPure`; without
`IO.lazyPure` the thunk is evaluated at the call site and the timer measures
nothing (this bug was hit and fixed; the first, wrong log is not reported).
Process floor on this host is 16.6–18.9 ms of `wall_ms` (row `X4-length`,
17.9 ms wall for a 0.00 ms operation), so `inner_ms` is the number to compare
and `wall_ms` is reported only to show the floor.

Percentages and ratios always show both source numbers.

---

## 1. Text carriers

### 1.1 What the API is now — the Slice migration

4.33.1 has moved the substring-shaped `String` API to `String.Slice`, and the
old spellings are deprecated. This is not a plan; it is what the compiler
prints today. The following warnings are the compiler's own output from
`$LOGS\probe.txt` and `$LOGS\probe2.txt` (command: `lake env lean probe.lean`,
`lake env lean probe2.lean`).

| Old spelling | Compiler says | New return type | Tag |
| --- | --- | --- | --- |
| `String.get` | deprecated, use `String.Pos.Raw.get` | `Char` | MEASURED (warning text) |
| `String.get!` | deprecated, use `String.Pos.Raw.get!` | `Char` | MEASURED |
| `String.trim` | deprecated, use `String.trimAscii`; *"The updated constant has a different type: `String → String.Slice`"* | `String.Slice` | MEASURED |
| `String.dropRight` | deprecated, use `String.dropEnd`; different type `String → Nat → String.Slice` | `String.Slice` | MEASURED |
| `String.toSubstring` | deprecated, use `String.toRawSubstring` | `Substring.Raw` | MEASURED |
| `Substring.toString` | deprecated, use `Substring.Raw.toString` | `String` | MEASURED |
| `Substring` (the type) | deprecated, use `Substring.Raw` | — | MEASURED |
| `String.posOf` | deprecated, use `String.find`; the replacement returns `s.Pos` and takes a `Pattern` | `s.Pos` | MEASURED |
| `String.validateUTF8` | deprecated, use `ByteArray.validateUTF8` | `Bool` | MEASURED |

Functions that **already return `String.Slice`, with no deprecation**, so the
migration is done for them:

| Function | Signature printed by `#check` | Source | Tag |
| --- | --- | --- | --- |
| `String.drop` | `String → Nat → String.Slice` | `Init/Data/String/TakeDrop.lean:42` `@[inline] def drop (s : String) (n : Nat) : Slice :=` | READ |
| `String.take` | `String → Nat → String.Slice` | `Init/Data/String/TakeDrop.lean:95` | READ |
| `String.dropEnd` | `String → Nat → String.Slice` | `Init/Data/String/TakeDrop.lean:64` | READ |
| `String.trimAscii` | `String → String.Slice` | `Init/Data/String/TakeDrop.lean:434` | READ |
| `String.toSlice` | `String → String.Slice` | `Init/Data/String/Defs.lean:426` `def toSlice (s : String) : Slice where` | READ |
| `String.split` | `… → Std.Iter String.Slice` | `Init/Data/String/Search.lean:258–259`; line 259 is `(s.toSlice.split pat : Std.Iter String.Slice)` | READ |

Deprecation attributes carry dates: `Init/Data/String/TakeDrop.lean:437` is
`@[deprecated String.trimAscii (since := "2025-11-17")]`,
`Init/Data/String/TakeDrop.lean:67` is `@[deprecated String.dropEnd (since := "2025-11-14")]`,
`Init/Data/String/Substring.lean:556` is `@[deprecated Substring.Raw (since := "2025-11-16")]`. (READ.)

There are 133 `@[deprecated` attributes in `Init/Data/String/*.lean`
(MEASURED: `Select-String -Path "$src\Init\Data\String\*.lean" -Pattern '@\[deprecated' -AllMatches` count).

**What did NOT change.** `String.splitOn` still returns `List String`:
`@String.splitOn : String → optParam String " " → List String` (`#check`,
`$LOGS\probe.txt`). Its definition is `Init/Data/String/Legacy.lean:112`,
`@[inline] def splitOn (s : String) (sep : String := " ") : List String :=`,
and the file's own docstring at `Init/Data/String/Legacy.lean:104` reads
*"This is a legacy function. Use `String.split` instead."* It carries no
`@[deprecated]` attribute today. (READ.)

`String.Slice.splitOn` does not exist; `#check @String.Slice.splitOn` is
`Unknown constant` (`$LOGS\probe2.txt`, MEASURED). The slice-side replacement
is `String.Slice.split`, an iterator.

### 1.2 What each carrier is, structurally

| Carrier | Definition | Source | Tag |
| --- | --- | --- | --- |
| `String` | `structure String where ofByteArray ::` with `toByteArray : ByteArray` and `isValidUTF8 : ByteArray.IsValidUTF8 toByteArray` | `Init/Prelude.lean:3537`, `:3541`, `:3543` | READ |
| `String.Slice` | `structure Slice where` with `str : String`, `startInclusive`/`endExclusive : str.Pos`, and `startInclusive_le_endExclusive : startInclusive ≤ endExclusive` | `Init/Data/String/Defs.lean:409`, `:411`, `:417` | READ |
| `String.Pos` | `structure Pos (s : String) where` — a position **indexed by the string**, carrying a validity proof | `Init/Data/String/Defs.lean:352` | READ |
| `String.Pos.Raw` | `structure String.Pos.Raw where` — a bare byte offset, no validity | `Init/Prelude.lean:3589` | READ |
| `Substring.Raw` | `structure Substring.Raw where` — `str` plus two `Pos.Raw`, no invariant | `Init/Prelude.lean:3614` | READ |
| `ByteArray` | `structure ByteArray where` with `data : Array UInt8` | `Init/Prelude.lean:3417`, `:3429` | READ |

The key structural difference: `String.Slice` bundles validity proofs;
`Substring.Raw` does not. `Init/Prelude.lean:3611` says of `Substring`,
verbatim, that it *"will be deprecated"*. (READ.)

The runtime representation is documented at `Init/Prelude.lean:3532–3535`:
*"At runtime, strings are represented by dynamic arrays of bytes using the
UTF-8 encoding. Both the size in bytes (`String.utf8ByteSize`) and in
characters (`String.length`) are cached and take constant time. Many
operations on strings perform in-place modifications when the reference to the
string is unique."* (READ.) That constant-time claim is confirmed below.

`Init/Prelude.lean:3538–3540` warns that the `toByteArray` projection
*"actually takes linear time and space at runtime"* and directs callers to
`String.utf8ByteSize` and `String.getUTF8Byte` for efficient byte access.
`String.toUTF8` is that projection: `Init/Data/String/Defs.lean:76`,
`def String.toUTF8 (a : @& String) : ByteArray := a.toByteArray`. (READ.)

### 1.3 Lemma support, counted

Command (run by me):

```powershell
Select-String -Path "<file>" -Pattern '^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |public |nonrec )*theorem\s' -AllMatches | Measure
```

| File | `theorem` count | Tag |
| --- | --- | --- |
| `Init/Data/String/Lemmas.lean` | **0** — it is an import hub only | MEASURED |
| `Init/Data/String/Lemmas/**` (38 files, recursive) | **1558** | MEASURED |
| `Init/Data/String/Basic.lean` | 360 | MEASURED |
| `Init/Data/String/Defs.lean` | 77 | MEASURED |
| `Init/Data/String/Slice.lean` | 2 | MEASURED |
| `Init/Data/String/Substring.lean` | **3** | MEASURED |
| `Init/Data/String/TakeDrop.lean` | 0 | MEASURED |
| `Init/Data/String/Lemmas/Splits.lean` | 134 | MEASURED |
| `Init/Data/String/Lemmas/Slice.lean` | 23 | MEASURED |
| `Init/Data/String/Lemmas/Basic.lean` | 74 | MEASURED |
| `Init/Data/Array/Lemmas.lean` | 821 | MEASURED |
| `Init/Data/List/Lemmas.lean` | 700 | MEASURED |
| `Init/Data/Vector/Lemmas.lean` | 642 | MEASURED |
| `Init/Data/ByteArray/Lemmas.lean` | 71 | MEASURED |
| `Init/Data/ByteArray/Bootstrap.lean` | 5 | MEASURED |

Two consequences. First, anyone opening `Init/Data/String/Lemmas.lean` to
judge the lemma surface will read zero and conclude wrongly; the 1558 theorems
are in the `Lemmas/` directory. Second, `Substring` has three theorems in the
whole subtree — it is verification-dead, and the repository's existing
avoidance of it is correct for a second reason beyond toolchain churn.

### 1.4 Cost: splitting 417 KB into lines

Case source: `$BENCH\R0Bench\Text.lean`, driver `$BENCH\Bin\TextBench.lean`.
Command: `& $BENCH\run-bench.ps1 -Exe textbench -Cases '<case>' -Log $LOGS\textbench-median.txt`.
Log: `$LOGS\textbench-median.txt`. All rows MEASURED, median of 3.

| Case | What it does | inner_ms | wall_ms | Answer |
| --- | --- | --- | --- | --- |
| `T1-splitOn` | `(s.splitOn "\n").length` | **2.76** | 22.6 | 8402 |
| `T2-gatesLines` | the `Gates.Common.lines` pipeline: `splitOn` then a `List Char` `dropLast` per CR-terminated line | **2.91** | 22.8 | 8401 |
| `T3-splitIter` | `(s.split '\n').fold (fun n _ => n+1) 0` — slices, never materialised | **0.75** | 19.9 | 8402 |
| `T4-splitIterCopy` | same, each slice copied back with `.toString` | **1.16** | 20.2 | 408485 |
| `T5-listChar` | hand-rolled split over `s.toList`, building real strings | **11.50** | 31.4 | 408486 |
| `T6-spansBang` | byte spans over `ByteArray` using `bs[i]!` | **0.74** | 18.6 | 8401 |
| `T7-spansTotal` | byte spans using a total `byteAt` (`dite`, no panic path) | **0.67** | 18.9 | 8401 |
| `T8-spansNatFold` | byte spans via `Nat.fold` | **0.47** | 19.7 | 8401 |
| `T9-spansFoldl` | byte spans via `ByteArray.foldl` | **1.14** | 20.1 | 8401 |

INFERRED, from T1/T3/T5/T8: the spread across "reasonable" line-splitting
strategies on this file is 0.47 ms to 11.50 ms, a factor of 11.50/0.47 = 24.5.
The cheapest is `Nat.fold` over `ByteArray` (T8) and the most expensive is
`List Char` (T5). Every one of them is under 12 ms; none is a bottleneck at
417 KB. Line splitting is not where P1 will spend its time.

INFERRED, from T6 vs T7: the total `byteAt` (`if h : i < bs.size then bs[i] else 0`)
was 0.67 ms against 0.74 ms for `bs[i]!`. The panic-free accessor was not
slower here. Avoiding `!` costs nothing measurable at this size.

### 1.5 Cost: finding every occurrence of a literal

| Case | What it does | inner_ms | wall_ms | Answer |
| --- | --- | --- | --- | --- |
| `F1-findBytes` | naive byte search over `ByteArray`, offsets returned | **8.36** | 29.3 | 229 |
| `F2-findSplitOn` | `(s.splitOn "<div algorithm>").length - 1` | **2.66** | 23.6 | 229 |
| `F3-findSplitIter` | `String.split` on the literal, iterator, counted | **3.58** | 23.8 | 229 |
| `F4-findChars` | the `Gates.Citations` algorithm (`toList.toArray`, `[i]!`) over the whole file | **16.65** | 36.6 | 229 |

All MEASURED, median of 3, log `$LOGS\textbench-median.txt`.

INFERRED, from F1/F4: the `Array Char` route costs 16.65 ms against 8.36 ms
for the byte route, 2.0× more, and it also loses byte offsets — a `Char` index
is not a byte index, and the census needs byte spans. F2 is fastest but
returns no offsets at all, only a count.

**A finding about the corpus, not the library.** The literal `<div algorithm>`
occurs **229** times in `index.bs`, not 248. The 248 figure counts
`<div algorithm`, i.e. 229 bare plus 19 with an attribute (`<div algorithm=`).
MEASURED with PowerShell on the vendored file:

```powershell
$t = Get-Content C:\Users\kokok\Dev\lean4-WHATWG-streams\vendor\whatwg-streams-b9ba9f49\index.bs -Raw
([regex]::Matches($t, [regex]::Escape('<div algorithm>'))).Count   # 229
([regex]::Matches($t, '<div algorithm')).Count                     # 248
([regex]::Matches($t, '<div algorithm=')).Count                    # 19
```

Both the Lean byte search (`F1-findBytes`, answer 229) and PowerShell agree on
229 for the exact literal. Also measured on the same file: 8402 newline-separated
lines, 0 CRLF pairs, 1020 occurrences of `[[`.

### 1.6 Cost: extracting a byte range and hashing it

| Case | What it does | inner_ms | wall_ms | Answer |
| --- | --- | --- | --- | --- |
| `H0-wholeFile` | `Gates.Sha256.hexDigest` of all 417,076 bytes | **8.48** | 26.7 | digest matches `Get-FileHash` |
| `H1b-extractOnly` | 229 `ByteArray.extract` calls, spans between anchors | **0.13** | 27.6 | 374,064 bytes extracted |
| `H1-spanDigests` | the same 229 extracts, each SHA-256'd and hexed | **7.98** | 34.7 | 229 digests |
| `X1c-toUTF8Digest` | `hexDigest text.toUTF8` (String → ByteArray, then hash) | **8.59** | 27.3 | same digest |

All MEASURED, median of 3, logs `$LOGS\textbench-median.txt` and
`$LOGS\textbench3-median.txt`.

INFERRED, from H1b/H1: extraction is 0.13 ms for 374 KB across 229 spans and
is not the cost; hashing is, at 7.98 ms for the same bytes, 61× the extraction.
INFERRED, from H0/H1: hashing 374,064 bytes in 229 pieces (7.98 ms) costs
slightly less than hashing 417,076 bytes in one piece (8.48 ms) — per-call
overhead of the digest is negligible at these sizes.

INFERRED, from H0/X1c: `String.toUTF8` on this file costs 8.59 − 8.48 = 0.11 ms,
i.e. it behaves as a memory copy of 417,076 bytes. Rows `X1-toUTF8` (0.01 ms)
and `X1b-toUTF8Forced` (0.01 ms) are **not trustworthy** — 417 KB in 0.01 ms is
41 GB/s, and the compiler is very likely folding `(toUTF8 s).size` to the cached
`utf8ByteSize`. They are reported here only to say they were discarded.

### 1.7 Miscellaneous text costs

| Case | Operation | inner_ms | Answer | Tag |
| --- | --- | --- | --- | --- |
| `X3-toList` | `text.toList.length` | 6.67 | 416,886 | MEASURED |
| `X4-length` | `text.length` | **0.00** | 416,886 | MEASURED |
| `X5-utf8ByteSize` | `text.utf8ByteSize` | **0.01** | 417,076 | MEASURED |
| `X2-fromUTF8` | `(String.fromUTF8? bytes).isSome` | 0.42 | true | MEASURED |

INFERRED, from X4/X5 and `Init/Prelude.lean:3532–3535`: both `String.length`
and `String.utf8ByteSize` are cached and constant time, exactly as the
docstring says. `String.length` on a 416,886-character string is free.
`Init/Data/String/Length.lean:24–26` is `@[extern "lean_string_length", expose, tagged_return]`
over the model body `b.toList.length` — the model is linear, the runtime is not.
(READ.)

INFERRED, from X3/X4: materialising `List Char` costs 6.67 ms where reading the
cached length costs 0.00 ms. `String.toList` is the expensive operation in the
`Gates.Common` idiom, not the splitting.

### 1.8 The interpreter gap

The same four computations, defined **locally** in the evaluated file so they
are interpreted rather than linked against compiled code. Source
`$BENCH\evalbench.lean`; the bodies are copied verbatim from the compiled
versions. Command: `lake env lean evalbench.lean`, three runs, log
`$LOGS\evalbench-3runs.txt`. Whole-file wall median 2859.7 ms.

| Operation | compiled `inner_ms` | `#eval` `inner_ms` | ratio | Tag |
| --- | --- | --- | --- | --- |
| `splitOn "\n"` on 417 KB | 2.76 (`T1`) | 3.72 (`E1`) | 3.72 / 2.76 = **1.3×** | MEASURED |
| byte line spans, total `byteAt` | 0.67 (`T7`) | 112.58 (`E2`) | 112.58 / 0.67 = **168×** | MEASURED |
| naive byte search for the literal | 8.36 (`F1`) | 305.60 (`E3`) | 305.60 / 8.36 = **36.6×** | MEASURED |
| SHA-256 of 64 KiB | — | 248.41 (`E4`) | — | MEASURED |
| SHA-256 of 417 KB | 8.48 (`H0`) | 1447.46 (`E5`) | 1447.46 / 8.48 = **171×** | MEASURED |

INFERRED: the interpreter penalty is not a single constant. Code that spends
its time inside one compiled stdlib call (`splitOn`) pays 1.3×. Code that is a
Lean-level loop over bytes pays 36× to 171×. A `#eval` known-answer test over
the whole spec file would take about 1.5 s per digest; over the 229 spans it
would be roughly the same total, since the same bytes are hashed. That is
tolerable for a handful of checks and intolerable as a per-build gate over
many.

---

## 2. Byte carriers

### 2.1 Structure and the extern surface

`ByteArray` is `structure ByteArray where` with the single field
`data : Array UInt8` (`Init/Prelude.lean:3417`, `:3429`), with externs attached
separately. Key operations, all READ:

| Operation | Source line | Note |
| --- | --- | --- |
| `push` | `Init/Prelude.lean:3455` `@[extern "lean_byte_array_push", implicit_reducible]` | amortised, in place when unique |
| `emptyWithCapacity` | `Init/Prelude.lean:3437` `@[extern "lean_mk_empty_byte_array", implicit_reducible]` | **`ByteArray.mkEmpty` does not exist in 4.33.1** — `#check @ByteArray.mkEmpty` is `Unknown constant` (`$LOGS\probe2.txt`, MEASURED) |
| `size` | `Init/Prelude.lean:3475` `@[extern "lean_byte_array_size", tagged_return, implicit_reducible]` | constant time, unboxed return |
| `get!` | `Init/Data/ByteArray/Basic.lean:69`; docstring `:66` *"Panics if the index is out of bounds."* | **panics** |
| `set!` | `Init/Data/ByteArray/Basic.lean:96`; docstring `:93` *"If the index is out of bounds, the array is returned unmodified."* | **does not panic** |
| `extract` | `Init/Data/ByteArray/Basic.lean:143` `def extract (a : ByteArray) (b e : Nat) : ByteArray :=` | pure Lean over `copySlice` |
| `append` | replaced in compiled code: `Init/Data/ByteArray/Basic.lean:161` `theorem append_eq_fastAppend : @ByteArray.append = @ByteArray.fastAppend := by` (a `@[csimp]`) | |
| `toList` | `Init/Data/ByteArray/Basic.lean:181` | a loop with `termination_by` |
| `toUInt64LE!` | `Init/Data/ByteArray/Extra.lean:20–21`; line 21 is `assert! bs.size == 8` | **panics twice over**: the assert, and eight `get!` calls |

### 2.2 Copy-on-write and reference counting — the uniqueness rule

**The rule, in one paragraph.** Every heap object in the Lean runtime carries a
reference count, and a write to an array is performed in place exactly when
that count is 1. `include/lean/lean.h:1197–1204` is the whole rule for byte
arrays:

```c
static inline lean_object * lean_byte_array_uset(lean_obj_arg a, size_t i, uint8_t v) {
    lean_obj_res r;
    if (lean_is_exclusive(a)) r = a;
    else r = lean_copy_byte_array(a);
    ...
}
```

`lean_is_exclusive` is `lean_internal_get_rc(o) == 1` for single-threaded
objects (`include/lean/lean.h:704–706`). So a write costs O(1) when the writer
holds the only reference and O(n) — a full copy of the array — when it does
not. `push` obeys the same rule. The practical consequence for Lean code: a
loop that threads one array through `mut` and never lets a second name escape
runs in place; the moment any other live binding, closure capture, or returned
tuple holds the old array, the next write copies the whole buffer. All READ.

`include/lean/lean.h:1206–1215` also confirms the `set!` semantics from the
Lean side: an out-of-range index returns `a` untouched, with no panic.

**Measured.** Source `$BENCH\Bin\ByteBench.lean`, logs
`$LOGS\bytebench-median.txt` and `$LOGS\bytebench2-median.txt`, median of 3.

| Case | What it does | inner_ms | Tag |
| --- | --- | --- | --- |
| `B1-push16MiB` | build 16 MiB by `push` from `ByteArray.empty` | 34.54 | MEASURED |
| `B2-pushCap16MiB` | same with `emptyWithCapacity (16*1024*1024)` | 30.60 | MEASURED |
| `B3-setUnique16MiB` | build 16 MiB, then 16,777,216 `set!` on the unique array | 47.79 | MEASURED |
| `B3b-setUnique100k` | 100,000 `set!` on a unique 100,000-byte array | **0.29** | MEASURED |
| `BB-aliasEvery100k` | 100,000 `set!` where a fresh alias is taken each iteration | **257.01** | MEASURED |
| `BB2-aliasEvery200k` | the same at 200,000 | **798.51** | MEASURED |
| `BA-aliasOnce100k` | one alias held to the original, then 100,000 `set!` | 0.33 | MEASURED |

INFERRED, from B3b vs BB: aliasing every write costs 257.01 ms against 0.29 ms
unique, a factor of 257.01 / 0.29 = 886. From BB vs BB2: doubling n from
100,000 to 200,000 took the time from 257.01 ms to 798.51 ms, a factor of
798.51 / 257.01 = 3.11, superlinear and consistent with one full copy per
write. From BA: holding a single alias to the original costs 0.33 ms against
0.29 ms — only the *first* write copies, after which the loop variable is
unique again. The trap is aliasing inside the loop, not aliasing before it.

INFERRED, from B1 vs B2: reserving capacity saved 34.54 − 30.60 = 3.94 ms out
of 34.54, 11%. Growth reallocation is not the dominant cost of a push loop.

### 2.3 Extraction and conversion

| Case | What it does | inner_ms | Tag |
| --- | --- | --- | --- |
| `B4-extract16MiB` | build 16 MiB, then one `extract 0 (8 MiB)` | 31.43 | MEASURED |
| `B5-extractMany` | build 16 MiB, then 1000 `extract` of 4096 bytes | 32.85 | MEASURED |
| `B6-toList1MiB` | `(1 MiB).data.toList.length` | 23.57 | MEASURED |
| `B7-toList16MiB` | `(16 MiB).data.toList.length` | **451.41** | MEASURED |
| `B8-toListSum1MiB` | `.data.toList.foldl` summing bytes | 23.33 | MEASURED |
| `B9-foldlSum1MiB` | `ByteArray.foldl` summing bytes, no list | **2.81** | MEASURED |
| `BD-listToByteArray1MiB` | `(List.replicate (1 MiB) 0x61).toByteArray.size` | 17.75 | MEASURED |

INFERRED, from B2 as the build baseline (30.60 ms): one 8 MiB `extract` costs
31.43 − 30.60 = 0.83 ms; 1000 extracts of 4096 bytes cost 32.85 − 30.60 = 2.25 ms,
about 2.3 µs each. Extraction is cheap and linear in the extracted size.

INFERRED, from B8 vs B9: summing 1 MiB through `List UInt8` costs 23.33 ms
against 2.81 ms with `ByteArray.foldl`, a factor of 23.33 / 2.81 = 8.3. From
B6 vs B7: `data.toList` costs 23.57 ms at 1 MiB and 451.41 ms at 16 MiB — a
16× size increase for a 19.2× time increase, i.e. roughly linear with
allocation pressure. `bs.data.toList` on a whole spec-sized file is affordable
once; on 16 MiB it is half a second and 16 million cons cells.

### 2.4 Lemma support for ByteArray

`Init/Data/ByteArray/Lemmas.lean` has **71** theorems and
`Init/Data/ByteArray/Bootstrap.lean` has **5** (MEASURED, counting command in
§1.3). `Init/Data/ByteArray/Basic.lean` has 5 more. Against
`Init/Data/Array/Lemmas.lean`'s 821, the ByteArray surface is 81/821 = 9.9% of
Array's.

The `Bootstrap.lean` five, verbatim by name: `data_push`, `toList_data_append'`,
`ext`, `List.toList_data_toByteArray`, `List.toByteArray_append'`.

The `Lemmas.lean` 71, verbatim by name, in file order:
`emptyc_eq_empty`, `emptyWithCapacity_eq_empty`, `data_empty`, `data_extract`,
`extract_zero_size`, `extract_same`, `fastAppend_eq_copySlice`,
`List.toByteArray_append`, `toList_data_append`, `data_append`, `size_empty`,
`List.data_toByteArray`, `List.size_toByteArray`, `List.toByteArray_nil`,
`empty_append`, `append_empty`, `size_append`, `size_eq_zero_iff`,
`getElem_eq_getElem_data`, `getElem_append_left`, `getElem_append_right`,
`List.getElem_toByteArray`, `List.getElem_eq_getElem_toByteArray`,
`size_extract`, `extract_eq_empty_iff`, `extract_add_left`,
`append_eq_empty_iff`, `toByteArray_eq_empty`, `append_right_inj`,
`append_left_inj`, `extract_append_extract`, `extract_eq_extract_append_extract`,
`append_inj_left`, `extract_append_eq_right`, `extract_append_eq_left`,
`extract_append_size_left`, `extract_append_size_add`, `extract_append`,
`extract_append_size_add'`, `extract_extract`, `getElem_extract_aux`,
`getElem_extract`, `extract_eq_extract_left`, `extract_add_one`,
`extract_add_two`, `extract_add_three`, `extract_add_four`, `append_assoc`,
`toList_empty`, `copySlice_eq_append`, `data_set`,
`set_eq_push_extract_append_extract`, `append_toByteArray_singleton`,
`extract_zero_max_size`, `append_eq_append_iff_of_size_eq_left`,
`append_eq_append_iff_of_size_eq_right`, `size_push`, `ext_getElem`,
`List.toByteArray_inj`, `extract_eq_extract_iff_getElem`, `getElem!_push_lt`,
`getElem!_push_eq`, `getElem!_push`, `getElem!_eq_data_getElem!`, `size_set!`,
`getElem!_set!_self`, `getElem!_set!_ne`, `getElem!_set!`, `getElem_set!_ne`,
`getElem_set!_self`, `getElem_set!`.

INFERRED: the extraction-and-concatenation half of that list
(`size_extract`, `getElem_extract`, `extract_append*`, `extract_extract`,
`ext_getElem`) is exactly what a span-digest argument needs, and it is present.
The gap is elsewhere: there is no `foldl` lemma, no `toList` lemma beyond
`toList_empty`, and nothing about `ByteArray.extract` interacting with a
search. Any P1 theorem about "the span at `[a,b)` is these bytes" is buildable;
any theorem about "the search found every occurrence" is from scratch.

### 2.5 Other byte carriers

`Array UInt8`, `List UInt8`, and `Vector UInt8 n` were not benchmarked as
carriers in their own right, because §2.3 already prices the conversions and
because the `Vector` lemma surface (642 theorems in
`Init/Data/Vector/Lemmas.lean`, MEASURED) makes `Vector` the natural choice for
fixed-width state rather than for a 417 KB document. Not measured: `Vector UInt8 n`
construction at document scale. Stated as not measured rather than estimated.

---

## 3. Loops and recursion

Source `$BENCH\Bin\LoopBench.lean`, n = 10,000,000 except `LA` (n = 1,000,000).
Logs `$LOGS\loopbench-median.txt`, `$LOGS\loopbench2-median.txt`. Median of 3.
Accumulator is `UInt64` unless the row says otherwise.

| Case | Construct | inner_ms | Tag |
| --- | --- | --- | --- |
| `L8-Partial` | `partial def`, tail recursive | **4.15** | MEASURED |
| `L2-NatFoldRev` | `Nat.foldRev` | **4.18** | MEASURED |
| `L7-WellFounded` | `termination_by n` / `decreasing_by omega` | **4.36** | MEASURED |
| `L1-NatFold` | `Nat.fold` | 6.23 | MEASURED |
| `L6-Structural` | structural recursion on `Nat`, tail position | 6.42 | MEASURED |
| `L5-ForInRange` | `for i in [0:n] do` with `mut` in `Id.run do` | 7.96 | MEASURED |
| `L9-Fuel` | fuel-indexed structural recursion | 12.64 | MEASURED |
| `LA-VectorOfFn` | `Vector.ofFn` then `Array.foldl` (n = 10^6) | 14.45 | MEASURED |
| `L4-ArrayFoldl` | `(Array.range n).foldl` | 67.66 | MEASURED |
| `L3-ListFoldl` | `(List.range n).foldl` | **120.76** | MEASURED |

### 3.1 Does well-founded recursion cost anything at runtime?

**No.** MEASURED: `L7-WellFounded` at 4.36 ms is faster than `L6-Structural`
at 6.42 ms and within noise of `L8-Partial` at 4.15 ms. The accessibility proof
is not being carried at runtime.

READ, the mechanism, two independent pieces:

1. `Init/WF.lean:135` declares `noncomputable def fix (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=`
   — the logical `WellFounded.fix` is noncomputable, so it is never what runs.
2. `Init/WFComputable.lean:88` declares `@[specialize] public def fixC {α : Sort u} {C : α → Sort v} {r : α → α → Prop}`
   whose body at `Init/WFComputable.lean:90` is `F x (fun y _ => fixC hwf F y)`.
   Note the `_`: the recursive call **discards the `r y x` proof**. It is
   installed as the compiled implementation by
   `Init/WFComputable.lean:95`, `@[csimp] public theorem fix_eq_fixC : @fix = @fixC := by`.

INFERRED, from L7 and those two lines: `termination_by` is free at runtime.
There is no performance reason to prefer `partial` over a well-founded
definition, and `partial` costs the equational lemmas and the induction
principle. The only remaining reason to write `partial` is that the
termination argument is genuinely unavailable.

### 3.2 Which constructs unfold cleanly in proofs

| Construct | Unfolding lemmas | Source | Tag |
| --- | --- | --- | --- |
| `Nat.fold` | `Nat.fold_zero`, `Nat.fold_succ`, both `@[simp]` | `Init/Data/Nat/Fold.lean:268`, `:271`; the definition is `Init/Data/Nat/Fold.lean:30` `@[specialize] def fold {α : Type u} : (n : Nat) → (f : (i : Nat) → i < n → α → α) → (init : α) → α` | READ |
| `Nat.foldRev` | `Nat.foldRev_zero`, `Nat.foldRev_succ`, both `@[simp]` | `Init/Data/Nat/Fold.lean` (same file, foldRev block) | READ |
| `Vector.ofFn` | `Vector.getElem_ofFn`, `@[simp, grind =]` | `Init/Data/Vector/OfFn.lean:27` `@[simp, grind =] theorem getElem_ofFn {α n} {f : Fin n → α} (h : i < n) :`; definition `Init/Data/Vector/Basic.lean:320` | READ |
| `for i in [0:n] do` | **`Std.Legacy.Range.forIn_eq_forIn_range'`, `@[simp]`** | `Init/Data/Range/Lemmas.lean:88` `@[simp] theorem forIn_eq_forIn_range' [Monad m] (r : Range)` | READ |
| `List.foldl` | the full `Init/Data/List/Lemmas.lean` surface, 700 theorems | MEASURED count | READ |

**Correction to received wisdom.** `for i in [0:n] do` **does** have an
unfolding lemma in 4.33.1, and it is `@[simp]`. The catch is the import: the
`[a:b]` notation comes from `Init/Data/Range/Basic.lean:70`
(`syntax:max "[" withoutPosition(term ":" term) "]" : term`), a different
module from `Init.Data.Range.Lemmas` where the lemma lives. A file that uses
the notation without importing the lemmas module sees no `@[simp]` rule and
concludes, wrongly, that the loop is opaque.

This does not overturn the existing house rule against `Id.run do` with
`for`/`mut` in definitions a theorem is stated about. The rewrite lands you in
`List.forIn` over `List.range' 0 n 1`, which is a monadic fold — provable, but
a longer road than `Nat.fold_succ`. The rule stands; the reason should be
"longer road", not "impossible".

### 3.3 Accumulator type dominates everything else

| Case | Accumulator | inner_ms | Tag |
| --- | --- | --- | --- |
| `LD-UInt32Acc` | `UInt32`, `Nat.fold` | 6.31 | MEASURED |
| `LB-NatAcc` | `Nat`, values up to 5·10^13 (below the scalar bound) | 8.17 | MEASURED |
| `LI-NatSmall` | `Nat` with `% 1000000` each step | 28.00 | MEASURED |
| `LC-BitVec32Acc` | `BitVec 32`, `+ BitVec.ofNat 32 i` | **2608.62** | MEASURED |
| `LH-NatBignum` | `Nat` held above 2^199 by `% (2^200)` | **3262.46** | MEASURED |

And the SHA-256-shaped comparison — rotate, xor, shift, add, no `Nat`
conversion inside the loop, 10^7 iterations:

| Case | Word type | inner_ms | Tag |
| --- | --- | --- | --- |
| `LG-UInt64Words` | `UInt64` | **8.40** | MEASURED |
| `LE-UInt32Words` | `UInt32` | **8.90** | MEASURED |
| `LF-BitVec32Words` | `BitVec 32` | **6572.78** | MEASURED |

**INFERRED, and this is the most consequential number in the document:**
`BitVec 32` costs 6572.78 ms against `UInt32`'s 8.90 ms for identical word
operations, a factor of 6572.78 / 8.90 = **738×**.

This refutes a prediction currently standing in the SHA-256 proof-graph
document (§2, "Measured baseline"), which predicts that an `Impl` over
`BitVec 32` runs "within one order of magnitude" of `Fast`, on the reasoning
that 32-bit values stay inside Lean's scalar `Nat` range. The reasoning about
the range is correct — `LB-NatAcc` at 8.17 ms confirms that small `Nat`s are
free — and the conclusion is still wrong by two orders of magnitude. The cost
is not bignums. `BitVec w` is a structure wrapping `Fin (2^w)` wrapping `Nat`
(§4), it has no unboxed runtime representation, and every operation allocates a
boxed structure and goes through modular `Nat` arithmetic. `UInt32` has a
native machine representation and does not.

`LH-NatBignum` at 3262.46 ms against `LI-NatSmall` at 28.00 ms is the separate
bignum effect: 3262.46 / 28.00 = 116× for `Nat` values pushed above the scalar
bound. Both effects are real; for 32-bit words the boxing effect is the larger
one by 6×.

---

## 4. Boxing and scalars

### 4.1 The type chain

READ, all from `Init/Prelude.lean`:

| Type | Line | Declaration | Wraps |
| --- | --- | --- | --- |
| `Fin n` | 2324, 2332 | `structure Fin (n : Nat) where` / `val : Nat` | `Nat` + proof |
| `BitVec w` | 2376, 2382 | `structure BitVec (w : Nat) where` / `toFin : Fin (hPow 2 w)` | `Fin (2^w)` |
| `UInt32` | 2615, 2623 | `structure UInt32 where` / `toBitVec : BitVec 32` | `BitVec 32` |
| `USize` | 2789 | `structure USize where` | `BitVec System.Platform.numBits` |
| `Char` | 2856, 2858 | `structure Char where` / `val : UInt32` (plus a `valid` field) | `UInt32` + proof |
| `ByteArray` | 3417, 3429 | `structure ByteArray where` / `data : Array UInt8` | `Array UInt8` |
| `String` | 3537, 3541 | `structure String where ofByteArray ::` / `toByteArray : ByteArray` | `ByteArray` + validity |

So `BitVec n` *is* `Fin (2^n)` *is* `Nat`, exactly as the SHA-256 document
says. `UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize` are each a one-field structure
over the corresponding `BitVec`, and each is given a native runtime
representation by extern attributes rather than by its declaration.

`UInt32.toBitVec` is the structure projection itself — it is the field at
`Init/Prelude.lean:2623` — with a runtime override attached at
`Init/Prelude.lean:2626`, `attribute [extern "lean_uint32_to_nat"] UInt32.toBitVec`.
(READ.) In proofs it is a projection and reduces by `rfl`; at runtime it is a
native conversion, not a heap operation.

### 4.2 The scalar bound for `Nat`

READ, `include/lean/lean.h:1475`:

```c
#define LEAN_MAX_SMALL_NAT (SIZE_MAX >> 1)
```

On a 64-bit host that is 2^63 − 1. The mechanism is a tagged pointer with one
tag bit:

- `include/lean/lean.h:334` — `static inline LEAN_ALWAYS_INLINE uint8_t lean_is_scalar(lean_object * o) { return ((size_t)(o) & 1) == 1; }`
- `include/lean/lean.h:335` — `static inline lean_object * lean_box(size_t n) { return (lean_object*)(((size_t)(n) << 1) | 1); }`

INFERRED, from that and rows `LB-NatAcc` (8.17 ms, values ≈ 5·10^13) and
`LH-NatBignum` (3262.46 ms, values ≈ 2^199): a `Nat` below 2^63 is an
immediate value with no allocation and no refcount traffic; above it, a heap
GMP object at 116× the cost. `UInt8`/`UInt16`/`UInt32`/`UInt64`/`USize`/`Bool`
are unboxed — supported by `LE`/`LG` at 8.90/8.40 ms for 10^7 word operations,
which is ~0.9 ns per iteration and cannot involve allocation.

`Float` was not measured and is not relevant to this repository's carriers.

**`BitVec n` is the exception that matters.** It is a structure, not a scalar,
and `LF-BitVec32Words` prices it at 738× `UInt32` (§3.3).

---

## 5. Kernel reduction

Source files under `$BENCH\kernel\` (default options) and `$BENCH\kernel2\`
(with `set_option maxRecDepth 100000` and `set_option maxHeartbeats 1000000`).
Runner `$BENCH\run-kernel.ps1` / `run-kernel2.ps1`: `lake env lean <file>`,
three runs, median wall, killed at 180 s. Logs `$LOGS\kernel-median.txt`,
`$LOGS\kernel2-median.txt`, plus per-run `$LOGS\<name>.run<N>.txt`.

### 5.1 Default options: everything fails

MEASURED, `$LOGS\kernel-median.txt`. With **default** `maxRecDepth`, every
`decide` and every `rfl` in the battery failed with exit 1 and the message
`maximum recursion depth has been reached`:

| File | Status |
| --- | --- |
| `k1a_bitvec_decide.lean` (`by decide`) | exit 1, `maximum recursion depth has been reached` |
| `k1c_bitvec_rfl.lean` (`by rfl`) | exit 1, same |
| `k1d_uint32_decide.lean`, `k1f_uint32_rfl.lean` | exit 1, same |
| `k2a_string_decide.lean`, `k2c_string_rfl.lean`, `k2d_string_neq.lean`, `k2e_string_toList.lean` | exit 1, same |
| `k3a_list_decide.lean`, `k3c_list_rfl.lean`, `k3d_list_neq_decide.lean`, `k3e_list_eq_decide.lean` | exit 1, same |
| `k1b_bitvec_kernel.lean` (`by decide +kernel`) | **ok**, 587 ms |
| `k1e_uint32_kernel.lean` | **ok**, 574 ms |
| `k2b_string_kernel.lean` | **ok**, 3253 ms |
| `k3b_list_kernel.lean` | **ok**, 1584 ms |

INFERRED: `decide +kernel` is not merely faster in some cases, it is the only
variant that works at all at default settings for anything of this size. That
is because the elaborator's `whnf` has a recursion-depth budget and the kernel
does not use it. `Init/Tactics.lean:1416` documents the difference:
*"`decide +kernel` uses kernel for reduction instead of the elaborator."* (READ.)

### 5.2 With limits raised

MEASURED, `$LOGS\kernel2-median.txt`, median wall of 3. The baseline row is a
file containing only the two `set_option` lines and `example : True := trivial`;
subtract it to get the reduction cost.

| File | Check | median wall_ms | minus baseline | Tag |
| --- | --- | --- | --- | --- |
| `m0_baseline.lean` | `trivial` | **586** | — | MEASURED |
| `m1b_bitvec_kernel.lean` | 64-round `BitVec 32` loop, `decide +kernel` | 589 | **3** | MEASURED |
| `m1c_bitvec_rfl.lean` | same, `rfl` | 596 | 10 | MEASURED |
| `m1a_bitvec_decide.lean` | same, `decide` | 598 | 12 | MEASURED |
| `m1f_uint32_rfl.lean` | 64-round `UInt32` loop, `rfl` | 605 | 19 | MEASURED |
| `m1d_uint32_decide.lean` | same, `decide` | 621 | 35 | MEASURED |
| `m3d_list_neq_decide.lean` | `List UInt8` 4096 ≠, differs at index 251 | 785 | **199** | MEASURED |
| `m3a_list_decide.lean` | `List UInt8` 4096 `==`, `decide` | 2586 | **2000** | MEASURED |
| `m3c_list_rfl.lean` | same, `rfl` | 3086 | 2500 | MEASURED |
| `m2f_string_eq_kernel.lean` | 1 KiB `String` `==`, `decide +kernel` | 3538 | **2952** | MEASURED |
| `m2a_string_decide.lean` | 1 KiB `String` `==`, `decide` | 5552 | **4966** | MEASURED |
| `m2c_string_rfl.lean` | same, `rfl` | 5739 | 5153 | MEASURED |
| `m2d_string_neq.lean` | 1 KiB `String` ≠, differs at the last byte | 5994 | 5408 | MEASURED |
| `m2e_string_toList.lean` | `s1.toList.length = 1024` by `decide` | **>3 min (killed at 180 s)** | — | MEASURED |

### 5.3 What this means

INFERRED, from `m1a`/`m1b`/`m1d`: a **64-round loop over 32-bit words is
essentially free in the kernel**, 3–35 ms above baseline, and `BitVec 32`
(3 ms) is *cheaper* than `UInt32` (35 ms) here. That is the exact inversion of
the runtime ranking in §3.3: `BitVec` reduces well in the kernel because it is
`Nat` all the way down and the kernel has GMP-backed `Nat` literals; `UInt32`
has to go through its structure. This is a positive result for the
`Spec`/`Impl` over `BitVec` and `Fast` over `UInt32` split — each layer is
cheap in the place it is used.

INFERRED, from `m3a`/`m3d`: comparing two 4096-element `List UInt8` costs
2000 ms when they are equal and 199 ms when they differ at index 251. `decide`
on lists is proportional to how far it gets, not to the length. A negative
known-answer test is cheap; a positive one is not.

INFERRED, from `m2a`/`m2f`/`m2e`: **`String` is the expensive carrier in the
kernel.** A 1 KiB string equality is 2952 ms by `decide +kernel` and 4966 ms by
`decide`, against 2000 ms for a 4096-byte list — so per byte, `String` costs
roughly 4966/1024 = 4.85 ms per byte via `decide` against 2000/4096 = 0.49 ms
per byte for `List UInt8`, a factor of about 10. And `s1.toList.length = 1024`
did not finish in 180 seconds. The kernel model of `String` is `List Char`
under a UTF-8 encoding relation (`Init/Prelude.lean:3541`, `:3557`), and
forcing it is very expensive.

INFERRED: any known-answer test that reduces a `String` in the kernel is
budget-hostile. Keep kernel-side checks on `ByteArray`/`List UInt8`, put the
hex spelling on the executable side, and never write a `decide` over
`String.toList`.

`maxHeartbeats` was never the binding limit in this battery; `maxRecDepth` was,
and only for the elaborator-side tactics.

---

## 6. Hashing and maps

### 6.1 What exists in 4.33.1

READ: `Std.HashMap` is `structure HashMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where`
at `Std/Data/HashMap/Basic.lean:64`. `Std.TreeMap` is
`structure TreeMap (α : Type u) (β : Type v) (cmp : α → α → Ordering := by exact compare) where`
at `Std/Data/TreeMap/Basic.lean:67`. `Std.HashSet`, `Std.ExtHashMap`,
`Std.TreeSet`, `Std.DHashMap`, `Std.DTreeMap` also exist. All require an
explicit import: with no imports, `#check @Std.HashMap` is
`Unknown identifier` (`$LOGS\probe.txt`, MEASURED); with `import Std.Data.HashMap`
it resolves (`$LOGS\probe2.txt`, MEASURED).

### 6.2 Lemma support — yes, decisively

| Lemma file | `theorem` count | Tag |
| --- | --- | --- |
| `Std/Data/HashMap/Lemmas.lean` | **704** | MEASURED (counting command in §1.3) |
| `Std/Data/HashSet/Lemmas.lean` | **318** | MEASURED |
| `Std/Data/TreeMap/Lemmas.lean` | **1013** | MEASURED |

**Is there a verified-lemma story for `HashMap` in 4.33.1? Yes.** The file is
`Std/Data/HashMap/Lemmas.lean`, 704 theorems. Example, read at the line:
`Std/Data/HashMap/Lemmas.lean:175` is
`@[grind =] theorem size_insert [EquivBEq α] [LawfulHashable α] {k : α} {v : β} :`. (READ.)
Note the typeclass gate: the lemmas assume `[EquivBEq α]` and `[LawfulHashable α]`,
so a custom key type must discharge lawfulness before any of the 704 apply.

### 6.3 Cost at 10^5 `String` keys

Source `$BENCH\Bin\MapBench.lean`, keys `s!"whatwg-streams-anchor-{i}"` for
i < 100000, built before the timed region. Log `$LOGS\mapbench-median.txt`,
median of 3. All MEASURED.

| Case | Operation | inner_ms |
| --- | --- | --- |
| `M4-TreeMapInsert` | 100,000 `Std.TreeMap.insert` | 26.11 |
| `M1-HashMapInsert` | 100,000 `Std.HashMap.insert` | 28.27 |
| `M3-HashSetInsert` | 100,000 `Std.HashSet.insert` | 30.04 |
| `M2-HashMapLookup` | build, then 100,000 `get?` | 36.26 |
| `M6-SortedArrayBinary` | `Array.qsort` then 100,000 binary searches | 36.33 |
| `M5-TreeMapLookup` | build, then 100,000 `get?` | 42.33 |

INFERRED: at 10^5 string keys all six are within 26–43 ms, a spread of
42.33 / 26.11 = 1.6×. **Container choice is not a performance question at this
scale.** It is an axiom question and a lemma question (§8). The census has
about 248 algorithm blocks and 66 slot names — three orders of magnitude below
this benchmark — so any of these is instant there.

Row `M0-mkKeys` in the log reads 0.01 ms and is **not trustworthy**: the key
array is bound before the timed region and the compiler evidently shared the
subexpression. It is reported only to say it was discarded.

---

## 7. IO and process boundaries

Source `$BENCH\Bin\IoBench.lean`. Logs `$LOGS\iobench-median.txt`,
`$LOGS\iobench2-median.txt`, `$LOGS\iobench3-median.txt`. Median of 3. All
MEASURED unless tagged otherwise.

| Case | Operation | inner_ms | Answer |
| --- | --- | --- | --- |
| `I6-readBinFileBadBytes` | `readBinFile` of a 9-byte non-UTF-8 file | 0.13 | `9 bytes, validateUTF8=false, fromUTF8?=false` |
| `I1-readBinFile` | `readBinFile index.bs` | **0.20** | 417,076 |
| `I5-readFileBadBytes` | `readFile` of the same bad file | 0.20 | **throws** (text below) |
| `I4-validateUTF8` | `ByteArray.validateUTF8` on 417 KB | 0.61 | true |
| `I3-readBinThenFromUTF8` | `readBinFile` then `String.fromUTF8?` | 0.63 | true |
| `I2-readFile` | `readFile index.bs` | **0.98** | 417,076 |
| `IB-100reads` | 100 × `readBinFile index.bs` | 5.18 | 41,707,600 |
| `I7-walkDir` | `walkDir` over the pinned `Init/` tree | 12.54 | 724 entries |
| `I8-walkDirAndStat` | the same plus an `isDir` per entry | 14.57 | 630 files |
| `I9-processOutput` | one `IO.Process.output` spawn | 17.70 | exit=1 (see note) |
| `IB2-processOutput10` | ten spawns | 126.90 | — |
| `IC-childSpew4MB` | spawn a child writing 4,168,860 chars to stdout | 237.04 | `exit=0 stdoutChars=4168860 err=0` |

### 7.1 `readBinFile` vs `readFile`

INFERRED, from I1/I2: `readFile` costs 0.98 ms against `readBinFile`'s 0.20 ms
on this 417 KB file — 0.78 ms more, 4.9×. From I1/I4: a standalone
`ByteArray.validateUTF8` on the same bytes is 0.61 ms, which accounts for
essentially all of the difference. `readFile` = `readBinFile` + a full
validating scan.

READ, the failure behaviour, from `Init/System/IO.lean:1229` and `:1233`:

```lean
def readFile (fname : FilePath) : IO String := do
  ...
  | none => throw <| .userError s!"Tried to read file '{fname}' containing non UTF-8 data."
```

and the docstring at `Init/System/IO.lean:1226`: *"An exception is thrown if
the contents of the file are not valid UTF-8."*

MEASURED confirmation, row `I5-readFileBadBytes`, verbatim from
`$LOGS\iobench-median.txt`:

```
threw: Tried to read file '.../nonutf8.bin' containing non UTF-8 data.
```

It throws a catchable `IO.userError`. It does not panic and does not
lossily substitute. The test file was 9 bytes: `41 42 FF FE 80 43 0A C3 28`.

### 7.2 `walkDir` is `partial`

READ, `Init/System/IO.lean:1181`:

```lean
partial def walkDir (p : FilePath) (enter : FilePath → IO Bool := fun _ => pure true) : IO (Array FilePath) :=
```

INFERRED: being `partial`, it has no equational lemmas and no induction
principle, so nothing can be proved about it. It also lives in `IO`, which the
SHA-256 lane's constraints already forbid in library modules. Every gate that
walks the tree — `Gates.Common.regularFilesBelow` calls `directory.walkDir` —
is therefore permanently in the "tooling, not theorem" category. This is
consistent with what `Gates/` already claims for itself and is not a new
problem; it is a boundary that cannot be moved by effort.

Note also `#check @IO.FS.walkDir` is `Unknown constant` (`$LOGS\probe2.txt`,
MEASURED): the name is `System.FilePath.walkDir`
(`@System.FilePath.walkDir : System.FilePath → (optParam (System.FilePath → IO Bool) …) → IO (Array System.FilePath)`).

### 7.3 `IO.Process.output` buffering

READ, `Init/System/IO.lean:1544` and `:1553`:

```lean
def output (args : SpawnArgs) (input? : Option String := none) : IO Output := do
  ...
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
```

stdout is drained on a dedicated task while stderr is read on the calling
thread, which is the standard way to avoid a full-pipe deadlock.

MEASURED, row `IC-childSpew4MB`: a child writing 4,168,860 characters was
captured in full, `exit=0`, `err=0`, in 237.04 ms. No truncation, no deadlock.

MEASURED, rows `I9`/`IB2`: process spawn costs 17.70 ms once and 126.90 ms for
ten, i.e. about 12.7 ms each amortised. INFERRED, with `IB-100reads` (100 file
reads in 5.18 ms, 0.05 ms each): **a process spawn costs about 245× a file
read** (12.7 / 0.052). Any gate that shells out per file is paying that.

Caveat on I9/IA: those two invocations returned `exit=1` with stderr *"The
system cannot find the path specified."* — a Windows `cmd.exe /c` argument
quoting artefact, not a Lean fault. The spawn itself succeeded (the exit code
and stderr came back), so the timing is a valid spawn measurement, but the
child did no work. `IC-childSpew4MB` is the row that demonstrates successful
large-output capture.

---

## 8. Axiom reach of candidate APIs — the constraint that dominates the rest

This section was not in the brief's list. It is here because it is the single
largest determinant of which APIs P1 may use, and because it can be measured in
one command.

The repository's axiom ceilings, from the "Gates" section of the root agent
router: `propext` and `Quot.sound` for `WhatwgStreams/` and
`WhatwgStreamsTest/`, plus `Classical.choice` for `Gates/` and named audit
modules. So a declaration reaching `Classical.choice` may be used in `Gates/`
and may **not** be used in the semantic tree.

Command: `lake env lean axioms2.lean` and `lake env lean json_axioms.lean`.
Logs `$LOGS\axioms2.txt`, `$LOGS\json-axioms.txt`. All rows MEASURED — this is
`#print axioms` output, quoted.

### 8.1 Inside the semantic ceiling (`propext` / `Quot.sound` or nothing)

| Declaration | Reported axioms |
| --- | --- |
| `String.utf8ByteSize` | *does not depend on any axioms* |
| `String.toUTF8` | *does not depend on any axioms* |
| `String.ofList` | *does not depend on any axioms* |
| `String.decEq` | *does not depend on any axioms* |
| `ByteArray.push` | *does not depend on any axioms* |
| `ByteArray.get!` | *does not depend on any axioms* |
| `ByteArray.set!` | *does not depend on any axioms* |
| `ByteArray.size` | *does not depend on any axioms* |
| `ByteArray.copySlice` | *does not depend on any axioms* |
| `ByteArray.extract` | *does not depend on any axioms* |
| `List.toByteArray` | *does not depend on any axioms* |
| `List.foldl`, `Array.foldl`, `List.range` | *does not depend on any axioms* |
| `ByteArray.toList` | `[propext]` |
| `Vector.ofFn` | `[propext]` |
| `Array.range`, `String.push`, `String.append`, `String.intercalate` | `[propext]` |
| `String.Slice.split` | `[propext]` |
| `ByteArray.foldl` | `[propext, Quot.sound]` |
| `Nat.fold`, `Nat.foldRev` | `[propext, Quot.sound]` |
| `Std.HashMap.insert`, `Std.HashMap.get?`, `Std.HashSet.insert` | `[propext, Quot.sound]` |

### 8.2 Over the semantic ceiling (`Classical.choice`)

| Declaration | Reported axioms |
| --- | --- |
| `String.length` | `[propext, Classical.choice, Quot.sound]` |
| `String.toList` | `[propext, Classical.choice, Quot.sound]` |
| `String.splitOn` | `[propext, Classical.choice, Quot.sound]` |
| `String.split` | `[propext, Classical.choice, Quot.sound]` |
| `String.trimAscii` | `[propext, Classical.choice, Quot.sound]` |
| `String.replace`, `String.find`, `String.startsWith` | `[propext, Classical.choice, Quot.sound]` |
| `String.toSlice` | `[propext, Classical.choice, Quot.sound]` |
| `String.Slice.toString`, `.foldl`, `.drop`, `.take`, `.lines` | `[propext, Classical.choice, Quot.sound]` |
| `String.dropEnd` | `[propext, Classical.choice, Quot.sound]` |
| `String.Pos.Raw.get` | `[propext, Classical.choice, Quot.sound]` |
| `String.fromUTF8?` | `[propext, Classical.choice, Quot.sound]` |
| `ByteArray.validateUTF8` | `[propext, Classical.choice, Quot.sound]` |
| `Std.TreeMap.insert`, `Std.TreeMap.get?` | `[propext, Classical.choice, Quot.sound]` |
| `Lean.Json.parse`, `Lean.Json.compress` | `[propext, Classical.choice, Quot.sound]` |

### 8.3 What follows

INFERRED, and this is the second most consequential finding:

1. **Effectively the entire `String`-facing API reaches `Classical.choice`,
   including the whole `String.Slice` API.** Note the shape: `String.Slice.split`
   is clean at `[propext]`, but `String.toSlice` — the only way to obtain a
   `Slice` from a `String` — is not. Cleanliness of an individual slice
   combinator is therefore worthless; the entry point taints the chain.
2. **The `ByteArray` API is almost entirely clean.** `push`, `get!`, `set!`,
   `size`, `copySlice`, `extract` reach no axioms at all; `toList` and `foldl`
   stay inside the ceiling.
3. `Std.HashMap` is inside the ceiling; `Std.TreeMap` is not. If a map is
   needed in the semantic tree, it is `HashMap`, and this is a hard constraint,
   not a preference.
4. `Lean.Json.parse` reaches `Classical.choice` and so **may not appear in
   `WhatwgStreams/` or `WhatwgStreamsTest/` under the current ceiling.**

This corroborates, from the other direction, the SHA-256 lane's existing
ruling R-3 that `Classical.choice` be admitted only for exactly-named
string-facing declarations. The measurement shows why that ruling was
necessary: there is no string-facing route that avoids it.

Caveat on method: `#print axioms` reports the transitive closure of a
definition, including the axioms used by its termination proofs. A
`Classical.choice` here means "this constant's elaboration reached it", which
is exactly what the repository's axiom gate checks, so the reading is the
operative one.

---

## 9. Recommendations

Each is a recommendation, not a ruling, and each names the evidence row it
rests on.

### 9.1 The P1 census generator

**Carrier for the file: `ByteArray`, obtained by `IO.FS.readBinFile`.**
Rests on I1 vs I2 (0.20 ms vs 0.98 ms), on §8.1 (`readBinFile`'s output is
consumed by an axiom-clean API while every `String` route is not), and on the
fact that the census rows are anchored *by byte span* — a `String` index is a
character index (X3/X4: 416,886 characters against 417,076 bytes; 190
characters are multi-byte) and converting between them is exactly the class of
error the census must not make.

**Finding anchors: a byte-level search over `ByteArray` with a total
accessor.** Rests on F1 (8.36 ms for the whole file), on T6 vs T7 (the total
`byteAt` is not slower than `bs[i]!`), and on §8.1 (the whole path is axiom-
clean). The `String.splitOn` route (F2, 2.66 ms) is faster but yields no
offsets; the `Array Char` route (F4, 16.65 ms) is both slower and offset-wrong.

**Search for `<div algorithm`, not `<div algorithm>`.** Rests on the corpus
measurement in §1.5: the bare literal occurs 229 times, the prefix 248 times.
A census built on the closing-bracket spelling silently omits 19 blocks.

**Span digests through the in-tree SHA-256 over `ByteArray`.** Rests on H1
(229 spans, 374,064 bytes, 7.98 ms) and H1b (extraction 0.13 ms). The whole
census digest pass costs under 10 ms compiled. Do not do it under `#eval`: E5
prices the same work at 1447 ms, 171× (§1.8).

**Making anchor lookup total and provable.** Use `Nat.fold` over
`bs.size` with the total `byteAt` (`if h : i < bs.size then bs[i] else 0`)
rather than `for … in [0:n]` with `mut`. Rests on: T8 is the fastest measured
line-span variant (0.47 ms); `Nat.fold_zero`/`Nat.fold_succ` are `@[simp]`
(`Init/Data/Nat/Fold.lean:268`, `:271`); and `Nat.fold` is inside the ceiling
(§8.1). The relevant `ByteArray` extraction lemmas exist (`size_extract`,
`getElem_extract`, `extract_append*`, `ext_getElem` — §2.4), so a theorem of
the form "the row at `[a,b)` denotes exactly these bytes" is reachable. A
theorem of the form "the search found every occurrence" is not supported by any
existing lemma and must be built.

Note the §3.2 correction if a `for` loop is nonetheless wanted: it *is*
unfoldable, via `@[simp] forIn_eq_forIn_range'` at
`Init/Data/Range/Lemmas.lean:88`, provided `Init.Data.Range.Lemmas` is
imported. The road is longer than `Nat.fold`, not blocked.

### 9.2 The WPT replay runner

**JSON in 4.33.1 exists only as `Lean.Json`.** READ:
`inductive Json where` at `Lean/Data/Json/Basic.lean:180`;
`def parse (s : String) : Except String Lean.Json :=` at
`Lean/Data/Json/Parser.lean:286`. There is no JSON under `Init/` or `Std/`.
It works: `#eval (Lean.Json.parse "{\"a\":[1,2,3],\"b\":null}").toOption.isSome`
prints `true` (MEASURED, `$LOGS\json-axioms.txt`).

**It may not be used in the semantic tree.** MEASURED:
`'Lean.Json.parse' depends on axioms: [propext, Classical.choice, Quot.sound]`.
That is over the `WhatwgStreams/` ceiling. It is admissible in `Gates/` and in
exactly-named audit modules only.

Cost was not measured — no WPT JSON corpus was available to this seat, and I
will not estimate. What *is* measured and bears on it: importing
`Lean.Data.Json` and running nine `#print axioms` plus one `#eval` took 1071 ms
wall (`$LOGS\json-axioms.txt`), so the import itself is roughly 1 s, against
586 ms for a bare `Init` baseline (§5.2) — about 0.5 s of extra import cost per
file that imports it. Lemma support: zero; there are no theorems about `Json`.

INFERRED recommendation: treat WPT manifest parsing as a **tooling boundary**,
outside the semantic tree — parse in `Gates/`-class code (or ahead of time into
a generated, digest-sealed table under `generated/`), and let the semantic
tree consume first-order data it can reason about. This matches the
representation rule that canonical content is first-order data and foreign
answers are typed decisions on the tape.

### 9.3 The SHA-256 Impl/Fast split — only what the DAG does not already say

The SHA-256 proof-graph document already forbids `BitVec 32` in definitions
`Fast` calls, already forbids `xs[i]!`, already forbids `Id.run do` with
`for`/`mut` where a theorem is stated, and already recommends `Nat.fold`,
`Vector.ofFn`, `byteAt`, and reasoning through `bs.data`. All of that is
confirmed by the measurements above and is not repeated.

Four things it does not say:

1. **The `BitVec 32` penalty is 738×, not "within one order of magnitude".**
   §3.3, rows `LE-UInt32Words` (8.90 ms) and `LF-BitVec32Words` (6572.78 ms).
   The document's §2 prediction is refuted. The prohibition it protects is
   already correct and becomes stronger; only the predicted magnitude changes.
   Whoever holds that document should record the refutation, since the
   prediction is written there as a thing to be measured at S1.1.

2. **The kernel ranking is the inverse of the runtime ranking.** §5.2: a
   64-round `BitVec 32` loop reduces in 3 ms above baseline while the same
   `UInt32` loop costs 35 ms. That is a positive argument for the three-layer
   split beyond proof shape: `Spec`/`Impl` over `BitVec` is *cheaper* in the
   place the kernel runs, and `Fast` over `UInt32` is cheaper in the place the
   executable runs. The split is not a compromise; each side wins where it is
   used.

3. **Keep every known-answer test off `String`.** §5.2: a 1 KiB `String`
   equality costs 2952 ms (`decide +kernel`) to 4966 ms (`decide`), and
   `s1.toList.length = 1024` did not finish in 180 s, while a 4096-byte
   `List UInt8` equality is 2000 ms and an *unequal* pair is 199 ms. KATs
   belong on `ByteArray`/`List UInt8`; the hex spelling is an executable-side
   convenience with no kernel obligation. Corollary: prefer stating a KAT so
   that the interesting case is a *disequality* where one is available — the
   kernel stops at the first difference (`m3d`, 199 ms against `m3a`, 2000 ms).

4. **`decide +kernel` is not optional at default settings.** §5.1: every
   `decide` and every `rfl` in the battery failed with
   `maximum recursion depth has been reached` under default `maxRecDepth`,
   while `decide +kernel` passed. A stage that plans a `rfl` KAT must budget a
   `set_option maxRecDepth` as part of the plan, or use `decide +kernel`.

### 9.4 Cross-cutting

**Do not build on `Substring`.** It is deprecated
(`Init/Data/String/Substring.lean:556`, `@[deprecated Substring.Raw (since := "2025-11-16")]`),
carries no validity invariant (`Init/Prelude.lean:3614`), and has 3 theorems in
the entire `Init/Data/String` subtree (§1.3).

**`Gates.Common`'s `List Char` policy is sound but expensive.** The stated
reason — reading the same on every toolchain minor, never depending on byte
positions — is vindicated by §1.1: the byte-position API churned hard in this
release and `splitOn` did not. The cost is X3 (6.67 ms per `toList` of the spec
file) and F4 (16.65 ms for a whole-file `Array Char` search against 8.36 ms for
bytes). For gates over small files that is invisible. For the P1 census over
417 KB it is 2× on the search and it loses the byte offsets the census is
anchored by, so P1 should not inherit it.

---

## 10. Traps

### 10.1 Silent panics and non-panics

| API | Behaviour | Source | Tag |
| --- | --- | --- | --- |
| `ByteArray.get!` | **panics** out of bounds — *"Panics if the index is out of bounds."* | `Init/Data/ByteArray/Basic.lean:66`, `:69` | READ |
| `ByteArray.set!` | **does NOT panic** — *"If the index is out of bounds, the array is returned unmodified."* Confirmed in the runtime: `include/lean/lean.h:1206–1215` returns `a` unchanged | `Init/Data/ByteArray/Basic.lean:93`, `:96` | READ |
| `ByteArray.toUInt64LE!` | **panics twice**: `assert! bs.size == 8` at `Init/Data/ByteArray/Extra.lean:21`, then eight `get!` | `Init/Data/ByteArray/Extra.lean:20–21` | READ |
| `String.Pos.Raw.get` | **does not panic** on an invalid position; returns `default : Char`. Docstring `Init/Data/String/Basic.lean:1878`: *"If `p` is not a valid position, returns the ..."* | `Init/Data/String/Basic.lean:1878`, `:1893` | READ |
| `String.Pos.Raw.get!` | **model and runtime disagree.** Docstring at `Init/Data/String/Basic.lean:1933` says *"Panics if `p` is not a valid position"*, but the Lean body at `Init/Data/String/Basic.lean:1949` is `\| s => Pos.Raw.utf8GetAux s.toList 0 p` — the same total function as `get`. Only the extern panics | `Init/Data/String/Basic.lean:1933`, `:1947`, `:1949` | READ |
| `String.fromUTF8!` | **panics** — `Init/Data/String/Basic.lean:192` | READ |

**The `!` suffix is not a reliable panic marker in 4.33.1.** `get!` panics,
`set!` silently no-ops, `String.Pos.Raw.get!` panics only in compiled code and
returns `'A'` in the kernel. A proof that relies on `get!`'s model behaviour is
proving something the executable does not do.

### 10.2 Where `decide` blows up

- **Default `maxRecDepth` kills everything non-trivial.** §5.1: 12 of 12
  `decide`/`rfl` files failed with `maximum recursion depth has been reached`.
- **`String` in the kernel.** §5.2: 1 KiB equality 2952–5408 ms;
  `s1.toList.length = 1024` **>3 min, killed at 180 s**.
- **Equal lists are far worse than unequal ones.** §5.2: 2000 ms vs 199 ms for
  4096 bytes.
- **`native_decide` / `bv_decide` are not an escape**: they close through
  `Lean.ofReduceBool`, which the repository forbids everywhere.

### 10.3 Deprecations that become errors under `--wfail`

The build is `lake --wfail build` for the SHA-256 lane, so every deprecation
warning below is a build failure today, not a future one. All MEASURED from the
compiler's own warnings in `$LOGS\probe.txt` / `$LOGS\probe2.txt`.

| Deprecated | Replacement | Type change |
| --- | --- | --- |
| `String.get` | `String.Pos.Raw.get` | namespace only |
| `String.get!` | `String.Pos.Raw.get!` | namespace only |
| `String.get?` | `String.Pos.Raw.get?` | namespace only |
| `String.trim` | `String.trimAscii` | `String → String` becomes `String → String.Slice` |
| `String.dropRight` | `String.dropEnd` | `String → Nat → String` becomes `… → String.Slice` |
| `String.takeRight` | `String.takeEnd` | to `String.Slice` |
| `String.dropRightWhile` | `String.dropEndWhile` | to `String.Slice` |
| `String.takeRightWhile` | `String.takeEndWhile` | to `String.Slice` |
| `String.trimLeft` | `String.trimAsciiStart` | to `String.Slice` |
| `String.trimRight` | `String.trimAsciiEnd` | to `String.Slice` |
| `String.stripPrefix` | `String.dropPrefix` | to `String.Slice` |
| `String.stripSuffix` | `String.dropSuffix` | to `String.Slice` |
| `String.toSubstring` | `String.toRawSubstring` | returns `Substring.Raw` |
| `Substring` (type) | `Substring.Raw` | — |
| `Substring.toString` | `Substring.Raw.toString` | namespace only |
| `String.posOf` | `String.find` | returns `s.Pos`, takes a `Pattern` |
| `String.validateUTF8` | `ByteArray.validateUTF8` | namespace only |
| `String.mk` | `String.ofList` | namespace only |
| `Std.Iter.size` | `Std.Iter.length` | universe change |

The `String.Slice`-returning ones are the dangerous class: the code still
compiles after a mechanical rename only if the call site accepts a `Slice`. A
site that needs a `String` must add `.toString`/`.copy`, which is a **copy**
(`Init/Data/String/Basic.lean:801`, `def Slice.copy (s : Slice) : String :=`)
and which drags `Classical.choice` in (§8.2).

Two more that are not deprecated but will bite:

- **`ByteArray.mkEmpty` does not exist.** It is `ByteArray.emptyWithCapacity`
  (`Init/Prelude.lean:3437`). MEASURED: `#check @ByteArray.mkEmpty` is
  `Unknown constant`.
- **`IO.FS.walkDir` does not exist.** It is `System.FilePath.walkDir`.
  MEASURED: `#check @IO.FS.walkDir` is `Unknown constant`.

### 10.4 `String.length` is characters, `String.utf8ByteSize` is bytes

MEASURED on `index.bs`: `String.length` = **416,886**, `String.utf8ByteSize` =
**417,076**. They differ by 190 on this file. Both are constant time
(X4 0.00 ms, X5 0.01 ms) and both are cached
(`Init/Prelude.lean:3532–3535`, READ), so there is no performance signal to
tell you which one you called. A census that anchors "by byte span" and
computes offsets with `String.length` will be wrong by 190 bytes at the end of
the file and by a varying amount in the middle, and every digest will still
verify against itself.

`String.length` also reaches `Classical.choice` while `String.utf8ByteSize`
reaches no axioms at all (§8) — so under the semantic ceiling, the byte-count
answer is the only one available anyway.

### 10.5 Aliasing turns a linear loop quadratic

§2.2: 100,000 `set!` on a unique array is 0.29 ms; the same loop with a fresh
alias taken each iteration is 257.01 ms, 886× worse, and it grows superlinearly
(798.51 ms at 200,000). The alias can be introduced by something as innocuous
as returning the array in a tuple, capturing it in a closure, or keeping a
"previous" binding for a comparison. There is no warning and no type-level
signal.

### 10.6 Benchmark hazards worth knowing

Two of my own measurements were wrong before they were right, and both failure
modes will recur for anyone benchmarking Lean:

1. **`pure (f ())` evaluates `f ()` at the call site.** Timing an `IO` action
   built that way measures nothing. Force inside the timed region with
   `IO.lazyPure`.
2. **The compiler shares subexpressions across the timed boundary.** Rows
   `M0-mkKeys` (0.01 ms to build 100,000 formatted strings) and `X1-toUTF8`
   (0.01 ms to copy 417 KB) are both artefacts of this. If a number is
   physically impossible, it is.

---

## 11. Appendix — the scratch package

Reproduction: create `$BENCH`, place the files below, put
`leanprover/lean4:v4.33.1` in `lean-toolchain`, copy `index.bs` in, then
`lake build textbench bytebench loopbench mapbench iobench`.

| Path | Role |
| --- | --- |
| `$BENCH\lakefile.toml` | package `r0bench`, one `lean_lib R0Bench`, five `lean_exe` |
| `$BENCH\lean-toolchain` | `leanprover/lean4:v4.33.1` |
| `$BENCH\R0Bench\Sha256.lean` | `Gates/Sha256.lean` copied verbatim, renamespaced, CLI dropped |
| `$BENCH\R0Bench\Timing.lean` | `timeIt` / `timePure` (the `IO.lazyPure` version) |
| `$BENCH\R0Bench\Text.lean` | cases T1–T9, F1–F4, H1, H1b |
| `$BENCH\Bin\TextBench.lean` | text driver |
| `$BENCH\Bin\ByteBench.lean` | cases B1–BD |
| `$BENCH\Bin\LoopBench.lean` | cases L1–LI |
| `$BENCH\Bin\MapBench.lean` | cases M0–M6 |
| `$BENCH\Bin\IoBench.lean` | cases I1–IC |
| `$BENCH\evalbench.lean` | interpreter cases E1–E5, definitions local to the file |
| `$BENCH\kernel\*.lean` | kernel battery, default options |
| `$BENCH\kernel2\*.lean` | kernel battery, `maxRecDepth 100000`, `maxHeartbeats 1000000` |
| `$BENCH\probe.lean`, `probe2.lean`, `probe3.lean` | `#check` sweeps that produced the deprecation warnings in §1.1 |
| `$BENCH\axioms2.lean`, `json_axioms.lean` | the `#print axioms` sweeps of §8 |
| `$BENCH\run-bench.ps1` | 3-run median driver for the executables |
| `$BENCH\run-kernel.ps1`, `run-kernel2.ps1` | 3-run median driver for the kernel files, 180 s kill |
| `$BENCH\verify-cites.ps1` | prints every line cited in this document |
| `$BENCH\nonutf8.bin` | 9 bytes `41 42 FF FE 80 43 0A C3 28` |

The definitions that carry the load, inline so the numbers can be read against
them:

```lean
-- the total byte accessor used by T7, T8, F1 (no panic path)
@[inline] def byteAt (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0

-- T8, the fastest measured line-span variant
def lineSpansNatFold (bs : ByteArray) : Array (Nat × Nat) :=
  let step := Nat.fold bs.size
    (fun i _ (acc : Array (Nat × Nat) × Nat) =>
      if byteAt bs i == 0x0A then (acc.1.push (acc.2, i), i + 1) else acc)
    (Array.mkEmpty 9000, 0)
  if step.2 < bs.size then step.1.push (step.2, bs.size) else step.1

-- F1, the anchor search
private def matchesAtBytes (hay needle : ByteArray) (start : Nat) : Bool := Id.run do
  for j in [0:needle.size] do
    if byteAt hay (start + j) != byteAt needle j then return false
  return true

def findAllBytes (hay needle : ByteArray) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  if needle.size == 0 || hay.size < needle.size then return out
  for i in [0:hay.size - needle.size + 1] do
    if matchesAtBytes hay needle i then out := out.push i
  return out

-- LE / LF, the 738x pair (identical shape, different word type)
@[inline] def rotrU (x : UInt32) (k : UInt32) : UInt32 := (x >>> k) ||| (x <<< (32 - k))
def le (n : Nat) : UInt32 :=
  Nat.fold n (fun _ _ acc => (rotrU acc 7 ^^^ rotrU acc 18 ^^^ (acc >>> 3)) + 0x9e3779b9) 1

@[inline] def rotrB (x : BitVec 32) (k : Nat) : BitVec 32 := (x >>> k) ||| (x <<< (32 - k))
def lf (n : Nat) : BitVec 32 :=
  Nat.fold n (fun _ _ acc => (rotrB acc 7 ^^^ rotrB acc 18 ^^^ (acc >>> 3)) + 0x9e3779b9) 1

-- BB, the copy-on-write trap: a fresh alias every iteration
def setAliasedEvery (n : Nat) : Nat := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do out := out.push 0
  let mut acc := 0
  for i in [0:n] do
    let alias := out
    out := out.set! i (UInt8.ofNat (i % 256))
    acc := acc + alias.size % 2
  return acc

-- the kernel loop, instantiated at BitVec 32 and at UInt32
def kloopB : Nat -> BitVec 32 -> BitVec 32
  | 0, x => x
  | n + 1, x => kloopB n ((x >>> 7 ||| x <<< 25) ^^^ (x + 0x9e3779b9))
-- example : kloopB 64 1 = BitVec.ofNat 32 2893450364 := by decide +kernel
```

The timing helper, since every `inner_ms` in this document depends on it being
right:

```lean
def timeIt (label : String) (act : IO String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let answer ← act
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}\t{(t1 - t0).toFloat / 1000000.0}\t{answer}"

def timePure (label : String) (f : Unit → String) : IO Unit :=
  timeIt label (IO.lazyPure f)
```

---

## 12. Decisions this document supports

Each line is one recommendation and the evidence row it rests on. None is a
ruling.

1. **P1 reads `index.bs` with `IO.FS.readBinFile` and keeps it as `ByteArray`.**
   — rows `I1` (0.20 ms) vs `I2` (0.98 ms); §8.1 (`ByteArray` API is axiom-clean,
   the `String` API is not).
2. **P1 finds anchors by byte search over `ByteArray`, with a total `byteAt`,
   not by `String` splitting or `Array Char`.** — rows `F1` (8.36 ms) vs `F4`
   (16.65 ms); rows `T6`/`T7` (the total accessor is not slower); §8.1.
3. **P1's anchor pattern is `<div algorithm`, not `<div algorithm>`.** — the
   corpus measurement in §1.5: 248 vs 229, 19 blocks carry an attribute.
4. **P1 computes offsets with `String.utf8ByteSize`, never `String.length`.** —
   §10.4: 417,076 vs 416,886 on this file; §8 (`length` reaches
   `Classical.choice`, `utf8ByteSize` reaches nothing).
5. **P1's scanning loops are `Nat.fold`, not `for … in [0:n]` with `mut`.** —
   row `T8` (fastest, 0.47 ms); `Init/Data/Nat/Fold.lean:268`, `:271` (`@[simp]`
   unfolding); §8.1 (inside the ceiling). The `for` form is provable via
   `Init/Data/Range/Lemmas.lean:88` if wanted, at a longer road.
6. **P1's span digests use the in-tree SHA-256 over `ByteArray.extract`, and are
   never computed under `#eval` in a gate.** — rows `H1` (7.98 ms compiled) and
   `E5` (1447 ms interpreted, 171×).
7. **`Substring` is not used anywhere new.** — `Init/Data/String/Substring.lean:556`
   (deprecated); 3 theorems in the subtree (§1.3).
8. **If the semantic tree needs a map, it is `Std.HashMap`, not `Std.TreeMap`.** —
   §8.1/§8.2 (`HashMap` `[propext, Quot.sound]`, `TreeMap` reaches
   `Classical.choice`); §6.2 (704 theorems in `Std/Data/HashMap/Lemmas.lean`);
   §6.3 (performance is not the deciding factor at this scale).
9. **WPT manifest JSON is parsed outside the semantic tree.** — `Lean.Json.parse`
   depends on `[propext, Classical.choice, Quot.sound]` (§8.2); zero theorems
   about `Json`; it lives only under the `Lean` library
   (`Lean/Data/Json/Parser.lean:286`).
10. **The SHA-256 lane's `Fast` layer stays on `UInt32`, and the DAG's §2
    prediction should be recorded as refuted.** — rows `LE` (8.90 ms) and `LF`
    (6572.78 ms), 738×, not "within one order of magnitude".
11. **The SHA-256 lane's `Spec`/`Impl` over `BitVec` is cheap where it is used.**
    — §5.2: `m1b` 3 ms above baseline for a 64-round `BitVec 32` loop, against
    `m1d` 35 ms for the same loop on `UInt32`.
12. **Known-answer tests are stated over `ByteArray`/`List UInt8` and never over
    `String`.** — §5.2: 1 KiB `String` equality 2952–5408 ms;
    `s1.toList.length = 1024` >3 min; 4096-byte list equality 2000 ms.
13. **Every stage that plans a `decide` or `rfl` known-answer test budgets a
    `set_option maxRecDepth`, or uses `decide +kernel`.** — §5.1: 12 of 12
    default-option `decide`/`rfl` files failed with
    `maximum recursion depth has been reached`.
14. **`termination_by` is preferred over `partial` wherever a measure exists.** —
    row `L7` (4.36 ms) vs `L8` (4.15 ms) vs `L6` (6.42 ms);
    `Init/WFComputable.lean:88`, `:90`, `:95` (the accessibility proof is
    discarded by the compiled `fixC`).
15. **Byte-mutating loops thread one uniquely-referenced array and take no alias
    inside the loop.** — rows `B3b` (0.29 ms) vs `BB` (257.01 ms), 886×;
    `include/lean/lean.h:1197–1204`.
16. **Gates that shell out per file are recognised as spending ~245 file reads per
    spawn.** — rows `IB2` (12.7 ms per spawn) and `IB` (0.05 ms per read).
17. **`ByteArray.set!` is never used as a bounds check.** — it returns the array
    unmodified out of bounds and does not panic
    (`Init/Data/ByteArray/Basic.lean:93`; `include/lean/lean.h:1206–1215`).

## 13. What was left out

- **WPT JSON parsing cost.** No pinned WPT corpus was available to this seat.
  Not estimated.
- **`Vector UInt8 n` at document scale**, and `Array UInt8` as a standalone
  document carrier. §2.3 prices the conversions; the carriers themselves were
  not benchmarked.
- **`Float`.** Not relevant to any carrier this repository uses.
- **`Std.ExtHashMap`, `Std.DHashMap`, `Std.TreeSet` performance.** Existence and
  lemma-file sizes only.
- **Multi-threaded or `Task`-parallel variants** of anything.
- **`String.Slice` performance under sustained slicing**, e.g. a slice-of-a-slice
  chain. Only the single-level `split`/`drop`/`take` costs in §1.4 were measured;
  §8.2 makes the whole family unusable in the semantic tree anyway.
- **Memory footprints.** Only wall time was measured. The kernel battery's peak
  RSS was not recorded, so this document cannot speak to the 6 GB figure the
  fips202 lane reports for its SHA3 kernel KATs.
