# What lean4-nlp learned about text processing in Lean 4

Status: R0-B, lean4-nlp at 2820c11b77dccb16acfecf9569c847706f546763, read 2026-09-01.

Source: https://github.com/mepuka/lean4-nlp, cloned `--depth 200` to a scratchpad clone.
HEAD commit message: `perf(bench): benchmark stable bucket layouts`, dated 2026-09-01.
275 `.lean` files; 159 of them under `Nlp/` and `Bench/`.

This document reports what transfers to the census generator (parsing a 417 KB Bikeshed
`index.bs` into byte-span-anchored rows) and to the later bounded WPT runner.

---

## 1. Toolchain and dependency facts

| Fact | Value | Source |
| --- | --- | --- |
| Toolchain | `leanprover/lean4:v4.33.1` | `lean-toolchain` (single line) |
| External dependencies | none | `lake-manifest.json`, `"packages": []` |
| Library root | `NlpCore`, roots `["Nlp"]` | `lakefile.toml:8-11` |
| `precompileModules` | `false` | `lakefile.toml:6` |
| Benchmark executables declared | 17 | `lakefile.toml:17-100` |
| Third-party data | EVALB fixtures; Unicode UCD 17.0.0 tables | `THIRD_PARTY_NOTICES.txt:4-27` |

**The toolchain matches the target repository exactly (v4.33.1) and the dependency count matches
exactly (zero).** Every technique below was developed under the same constraints the target repo
operates under. There is no dependency to flag for any transferable piece.

One nuance: `Nlp/Core/Data/Interner.lean:1` imports `Std.Data.HashMap` and
`Nlp/Pipeline/Parallel.lean:3` imports `Std.Tactic.Do`. `Std` ships inside the Lean toolchain, so
these are not external requires — the manifest is still empty.

Only 15 of the 17 benchmark targets are documented in the README (`README.md:96-112`);
`tokenregex-benchmark` and `stable-buckets-benchmark` are declared in `lakefile.toml:95-100` but
absent from that list. The README's benchmark documentation is stale relative to HEAD.

---

## 2. Headline finding: the axiom ceiling cuts through `String.Pos`

The target repo's ceiling is `propext` and `Quot.sound` — no `Classical.choice`. I measured the
axiom footprint of lean4-nlp's tokenizer directly (`lake env lean` on a scratch probe file in my
clone, at the recorded commit):

| Declaration | Axioms |
| --- | --- |
| `Nlp.Tokenize.Token.span_wf` | none |
| `Nlp.Tokenize.Token.span_end_le_source` | `propext` |
| `Nlp.Tokenize.Tokenization.ordered` | none |
| `Nlp.Tokenize.Token.span` | none |
| `Nlp.StableBuckets.build` | `propext`, `Quot.sound` |
| `Nlp.Tokenize.Cursor.start` | `propext`, `Quot.sound` |
| `Nlp.Tokenize.Cursor.next?` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `Nlp.Tokenize.Cursor.collect` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `Nlp.Tokenize.Tokenizer.tokenize` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `Nlp.Tokenize.Tokenizer.tokenize_wf` | `propext`, **`Classical.choice`**, `Quot.sound` |

I then traced where the classical dependency enters. It is not lean4-nlp's doing — it is Lean
4.33.1 core:

| Core declaration | Axioms |
| --- | --- |
| `String.Pos.next` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `String.Pos.get` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `String.extract` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `Substring.toString` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `String.fromUTF8?` | `propext`, **`Classical.choice`**, `Quot.sound` |
| `String.toUTF8` | none |
| `String.utf8ByteSize` | none |
| `String.Pos.Raw.byteIdx` | none |
| `ByteArray.get!`, `ByteArray.size`, `ByteArray.extract` | none |
| `Array.emptyWithCapacity`, `Array.set!` | none |

**Consequence for the census generator.** If the axiom ceiling is enforced strictly as
`{propext, Quot.sound}`, the generator cannot carry `String` and cannot use the validated
`text.Pos` cursor API that lean4-nlp's tokenizer is built on. It must carry `ByteArray` with `Nat`
offsets. That carrier is entirely axiom-free, and `ByteArray.extract` is exactly the operation a
SHA-256 span digest needs. This is the single most important thing to settle before writing the
generator, and it is cheap to settle: run `#print axioms` on the first spike.

This is a fact about Lean 4.33.1 core, so it will bite the target repo the same way it did here.
It is not a criticism of lean4-nlp, whose stated boundary (`README.md:439-442`) is about `sorry`,
`partial` and `unsafe`, not about `Classical.choice`.

---

## 3. Benchmark inventory

All 17 `Bench/*.lean` modules. "Compares" means the file times two or more carriers over one
fixture; "single-variant" means one kernel across fixture shapes.

| Module | Measures | Carriers compared | Recorded result | Lesson |
| --- | --- | --- | --- | --- |
| `Bench/Tokenize.lean` | Scanner byte/token throughput, 3 corpora | pure scanner vs checked effect x1 vs byte-weighted parallel x8 | no recorded result | Parallel corpus tokenization pays ~3-4x on 8 workers; adversarial near-miss lane is the design's stress test |
| `Bench/StableBuckets.lean` | Counting-sort layout vs nested `Array (Array _)` rows | 4 comparisons across 7 bucket/entry shapes | no recorded result | Packed layout wins hugely at low fan-out, **loses** when buckets ≫ entries |
| `Bench/Parallel.lean` | Chunked concurrency prototype | serial vs chunked traversal | no recorded result | Chunk-order result collection keeps output deterministic |
| `Bench/Pos.lean` | HMM POS tagging, 1024 docs x 128 tokens | pure vs checked serial vs checked parallel | no recorded result | Purity/concurrency comparison, not a layout one |
| `Bench/Morphology.lean` | Lemmatization, 2048 docs x 256 tokens | pure vs checked serial vs checked parallel | no recorded result | Same three-lane shape as Pos |
| `Bench/Unary.lean` | Unary-chain elimination | success path vs deliberate budget-rejection path | no recorded result | Times the *rejection* path too — budget failures must also be fast |
| `Bench/CompiledViterbi.lean` | Viterbi over 3 grammars | legacy indexed vs compiled dense vs compiled sparse pair layout | no recorded result | Asserts a *footprint* expectation (`Bench/CompiledViterbi.lean:217-219`), never a timing one |
| `Bench/Dependency.lean` | Eisner parsing, n = 16..96 | boxed semiring-generic vs unboxed labeled min-cost | no recorded result | Specialization measured against a generic reference with exact goal-bit parity |
| `Bench/Arborescence.lean` | Chu-Liu-Edmonds, n = 32..512 | single-variant, 9 topologies | no recorded result | Topology, not size, is what breaks this kernel |
| `Bench/EnhancedDependency.lean` | Enhanced UD graph construction, ~16k tokens | single-variant, 4 fixture shapes | no recorded result | Calibrated 25 ms batches, 7-sample median |
| `Bench/Ner.lean` | NER tagging, 6144 tokens/lane | per-sentence forms vs encode-once rich vs encode-once flat | no recorded result | Encode-once beats re-encoding per sentence |
| `Bench/Constituency.lean` | Sentence-range CKY, ~4096 tokens | materialized `Array.extract` slices vs zero-slice ranges | no recorded result | **Zero-slice ranges vs copying slices — the clearest carrier lesson in the repo** |
| `Bench/RegexNer.lean` | Bounded RegexNER matching | compiled matcher lanes | no recorded result | Budgets checked before matching |
| `Bench/TokenRegex.lean` | Bounded textual token-regex | compiled matcher lanes | no recorded result | Same bounded-matcher shape |
| `Bench/Numeric.lean` | Numeric normalization, 4774 and 19096 tokens | single-variant, 2 scales exactly 4x apart | no recorded result | Two scales 4x apart make superlinearity visible without a threshold |
| `Bench/TreeQuery.lean` | Tregex-style tree query, 4096 and 16384 nodes | single-variant, 2 scales 4x apart | no recorded result | Fixture built iteratively so the *builder* does not recurse (`Bench/TreeQuery.lean:69`) |
| `Bench/GraphQuery.lean` | Semgrex-style graph query, 4096 and 16384 nodes | single-variant, 2 scales 4x apart | no recorded result | Same 4x-scale idiom |

**Every row says "no recorded result", and that is a finding, not a gap in my reading.** See §4.

### Benchmark methodology worth copying

Two families, no shared helper — the scaffold is duplicated per file, deliberately, so a benchmark
pulls in no dependency (`Bench/TreeQuery.lean:119`, "Sort a small duration sample without adding
benchmark dependencies", and the same comment at `Bench/EnhancedDependency.lean:289`).

- **Family 1, calibrated-batch median** (`Arborescence`, `EnhancedDependency`, `GraphQuery`,
  `Numeric`, `TreeQuery`): two untimed warmups compared for equality, then calibrate the batch
  toward ~25 ms, then 7 batches, report median plus `[min, max]`. See
  `Bench/GraphQuery.lean:115-139` for the canonical `sample`/`calibrate` pair.
- **Family 2, fixed-repetition mean** (`CompiledViterbi`, `Constituency`, `Dependency`,
  `Morphology`, `Ner`, `Pos`, `Tokenize`, `Unary`): one warmup, N timed runs inside one
  `IO.monoNanosNow` pair, divide by N. See `Bench/Dependency.lean:123-134`.

Four invariants hold across all 17:

1. **`IO.monoNanosNow` everywhere.** `IO.monoMsNow` appears nowhere in `Bench/`.
2. **`IO.lazyPure` inside the timed loop**, so a pure value is recomputed per repetition rather
   than shared. `Bench/Tokenize.lean:243`, `Bench/GraphQuery.lean:121`.
3. **Every timed repetition's complete output is compared to the warmup snapshot**, and a mismatch
   throws. `Bench/Tokenize.lean:244-245`. An elided or unstable computation fails the run instead
   of producing a fast number.
4. **No machine-specific threshold is ever asserted.** Stated in the module docstring of nearly
   every bench file — `Bench/Tokenize.lean:8`, `Bench/Morphology.lean:7`, `Bench/Pos.lean:7-8`,
   `Bench/Ner.lean:10`, `Bench/Constituency.lean:7-9`, `Bench/Arborescence.lean:11`.

Supporting devices: `@[noinline]` on the observer functions so inlining cannot cross the timing
boundary (`Bench/Tokenize.lean:144`, `:153`, `:162`); a deterministic checksum mixer duplicated
byte-identically in 10 of 12 inspected files (`Bench/GraphQuery.lean:41-45`), avoiding runtime
hash seeding (`Bench/Ner.lean:91`); and fixtures fully materialized before the first timer starts
(`Bench/Tokenize.lean:105`).

**No benchmark reads from disk.** A grep for `IO.FS`, `readFile`, `FilePath`, `getStdin`,
`IO.Process` across all 17 `Bench/` files returns zero hits. Every corpus is synthesized in
memory. File I/O exists only in `Nlp/Pipeline/Files.lean`, `Nlp/Pipeline/Corpora.lean`,
`Nlp/Pipeline/Evalb.lean` and the test tree. This matters for the census generator: lean4-nlp has
**no measurement at all** of reading a 417 KB file off disk. That cost is unmeasured here.

---

## 4. Recorded numbers: there are none

I checked three places for numbers to quote.

1. **README.** No benchmark results section. Headings are at `README.md:1, 12, 69, 114, 288, 437,
   448, 473`; none is a results table.
2. **Committed result files.** `git ls-files` returns 11 non-`.lean` files: a CI workflow, three
   EVALB fixtures plus their licence, `README.md`, `THIRD_PARTY_NOTICES.txt`,
   `lake-manifest.json`, `lakefile.toml`, `lean-toolchain`. No log, CSV, or JSON of results.
3. **Commit messages.** 92 commits; 22 match `perf|bench|fast|speed|alloc|memory|optimi`. Exactly
   two commits in the whole history have a message body (`05ea14f`, `afe666e`), and neither
   carries a number.

**QUOTED rows in this document: zero.** lean4-nlp is a runnable measurement harness, not a
recorded-results repository. Every number below I produced myself.

That is a defensible choice given the "no machine-specific threshold" stance — but it means the
target repo inherits *methodology*, not *baselines*. If the census generator wants regression
detection rather than one-off timing, it will have to add the thing lean4-nlp deliberately did not:
a committed baseline. lean4-nlp's CI (`.github/workflows/ci.yml`) does not gate on performance.

---

## 5. RE-MEASURED numbers

Host: this Windows 11 box, 16 hardware threads, benchmark selected 8 workers (reported by
`Bench/Tokenize.lean:341-342, 352`). Build in the scratchpad clone, not in the target repo.

Build command (exit 0, 289 jobs):

```
lake build tokenize-benchmark stable-buckets-benchmark
```

Both executables built clean on v4.33.1 with no patching. Build log:
`…\scratchpad\build.log`. The single slowest module was `Nlp.Tokenize.Scanner` at 28s — the
Unicode classifier tables in `Nlp/Tokenize/Scanner.lean:44-146` are elaboration-heavy.

### 5.1 `tokenize-benchmark` — RE-MEASURED

Command: `.lake\build\bin\tokenize-benchmark.exe`, run 3 times.
Logs: `…\scratchpad\tokenize-run1.log`, `-run2.log`, `-run3.log`.
Values are the **median of three**. Checksums were byte-identical across all three runs in every
lane, so the workload is deterministic.

| Lane | Corpus | Path | Median MiB/s | Median tok/s | Median us |
| --- | --- | --- | --- | --- | --- |
| baseline | 2048 docs, 482,731 B, 99,310 tok | pure scanner | 7.24 | 1,562,220 | 63,569 |
| baseline | " | checked weighted x8 | 20.91 | 4,509,663 | 22,021 |
| web-heavy | 1024 docs, 716,750 B, 60,207 tok | pure scanner | 18.31 | 1,612,599 | 37,335 |
| web-heavy | " | checked weighted x8 | 52.55 | 4,628,193 | 13,008 |
| long web near-miss | 32 docs, 1,049,984 B, 524,512 tok | pure scanner | 4.73 | 2,477,476 | 211,712 |
| long web near-miss | " | checked weighted x8 | 16.15 | 8,460,608 | 61,994 |

Median parallel/serial speedup on 8 workers: baseline **3.19x**, web-heavy **3.41x**, near-miss
**3.80x**. Median tokenize-and-split speedup: **3.53x / 3.72x / 4.12x**.

**Extrapolation for the census generator.** The target's `index.bs` is 417 KB ≈ 0.398 MiB. At the
baseline single-threaded rate of 7.24 MiB/s that is **~55 ms**; at the web-heavy rate of 18.31
MiB/s, ~22 ms. So a full rule-based tokenization pass over the whole spec source is tens of
milliseconds, single-threaded, with no `partial` and no `unsafe`. Byte-span extraction over a
417 KB file is not a performance problem in Lean 4.33.1. Treat this as an order-of-magnitude
anchor, not a promise: the census generator's per-byte work differs from English tokenization, and
the MiB/s figure varies 4x across these three lanes on identical code.

Note the near-miss lane is the *slowest* in MiB/s and the *fastest* in tok/s — it is 1 MB of
pathological punctuation runs producing 524k tokens. It exists to catch rescanning; a linear
single-pass recognizer stays linear there (`Bench/Tokenize.lean:90-99`).

### 5.2 `stable-buckets-benchmark` — RE-MEASURED

Command: `.lake\build\bin\stable-buckets-benchmark.exe`, run 3 times.
Logs: `…\scratchpad\buckets-run1.log`, `-run2.log`, `-run3.log`.
The benchmark self-reports a median with `[min, max]` per run; the column below is the **median of
the three run-level ratios**. Ratio > 1 means the packed counting-sort layout is faster than the
nested `Array (Array _)` reference.

| Shape | Buckets | Entries | Median nested/packed ratio |
| --- | --- | --- | --- |
| all entries in one bucket | 1 | 16,384 | **868.11x** |
| uniform | 256 | 65,536 | **14.88x** |
| buckets ≫ entries | 65,536 | 4,096 | **0.82x** (packed loses) |
| low fan-out B/E=1 | 16,384 | 16,384 | 1.71x |
| low fan-out B/E=2 | 32,768 | 16,384 | 1.24x |
| low fan-out B/E=4 | 65,536 | 16,384 | 1.07x |
| low fan-out B/E=8 | 131,072 | 16,384 | **0.47x** (packed loses) |
| retained values, one bucket | 1 | 16,384 | **452.44x** |
| retained values, uniform | 256 | 65,536 | 10.01x |
| retained values, buckets ≫ entries | 65,536 | 4,096 | **0.34x** (packed loses) |
| three-column gather (layout excluded) | 256 | 65,536 | 1.13x |

Absolute times from run 1 for the two extremes: all-in-one-bucket nested build median 107,820 us
vs packed 125 us; buckets-≫-entries nested 410 us vs packed 478 us.

**The crossover is at roughly B/E = 4.** Below it the packed layout wins; above it the cost of
allocating and scanning the `bucketCount + 1` offsets array dominates and the nested representation
wins. The operator built this benchmark to find where their own optimization *loses*, and it does
lose, by up to 4x. That is the honest reading.

---

## 6. Text-processing primitives lean4-nlp settled on

### 6.1 Span representation

`Nlp/Core/Data/Span.lean:11-18`:

- `Span` is a bare `structure` of two `Nat` fields, `b` and `e`, half-open, **UTF-8 byte offsets**.
- `Span.WF span : Prop := span.b ≤ span.e`, with a `Decidable` instance at `:20-22`.
- The docstring at `:4-6` states the reason: spans "deliberately do not depend on Lean's evolving
  `String.Pos` interface."

That decoupling decision is exactly right for the target repo, and for a stronger reason than the
one stated: as §2 shows, `String.Pos` also drags in `Classical.choice`.

Identifier types are `def TokId := Nat`, `def SentId := Nat`, `def SymbolId := UInt32`
(`Nlp/Core/Data/Span.lean:25-34`) — transparent `def`s with derived instances, not wrapper
structures.

### 6.2 Tokenizer design: source-indexed positions, proof-carrying

`Nlp/Tokenize/Types.lean:65-69` is the central type:

```
structure Token (text : String) where
  private mk ::
  startPos : text.Pos
  endPos : text.Pos
  nonempty : startPos < endPos
  kind : TokenKind
```

The token is **indexed by the string it came from**, carries dependent `text.Pos` values (valid by
construction in 4.33.1), and carries a `nonempty` proof field. The constructor is private, so no
caller can manufacture an invalid token. Four theorems then come out almost free
(`Nlp/Tokenize/Types.lean:88-101`): `span_wf`, `span_nonempty`, `span_begin_le_source`,
`span_end_le_source` — each a one-line `exact`.

`Tokenization` (`:106-108`) pairs `text : String` with `tokens : Array (Token text)`, so the source
is retained for exact recovery and every offset is provably an offset into *that* string. Ordering
is executable: `ordered` at `:116-119` checks adjacent pairs only, with the docstring noting
"transitivity orders every later token as well."

The scanner is **byte-position-based, never char-list-based**. `Nlp/Tokenize/Scanner.lean:7-11`
states it: "The scanner never converts the source to a character list: it advances through Unicode
scalar values while retaining UTF-8 byte positions, and it uses an ASCII-first classifier for the
common English path. Maximal source runs stay as positions; only short split candidates are
temporarily sliced, and emitted forms are materialized on demand."

Three allocation disciplines are visible in that sentence and are the real lesson:

1. **ASCII-first dispatch.** `isPunctuation` / `isSymbol` / `isWordScalar`
   (`Nlp/Tokenize/Scanner.lean:159-171`) branch on `isAscii` first and only consult the large
   Unicode range tables (`:44-146`) on the non-ASCII path.
2. **Positions, not slices.** Runs are represented as position pairs; `Token.original`
   (`Nlp/Tokenize/Types.lean:84-85`) materializes the string **on demand**, and the projection
   columns `spans` / `forms` / `kinds` (`:134-143`) are separate struct-of-arrays materializations
   the caller opts into.
3. **Presized output.** `Array.emptyWithCapacity (text.utf8ByteSize / 4 + 1)`
   (`Nlp/Tokenize/Scanner.lean:829`) — one token per four bytes as the capacity heuristic.

### 6.3 How `partial` is avoided: fuel, everywhere

This is the house technique and it recurs in every scanning loop.

- `Scanner.scanNext` calls `scanNextAux` with fuel `text.utf8ByteSize + 1`
  (`Nlp/Tokenize/Scanner.lean:629-631`).
- `Cursor.collectAux` is structural on a `Nat` fuel argument
  (`Nlp/Tokenize/Scanner.lean:782-787`), driven by `collect` with the same
  `text.utf8ByteSize + 1` bound (`:827-829`), documented as "at most one iteration per source
  byte".
- `takeRest` uses the loop form `for _ in [0:text.utf8ByteSize] do … return`
  (`Nlp/Tokenize/Scanner.lean:200-212`) — a bounded `for` with early return instead of recursion.
- `UnionFind.findGo` takes fuel and `find` supplies `sets.size + 1`
  (`Nlp/Core/Data/UnionFind.lean:33-52`). The docstring at `:5-6` states the reason outright:
  "`find` is fuel-bounded by the number of nodes, so malformed parent cycles return `none` rather
  than introducing partial recursion."

The pattern is: **fuel bound = a size the data already carries, plus one; exhaustion returns
`none` or the accumulated output, never `panic`.** Because the bound is generous by construction,
exhaustion is unreachable in practice, but the totality checker does not need to know that.

Proofs are then done by induction on the fuel: `scanNextAux_piecesWF`
(`Nlp/Tokenize/Scanner.lean:601-626`) and `collectAux_ordered`
(`:789-824`) are both `induction fuel`. The top-level `Tokenizer.tokenize_wf`
(`:866-870`) is three lines because all the work is in those two.

A second device threads the *proof* through the loop rather than reconstructing it. `EndAfter`
(`Nlp/Tokenize/Scanner.lean:183-197`) is a position bundled with `after : start < position`, and
`EndAfter.next` rebuilds the proof by `String.Pos.lt_trans` at each step. So the scan loop carries
its own nonemptiness witness and the token constructor gets it for free.

### 6.4 String search and regex: own engine, Thompson NFA, no backtracking

`Nlp/Pattern/Regular.lean:49-62` defines `Regular Atom` with exactly six constructors: `empty`,
`epsilon`, `atom`, `alt`, `seq`, `star`. **No backreferences, no negation, no lookaround** — a
genuine regular language, so matching is total and decidable.

Two semantics are kept deliberately (`Nlp/Pattern/Regular.lean:4-7`): `Regular.Accepts`, the
denotational relation used by proofs, and `Regular.endpoints`, "a finite executable reference
matcher used to validate compiled automata." The compiled automaton is then checked against the
reference matcher rather than trusted.

Atoms are **symbolic predicates over absolute positions**, consumed through `holdsAt`, so
"neither representation owns or slices the underlying token column"
(`Nlp/Pattern/Regular.lean:6-7`). Matching is zero-copy.

`normalizeRange` (`Nlp/Pattern/Regular.lean:34-36`) clamps a caller range to the input size and
collapses inverted ranges, "never requires allocating an input slice" (`:33`), with two theorems
at `:39-46`.

Compilation is a bounded Thompson construction (`Nlp/Pattern/Automaton.lean:5-10`) with explicit
budgets as data — `maxStates := 65_536`, `maxEdges := 262_144`, `maxRules := 65_536`
(`:16-23`) — and search budgets `maxWork := 67_108_864`, `maxMatches := 1_048_576` (`:26-31`).
Every budget overrun is a typed `CompileError` constructor (`:34-48`), never a panic. The
`Automaton` constructor is private "so callers cannot manufacture invalid transition tables"
(`:10`).

Transitions are stored **CSR-style**: parallel `offsets` / `targets` / `atoms` arrays rather than
an array of adjacency arrays. See §8 for how they got there.

### 6.5 Stable bucketing: counting sort with no default value

`Nlp/Core/Data/StableBuckets.lean` is 114 lines and is the most directly reusable file in the
repository.

`Layout` (`:51-57`) is `bucketCount`, `entryCount`, `offsets : Array Nat`,
`sourceOrder : Array Nat`, with a private constructor. The invariant, stated at `:48-49`:
"`offsets` has exactly one terminal sentinel, and `sourceOrder` is a stable permutation of every
source ordinal."

`build` (`:94-132`) is a four-pass counting sort:

1. Validate every bucket key and report **the first invalid source ordinal deterministically**
   (`:102-107`).
2. Count (`:109-112`).
3. Prefix-sum into `offsets`, reusing the `counts` array as `cursors` (`:114-122`).
4. Stable fill of `sourceOrder` (`:124-131`).

Three properties matter for reuse:

- **All policy, capacity and key checks finish before any bucket-driven array is allocated**
  (docstring `:90-92`). A rejected input allocates nothing.
- **`offsets` capacity is checked against `USize.size`** (`:100-101`) with a typed
  `offsetCapacity` error — overflow is a domain error, not UB.
- **`gatherMap` (`:74-83`) projects a source-aligned column into bucket order without requiring a
  default value**, because it pushes into an `emptyWithCapacity` array rather than
  `replicate`-then-`set`. This is why the module's docstring (`:4-5`) says it builds the layout
  "without allocating or default-initializing any caller payload columns."

And it is axiom-clean: `propext`, `Quot.sound` only (§2).

### 6.6 Interning and identifier capacity

`Nlp/Core/Data/Interner.lean:14-16` is `Std.HashMap String UInt32` plus a reverse
`Array String`. The lesson is at `:6-8`: "insertion checks capacity before `UInt32.ofNat`, so
exhaustion is a typed error rather than a silent wrap at `2^32`." `Capacity` (`:21-23`) is a
`Nat` limit carrying a proof `limit ≤ UInt32.size`, so the check cannot be forgotten.
`WF` (`:76-77`) is the round-trip property: forward lookup then reverse lookup returns the name.

### 6.7 Parallelism: pure planner, `Task` executor, chunk-order results

`Nlp/Pipeline/Parallel.lean` separates planning from execution, stated at `:8-10`: "Planning is
pure and independently testable. Execution eagerly starts coarse chunks on dedicated threads, then
collects results in chunk order. The observed error is therefore the first error in chunk order,
not necessarily the first one in wall-clock time."

- **Planner.** `chunkPlan` (`:60-62`) for uniform work; `weightedChunkPlan` (`:142-145`) for
  skewed work — it builds the maximal grain-feasible partition (`grainChunkPlan`, `:76-95`) then
  groups atoms toward cumulative-weight targets (`balanceGrainChunks`, `:98-127`). Intended "for
  skewed inputs such as documents whose tokenization cost tracks UTF-8 byte size more closely than
  document count" (`:702-703`).
- **Executable checkers.** `validPlan` (`:511-519`), `weightedCoarsePlan` (`:527-532`),
  `balancedPlan` (`:535-543`), `coarsePlan` (`:579-580`), `boundedPlan` (`:600-601`) — each with a
  `@[simp]` theorem discharging it for the planner's own output (`:545-576`, `:582-597`,
  `:603-609`).
- **Executor.** `EIO.asTask action Task.Priority.dedicated` (`:669`), results collected by
  iterating the task array in order (`:674-678`). Errors cancel and drain every sibling before
  rethrowing (`:681-683`).
- **Nested parallelism is suppressed.** `workersFor` returns 1 when `env.parallelDepth ≠ 0`
  (`:620-624`).
- **Cancellation is cooperative** and cannot preempt a pure inner loop (`:12-13`); workers call
  `NLP.checkCancelled` between bounded units.
- The runtime **revalidates the plan before indexing** (`:647-648`, `:716-719`) — planning proofs
  exist, but execution still checks.

The proof style here uses `mvcgen` with explicit loop invariants (`:147-182`), which needs
`import Std.Tactic.Do` (`:3`).

### 6.8 Is any of this proof-bearing?

Yes, and the split is clean.

Proof-bearing: token span ordering and bounds (`Nlp/Tokenize/Types.lean:88-101`), whole-scan
ordering (`Nlp/Tokenize/Scanner.lean:838-843`, `:866-870`), chunk-plan contiguity, coverage,
grain, balance and worker bounds (`Nlp/Pipeline/Parallel.lean:474-609`), interner round-trip
(`Nlp/Core/Data/Interner.lean:80-83`), range normalization (`Nlp/Pattern/Regular.lean:39-46`).

Executable-only: the `StableBuckets` layout invariants are enforced by a private constructor and
runtime checks, not by theorems — `Nlp/Core/Data/StableBuckets.lean` contains no `theorem`. Same
for the automaton's transition tables.

**Verified constraint compliance.** I grepped all 159 `.lean` files under `Nlp/` and `Bench/` for
`partial`, `unsafe`, `native_decide`, `@[extern]`. Zero real hits — the eight matches are English
prose in docstrings (e.g. "a partial year-month value") or a local variable named `partials`
(`Bench/Parallel.lean:146`). The library and benchmarks are `partial`-free, `unsafe`-free,
`extern`-free, exactly as `README.md:439-440` claims.

**But the test suite is not.** `native_decide` appears on 731 lines across the `NlpTests/` tree
(my grep). lean4-nlp states this boundary itself at `README.md:444-446`: those checks "rely on
Lean's native compiler/runtime for evaluation; they should not be confused with fully
kernel-reduced proof terms." The target repo forbids `native_decide`, so **lean4-nlp's library
style transfers and its test style does not.**

---

## 7. Design decisions with commit citations

The history is 92 commits, all dated 2026-09-01, all with empty bodies except two. Reasons must be
read from the diffs and from docstrings, not from messages.

| Commit | Subject | Decision, as evidenced by the diff |
| --- | --- | --- |
| `21a12da` | `perf(pattern): pack automaton transition rows` | Replaced nested `Array (Array UInt32)` CSR accumulation with `StableBuckets.build`; `buildEpsilonCsr`/`buildAtomCsr` changed return type from a bare tuple to `Except CompileError _`, adding `transitionOffsetCapacity` and `transitionPackingInvariant` error constructors. Optimizing made the function fallible, and the fallibility was pushed into the domain error type rather than hidden. |
| `2820c11` (HEAD) | `perf(bench): benchmark stable bucket layouts` | Added `Bench/StableBuckets.lean` to measure the `21a12da` change *after* making it — and it found two shapes where the new layout loses. |
| `384c787` | `feat(core): add stable packed buckets` | Introduced `Nlp/Core/Data/StableBuckets.lean` as shared infrastructure before the automaton adopted it. |
| `90db903` | `perf(grammar): stage validation before allocation` | +125/-24 across `CompiledCNF.lean` and `Unary.lean`. The same principle later baked into `StableBuckets.build`: finish all checks before allocating. |
| `8810616` | `perf(dependency): eliminate Viterbi index overhead` | +160/-28; 105 of the added lines are tests. Performance change shipped with a larger test delta than code delta. |
| `b85d82b` | `perf(ner): remove indexed corpus staging` | Net -3 lines in `Nlp/Pipeline/Ner.lean` (17 changed) and +10 in its tests. A staging structure was deleted, not added. |
| `9e4893f`, `c193a3e` | adaptive compiled Viterbi, then benchmark | Adaptive dense/sparse pair layout added, benchmark added immediately after to compare all three layouts. |
| `71f3abe` | `perf(parse): add checked zero-slice Viterbi ranges` | The zero-slice range API that `Bench/Constituency.lean` later measures against materialized `Array.extract` slices. |

Recurring shape: **feature commit, then a `perf(...)` benchmark commit for the same subsystem,
then sometimes a `docs:` commit.** Benchmarks are written to *justify or falsify* a change already
made, not to guide it beforehand.

---

## 8. What lean4-nlp abandoned or got wrong

**1. Nested `Array (Array _)` bucket accumulation — abandoned at `21a12da`.**

The prior code in `buildEpsilonCsr` was:

```
let mut buckets : Array (Array UInt32) := Array.replicate stateCount #[]
for edge in edges do
  let source := edge.source.toNat
  buckets := buckets.set! source ((buckets.getD source #[]).push edge.target)
```

`buckets.getD source #[]` hands out a reference to the inner array while `buckets` still holds
one, so the refcount is ≥ 2 and `.push` **copies the whole inner bucket**. Cost is quadratic in
the size of the largest bucket. My re-measurement puts the penalty at **868x** in the
all-entries-in-one-bucket shape (§5.2) — the exact shape a skewed key distribution produces.

This is the most transferable negative result in the repository. Any census-generator code that
groups rows by a key — by section, by algorithm id, by `<div>` nesting depth — must not accumulate
into `Array (Array Row)` by index.

**2. But the replacement is not universally better, and the operator proved it.**

`Bench/StableBuckets.lean` includes low-fan-out and sparse shapes specifically to find the
crossover, and finds it at roughly B/E = 4. Beyond that the packed layout runs at **0.82x** and
**0.47x** of the nested one; the retained-value sparse case is **0.34x**. Building a
`bucketCount + 1` offsets array is a real cost when `bucketCount` dwarfs `entryCount`. Adopt
`StableBuckets` for dense keying; do not adopt it for sparse keying.

**3. The nested shape was a real prior implementation, not a strawman.** The comment at
`Bench/StableBuckets.lean:162-164` says so: "This is Unary's former retention shape: the nested
value rows remain the output. In particular, the timed path never pays to flatten them into a
second representation." The benchmark preserves the abandoned implementation as the reference and
asserts exact output parity against it (`requireBuildParity` `:253-265`,
`requireRetentionParity` `:267-279`, `requireGatherParity` `:324-331`) before timing anything.
**That is the right way to retire an implementation: keep it as the differential oracle.**

**4. `gatherMap` is not where the win is.** The three-column gather lane, with layout construction
excluded, measured **1.13x** median — essentially parity. All of the benefit is in *building* the
layout, none in *using* it. A reader who adopted `StableBuckets` for its gather API would get
nothing.

**5. Staged benchmarking arrived late.** All 17 benchmarks are dated 2026-09-01, most in the last
third of the history, several within minutes of HEAD. The measurement discipline is real but was
retrofitted; the `Bench/` methodology also drifted into two incompatible families (§3), with the
newer calibrated-median family not backported to the older mean-based files. `Bench/Tokenize.lean`
— the file most relevant to the target repo — is in the *older, weaker* family: fixed repetitions,
mean not median, no calibration. That is why I ran it three times and took a median by hand.

**6. Stale README.** Two of 17 benchmark targets are undocumented (§1).

No evidence of an abandoned char-list tokenizer, an abandoned backtracking regex engine, or a
reverted parallelism model. The `partial`-free, fuel-bounded, position-based approach appears to
have been the design from `0e8f6a0` (`feat(tokenize): add verified UTF-8 tokenization`) onward.

---

## 9. Transfer to the census generator

The census generator parses a 417 KB `index.bs` (~8,400 lines, 248 `<div algorithm>` blocks) into
rows anchored by byte span and SHA-256 span digest.

### 9.1 Transfers directly

| Technique | lean4-nlp file | Shape to reproduce |
| --- | --- | --- |
| Half-open byte-offset span as a two-`Nat` structure with a decidable `WF` | `Nlp/Core/Data/Span.lean:11-22` | Copy the shape verbatim: `structure Span where b : Nat; e : Nat`, `WF := b ≤ e`, `Decidable` by `unfold; infer_instance`. Do not wrap `String.Pos`. |
| Fuel-bounded scan, fuel = `size + 1` | `Nlp/Tokenize/Scanner.lean:629-631`, `:782-787`, `:827-829`; `Nlp/Core/Data/UnionFind.lean:33-52` | `scanAux : Nat → State → Array Row → Array Row`, structural on fuel, driven with `bytes.size + 1`. Satisfies the no-`partial` rule with no well-founded recursion obligation. |
| Bounded `for` with early return instead of inner recursion | `Nlp/Tokenize/Scanner.lean:200-212` | `for _ in [0:bytes.size] do … return` for maximal-run consumption. |
| Ordering theorem by induction on fuel | `Nlp/Tokenize/Scanner.lean:789-824`, `:838-843` | Prove `rows are ordered and non-overlapping` once over `collectAux`; the top-level theorem is then three lines. This is the census generator's main correctness property and it is provable at this exact shape. |
| Proof-carrying cursor | `Nlp/Tokenize/Scanner.lean:183-197` | An `EndAfter`-style bundle of a position with `start < position`, so block-nonemptiness is threaded, not re-derived. |
| Presized output array | `Nlp/Tokenize/Scanner.lean:829` | `Array.emptyWithCapacity 256` for 248 known blocks. `Array.emptyWithCapacity` is axiom-free. |
| ASCII-first classification | `Nlp/Tokenize/Scanner.lean:159-171` | Bikeshed source is overwhelmingly ASCII. Branch on `< 0x80` first; the non-ASCII path only needs to preserve bytes, not classify them. |
| Struct-of-arrays projections materialized on demand | `Nlp/Tokenize/Types.lean:84-85`, `:134-143` | Emit `spans : Array Span` always; materialize `text` per row only when the caller asks. A row's digest needs bytes, not a `String`. |
| Counting-sort grouping | `Nlp/Core/Data/StableBuckets.lean:94-132` | If rows are grouped by section or algorithm id, use this and not `Array (Array Row)`. Axiom-clean. Check B/E first (§8.2). |
| Typed capacity with a carried proof | `Nlp/Core/Data/Interner.lean:21-23` | If ids are `UInt32`, make the limit a structure carrying `limit ≤ UInt32.size`. |
| All checks before any allocation | `Nlp/Core/Data/StableBuckets.lean:90-92`, `:96-107` | A malformed spec should cost zero allocations and report the *first* offending byte offset deterministically. |
| Benchmark methodology | `Bench/GraphQuery.lean:115-139` | Two equality-checked warmups, calibrate to ~25 ms, 7 batches, median + range, `IO.lazyPure` in the loop, checksum every output. Use the *newer* family, not `Bench/Tokenize.lean`'s. |

### 9.2 Needs adaptation

**Carrier: `ByteArray`, not `String`.** This is the one substantial rewrite. lean4-nlp's
`Token (text : String)` with `text.Pos` fields gets its validity from Lean core's dependent
`String.Pos`, and that API costs `Classical.choice` (§2). To stay inside `{propext, Quot.sound}`:

- Carry `source : ByteArray` and `Nat` offsets. `ByteArray.get!`, `.size`, `.extract` are all
  axiom-free.
- Keep the *indexed-structure* idea — `structure Row (source : ByteArray)` with a private
  constructor and a `b < e` proof field — but let the bounds be `Nat` inequalities against
  `source.size` rather than `text.Pos` validity. The four free theorems of
  `Nlp/Tokenize/Types.lean:88-101` become four `omega`-sized obligations instead of four `exact`s.
- Decode UTF-8 yourself only where the census actually needs characters. Byte-span extraction and
  SHA-256 digesting need no decoding at all.
- Verify the choice with `#print axioms` on the first spike rather than trusting this document.

**Parallelism: probably skip it for the census.** `Nlp/Pipeline/Parallel.lean` is 650 lines and its
measured payoff on 8 workers is 3.2-3.8x (§5.1). A 417 KB single file at ~55 ms single-threaded
does not justify that machinery. Take one idea from it instead: byte-weighted rather than
count-based chunking (`Nlp/Pipeline/Parallel.lean:700-704`), and only if the WPT runner later
sweeps thousands of test files. If it is ever adopted, keep the two rules that make it
deterministic — collect in chunk order, and revalidate the plan before indexing.

**Budgets as data.** `Nlp/Pattern/Automaton.lean:16-31` puts limits in a `CompileConfig`
structure with typed error constructors. Adapt the shape; the values are automaton-specific.

### 9.3 Transfer to the WPT runner

The bounded runner replays JSON-ish and JS test files.

- **`Nlp/Pattern/Regular.lean:49-62` transfers well.** A six-constructor regular algebra with no
  backreferences is total and needs no backtracking budget. For scanning JS test files for
  `promise_test(...)` / `test(...)` shapes, this is the right power level.
- **The dual-semantics discipline transfers** (`Nlp/Pattern/Regular.lean:4-7`): keep a slow
  executable reference matcher and check the fast compiled one against it. Cheaper than proving
  the compiled matcher correct, and it is what lean4-nlp actually does.
- **Symbolic atoms over positions, never slices** (`:6-7`) — match against the byte array in place.
- **Budgets before matching** (`Nlp/Pattern/Automaton.lean:26-31`) — a WPT corpus is adversarial by
  nature; a `maxWork` bound checked up front is the right shape.
- **The near-miss fixture idea transfers** (`Bench/Tokenize.lean:90-99`). Build one deliberately
  pathological input — a long almost-matching `<div algorithm>` opener, an unterminated block —
  and keep it in the benchmark set. It is what catches accidental rescanning.

---

## 10. What does not transfer

| Item | Why not |
| --- | --- |
| `Token (text : String)` with `text.Pos` fields | Costs `Classical.choice` via Lean 4.33.1 core `String.Pos.next`/`get` (§2). The idea transfers; the carrier does not. |
| `String.extract`, `Substring.toString`, `String.fromUTF8?` | All classical (§2). Use `ByteArray.extract`. |
| `native_decide` regression style | 731 lines in `NlpTests/`; forbidden by the target's ceiling. Use `decide`, `rfl`, or `#guard` on small fixtures, accepting that some checks become too slow to kernel-reduce and must be restated. |
| `mvcgen` loop-invariant proofs (`Nlp/Pipeline/Parallel.lean:147-182`) | Not forbidden — `Std.Tactic.Do` ships with the toolchain — but it is a heavy tactic for the census generator's loops, which fuel-induction handles directly. |
| The whole `Nlp/Pipeline/Parallel.lean` executor | 650 lines and `Task`-based concurrency for a workload measured at ~55 ms single-threaded. |
| Everything NLP-specific | CKY, Eisner, Chu-Liu-Edmonds, HMM, unary elimination, EVALB, CoNLL-U/PTB readers — roughly 80% of the repository. No relevance to Bikeshed parsing. |
| Any performance baseline | None exists (§4). Only methodology transfers. |
| Disk-read cost model | No benchmark in the repo reads a file (§3). Reading 417 KB from disk is unmeasured here. |
| `Bench/Tokenize.lean`'s timing family | Fixed-repetition mean without calibration; superseded within the same repo by the calibrated-median family. Copy `Bench/GraphQuery.lean` instead. |

---

## 11. Open questions this document could not close

1. **Is the target's axiom ceiling enforced on definitions or only on theorems?** If only on
   theorems, `String.Pos` remains usable and lean4-nlp's tokenizer transfers almost verbatim. If
   on definitions too, the `ByteArray` rewrite in §9.2 is mandatory. I did not read the target's
   gate configuration, since the citation rules bar me from citing those files by line.
2. **Disk-read cost for a 417 KB file.** Unmeasured in lean4-nlp and unmeasured by me.
3. **SHA-256 throughput over ~248 spans.** lean4-nlp contains no SHA-256 implementation, so
   nothing here bears on the target's `Sha256/` module.
4. **I re-measured 2 of 17 benchmarks.** The other 15 are inventoried from source only; their
   "no recorded result" entries mean the repository records none, not that they fail.

---

## Appendix: reproduction

```
git clone --depth 200 https://github.com/mepuka/lean4-nlp
cd lean4-nlp
git rev-parse HEAD                       # 2820c11b77dccb16acfecf9569c847706f546763
lake build tokenize-benchmark stable-buckets-benchmark
.lake/build/bin/tokenize-benchmark
.lake/build/bin/stable-buckets-benchmark
```

Both built and ran clean on Lean 4.33.1 on Windows 11 with no source changes. Elapsed build:
289 jobs, dominated by `Nlp.Tokenize.Scanner` at 28s.

Axiom probe (a scratch file placed in the clone, then deleted):

```
lake env lean ZZAxiomProbe.lean
```

with `#print axioms` on each declaration named in §2.
