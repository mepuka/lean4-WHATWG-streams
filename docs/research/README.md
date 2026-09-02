# Research record

Authored research deliverables, one file per pass, each self-contained with
its commands, log paths, and pins. This index carries the findings that
later decisions cite, so that nothing depends on a session transcript.

## R0 (released 2026-09-01)

| Document | State | Findings that decisions rest on |
| --- | --- | --- |
| `2026-09-01-lean4-nlp-learnings.md` | landed | lean4-nlp at `2820c11b` shares this toolchain and zero-dependency posture and records no numbers of its own; every figure was re-measured. Lean 4.33.1's `String.Pos` API (`next`, `get`, `extract`, `Substring.toString`, also `String.length` and `splitOn`) depends on `Classical.choice`; `ByteArray.extract`, `ByteArray.get!`, `String.toUTF8`, `String.ofList`, `List.toByteArray` are axiom-free (reproduced by the coordinator with `#print axioms`). Fuel-bounded scanning with fuel = size + 1 replaces `partial` and gives an ordering theorem by induction on fuel. Index accumulation into `Array (Array _)` is up to 868x slower than packed counting sort at one bucket and slower than it when buckets outnumber entries; crossover near four entries per bucket. The tokenizer measured 7.24 MiB/s single-threaded and 3.2–3.8x on eight workers. |
| `2026-09-01-lean-stdlib-strategy-and-performance.md` | in progress | text and byte carriers, loop forms, boxing, kernel reduction costs, hash maps, IO, measured in a scratchpad package on this host |
| `2026-09-01-web-reification-targets-survey.md` | in progress | scored ranking of web and internet standards as Lean reification targets by expressivity and cross-runtime compatibility; dependency-ordered programs; prior art; top five |

## Decisions already taken on this evidence

- The P1 census generator carries `ByteArray` and `Nat` offsets, never
  `String` positions, so its definitions stay under the semantic ceiling.
- SHA-256 `Hex` (lane S1, ruling R-3) is a `List Char` producer wrapped by
  `String.ofList`, with length theorems stated on the list form; the
  exact-admission list is expected to be empty.
- Benchmarks in this repository copy lean4-nlp's calibrated-median
  methodology and keep a retired implementation as a differential oracle
  before any timing is reported.

## How to add a pass

One file per document, named by date and subject. Every number carries its
command and log path; every external fact carries a URL and fetch date;
every claim about another repository carries its commit. No line-numbered
citation into the protected authored documents (the citation gate rejects
it). Update the table above in the same change.
