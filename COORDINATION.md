# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-01 (P0 bootstrap).

## Who is active

| Agent | Working on |
| --- | --- |
| Claude (coordinator, P0) | bootstrap: package, routers, gates, pins, documents |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `Sha256/**`, `Sha256.lean`, `test/contracts/sha256.contract.md`, `vendor/nist-cavp-sha256/**`, `vendor/nist-fips-180-4/**`, `generated/vendor-manifest.tsv`, `LICENSE`, `lakefile.toml`, `WhatwgStreamsTest.lean`, `WhatwgStreamsTest/Audit/AxiomGate.lean` (Sha256 tree rows only), `Gates/TrustSelfTest.lean` (copied-tree list only), `.github/workflows/ci.yml` (Sha256 steps only), `docs/PROVENANCE.md` (S1.0 rows only), `workshop/**` | S1.0 seat (Opus subagent, dispatched by the coordinator) | in progress; coordinator commits |

| `docs/research/2026-09-01-lean-stdlib-strategy-and-performance.md` | R0-A seat (Opus subagent) | in progress; benchmarks run in a scratchpad package, never in this tree |
| `docs/research/2026-09-01-lean4-nlp-learnings.md` | R0-B seat (Opus subagent) | in progress; reads a scratchpad clone of `mepuka/lean4-nlp` |
| `docs/research/2026-09-01-web-reification-targets-survey.md` | R0-C seat (Opus subagent) | in progress; web research only |

The P0 bootstrap claim on the whole tree was released at the P0 commit. No
seat runs `lake` in this tree while the S1.0 seat holds its build; the R0
seats measure elsewhere.

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.
