# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-02 (S1.5–S1.7 merged as `a1383bc`; P3 breaker merged).

## Who is active

| Agent | Working on |
| --- | --- |
| Claude (coordinator) | reviews, commits, rulings, routers, PLAN, SPEC-MANIFEST, docs/*.md |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `test/contracts/queue-with-sizes.contract.md` | P3 breaker (landed) | frozen 2026-09-02; the builder may not edit it |
| `WhatwgStreamsTest/Data/QueueContract.lean`, `WhatwgStreamsTest/Data/QueueAxiomReport.lean` | P3 breaker (landed) | frozen and RED; declared in `test/fixtures/trust-gate/known-red.txt`; the builder may repair elaboration only, never a statement |
| `WhatwgStreamsTest/Counterexamples/Data/Queue.lean`, `test/counterexamples/data/ATTACKS.md`, the `WS-DATA-*` rows of `test/counterexamples/REGISTER.md` | P3 breaker (landed) | green; breaker-owned, retained after the repair |
| `docs/DATA-DAG.md` | P3 breaker (landed) | carries `DATA-PG-QUEUE` and ruling request `P3-R1`; the coordinator answers `P3-R1` there |
| `WhatwgStreams/Data/Queue.lean`, `WhatwgStreams/Data/Strategy.lean`, `WhatwgStreams/Strategy/**` (only if the contract's fence names them), `test/fixtures/trust-gate/known-red.txt` (remove the two entries when green), `WhatwgStreamsTest/Data/QueueContract.lean` and `QueueAxiomReport.lean` (elaboration repairs only, never a statement) | P3 builder seat (Opus subagent, dispatched 2026-09-02 after `P3-R1`) | in progress; the only seat running `lake` in this checkout |

Released: the P0 bootstrap claim; the S1.0 seat; the three R0 seats; the S1
one-shot builder (`a8f08d0`); the P1 census seat (`72b1bfd`); the P2 + P1.1
seat (`c2b4497`); the S1.5–S1.7 seat (`a1383bc`); the P3 breaker seat (this
merge). The worktrees `..\lean4-WHATWG-streams-p1`, `-s1`, and `-p3` are
merged and unclaimed.

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds a claim on a Lean tree runs `lake` in this checkout.
Research seats measure in scratchpad packages; a second builder works in a
git worktree on its own branch. The coordinator runs the gates only at
landing, after the seat has reported and stopped.