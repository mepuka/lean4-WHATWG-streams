# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-02 (S1 landed as `a8f08d0`; P1 merged as `72b1bfd`).

## Who is active

| Agent | Working on |
| --- | --- |
| Claude (coordinator) | reviews, commits, rulings, routers, PLAN, SPEC-MANIFEST, docs/*.md |
| P3 breaker seat | the P3 queue-with-sizes contract packet, red battery, and counterexample witnesses, in the worktree `C:\Users\kokok\Dev\lean4-WHATWG-streams-p3` on branch `p3/queue-breaker`, base `c07cdba`. Leaves the branch dirty and uncommitted. Does not touch `WhatwgStreams/`, `Sha256/`, `Gates/`, `vendor/`, or the routers |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `test/contracts/queue-with-sizes.contract.md` | P3 breaker seat | frozen 2026-09-02; the builder may not edit it |
| `WhatwgStreamsTest/Data/QueueContract.lean` | P3 breaker seat | frozen and red; declared in `test/fixtures/trust-gate/known-red.txt` |
| `WhatwgStreamsTest/Data/QueueAxiomReport.lean` | P3 breaker seat | frozen and red; declared in the same file |
| `WhatwgStreamsTest/Counterexamples/Data/Queue.lean` | P3 breaker seat | green; breaker-owned, retained after the repair |
| `test/counterexamples/data/ATTACKS.md`, and the `WS-DATA-*` rows of `test/counterexamples/REGISTER.md` | P3 breaker seat | frozen 2026-09-02 |
| `docs/DATA-DAG.md` | P3 breaker seat | new; carries `DATA-PG-QUEUE` and ruling request `P3-R1` |
| `WhatwgStreams/Data/Queue.lean`, `WhatwgStreams/Data/Strategy.lean` | **unclaimed; the P3 builder's fence** | do not create them from the breaker seat. The P2 breadth stubs land on `main` |

The P3 breaker seat holds no claim on `WhatwgStreams/`. Ruling `P3-R1` in
`docs/DATA-DAG.md` must be answered before the builder starts, because the
`SizeClass` instance depends on it and none of the frozen statements do.

Released: the P0 bootstrap claim (P0 commit); the S1.0 seat's claim (landed
2026-09-02); the three R0 seats' claims (documents landed 2026-09-01/02);
the S1 one-shot builder's claim (landed as `a8f08d0`, 2026-09-02); the P1
census seat's claim (merged as `72b1bfd`, 2026-09-02). The worktree
`C:\Users\kokok\Dev\lean4-WHATWG-streams-p1` on branch `p1/census` remains
for the P1.1 follow-ups and is otherwise unclaimed.

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds a claim on a Lean tree runs `lake` in this checkout.
Research seats measure in scratchpad packages; a second builder works in a
git worktree on its own branch. The coordinator runs the gates only at
landing, after the seat has reported and stopped.