# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-02 (S1 landed as `a8f08d0`; P1 merged as `72b1bfd`).

## Who is active

| Agent | Working on |
| --- | --- |
| Claude (coordinator) | reviews, commits, rulings, routers, PLAN, SPEC-MANIFEST, docs/*.md |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| worktree `..\lean4-WHATWG-streams-s1` on `s1/streaming`: `Sha256/**`, `Sha256.lean`, `vendor/nist-cavp-sha224/**`, `generated/vendor-manifest.tsv`, `Gates/Sha256.lean` (self-test over both files), `test/counterexamples/REGISTER.md` and `sha/ATTACKS.md` (`WS-SHA-CE-005` onward), `WhatwgStreamsTest/Counterexamples/Sha/**`, `docs/PROVENANCE.md` (S1.6 rows), `.github/workflows/ci.yml` (Sha256 steps only) | S1.5–S1.7 seat (Opus subagent) | in progress on its own branch |
| worktree `..\lean4-WHATWG-streams-p3` on `p3/queue-breaker`: `test/contracts/queue-with-sizes.contract.md`, `docs/DATA-DAG.md`, `WhatwgStreamsTest/Data/**`, `WhatwgStreamsTest/Counterexamples/Data/**`, `test/counterexamples/data/ATTACKS.md`, `test/counterexamples/REGISTER.md` (`WS-DATA-CE-*` rows only), `test/fixtures/trust-gate/known-red.txt`, `WhatwgStreamsTest.lean` (import lines only) | P3 breaker seat (Opus subagent) | in progress on its own branch; the builder is a later, separate seat |

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