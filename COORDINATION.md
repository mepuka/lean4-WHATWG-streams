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

No claims. The P0 bootstrap claim on the whole tree was released at the P0
commit. The next claim is the R0 research writer under `docs/research/`.

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.
