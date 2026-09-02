# Live coordination between concurrent agents

Agents editing this worktree at the same time cannot message each other.
This file is the channel. Read it before you write, and update your claims
when you take or release a file.

Last updated: 2026-09-02 (S1.0 landed; one-shot S1 builder dispatched).

## Who is active

| Agent | Working on |
| --- | --- |
| Claude (coordinator) | reviews, commits, rulings, routers, PLAN, SPEC-MANIFEST, docs/*.md |
| S1 one-shot builder (Opus subagent, ruling R-10) | lane S1 stages S1.1-S1.4, stretch S1.5-S1.6, in the `Sha256/` tree |
| P1 census seat (Opus subagent) | the specification census generator, in the separate worktree `C:\Users\kokok\Dev\lean4-WHATWG-streams-p1` on branch `p1/census`; never in this checkout |

## Current claims

Claim a file by adding a row. Release it by deleting the row. A file with no
row is unclaimed.

| File or tree | Claimed by | State |
| --- | --- | --- |
| `Sha256/**` except `Sha256/Audit.lean` (only `minimumDeclarations` and the R-3 list may change there), `Sha256.lean`, `Sha256/Verified.lean` (imports and pin text), `test/fixtures/trust-gate/known-red.txt`, `test/counterexamples/REGISTER.md` and `test/counterexamples/sha/ATTACKS.md` (`WS-SHA-CE-*` rows only), `WhatwgStreamsTest/Counterexamples/Sha/**`, `Gates/Sha256.lean` and `Gates/VendorSeal.lean` (S1.4 cutover only), `Gates/AGENTS.md` (S1.4 wrapper note only), `.github/workflows/ci.yml` (Sha256 steps only), `docs/PROVENANCE.md` (S1 rows only), `workshop/**` | S1 one-shot builder | in progress; coordinator commits; no other seat runs `lake` in this tree meanwhile |

| branch `p1/census` (worktree): `Gates/Census.lean`, `bin/Census.lean`, `Gates.lean` (import line), `lakefile.toml` (census exe and default target), `census/**` (authored inputs), `generated/spec-algorithm-census.tsv`, `WhatwgStreamsTest/Audit/SpecCoverage.lean`, `WhatwgStreamsTest.lean` (import line), `WhatwgStreamsTest/Audit/AxiomGate.lean` (exact-module list only), `Gates/TrustSelfTest.lean` (copied-tree list only), `.github/workflows/ci.yml` (census steps only), `Gates/AGENTS.md` (census row in the gates table only) | P1 census seat | in progress on its own branch; the coordinator merges into `main` after review |

Released: the P0 bootstrap claim (P0 commit); the S1.0 seat's claim (landed
2026-09-02); the three R0 seats' claims (documents landed 2026-09-01/02).

## Collision record

None yet. When one happens, record what it cost here so the rule that
prevents it is not relaxed later.

## Standing rule while a builder holds the tree

Only the seat that holds the `Sha256/` claim runs `lake` in this checkout.
Research seats measure in scratchpad packages. The coordinator runs the
gates only at landing, after the seat has reported and stopped.