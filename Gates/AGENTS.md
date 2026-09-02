# Gates tooling routing

This boundary contains the repository's gates implemented in Lean: SHA-256,
the vendor seal, the internal-citation gate, and the trust self-test. It is
the sixth authored router because this tree has a distinct trust boundary
from the other five: it is tooling that reads files, spawns processes, and
produces projections, and it is admitted to the implementation ceiling as a
whole.

## Why the gates are Lean

Every check that decides whether the tree is green runs under the same
toolchain as the proofs and is itself audited by the axiom gate. A gate is
never a shell one-liner whose behaviour differs between hosts. Shell and
PowerShell files, where they exist, only orchestrate `lake exe` invocations;
they decide nothing.

## Rules

- No semantic declaration lives here. A definition that models the
  specification belongs under `WhatwgStreams/` behind a contract.
- Totality holds: no `partial`, no `unsafe`. Loops are bounded by fuel or by
  the structure they traverse.
- The ceiling is the implementation ceiling: `propext`, `Quot.sound`, and
  `Classical.choice`. `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`,
  and `Lean.trustCompiler` remain forbidden.
- A gate reports a stable `PASS` or `FAIL` line stating exactly what was
  checked and, on failure, every offending item. It never truncates the
  failure list.
- A gate that writes a projection under `generated/` records that it did,
  names the file, and never writes an `AGENTS.md`.
- SHA-256 here is finite executable evidence against the FIPS 180-4 vectors,
  checked by `lake exe sha256 --self-test`. It carries no theorem. Digests it
  produces are cross-checked against a second implementation at pin time and
  recorded in `docs/PROVENANCE.md`.
- Every gate resolves the repository root by searching upward for
  `WhatwgStreams.lean`; none reads an environment variable for that.

## Gates

| Command | Checks | Writes |
| --- | --- | --- |
| `lake exe sha256 --self-test` | the SHA-256 implementation against seven vectors | nothing |
| `lake exe vendorseal` | `vendor/` against `generated/vendor-manifest.tsv` in both directions; Windows path validity | nothing |
| `lake exe vendorseal --write` | Windows path validity | `generated/vendor-manifest.tsv` |
| `lake exe citations` | no line-numbered citation into a protected authored document | nothing |
| `lake exe trustselftest` | the declared red set; then planted `partial`, `unsafe`, `Classical.choice`, `sorry`, `native_decide`, malformed literals, and an unreachable module are each rejected for the stated reason | a throwaway copy outside the tree, removed afterwards |
