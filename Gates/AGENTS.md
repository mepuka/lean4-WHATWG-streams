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
- SHA-256 here is a command-line wrapper and holds no hash arithmetic of its
  own. Since stage S1.4 of `docs/SHA256-DAG.md`, `Gates/Sha256.lean` computes
  every digest through `Sha256.sha256` and every hexadecimal spelling through
  `Sha256.Hex.encode`, from the `Sha256/` tree, which is audited at the
  semantic ceiling and whose meaning is `Sha256.Bridge.sha256_bridge`.
  `Gates/VendorSeal.lean` computes its row digests through the same API.
  The P0 implementation, written in the `Id.run do` / `xs[i]!` style that
  `docs/SHA256-DAG.md` §3.3 forbids for theorem-bearing code, is gone.
- `lake exe sha256 --self-test` remains finite executable evidence and carries
  no theorem, but it no longer contains a literal: it reads
  `vendor/nist-cavp-sha256/SHA256ShortMsg.rsp` at run time and reproduces every
  record in it, so it cannot drift from the pin. Each record's `Len` field, not
  its `Msg` text, is the authority for the message length. Digests this gate
  produces are cross-checked against a second implementation at pin time and
  recorded in `docs/PROVENANCE.md`.
- Every gate resolves the repository root by searching upward for
  `WhatwgStreams.lean`; none reads an environment variable for that.

## Gates

| Command | Checks | Writes |
| --- | --- | --- |
| `lake exe sha256 --self-test` | the proved SHA-256 library against every record of the pinned NIST CAVP short-message file | nothing |
| `lake exe vendorseal` | `vendor/` against `generated/vendor-manifest.tsv` in both directions; Windows path validity | nothing |
| `lake exe vendorseal --write` | Windows path validity | `generated/vendor-manifest.tsv` |
| `lake exe citations` | no line-numbered citation into a protected authored document | nothing |
| `lake exe trustselftest` | the declared red set; then planted `partial`, `unsafe`, `Classical.choice`, `sorry`, `native_decide`, malformed literals, and an unreachable module are each rejected for the stated reason | a throwaway copy outside the tree, removed afterwards |
