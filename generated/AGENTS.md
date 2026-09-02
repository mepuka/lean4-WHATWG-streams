# Generated-output routing

This directory contains deterministic projections of canonical inputs. It
contains no semantic source and no policy.

This `AGENTS.md` file is the directory's only authored file. Generators must
exclude every `AGENTS.md`; they may neither create nor replace instructions.

## Allowed projections

- the vendor manifest: one row per pinned third-party file with its SHA-256
  and size, written by `lake exe vendorseal --write`;
- the specification algorithm census: one row per abstract operation,
  internal slot, and IDL member of the pinned `index.bs`, anchored by span
  digest (P1);
- declaration and public-signature snapshots;
- existing-type and spec-disposition snapshots;
- graph-bearing owner obligation ledgers, leaf receipt indexes, and
  per-declaration assurance snapshots;
- theorem and axiom receipt indexes;
- counterexample coverage indexes; and
- host-profile conformance and refusal coverage.

Each projection records its canonical inputs, generator identity, format
version, and exact regeneration command, either in a header line or in the
generator's module documentation. Output must be byte-deterministic and must
not contain machine-specific absolute paths or timestamps that make an
unchanged input drift.

Never hand-edit a generated projection. Repair its authored input or generator,
regenerate into a clean tree, and run the byte-for-byte drift gate. A generator
may report an open proof edge, open leaf receipt, or missing annotation, but it
may not supply a manual completion override, invent a disposition, or
generate an instruction file.
