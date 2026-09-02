/-!
# `Sha256` — SHA-256 from FIPS 180-4

The public root of the `Sha256` library. A consumer imports this module and
nothing else.

At stage S1.0 this root is empty on purpose: the stage freezes the question
(`test/contracts/sha256.contract.md`), pins the transcription sources
(`vendor/nist-fips-180-4/`, `vendor/nist-cavp-sha256/`), and builds the audit
scaffold. No specification, reference implementation, bridge, or native layer
exists yet, and this file therefore states nothing and imports nothing.

`docs/SHA256-DAG.md` §5.1 fixes what this root will import: `Sha256.Spec`,
`Sha256.Impl`, `Sha256.Lengths`, `Sha256.Bridge`, `Sha256.Hex`,
`Sha256.Digest`, `Sha256.Api`, and `Sha256.Fast`. The known-answer tests and
the axiom audit stay out of this closure and are reached only through
`Sha256.Verified`, so a consumer never pays for them.

The axiom ceiling of every `Sha256.*` module is the repository's semantic
ceiling, `propext` and `Quot.sound`. `Sha256.Audit` is the one exception,
named exactly in `WhatwgStreamsTest/Audit/AxiomGate.lean`, because `MetaM`
reaches `Classical.choice`.
-/
