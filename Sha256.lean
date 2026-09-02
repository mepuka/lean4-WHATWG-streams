import Sha256.Spec
import Sha256.Impl
import Sha256.Lengths
import Sha256.Bridge
import Sha256.Hex
import Sha256.Digest
import Sha256.Fast
import Sha256.Api

/-!
# `Sha256` — SHA-256 from FIPS 180-4

The public root of the `Sha256` library. A consumer imports this module and
nothing else.

`docs/SHA256-DAG.md` §5.1 fixes what this root imports: `Sha256.Spec`,
`Sha256.Impl`, `Sha256.Lengths`, `Sha256.Bridge`, `Sha256.Hex`,
`Sha256.Digest`, `Sha256.Api`, and `Sha256.Fast`. The known-answer tests and
the axiom audit stay out of this closure and are reached only through
`Sha256.Verified`, so a consumer never pays for them.

The axiom ceiling of every `Sha256.*` module is the repository's semantic
ceiling, `propext` and `Quot.sound`. `Sha256.Audit` is the one exception, named
exactly in `WhatwgStreamsTest/Audit/AxiomGate.lean`, because `MetaM` reaches
`Classical.choice`.
-/
