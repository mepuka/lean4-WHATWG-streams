import Sha256
import Sha256.Kats
import Sha256.Audit

/-!
# `Sha256.Verified` — the audited root

The root of the `Sha256Verified` Lake library. It imports the public library
and the audit, and pins the audit's verdict line with `#guard_msgs`, so any
drift in the declaration count, the module count, the ceiling, or the number
of admitted string declarations is a build error that must be updated
deliberately rather than noticed later.

`docs/SHA256-DAG.md` §5.1 adds `Sha256.Kats` to this closure. Nothing imported
here is reachable from `Sha256`, so a consumer of the library does not build
the known-answer tests or the audit.

The pinned counts after stages S1.1 to S1.6 are 422 declarations across twelve
modules: `Sha256.Vec`, `Spec`, `Impl`, `Lengths`, `Bridge`, `Hex`, `Digest`,
`Api`, `Fast`, `Context`, `Sha224`, and `Kats`. `Sha256.Audit` is excluded from
its own audit and `Sha256.Verified` states nothing, so neither is counted.
S1.1–S1.4 had pinned 280 across ten; S1.5 added `Sha256.Context` and S1.6
`Sha256.Sha224`.

The number of admitted string declarations is `0`. Ruling R-3 anticipated that
`Hex.encode`, `Hex.decode?`, `Digest.toHex` and `Digest.ofHex?` might have to
be admitted to `Classical.choice`; they did not. `Sha256.Hex` records how that
was achieved and what it cost.
-/

/-- info: sha256 axiom audit: 422 declarations across 12 modules; ceiling [propext, Quot.sound]; 0 admitted string declarations; 0 offenders -/
#guard_msgs in
#sha256_axiom_audit
