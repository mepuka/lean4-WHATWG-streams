import Sha256
import Sha256.Audit

/-!
# `Sha256.Verified` — the audited root

The root of the `Sha256Verified` Lake library. It imports the public library
and the audit, and pins the audit's verdict line with `#guard_msgs`, so any
drift in the declaration count, the module count, the ceiling, or the number
of admitted string declarations is a build error that must be updated
deliberately rather than noticed later.

`docs/SHA256-DAG.md` §5.1 adds `Sha256.Kats` to this closure at S1.1. Nothing
imported here is reachable from `Sha256`, so a consumer of the library does
not build the known-answer tests or the audit.

The pinned counts are `0` and `0` at S1.0 because the library is empty by
design at this stage: `Sha256.lean` states nothing, and `Sha256.Audit` is
excluded from its own audit.
-/

/-- info: sha256 axiom audit: 0 declarations across 0 modules; ceiling [propext, Quot.sound]; 0 admitted string declarations; 0 offenders -/
#guard_msgs in
#sha256_axiom_audit
