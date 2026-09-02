# Counterexamples

This is the central, durable home for counterexamples that can change a
declaration, theorem, admission rule, host-profile refusal, or cutover
decision.

`REGISTER.md` assigns stable IDs and records the exact attacked statement,
witness, evidence command, proof assumptions, forced repair, and current
status. Lean witnesses live under `WhatwgStreamsTest/Counterexamples/<Area>/`
and are linked from the register; each area also keeps an `ATTACKS.md`
describing the attack shapes in prose. Negative fixtures and implementation
mutants are recorded separately because they attack gates rather than
semantic statements.

## Stable ID scheme

`WS-<AREA>-CE-<nnn>`. The area token is the directory name in upper case
when it has six characters or fewer, and its first three or four letters
otherwise: `DATA`, `READ` (readable), `WRITE`, `TRANS` (transform), `PIPE`
(piping), `CONF` (configuration), `LOGIC`, `TARGET`, `BRIDGE`, `SHA` (the
SHA-256 lane). IDs are never reused.

## Statuses

- `PINNED`: the witness exists at a named immutable source revision.
- `SEEDED`: the packet has frozen the attack, but no immutable provenance pin
  for its witness has been recorded yet.
- `RESERVED`: the stable row and forced repair are frozen now; the executable
  witness belongs to a later packet whose declarations are not open yet.
- `CLOSED`: the witness is retained and the repaired declaration mechanically
  rejects the attack.
