# Contract packets

Every semantic implementation slice begins with a breaker-authored packet in
this directory. A packet states its claim boundary, categories, requirements,
frozen public declarations, algebraic laws, preconditions, postconditions,
decrease arguments, frame, executable falsifiers, the specification anchors
it models with their span digests, and the counterexample rows it exercises.
The breaker commits the packet and the red battery, declares the red modules
in `test/fixtures/trust-gate/known-red.txt`, and records a claim in
`COORDINATION.md` before the builder changes the implementation.

The Lean battery is the authority on names and propositions; the packet's
Lean is a reading aid. Every theorem statement in a battery is frozen by
`#check (@name : proposition)` ascription.

P0 contains no packet. The first packets arrive at P3 and S1.
