/-!
# Primitive.Singleton

Owner: the four singleton types of section `singleton` of
`vendor/whatwg-infra-3f984adc/infra.bs`: allowed, blocked, failure, success.

The text says these "can be used as inputs or outputs of algorithmic prose to
improve comprehension", "have no observable representation beyond their
effect on the flow of any given algorithm, and they can only be compared with
'is'". They pair off by the text's own "often used in opposition to" phrases,
so the carriers are two two-constructor inductives, `Permission` for allowed
and blocked and `Outcome` for failure and success, each with decidable
equality as the "is" comparison and nothing else.

Ruling INFRA-R3 (`docs/INFRA-PROOF-PLAN.md` section 3) fixes how the
singletons meet a value: an algorithm that returns "failure or a value", the
shape of the text's own example ("if status is less than 200 or greater than
599, then return failure … return status"), is modelled as `Option` of the
value type with `none` as failure; the inductives here are used only where an
algorithm returns a singleton bare.
-/

set_option autoImplicit false

namespace Whatwg.Infra

/-- The allowed/blocked pair of section `singleton`. Allowed "indicates that
some operation is permitted, often used in opposition to blocked"; blocked
"indicates that some operation is not permitted, often used in opposition to
allowed". The two "can only be compared with 'is'", which is `DecidableEq`. -/
inductive Permission where
  /-- Allowed, section `singleton`: "indicates that some operation is
  permitted, often used in opposition to blocked". -/
  | allowed
  /-- Blocked, section `singleton`: "indicates that some operation is not
  permitted, often used in opposition to allowed". -/
  | blocked
  deriving DecidableEq, Repr

/-- The failure/success pair of section `singleton`. Failure "indicates that
some operation did not proceed as expected, often used in opposition to
success or in combination with a more concrete type"; success "indicates that
some operation proceeded as expected, often used in opposition to failure".
The two "can only be compared with 'is'", which is `DecidableEq`.

When failure is used "in combination with a more concrete type", that is when
an algorithm "can fail or return a value", the result is modelled as `Option`
of the value type with `none` as failure (ruling INFRA-R3); this inductive is
for algorithms that return success or failure bare. -/
inductive Outcome where
  /-- Failure, section `singleton`: "indicates that some operation did not
  proceed as expected, often used in opposition to success or in combination
  with a more concrete type". -/
  | failure
  /-- Success, section `singleton`: "indicates that some operation proceeded
  as expected, often used in opposition to failure". -/
  | success
  deriving DecidableEq, Repr

end Whatwg.Infra
