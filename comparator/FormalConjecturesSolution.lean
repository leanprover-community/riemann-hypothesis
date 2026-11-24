import Main
import FormalConjecturesBridge

/-!
# The formal-conjectures statements, proved from the submission

This file is not part of the submission. It is the solution module of the second Comparator
setup, `comparator/formal-conjectures.json`. The challenge of that setup,
`FormalConjecturesChallenge.lean`, is the Riemann Hypothesis and the Generalized Riemann
Hypothesis as [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
states them.

Each theorem below has the name it has there, and is proved from a theorem of the submission's
`Main.lean`. Comparator checks that the statements are the ones in the challenge.

This is the one file of the three that imports the submission, so the GRH statement is not
written out here. `type_of%` takes it from the signature of
`FormalConjecturesBridge.generalized_riemann_hypothesis_of_primitive`, which Lean elaborated
without the submission in scope. The `_root_` prefixes are for the same reason: a name must not
come to mean something the submission declares.
-/

set_option autoImplicit false

theorem RiemannHypothesis.riemannHypothesis : _root_.RiemannHypothesis :=
  _root_.riemannHypothesis

theorem GRH.generalized_riemann_hypothesis :
    type_of% (_root_.FormalConjecturesBridge.generalized_riemann_hypothesis_of_primitive
      _root_.LFunction_eq_zero_re_of_isPrimitive) :=
  _root_.FormalConjecturesBridge.generalized_riemann_hypothesis_of_primitive
    _root_.LFunction_eq_zero_re_of_isPrimitive
