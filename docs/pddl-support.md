# PDDL support

Supports STRIPS, typing (including hierarchies and `either`), equality, negative
and disjunctive preconditions, existential and universal quantification,
conditional effects, and the `total-cost` action-cost fragment. Action costs may
be constants or functions of action parameters.

Durative actions, general numeric fluents, timed initial literals, preferences,
constraints, and explicit derived predicates are rejected. Translator-generated
axioms are handled by finite-domain search. State-dependent cost increases nested
inside `when` or `forall` are accepted but currently contribute zero.
