# The Privacy Cash specification

A hand-written Lean model of the protocol, from the documentation (SOL only). It imports
only Mathlib. The files, in order:

- `Spec.lean`: the model: state, `transact`, its preconditions and effects, `initWorld`.
- `Vocabulary.lean`: the building blocks the statements use (runs, notes, hash breaks, the
  pieces of G3a).
- `Statements.lean`: the review surface: goals (each a property and its theorem), trusted
  assumptions.
  Start here ("How to review" at its top).
- `Proofs.lean`: lemmas and proofs (not for review).
- `NonVacuity.lean`: toy-model checks that the hypotheses can hold.
- `Axioms.lean`: machine check that no theorem uses `sorry` or an extra axiom.
- `written_spec.md`: the protocol in prose (being updated to match the Lean spec).

Build from `formal-verification/`:

```bash
nix develop path:. -c bash -c "cd lean && lake build Spec"
```
