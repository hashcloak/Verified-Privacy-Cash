import Spec.Statements

/-! The Privacy Cash specification, in one import. The files, in order:
- `Spec/Spec.lean`: the model (sections (1)–(4)).
- `Spec/Vocabulary.lean`: the definitions the theorem statements use.
- `Spec/Proofs.lean`: lemmas and proofs (not for review).
- `Spec/NonVacuity.lean`: toy-model checks that the hypotheses can hold.
- `Spec/Statements.lean`: the review surface: goals, trusted assumptions, theorem statements.
- `Spec/Axioms.lean`: machine check that no theorem uses `sorry` or an extra axiom. -/
