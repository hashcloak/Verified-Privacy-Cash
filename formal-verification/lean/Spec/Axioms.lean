import Spec.Statements

/-! # Axiom check

For every theorem in `Spec/Statements.lean`, the axioms it depends on. `#guard_msgs` makes
the build fail if the list changes: a `sorry` would show up as `sorryAx`, an extra axiom by
its name. The only axioms are Lean's standard three (`propext`, `Classical.choice`,
`Quot.sound`). So a successful build of this file means no theorem relies on anything else,
without reading the proofs. -/

/-- info: 'LeanSpec.Goals.spends_are_genuine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.spends_are_genuine

/-- info: 'LeanSpec.Goals.no_double_spend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.no_double_spend

/-- info: 'LeanSpec.Goals.balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.balance

/-- info: 'LeanSpec.Goals.honest_note_spent_only_with_owner_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.honest_note_spent_only_with_owner_key

/-- info: 'LeanSpec.Goals.transact_requires_valid_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.transact_requires_valid_proof

/-- info: 'LeanSpec.Goals.same_public_inputs_same_external_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.same_public_inputs_same_external_data

/-- info: 'LeanSpec.Goals.shared_nullifier_requires_owner_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.shared_nullifier_requires_owner_key

/-- info: 'LeanSpec.Goals.unspent_note_is_spendable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.unspent_note_is_spendable

/-- info: 'LeanSpec.Goals.unspent_note_cannot_be_blocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.unspent_note_cannot_be_blocked

/-- info: 'LeanSpec.Goals.full_tree_freezes_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.full_tree_freezes_pool

/-- info: 'LeanSpec.Goals.no_sol_created' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.no_sol_created

/-- info: 'LeanSpec.Goals.balance_changes_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.balance_changes_exact

/-- info: 'LeanSpec.Goals.config_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.config_constant

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_spend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_spend

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_G3a_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_G3a_hypotheses

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_withdrawal_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_withdrawal_accepted

