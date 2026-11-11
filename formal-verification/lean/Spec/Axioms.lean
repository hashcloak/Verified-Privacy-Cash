import Spec.NonVacuityStatements

/-! # Axiom check

For every theorem in `Spec/Statements.lean` and `Spec/NonVacuityStatements.lean`, the axioms
it depends on. `#guard_msgs` makes
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

/-- info: 'LeanSpec.Goals.same_public_inputs_same_external_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.same_public_inputs_same_external_data

/-- info: 'LeanSpec.Goals.shared_nullifier_requires_owner_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.shared_nullifier_requires_owner_key

/-- info: 'LeanSpec.Goals.honest_spend_is_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.honest_spend_is_accepted

/-- info: 'LeanSpec.Goals.admins_cannot_lock_withdrawals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.admins_cannot_lock_withdrawals

/-- info: 'LeanSpec.Goals.only_signers_pay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.only_signers_pay

/-- info: 'LeanSpec.Goals.exact_payouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.exact_payouts

/-- info: 'LeanSpec.Goals.only_authorities_change_config' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.only_authorities_change_config

/-- info: 'LeanSpec.Goals.admin_powers_limited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.admin_powers_limited

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_spend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_spend

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_G3_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_G3_hypotheses

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_G3b_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_G3b_hypotheses

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_G4_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_G4_hypotheses

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_G2a_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_G2a_hypotheses

/-- info: 'LeanSpec.Goals.NonVacuous.nonvacuous_G2b_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms LeanSpec.Goals.NonVacuous.nonvacuous_G2b_hypotheses

