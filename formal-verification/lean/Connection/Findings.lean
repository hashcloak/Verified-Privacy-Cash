import Connection.NonVacuityStatements
open Aeneas Aeneas.Std Result

/-! # Findings

REVIEW SURFACE. The differences between the code and the spec. Each is stated as what the code
never accepts, and as a counterexample to completeness (the spec allows it, the code rejects
it). That these are the only differences for `transact` is `transact_complete_except_L1_A0`
(`ConnectionTheorems.lean`). Details and recommendations: `FINDINGS.md`.

- **L1**: the code rejects a zero external amount (an internal transfer), which the docs and
  the spec allow.
- **A0**: the code rejects a `proof_a` of 64 zero bytes, which the syscalls (and so the spec)
  read as the identity point: `negate_g1` decodes it with arkworks, which rejects it.
-/

namespace Connection

/-! ## L1 at the level of `check_public_amount` -/

/-- **L1 in `check_public_amount`.** For an internal transfer (amount 0, fee 0, public amount 0)
    the spec's checks hold and the code returns `false`. -/
theorem checkPublicAmount_L1_counterexample :
    CodeModel.check_public_amount CodeModel.arkFr 0#i64 0#u64 zeroBytes = ok false ∧
      Spec.pubAmtConsistent (0#i64).val (0#u64).val (toF zeroBytes) ∧
        Spec.amountsInRange (0#i64).val (0#u64).val :=
  checkPublicAmount_L1

/-! ## L1 and A0 at the level of `step`

The code never accepts these, in any deployment and state; the counterexamples show that
`transact_complete_except_L1_A0` fails without each exclusion. -/

section
variable {d : CodeModel.Deployment} {s : CodeModel.State} {tx : TransactTx}
  {sysvarRent : Option (Nat → U64)}

/-- **FINDING L1: the code never accepts an internal transfer** (external amount zero):
    `check_public_amount` rejects it. -/
theorem code_rejects_internal_transfer (h : tx.args.extAmount.val = 0) :
    ¬ Accepts d s (tx.env sysvarRent) tx.instruction :=
  fun hacc => accepts_ext_ne_zero hacc h

/-- **FINDING A0: the code never accepts a `proof_a` of 64 zero bytes**: `negate_g1` rejects
    them. -/
theorem code_rejects_zero_proof_a (h : tx.args.proof.proof_a.val = List.replicate 64 0#u8) :
    ¬ Accepts d s (tx.env sysvarRent) tx.instruction :=
  fun hacc => accepts_proof_a_ne_zero hacc h

end

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **FINDING L1, counterexample: the spec allows an internal transfer the code rejects.** In the
    example deployment (`Proofs/Toy.lean`), after `initialize`, an internal transfer (amount 0,
    fee 0) meets every hypothesis of `transact_complete_except_L1_A0` except "not L1"
    (`ExampleHypotheses`; it is not A0, and no address collision occurs). The spec allows it;
    the code rejects it. -/
theorem transact_complete_fails_for_internal_transfer
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ s : CodeModel.State,
      ExampleHypotheses s Toy.l1Tx
      ∧ Toy.l1Tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8
      ∧ SpecAllows (d := Toy.toyD) Toy.toyC Toy.toyRent s Toy.l1Tx
      ∧ ¬ Accepts Toy.toyD s (Toy.l1Tx.env Toy.toyTx.minimumBalance) Toy.l1Tx.instruction :=
  let ⟨s, hrun, hi, hp, hs, _, _, pre⟩ := Toy.toy_complete_examples
  ⟨s, ⟨Toy.toyProgramNotSystem, Toy.toyLaws, Toy.toyHashesAgree, Toy.toyCryptoSucceeds, Toy.toyRuntime h64, hp,
    noCollision_of_free (Toy.toy_collisionFree _ _), rfl, Toy.depA_listed _ _, hs,
    ⟨_, _, Toy.toyGenesis, hrun⟩, hi⟩, Toy.alpha_ne_zeros, pre, code_rejects_internal_transfer rfl⟩

/-- **FINDING A0, counterexample: the spec allows a zero `proof_a` the code rejects.** Excluding
    L1 is not enough. In the same state, a deposit of 2 lamports (not L1) with a `proof_a` of 64
    zero bytes meets every hypothesis except "not A0", and no address collision occurs. The
    spec allows it (reading the identity point); the code rejects it. -/
theorem transact_complete_fails_for_zero_proof_a
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ s : CodeModel.State,
      ExampleHypotheses s Toy.a0Tx
      ∧ Toy.a0Tx.args.extAmount.val ≠ 0
      ∧ SpecAllows (d := Toy.toyD) Toy.toyC Toy.toyRent s Toy.a0Tx
      ∧ ¬ Accepts Toy.toyD s (Toy.a0Tx.env Toy.toyTx.minimumBalance) Toy.a0Tx.instruction :=
  let ⟨s, hrun, hi, hp, hs, _, pre, _⟩ := Toy.toy_complete_examples
  ⟨s, ⟨Toy.toyProgramNotSystem, Toy.toyLaws, Toy.toyHashesAgree, Toy.toyCryptoSucceeds, Toy.toyRuntime h64, hp,
    noCollision_of_free (Toy.toy_collisionFree _ _), rfl, Toy.depA_listed _ _, hs,
    ⟨_, _, Toy.toyGenesis, hrun⟩, hi⟩, by simp, pre,
    code_rejects_zero_proof_a (by simp [Toy.toyProof, Toy.zeros64, Std.Array.repeat_val])⟩

end

end Connection
