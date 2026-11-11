import Spec.Statements
import Spec.NonVacuityProofs

/-! # Non-vacuity: the hypotheses can hold (for review)

A theorem whose hypotheses can never hold together says nothing (it is vacuous). For each
goal, a toy model shows its hypotheses can hold together. Its setting, also for review, is in
`Spec/NonVacuitySetting.lean`; the proofs, not for review, in `Spec/NonVacuityProofs.lean`.
- **G1a–G1d, G5a, G5b:** a run with a real spend (`nonvacuous_spend`);
- **G3a, G3b:** an honest spend (`nonvacuous_G3_hypotheses`, `nonvacuous_G3b_hypotheses`, for
  every way to withdraw, so whichever G3b picks); for G3a, the toy also shows directly that
  the program accepts the spend;
- **G4a, G4b:** an accepted transaction (`nonvacuous_G4_hypotheses`);
- **G2a, G2b:** `nonvacuous_G2a_hypotheses`, `nonvacuous_G2b_hypotheses`.

The toy setting is not cryptography: `H2` is constant, `G1 = G2 = F`, every pairing is `1`
and the key is all zeros (`toyHashes`, `toySha`, `toyGroups`, `toyPairing`, `toyDeployment`
in `NonVacuitySetting.lean`), so every proof verifies (`toyCompleteBytes`) and collisions are
trivial. These statements show only that the spec's own rules (preconditions of `transact`,
`WitnessesFor`, tree and balance bookkeeping) do not contradict each other. They show nothing
about real cryptography, and miss spec mistakes visible only with real hash values (e.g. in
Merkle paths, hidden by the constant `H2`). -/
namespace LeanSpec.Goals.NonVacuous
open LeanSpec

attribute [local instance] NonVacuity.toyHashes NonVacuity.toySha NonVacuity.toyGroups
  NonVacuity.toyG1Group NonVacuity.toyG2Group NonVacuity.toyG1Module NonVacuity.toyG2Module
  NonVacuity.toyGTGroup NonVacuity.toyPairing NonVacuity.toyDeployment

/-- **The hypotheses of G1a–G1d can hold, on a real spend.** A run of two transactions (a
    deposit, then a withdrawal) with witnesses for both proofs, where the withdrawal spends a
    real (non-zero) note: the one the deposit put at leaf 0. -/
theorem nonvacuous_spend :
    ∃ (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness),
      r.txs.length = 2 ∧ r.WitnessesFor wit
      -- transaction 1 spends a real note, the one transaction 0 put at leaf 0
      ∧ (wit 1).inAmt 0 ≠ 0 ∧ openedPos wit 1 0 = 0 ∧ (wit 1).inNote 0 = leafNote wit 0 :=
  NonVacuity.run_with_spend_exists NonVacuity.toyCompleteBytes

/-- **The hypotheses of G3a can all hold together, on a real spend, and the program accepts
    it.** After a one-deposit run, withdrawing the deposit's note (input 0 has a non-zero
    amount) satisfies every hypothesis of G3a, and the program accepts it (`CanBeAccepted`). -/
theorem nonvacuous_G3_hypotheses :
    ∃ (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness) (inputs : TxInputs)
      (witness : Witness) (k : ℕ),
      -- the hypotheses of G3a
      r.WitnessesFor wit ∧ HonestSpend r wit inputs witness k ∧ LimitsNotHit r.final inputs
      -- a real spend
      ∧ witness.inAmt 0 ≠ 0
      -- the program accepts it
      ∧ CanBeAccepted inputs r.final :=
  NonVacuity.toy_G3_hypotheses NonVacuity.toyCompleteBytes

/-- **The hypotheses of G3b's `WayIsAccepted` can all hold together, on a real spend, for
    whichever way G3b picks.** After a one-deposit run, withdrawing the deposit's 2-lamport note
    satisfies each of them for every way to withdraw 2 lamports (`WithdrawalWay`). -/
theorem nonvacuous_G3b_hypotheses :
    ∃ (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness),
      r.WitnessesFor wit
      -- for every way to withdraw 2 lamports
      ∧ ∀ payout fee : ℕ, WithdrawalWay r.final.state.config 2 payout fee →
        ∃ (inputs : TxInputs) (witness : Witness) (k : ℕ),
          HonestSpend r wit inputs witness k
          -- a real spend
          ∧ witness.inAmt 0 ≠ 0
          -- of 2 lamports, using that way
          ∧ witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : F)
          ∧ inputs.extAmt = -(payout : ℤ) ∧ inputs.f = fee
          -- the limits outside the admins' reach
          ∧ inputs.R ∈ Set.range r.final.state.tree.history
          ∧ treeHasRoom r.final.state.tree
          ∧ balancesFit inputs r.final :=
  let ⟨params, r, wit, hwit, h⟩ := NonVacuity.toy_G3b_hypotheses NonVacuity.toyCompleteBytes
  ⟨params, r, wit, hwit, fun payout fee hway => h payout fee hway.2.1⟩

/-- **The hypotheses of G4a and G4b can hold.** The program accepts a transaction: the toy
    withdrawal. -/
theorem nonvacuous_G4_hypotheses :
    ∃ (inputs : TxInputs) (oldWorld newWorld : World), transact inputs oldWorld newWorld :=
  NonVacuity.toy_G4_hypotheses NonVacuity.toyCompleteBytes

/-- **The hypotheses of G2a can all hold together.** The toy withdrawal, accepted after the same
    run, serves as both the honest transaction (well formed) and the attacker's (same public
    inputs, accepted). -/
theorem nonvacuous_G2a_hypotheses :
    ∃ (T T' : TxInputs) (oldWorld' newWorld' : World),
      ExtDataWellFormed T ∧ T.pubInputs = T'.pubInputs ∧ transact T' oldWorld' newWorld' :=
  NonVacuity.toy_G2a_hypotheses NonVacuity.toyCompleteBytes

/-- **The hypotheses of G2b can all hold together.** The toy withdrawal's witness, used as both
    witnesses, satisfies the circuit, and the two reveal the same nullifier. -/
theorem nonvacuous_G2b_hypotheses :
    ∃ (x : PubInputs) (w : Witness) (x' : PubInputs) (w' : Witness) (i i' : Fin 2),
      RelationS x w ∧ RelationS x' w' ∧ x.nullifiers i = x'.nullifiers i' :=
  NonVacuity.toy_G2b_hypotheses NonVacuity.toyCompleteBytes

end LeanSpec.Goals.NonVacuous
