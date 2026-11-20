import Connection.ConnectionTheorems
import Connection.Proofs.ToySpend
import Connection.Proofs.ToyDonate
import Connection.Proofs.ToyComplete
import Connection.Proofs.ToyRunComplete
open Aeneas Aeneas.Std Result

/-! # Non-vacuity of the connection theorems

REVIEW SURFACE. The hypotheses of the connection theorems can all hold together, shown on
example code runs. Kept apart, as in the spec: the theorems do not depend on the examples,
whose proofs (not for review) are in `Proofs/Toy*.lean`. -/

namespace Connection

/-! ## Non-vacuity

All in one example deployment:
- **`connection_nonvacuous`:** `initialize`, a deposit of 2 lamports, then a withdrawal of 1
  lamport with fee 1 spending the deposit's note. Meets every hypothesis of `run_connection`
  and of the goals about histories (`CodeModelStatements.lean`), with a real spend.
- **`donation_nonvacuous`:** `initialize`, an outside action sending 1 lamport to the pool,
  then the deposit. Meets every hypothesis of `run_connection`; the spec run counts the
  lamport as donated.
- **`transact_connection_nonvacuous`:** the deposit and the withdrawal each meet every
  hypothesis of `transact_connection` (so also of G2a, G4a, G4b for the code).
- **`transact_complete_nonvacuous`:** after `initialize`, the deposit meets every hypothesis of
  `transact_complete_except_L1_A0`, and the spec allows it.
- **`run_complete_nonvacuous`:** the spec run of `initialize` and the deposit meets every
  hypothesis of `run_complete_except_L1_A0`.
G3a and G3b for the code: `CodeModelStatements.lean`.

The example deployment is deliberately insecure (`Proofs/Toy.lean`): `G1 = G2 = GT = Unit`,
every pairing 1, Poseidon always 1, SHA-256 always zero, a simplified PDA derivation; only the
G1 decoding is real. It shows the hypotheses can hold together, not that real cryptography
reaches the outcome. The code never computes `H1`, `H3`, `H4`; the example takes `H1` the
identity and `H3`, `H4` the sums of their arguments, so that its spec transactions have circuit
witnesses. -/

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **The connection theorems are not vacuous, with a real spend**: a code run with a deposit
    and then a withdrawal.
    - **`run_connection`'s hypotheses** all hold;
    - **the goals' hypotheses** hold: the program is initialized, and `wit` are circuit
      witnesses for both spec transactions (for every spec run: `IsRunOf` fixes its spec
      transactions);
    - **a real spend:** the withdrawal spends a non-zero note, the deposit's, at leaf 0.
    So G1a–G1d are not vacuous on a spend. -/
theorem connection_nonvacuous :
    ∃ (d : CodeModel.Deployment) (s₀ sₙ : CodeModel.State) (steps : List RunStep)
      (C : CodeModel.AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- every hypothesis of `run_connection`
      PairingLaws C.e ∧ CodeModel.Genesis d.programId s₀
      ∧ CodeRun d s₀ steps sₙ
      ∧ ProgramNotSystem d ∧ HashesAgree d
      ∧ TransactAssumptionsInRun d (eventsOf steps)
      -- no address collision occurs
      ∧ ¬ AddressCollision d (proofsIn (eventsOf steps))
      ∧ (∀ txEnv ix em, .program txEnv ix em ∈ eventsOf steps →
          SameRent Toy.toyRent txEnv.minimumBalance)
      -- the program is initialized, and the code run has two `transact` instructions
      ∧ Initialized d sₙ ∧ (runTxs (eventsOf steps)).length = 2
      -- with circuit witnesses for both spec transactions
      ∧ ∃ wit : ℕ → Spec.Witness,
        (∀ j (h : j < (runTxs (eventsOf steps)).length),
          Spec.RelationS (runTxs (eventsOf steps))[j].pubInputs (wit j))
        -- in which spec transaction 1 spends a real note, the one the deposit put at leaf 0
        ∧ (wit 1).inAmt 0 ≠ 0 ∧ Spec.openedPos wit 1 0 = 0
        ∧ (wit 1).inNote 0 = Spec.leafNote wit 0 :=
  Toy.toy_spend_nonvacuous

section
-- The spec's groups, pairing and key are the example deployment's, as `run_connection` fixes
-- them (`syscallGroups`, `syscallPairing`, `programKey`).
attribute [local instance] Toy.toySpecGroups Toy.toySpecG1Group
  Toy.toySpecG1Module Toy.toySpecGTGroup Toy.toySpecPairing Toy.toySpecDeployment

/-- **`run_connection` is not vacuous on an outside action**: the code run `initialize`, an
    outside action (`EnvStep`) sending 1 lamport to the pool, then a deposit of 2 lamports.
    - **`run_connection`'s hypotheses** all hold;
    - **the outside action reaches the spec:** every spec run of it counts the lamport as
      donated (`r.donated = 1`). -/
theorem donation_nonvacuous :
    ∃ (s₀ sₙ : CodeModel.State) (steps : List RunStep),
      -- every hypothesis of `run_connection`, for the example deployment
      CodeModel.Genesis Toy.toyD.programId s₀ ∧ CodeRun Toy.toyD s₀ steps sₙ
      ∧ ProgramNotSystem Toy.toyD ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD
      ∧ TransactAssumptionsInRun Toy.toyD (eventsOf steps)
      ∧ ¬ AddressCollision Toy.toyD (proofsIn (eventsOf steps))
      ∧ (∀ txEnv ix em, .program txEnv ix em ∈ eventsOf steps →
          SameRent Toy.toyRent txEnv.minimumBalance)
      -- the code run contains an outside action
      ∧ CodeModel.Event.env ∈ eventsOf steps
      -- and every spec run of it counts 1 lamport as donated
      ∧ ∀ params r, IsRunOf Toy.toyD Toy.toyRent steps sₙ params r → r.donated = 1 :=
  Toy.toy_donation_nonvacuous

end

/-- **`transact_connection` is not vacuous, for a deposit and for a withdrawal**: in one
    deployment meeting the deployment-level hypotheses, the code accepts a deposit
    (`extAmount > 0`) and a withdrawal (`extAmount < 0`), each after a code run from genesis,
    meeting the per-instruction hypotheses, with no address collision. Together they cover
    both payment paths: the signer pays the pool, and the pool pays the recipient. -/
theorem transact_connection_nonvacuous :
    ∃ (d : CodeModel.Deployment) (rent : Nat → U64)
      (C : CodeModel.AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- the deployment-level hypotheses of `transact_connection`
      PairingLaws C.e ∧ ProgramNotSystem d ∧ HashesAgree d
      -- a deposit the code accepts, with the per-instruction hypotheses
      ∧ (∃ (s s' : CodeModel.State) (tx : TransactTx) (sysvarRent : Option (Nat → U64))
          (events : List CodeModel.CommitmentData),
        CodeModel.Reachable d s
        ∧ CodeModel.Run d s [.program (tx.env sysvarRent) tx.instruction events] s'
        ∧ tx.args.extAmount.val > 0
        ∧ TransactAssumptions d tx.ctx tx.args.proof ∧ ¬ AddressCollision d {tx.args.proof}
        ∧ SameRent rent sysvarRent)
      -- and a withdrawal the code accepts, with the per-instruction hypotheses
      ∧ (∃ (s s' : CodeModel.State) (tx : TransactTx) (sysvarRent : Option (Nat → U64))
          (events : List CodeModel.CommitmentData),
        CodeModel.Reachable d s
        ∧ CodeModel.Run d s [.program (tx.env sysvarRent) tx.instruction events] s'
        ∧ tx.args.extAmount.val < 0
        ∧ TransactAssumptions d tx.ctx tx.args.proof ∧ ¬ AddressCollision d {tx.args.proof}
        ∧ SameRent rent sysvarRent) :=
  Toy.toy_transact_nonvacuous

/-- `ExampleHypotheses s tx`: every hypothesis of `transact_complete_except_L1_A0` except
    the two exclusions, and no address collision, for the example deployment and the `transact`
    instruction `tx`, with the example's rent sysvar, in the chain state `s`. -/
def ExampleHypotheses (s : CodeModel.State) (tx : TransactTx) : Prop :=
  ProgramNotSystem Toy.toyD ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD
    ∧ CryptoSucceeds Toy.toyD.crypto Toy.toyC ∧ RuntimeFacts Toy.toyRent
    ∧ PdasOnlyByProgram Toy.toyD s ∧ ¬ AddressCollision Toy.toyD {tx.args.proof}
    ∧ SameRent Toy.toyRent Toy.toyTx.minimumBalance
    ∧ AccountsListed Toy.toyD tx.accounts tx.args.proof ∧ SignerIsPlain s tx.accounts
    ∧ CodeModel.Reachable Toy.toyD s ∧ Initialized Toy.toyD s

/-- **`transact_complete_except_L1_A0` is not vacuous**: after `initialize`, a deposit of 2
    lamports (not L1) whose `proof_a` is the key's `alpha` (not A0) meets every hypothesis, and
    the spec allows it. -/
theorem transact_complete_nonvacuous
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ s : CodeModel.State,
      ExampleHypotheses s Toy.depTx
      ∧ Toy.depTx.args.extAmount.val ≠ 0 ∧ Toy.depTx.args.proof.proof_a.val ≠ List.replicate 64 0#u8
      ∧ SpecAllows (d := Toy.toyD) Toy.toyC Toy.toyRent s Toy.depTx :=
  let ⟨s, hrun, hi, hp, hs, pre, _, _⟩ := Toy.toy_complete_examples
  ⟨s, ⟨Toy.toyProgramNotSystem, Toy.toyLaws, Toy.toyHashesAgree, Toy.toyCryptoSucceeds, Toy.toyRuntime h64, hp,
    noCollision_of_free (Toy.toy_collisionFree _ _), rfl, Toy.depA_listed _ _, hs,
    ⟨_, _, Toy.toyGenesis, hrun⟩, hi⟩, by simp, Toy.alpha_ne_zeros, pre⟩

end

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **`run_complete_except_L1_A0` is not vacuous**: the spec run of `initialize` and that
    deposit meets every hypothesis, with no address collision. -/
theorem run_complete_nonvacuous
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ (params : Spec.InitParams) (r : SpecRun Toy.toyC params),
      ProgramNotSystem Toy.toyD ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD
      ∧ CryptoSucceeds Toy.toyD.crypto Toy.toyC ∧ RuntimeFacts Toy.toyRent
      ∧ RunOfDeployment Toy.toyD Toy.toyRent params
      ∧ (∀ tx ∈ r.txs, tx.extAmt ≠ 0)                      -- not L1
      ∧ (∀ tx ∈ r.txs, tx.π.A ≠ List.replicate 64 0)        -- not A0
      ∧ ¬ AddressCollision Toy.toyD (fromSpecProof '' {tx | tx ∈ r.txs})
      ∧ r.txs = [Toy.depInputs] :=                         -- one spec transaction: the deposit
  Toy.toy_run_complete_nonvacuous h64

end

end Connection
