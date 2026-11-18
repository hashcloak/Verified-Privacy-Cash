import Connection.ConnectionTheorems
import Connection.Proofs.Goals
import Connection.Proofs.ToyG3
import Connection.Proofs.ToyAdmin
open Aeneas Aeneas.Std Result

/-! # The spec's security goals, stated of the code model

REVIEW SURFACE, read after `ConnectionTheorems.lean`. Every proof here is one line pointing into
`Proofs/`, which is not for review.

A sanity check, not a new result: each goal is a property of the spec (`Spec/Statements.lean`,
`Spec.Goals`), stated here of the code and proved from the connection theorems
(`run_connection`, `transact_connection`, and for G3 `transact_complete_except_L1_A0`).

## Contents

1. **The security goals hold for the code**, grouped by hypotheses (G1, G5 | G2, G4 | G3):
   - goals about histories (G1a–G1d, G5a, G5b) hold of the execution's run;
   - goals about one transaction (G2a, G4a, G4b) hold of every transaction the code accepts;
   - G3a and G3b use completeness;
   - G2b has no code version: it is about circuit witnesses only.
2. **Non-vacuity** of what `NonVacuityStatements.lean` does not cover.

Each statement opens with `withSyscallSpec C in`; it only fixes the spec's groups, pairing and
key to the program's (`syscallGroups`, `syscallPairing`, `programDeployment`). -/

namespace Connection

/-! ## 1. The security goals hold for the code

### G1 and G5: goals about histories

For an execution from genesis to `s` that initialized the pool, under the hypotheses of
`run_connection`: the execution's run (`IsRunOf`) satisfies the goal, for any witnesses of its
proofs where the goal needs them. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : CodeModel.Deployment} {rent : Nat → U64} {sGenesis s : CodeModel.State}
  {evs : List CodeModel.Event} {states : List CodeModel.State}
  (notSystem : ProgramNotSystem d)                             -- [assumption] see the definition
  (C : CodeModel.AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
                                                           -- [assumption] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumption] the pairing laws
  (hashes : HashesAgree d)                          -- [assumption] the hashes are the spec's
  (assume : ExecutionAssumptions d evs)      -- [assumption] as in `run_connection`
  (sameRent : ∀ txEnv ix em, .program txEnv ix em ∈ evs → SameRent rent txEnv.minimumBalance) -- [assumption] same rent as the spec
  (hgen : CodeModel.Genesis d.programId sGenesis)          -- [premise] an execution from genesis
  (hrun : ExecutionPath d sGenesis evs states s)           --   ...that reached `s` through `states`
  (hi : Initialized d s)                                   -- [premise] the pool is initialized
include notSystem C laws hashes assume sameRent hgen hrun hi

/-! #### G1. Balance -/

/-- **G1a for the code**: every spend in the execution is of a real note
    (`SpendsAreGenuine`). -/
theorem spendsAreGenuine_code :
    withSyscallSpec C in
    (∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.SpendsAreGenuine r wit)
      ∨ AddressCollision d (proofsIn evs) :=
  or_collision fun hc => spends_are_genuine_pf hgen hrun notSystem C laws hashes
    (ExecutionFacts.of_assumptions assume hc) sameRent hi

/-- **G1b for the code**: no note is spent twice in the execution (`NoDoubleSpend`). -/
theorem noDoubleSpend_code :
    withSyscallSpec C in
    (∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.NoDoubleSpend r wit)
      ∨ AddressCollision d (proofsIn evs) :=
  or_collision fun hc => no_double_spend_pf hgen hrun notSystem C laws hashes
    (ExecutionFacts.of_assumptions assume hc) sameRent hi

/-- **G1c for the code**: at the end of the execution, the pool's SOL exactly backs the
    unspent notes (`PoolBacksNotes`). -/
theorem poolBacksNotes_code :
    withSyscallSpec C in
    (∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.PoolBacksNotes params r wit)
      ∨ AddressCollision d (proofsIn evs) :=
  or_collision fun hc => pool_backs_notes_pf hgen hrun notSystem C laws hashes
    (ExecutionFacts.of_assumptions assume hc) sameRent hi

/-- **G1d for the code**: every spend in the execution uses the owner's secret key
    (`OnlyOwnerSpends`). -/
theorem onlyOwnerSpends_code :
    withSyscallSpec C in
    (∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.OnlyOwnerSpends r wit)
      ∨ AddressCollision d (proofsIn evs) :=
  or_collision fun hc => only_owner_spends_pf hgen hrun notSystem C laws hashes
    (ExecutionFacts.of_assumptions assume hc) sameRent hi

/-! #### G5. Admin control -/

/-- **G5a for the code**: only the execution's admin changes, each signed by the initializer,
    change the config (`OnlyAuthoritiesChangeConfig`). By `IsRunOf`, the initializer is the
    deployment's admin key, when it has one. -/
theorem onlyAuthoritiesChangeConfig_code :
    withSyscallSpec C in
    (∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      Spec.Goals.OnlyAuthoritiesChangeConfig params r)
      ∨ AddressCollision d (proofsIn evs) :=
  or_collision fun hc => only_authorities_change_config_pf hgen hrun notSystem C laws hashes
    (ExecutionFacts.of_assumptions assume hc) sameRent hi

/-- **G5b for the code**: the authorities never change, and the fee rates and fee error margin
    stay at most 100% (`AdminPowersLimited`). -/
theorem adminPowersLimited_code :
    withSyscallSpec C in
    (∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      Spec.Goals.AdminPowersLimited params r)
      ∨ AddressCollision d (proofsIn evs) :=
  or_collision fun hc => admin_powers_limited_pf hgen hrun notSystem C laws hashes
    (ExecutionFacts.of_assumptions assume hc) sameRent hi

end

/-! ### G2 and G4: goals about one transaction

For a `transact` that `step` accepts after an execution from genesis, under the hypotheses of
`transact_connection`, between the mapped worlds before and after. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : CodeModel.Deployment} {rent : Nat → U64} {s s' : CodeModel.State}
  {tx : TransactTx} {sysvarRent : Option (Nat → U64)} {events : List CodeModel.CommitmentData}
  (notSystem : ProgramNotSystem d)                             -- [assumption] see the definition
  (C : CodeModel.AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
                                                           -- [assumption] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumption] the pairing laws
  (hashes : HashesAgree d)                          -- [assumption] the hashes are the spec's
  (pdasDoNotSign : PdasDoNotSign d tx.ctx)                 -- [assumption] no PDA signs
  (circuit : CircuitFacts d {tx.args.proof})               -- [assumption] the circuit keeps the nullifiers distinct (I1)
  (sameRent : SameRent rent sysvarRent)                    -- [assumption] same rent as the spec
  (reachable : CodeModel.Reachable d s)                    -- [premise] an execution from genesis reached `s`
  (hstep : CodeModel.Run d s [.program (tx.env sysvarRent) tx.instruction events] s')
                                                           -- [premise] ...then accepted a transact (one more step)
include notSystem C laws hashes pdasDoNotSign circuit sameRent reachable hstep

/-! #### G2. Non-malleability

G2b (`shared_nullifier_requires_owner_key`) has no code version: it is about circuit witnesses
only. -/

/-- **G2a for the code**: if the accepted transaction has the public inputs of a
    well-formed honest transaction `T`, the two pay out the same (`SamePayout`). -/
theorem samePayout_code :
    withSyscallSpec C in
    let inputs := toInputs tx
    (∀ (T : Spec.TxInputs)                              -- [premise] an honest transaction, seen
                                                           --   but not yet accepted
      (_hT : Spec.Goals.ExtDataWellFormed T)           -- [premise] ...well formed
      (_hSame : T.pubInputs = inputs.pubInputs),           -- [attacker] the accepted transaction
                                                           --   has its public inputs
      Spec.Goals.SamePayout T inputs)
      ∨ AddressCollision d {tx.args.proof} :=
  or_collision fun hc => same_payout_pf reachable notSystem hstep C laws hashes pdasDoNotSign
    (newDiffer_of_noCollision (Set.mem_singleton _) hc) circuit sameRent

/-! #### G4. Correct public payouts -/

/-- **G4a for the code**: in the accepted transaction, only accounts that signed pay, and at most
    what they agreed to (`OnlySignersPay`). -/
theorem onlySignersPay_code :
    withSyscallSpec C in
    let inputs := toInputs tx
    Spec.Goals.OnlySignersPay inputs (toWorld d rent s) (toWorld d rent s')
      ∨ AddressCollision d {tx.args.proof} :=
  or_collision fun hc => only_signers_pay_pf reachable notSystem hstep C laws hashes pdasDoNotSign
    (newDiffer_of_noCollision (Set.mem_singleton _) hc) circuit sameRent

/-- **G4b for the code**: in the accepted transaction, every account changes by exactly what
    it should receive minus what it should pay (`ExactPayouts`). -/
theorem exactPayouts_code :
    withSyscallSpec C in
    let inputs := toInputs tx
    Spec.Goals.ExactPayouts inputs (toWorld d rent s) (toWorld d rent s')
      ∨ AddressCollision d {tx.args.proof} :=
  or_collision fun hc => exact_payouts_pf reachable notSystem hstep C laws hashes pdasDoNotSign
    (newDiffer_of_noCollision (Set.mem_singleton _) hc) circuit sameRent

end

/-! ### G3. Liveness: G3a and G3b

From the spec's G3a and G3b and completeness (`transact_complete_except_L1_A0`), so for the
whole `step`. `ReachesProgram`: what they take about the transaction as the owner submits it.
- **No gap:** nothing changed since the run's last transaction (`toWorld … = r.final`); a
  transfer or admin change in that gap is not covered.
- **"Accepted"** means by core-model's `step`, which leaves out some of Solana's rejections
  (writable flags, rent exemption, compute and size limits; `core-model/README.md`).

`r`: any spec run ending at the code's world, the execution's own (`IsRunOf`) among them. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : CodeModel.Deployment} {rent : Nat → U64} {s : CodeModel.State}
  (notSystem : ProgramNotSystem d)                             -- [assumption] see the definition
  (C : CodeModel.AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
                                                           -- [assumption] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumption] the pairing laws
  (hashes : HashesAgree d)                          -- [assumption] the hashes are the spec's
  (crypto : CryptoSucceeds d.crypto C)                     -- [assumption] the hash and syscalls return values
  (runtime : RuntimeFacts rent)                            -- [assumption] 64-bit `usize`, positive rent
  (pdas : PdasOnlyByProgram d s)                           -- [assumption] only the program creates
                                                           --   accounts at its addresses
  (reachable : CodeModel.Reachable d s)                    -- [premise] an execution from genesis reached `s`
  (initialized : Initialized d s)                          -- [premise] the pool is initialized
include notSystem C laws hashes crypto runtime pdas reachable initialized

/-- **G3a for the code.** An honest spend with no limit hit is accepted by `step`, or a hash break
    occurs. Excluded, as the code rejects them: L1 and A0 (`Findings.lean`). -/
theorem honestSpendIsAccepted_code
    {tx : TransactTx} {sysvarRent : Option (Nat → U64)}
    (reach : ReachesProgram d s tx.accounts tx.args.proof) -- [owner] the transaction as submitted
    (sameRent : SameRent rent sysvarRent)                  -- [assumption] same rent as the spec
    (notL1 : tx.args.extAmount.val ≠ 0)                    -- [finding L1] excluded
    (notA0 : tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8) : -- [finding A0] excluded
    withSyscallSpec C in
    let inputs := toInputs tx
    ∀ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness) (witness : Spec.Witness) (k : ℕ),
      toWorld d rent s = r.final →          -- [premise] nothing changed since the
                                                           --   run's last transaction
      r.WitnessesFor wit →                                 -- [assumption T1]
      Spec.HonestSpend r wit inputs witness k →        -- [owner]
      Spec.LimitsNotHit r.final inputs →               -- [limit]
      Accepts d s (tx.env sysvarRent) tx.instruction
        ∨ Spec.SpendBlockedByBreak r wit inputs witness k
        ∨ AddressCollision d {tx.args.proof} :=
  honest_spend_is_accepted_pf reachable notSystem C laws hashes crypto runtime pdas initialized reach sameRent notL1 notA0

/-- **G3b for the code.** A way to withdraw notes worth `spentAmt` lamports exists, at least half
    reaches the recipient, and an honest transaction using that way is accepted by `step`, or a
    hash break occurs. A0 is excluded (`Findings.lean`); L1 cannot arise, as a withdrawal's
    amount is not zero. -/
theorem adminsCannotLockWithdrawals_code :
    withSyscallSpec C in
    ∀ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness) (spentAmt : ℕ),
      toWorld d rent s = r.final →          -- [premise] nothing changed since the
                                                           --   run's last transaction
      r.WitnessesFor wit →                                 -- [assumption T1]
      2 ≤ spentAmt →                                       -- [premise] the total of the notes the owner spends
      ∃ payout feeAmount : ℕ,
        Spec.Goals.WithdrawalWay r.final.state.config spentAmt payout feeAmount
        ∧ spentAmt / 2 ≤ payout
        -- an honest transaction using that way:
        ∧ ∀ (tx : TransactTx) (sysvarRent : Option (Nat → U64)) (witness : Spec.Witness) (k : ℕ),
          ReachesProgram d s tx.accounts tx.args.proof →   -- [owner] the transaction as submitted
          SameRent rent sysvarRent →                       -- [assumption] same rent as the spec
          tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8 → -- [finding A0] excluded
          let inputs := toInputs tx
          Spec.HonestSpend r wit inputs witness k →    -- [owner] everything the owner controls
          witness.inAmt 0 + witness.inAmt 1 = (spentAmt : Spec.F) → -- [premise] it spends `spentAmt`
          inputs.extAmt = -(payout : ℤ) → inputs.f = feeAmount → -- [owner] it uses this split
          inputs.R ∈ Set.range r.final.state.tree.history → -- [limit] the root is in the history
          Spec.treeHasRoom r.final.state.tree →        -- [limit] the tree is not full
          Spec.balancesFit inputs r.final →            -- [limit] no credited balance overflows
          Accepts d s (tx.env sysvarRent) tx.instruction
            ∨ Spec.SpendBlockedByBreak r wit inputs witness k
            ∨ AddressCollision d {tx.args.proof} :=
  admins_cannot_lock_withdrawals_pf reachable notSystem C laws hashes crypto runtime pdas initialized

end

/-! ## 2. Non-vacuity

The goals about histories and G2a, G4a, G4b are covered by `connection_nonvacuous` and
`transact_connection_nonvacuous` (`NonVacuityStatements.lean`). Here, in the same deliberately
insecure example deployment:
- **`admin_change_nonvacuous`:** `initialize`, `update_deposit_limit`, then a deposit; every run
  records the admin change, so G5a and G5b are not vacuous on one.
- **`liveness_code_nonvacuous`:** the withdrawal of `connection_nonvacuous`, with every split
  G3b allows, meets every hypothesis of G3a and G3b for the code, and `step` accepts it. -/

section
-- The spec's hashes, groups, pairing, key and SOL mint are the example deployment's, as the
-- theorems fix them (`syscallGroups`, `syscallPairing`, `programDeployment`).
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha Toy.toySpecGroups Toy.toySpecG1Group
  Toy.toySpecG1Module Toy.toySpecGTGroup Toy.toySpecPairing
  Toy.toySpecDeployment

/-- **G5a and G5b for the code are not vacuous on an admin change**: the execution `initialize`,
    `update_deposit_limit` signed by the authority, then a deposit of 2 lamports, meets every
    hypothesis of `run_connection`, and every run of it (`IsRunOf`) records an admin change. -/
theorem admin_change_nonvacuous :
    ∃ (sGenesis s : CodeModel.State) (evs : List CodeModel.Event) (states : List CodeModel.State),
      -- every hypothesis of `run_connection`, for the example deployment
      CodeModel.Genesis Toy.toyD.programId sGenesis ∧ ExecutionPath Toy.toyD sGenesis evs states s
      ∧ ProgramNotSystem Toy.toyD ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD
      ∧ ExecutionAssumptions Toy.toyD evs ∧ ¬ AddressCollision Toy.toyD (proofsIn evs)
      ∧ (∀ txEnv ix em, .program txEnv ix em ∈ evs → SameRent Toy.toyRent txEnv.minimumBalance)
      -- the pool is initialized
      ∧ Initialized Toy.toyD s
      -- every run of the execution records an admin change
      ∧ ∀ params r, IsRunOf Toy.toyD Toy.toyRent sGenesis evs states s params r →
          r.adminChangesUpTo r.txs.length ≠ [] :=
  Toy.toy_admin_change_nonvacuous

/-- **G3a and G3b for the code are not vacuous, with a real spend the code accepts**: after
    `initialize` and a deposit of 2 lamports, for every way to withdraw 2 lamports
    (`WithdrawalWay`), the withdrawal spending the deposit's note that way meets every
    hypothesis of `honestSpendIsAccepted_code` and `adminsCannotLockWithdrawals_code`, and
    `step` accepts it. -/
theorem liveness_code_nonvacuous
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ (s : CodeModel.State)
      (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness),
      -- the hypotheses of the section, for the example deployment
      CodeModel.Reachable Toy.toyD s ∧ ProgramNotSystem Toy.toyD
      ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD ∧ CryptoSucceeds Toy.toyD.crypto Toy.toyC
      ∧ RuntimeFacts Toy.toyRent
      ∧ PdasOnlyByProgram Toy.toyD s ∧ Initialized Toy.toyD s
      -- the hypotheses of G3a and G3b for the code about the run
      ∧ toWorld Toy.toyD Toy.toyRent s = r.final
      ∧ r.WitnessesFor wit
      -- for every way to withdraw 2 lamports
      ∧ ∀ payout feeAmount : ℕ,
        Spec.Goals.WithdrawalWay r.final.state.config 2 payout feeAmount →
        ∃ (tx : TransactTx) (sysvarRent : Option (Nat → U64)) (witness : Spec.Witness) (k : ℕ),
          let inputs := toInputs tx
          -- the hypotheses of G3a for the code about the transaction
          ReachesProgram Toy.toyD s tx.accounts tx.args.proof ∧ SameRent Toy.toyRent sysvarRent
          ∧ tx.args.extAmount.val ≠ 0 ∧ tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8
          ∧ Spec.HonestSpend r wit inputs witness k
          ∧ Spec.LimitsNotHit r.final inputs
          -- a real spend
          ∧ witness.inAmt 0 ≠ 0
          -- the further hypotheses of G3b for the code: it spends 2 lamports, using that way
          ∧ witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : Spec.F)
          ∧ inputs.extAmt = -(payout : ℤ) ∧ inputs.f = feeAmount
          -- the code accepts it
          ∧ Accepts Toy.toyD s (tx.env sysvarRent) tx.instruction :=
  Toy.toy_G3_code_nonvacuous h64

end

end Connection
