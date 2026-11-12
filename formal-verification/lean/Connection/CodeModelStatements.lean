import Connection.ConnectionTheorems
import Connection.Proofs.Goals
import Connection.Proofs.ToyG3
import Connection.Proofs.ToyAdmin
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The spec's security goals, stated of the code model

REVIEW SURFACE, read after `Connection/ConnectionTheorems.lean`. Every proof here is one line
pointing into `Connection/Proofs/`, which is not for review.

A sanity check, not a new result: each goal is a named property of the spec, defined and proved
in `Spec/Statements.lean` (`LeanSpec.Goals`); here the same property is stated of the code and
follows from the connection theorems in `ConnectionTheorems.lean` (`run_connection`,
`transact_connection`, and for G3 the completeness behind `handler_complete_except_L1_A0`).

## Contents

1. **The security goals hold for the code.** Grouped by hypotheses, so that each set is stated
   once; within that, in the order of `Spec/Statements.lean`: G1, G5 | G2, G4 | G3.
   Goals about runs (G1a–G1d, G5a, G5b) hold of the execution's run; goals about one
   transaction (G2a, G4a, G4b) hold of every transaction the code accepts. That the code checks
   every accepted transaction's proof is part of `transact_connection` (the spec's `transact`
   requires `validZKP`). G2b is about circuit witnesses only (no code involved). G3a and G3b
   (liveness) use completeness.
2. **Non-vacuity** of the statements here not already covered in `ConnectionTheorems.lean`.

As in `ConnectionTheorems.lean`, every statement starts with the same three `letI` lines, which
only fix the spec's cryptography to the deployment's (`syscallGroups`, `syscallPairing`,
`programKey`). -/

namespace Connection

/-! ## 1. The security goals hold for the code

### G1 and G5: goals about runs, they hold of the execution's run

For an execution `evs` from a genesis state `sGenesis` to `s` that initialized the pool, under the
hypotheses of `run_connection`: the execution's run (`IsRunOf`) satisfies the goal, for any
witnesses of its proofs (T1) where the goal needs them. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
variable {d : Deployment} {rent : Nat → U64} {sGenesis s : State} {evs : List Event} {states : List State}
  (deploy : DeploymentFacts d)                             -- [assumed] see the structure
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)       -- [assumed] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumed] the pairing laws
  (hashes : HashesAgree d.crypto)                          -- [assumed] the hashes are the spec's
  (assume : ExecutionAssumptions d sGenesis evs)      -- [assumed] as in `run_connection`
  (outside : ExecutionOutsideSpecDetail d rent sGenesis evs) -- [by design] the rent is fixed
  (hgen : Genesis d.programId sGenesis)                    -- [premise] an execution from genesis
  (hrun : ExecutionPath d sGenesis evs states s)           --   ...that reached `s` through `states`
  (hi : Initialized d s)                                   -- [premise] the pool is initialized
include deploy C laws hashes assume outside hgen hrun hi

/-! #### G1. Balance -/

/-- **G1a for the code**: every spend in the execution is of a real note
    (`SpendsAreGenuine`). -/
theorem spendsAreGenuine_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.SpendsAreGenuine r wit :=
  spends_are_genuine_pf hgen hrun deploy.programNotSystem C laws hashes assume outside hi

/-- **G1b for the code**: no note is spent twice in the execution (`NoDoubleSpend`). -/
theorem noDoubleSpend_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.NoDoubleSpend r wit :=
  no_double_spend_pf hgen hrun deploy.programNotSystem C laws hashes assume outside hi

/-- **G1c for the code**: at the end of the execution, the pool's SOL exactly backs the
    unspent notes (`PoolBacksNotes`). -/
theorem poolBacksNotes_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.PoolBacksNotes params r wit :=
  pool_backs_notes_pf hgen hrun deploy.programNotSystem C laws hashes assume outside hi

/-- **G1d for the code**: every spend in the execution uses the owner's secret key
    (`OnlyOwnerSpends`). -/
theorem onlyOwnerSpends_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.OnlyOwnerSpends r wit :=
  only_owner_spends_pf hgen hrun deploy.programNotSystem C laws hashes assume outside hi

/-! #### G5. Admin control -/

/-- **G5a for the code**: the execution's run satisfies `OnlyAuthoritiesChangeConfig`: its admin
    changes are the code's, each signed by whoever initialized the pool, and they alone produced
    the config (with `IsRunOf`: the initializer is the deployment's admin key, when it has one). -/
theorem onlyAuthoritiesChangeConfig_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      LeanSpec.Goals.OnlyAuthoritiesChangeConfig params r :=
  only_authorities_change_config_pf hgen hrun deploy.programNotSystem C laws hashes assume outside hi

/-- **G5b for the code**: the execution's run satisfies `AdminPowersLimited`: the authorities stay
    whoever initialized the pool, and the fee rates and fee error margin stay at most 100%. -/
theorem adminPowersLimited_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent sGenesis evs states s params r ∧
      LeanSpec.Goals.AdminPowersLimited params r :=
  admin_powers_limited_pf hgen hrun deploy.programNotSystem C laws hashes assume outside hi

end

/-! ### G2 and G4: goals about one transaction, they hold of every transaction the code accepts

For a `transact` that `step` accepts in an execution from genesis, under the hypotheses of
`transact_connection`, between the mapped worlds before and after. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
variable {d : Deployment} {rent : Nat → U64} {sGenesis s s' : State} {evs : List Event} {tx : TxEnv}
  {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
  {out1 out2 : Slice U8} {events : List CommitmentData}
  (deploy : DeploymentFacts d)                             -- [assumed] see the structure
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)       -- [assumed] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumed] the pairing laws
  (hashes : HashesAgree d.crypto)                          -- [assumed] the hashes are the spec's
  (solana : SolanaFacts d tx)               -- [assumed] Solana runtime facts
  (crypto : CryptoFacts d proof)                           -- [assumed] SHA-256 facts
  (circuit : CircuitFacts d {proof})                     -- [assumed] the circuit keeps the nullifiers distinct (I1)
  (outside : OutsideSpecDetail d rent s tx a proof)        -- [by design] details the spec omits
  (hgen : Genesis d.programId sGenesis)                    -- [premise] an execution from genesis
  (hrun : Run d sGenesis evs s)                            --   ...that reached `s`
  (hstep : Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s')
                                                           -- [premise] ...then accepted a transact (one more step)
include deploy C laws hashes solana crypto circuit outside hgen hrun hstep

/-! #### G2. Non-malleability

G2b (`shared_nullifier_requires_owner_key`) has no code version: it is about circuit witnesses
only, with no code involved. -/

/-- **G2a for the code**: if the accepted transaction has the public inputs of a
    well-formed honest transaction `T`, the two pay out the same (`SamePayout`). Like
    `transact_connection`, it excludes what `OutsideSpecDetail` rules out. -/
theorem samePayout_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    ∀ (T : LeanSpec.TxInputs)                              -- [premise] an honest transaction, seen
                                                           --   but not yet accepted
      (_hT : LeanSpec.Goals.ExtDataWellFormed T)           -- [premise] ...well formed
      (_hSame : T.pubInputs = inputs.pubInputs),           -- [attacker] the accepted transaction
                                                           --   has its public inputs
      LeanSpec.Goals.SamePayout T inputs :=
  same_payout_pf hgen hrun deploy.programNotSystem hstep C laws hashes solana crypto circuit outside

/-! #### G4. Correct public payouts -/

/-- **G4a for the code**: in the accepted transaction, only accounts that signed pay, and at most
    what they agreed to (`OnlySignersPay`). Like `transact_connection`, it excludes what
    `OutsideSpecDetail` rules out: a different rent, a pre-funded nullifier address, or a payee that
    is a nullifier account. -/
theorem onlySignersPay_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    LeanSpec.Goals.OnlySignersPay inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  only_signers_pay_pf hgen hrun deploy.programNotSystem hstep C laws hashes solana crypto circuit outside

/-- **G4b for the code**: in the accepted transaction, every account changes by exactly what
    it should receive minus what it should pay (`ExactPayouts`). Like `transact_connection`, it
    excludes what `OutsideSpecDetail` rules out: a different rent, a pre-funded nullifier address, or
    a payee that is a nullifier account. -/
theorem exactPayouts_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    LeanSpec.Goals.ExactPayouts inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  exact_payouts_pf hgen hrun deploy.programNotSystem hstep C laws hashes solana crypto circuit outside

end

/-! ### G3. Liveness: G3a and G3b

**These assume the transaction gets past Anchor's account checks** (`ReachesProgram`): they cover
Anchor's `init`s, the handler and the runtime's lamport check, not the account constraints. They
also take nothing to have changed since the run's last transaction (the premise
`toWorld … = r.final`), so a transfer or an admin change in that gap isn't covered. "Accepted" means by the code model's `step`, which leaves
out some of Solana's rejections (`core-model/README.md`: writable flags, rent exemption, compute
and size limits).

`r` is any spec run ending at the code's world, so in particular the execution's own (`IsRunOf`). -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
variable {d : Deployment} {rent : Nat → U64} {sGenesis s : State} {evs : List Event}
  (deploy : DeploymentFacts d)                             -- [assumed] see the structure
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)       -- [assumed] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumed] the pairing laws
  (hashes : HashesAgree d.crypto)                          -- [assumed] the hashes are the spec's
  (assume : CompletenessAssumptions d.crypto C)            -- [assumed] the primitives answer
  (hgen : Genesis d.programId sGenesis)                    -- [premise] an execution from genesis
  (hrun : Run d sGenesis evs s)                            --   ...that reached `s`
include deploy C laws hashes assume hgen hrun

/-- **G3a for the code.** An honest spend with no limit hit is accepted by `step`, or a hash break
    occurs. Assumes it gets past Anchor (`ReachesProgram`).

    Excluded by name, because the code rejects them: L1 (an internal transfer) and A0
    (`Findings.lean`). -/
theorem honestSpendIsAccepted_code
    {tx : TxEnv} {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (reach : ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config)
                                                           -- [owner, assumed, by design, limit:
                                                           --   one per field] gets past Anchor
    (notL1 : ext.val ≠ 0)                                  -- [finding L1] excluded
    (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) : -- [finding A0] excluded
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof ext fee out1 out2
    ∀ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
      (wit : ℕ → LeanSpec.Witness) (witness : LeanSpec.Witness) (k : ℕ),
      toWorld d rent (runSpent evs) s = r.final →          -- [premise] nothing changed since the
                                                           --   run's last transaction
      r.WitnessesFor wit →                                 -- [assumption T1]
      LeanSpec.HonestSpend r wit inputs witness k →        -- [owner]
      LeanSpec.LimitsNotHit r.final inputs →               -- [limit]
      (∃ s' events, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events))
        ∨ LeanSpec.SpendBlockedByBreak r wit witness k :=
  honest_spend_is_accepted_pf hgen hrun deploy.programNotSystem C laws hashes assume reach notL1 notA0

/-- **G3b for the code.** A way to withdraw notes worth `spentAmt` lamports exists, at least half
    of `spentAmt` reaches the recipient, and an honest transaction using that way is accepted by `step`, or a
    hash break occurs. Assumes it gets past Anchor (`ReachesProgram`).

    L1 can't arise: a withdrawal's amount isn't zero. A0 is excluded by name (`Findings.lean`). -/
theorem adminsCannotLockWithdrawals_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∀ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
      (wit : ℕ → LeanSpec.Witness) (spentAmt : ℕ),
      toWorld d rent (runSpent evs) s = r.final →          -- [premise] nothing changed since the
                                                           --   run's last transaction
      r.WitnessesFor wit →                                 -- [assumption T1]
      2 ≤ spentAmt →                                       -- [premise] the total of the notes the owner spends
      ∃ payout feeAmount : ℕ,
        LeanSpec.Goals.WithdrawalWay r.final.state.config spentAmt payout feeAmount
        ∧ spentAmt / 2 ≤ payout
        -- an honest transaction using that way:
        ∧ ∀ (tx : TxEnv) (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (ext : I64)
            (fee : U64) (out1 out2 : Slice U8) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
            (tt : zkcash_core.admin.TreeTokenAccount) (config : zkcash_core.admin.GlobalConfig)
            (witness : LeanSpec.Witness) (k : ℕ),
          ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config →
                                                           -- [owner, assumed, by design, limit:
                                                           --   one per field] gets past Anchor
          proof.proof_a.val ≠ List.replicate 64 0#u8 →     -- [finding A0] excluded
          let inputs := toInputs tx.signers a proof ext fee out1 out2
          LeanSpec.HonestSpend r wit inputs witness k →    -- [owner] everything the owner controls
          witness.inAmt 0 + witness.inAmt 1 = (spentAmt : LeanSpec.F) → -- [premise] it spends `spentAmt`
          inputs.extAmt = -(payout : ℤ) → inputs.f = feeAmount → -- [owner] it uses this split
          inputs.R ∈ Set.range r.final.state.tree.history → -- [limit] the root is in the history
          LeanSpec.treeHasRoom r.final.state.tree →        -- [limit] the tree is not full
          LeanSpec.balancesFit inputs r.final →            -- [limit] no credited balance overflows
          (∃ s' events, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events))
            ∨ LeanSpec.SpendBlockedByBreak r wit witness k :=
  admins_cannot_lock_withdrawals_pf hgen hrun deploy.programNotSystem C laws hashes assume

end

/-! ## 2. Non-vacuity

The hypotheses of the goals about runs, and of G2a, G4a and G4b, are covered by
`connection_nonvacuous` and `transact_connection_nonvacuous` (`ConnectionTheorems.lean`). Here:
- **`admin_change_nonvacuous`:** `initialize`, `update_deposit_limit`, then a deposit. The admin
  change comes before a transaction, so every run of the execution records it: G5a and G5b for
  the code are not vacuous on an admin change (`connection_nonvacuous` has none).
- **`liveness_code_nonvacuous`:** the withdrawal of `connection_nonvacuous`, with every split of
  the note between recipient and fee that G3b allows (so whichever G3b picks), satisfies every
  hypothesis of G3a and G3b for the code, and `step` accepts it.

Same toy deployment as in `ConnectionTheorems.lean` (deliberately broken cryptography): it shows
the hypotheses can hold together, not that real cryptography reaches the outcome. -/

section
-- The spec's hashes are the toy's; its groups, pairing and key are the toy deployment's, as the
-- theorems fix them (`syscallGroups`, `syscallPairing`, `programKey`).
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha Toy.toySpecGroups Toy.toySpecG1Group
  Toy.toySpecG2Group Toy.toySpecG1Module Toy.toySpecG2Module Toy.toySpecGTGroup Toy.toySpecPairing
  Toy.toySpecDeployment

/-- **G5a and G5b for the code are not vacuous on an admin change**: the toy execution
    `initialize`, `update_deposit_limit` signed by the authority, then a deposit of 2 lamports,
    satisfies every hypothesis of `run_connection` and initializes the pool, and every run of it
    (`IsRunOf`) records an admin change. -/
theorem admin_change_nonvacuous :
    ∃ (sGenesis s : State) (evs : List Event) (states : List State),
      -- every hypothesis of `run_connection`, for the toy deployment
      Genesis Toy.toyD.programId sGenesis ∧ ExecutionPath Toy.toyD sGenesis evs states s
      ∧ DeploymentFacts Toy.toyD ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD.crypto
      ∧ ExecutionAssumptions Toy.toyD sGenesis evs
      ∧ ExecutionOutsideSpecDetail Toy.toyD Toy.toyRent sGenesis evs
      -- the pool is initialized
      ∧ Initialized Toy.toyD s
      -- every run of the execution records an admin change
      ∧ ∀ params r, IsRunOf Toy.toyD Toy.toyRent sGenesis evs states s params r →
          r.adminChangesUpTo r.txs.length ≠ [] :=
  Toy.toy_admin_change_nonvacuous

/-- **G3a and G3b for the code are not vacuous, with a real spend, for whichever way G3b picks,
    and the code accepts it**: after `initialize` and a deposit of 2 lamports, with nothing
    changed since, for every way to withdraw 2 lamports (`WithdrawalWay`), the withdrawal
    spending the deposit's note with that split satisfies every hypothesis of
    `honestSpendIsAccepted_code` and of `adminsCannotLockWithdrawals_code`, and `step` accepts
    it. -/
theorem liveness_code_nonvacuous
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ (sGenesis s : State) (evs : List Event)
      (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
      (wit : ℕ → LeanSpec.Witness),
      -- the hypotheses of the section, for the toy deployment
      Genesis Toy.toyD.programId sGenesis ∧ Run Toy.toyD sGenesis evs s ∧ DeploymentFacts Toy.toyD
      ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD.crypto ∧ CompletenessAssumptions Toy.toyD.crypto Toy.toyC
      -- the hypotheses of G3a and G3b for the code about the run
      ∧ toWorld Toy.toyD Toy.toyRent (runSpent evs) s = r.final
      ∧ r.WitnessesFor wit
      -- for every way to withdraw 2 lamports
      ∧ ∀ payout feeAmount : ℕ,
        LeanSpec.Goals.WithdrawalWay r.final.state.config 2 payout feeAmount →
        ∃ (tx : TxEnv) (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (ext : I64)
          (fee : U64) (out1 out2 : Slice U8) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
          (tt : zkcash_core.admin.TreeTokenAccount) (config : zkcash_core.admin.GlobalConfig)
          (witness : LeanSpec.Witness) (k : ℕ),
          let inputs := toInputs tx.signers a proof ext fee out1 out2
          -- the hypotheses of G3a for the code about the transaction
          ReachesProgram Toy.toyD Toy.toyRent s tx a proof ext fee out1 out2 tree tt config
          ∧ ext.val ≠ 0 ∧ proof.proof_a.val ≠ List.replicate 64 0#u8
          ∧ LeanSpec.HonestSpend r wit inputs witness k
          ∧ LeanSpec.LimitsNotHit r.final inputs
          -- a real spend
          ∧ witness.inAmt 0 ≠ 0
          -- the further hypotheses of G3b for the code: it spends 2 lamports, using that way
          ∧ witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : LeanSpec.F)
          ∧ inputs.extAmt = -(payout : ℤ) ∧ inputs.f = feeAmount
          -- the code accepts it
          ∧ ∃ s' events, step Toy.toyD s tx (.transact a proof ext fee out1 out2) = .ok (s', events) :=
  Toy.toy_G3_code_nonvacuous h64

end

end Connection
