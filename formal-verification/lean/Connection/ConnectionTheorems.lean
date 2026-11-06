import Connection.Proofs.Checks
import Connection.Proofs.ExtData
import Connection.Proofs.Tree
import Connection.Proofs.Verifier
import Connection.Proofs.Transact
import Connection.Proofs.Bridge
import Connection.Proofs.WellFormed
import Connection.Proofs.HandlerComplete
import Connection.Proofs.ToyRun
import Connection.Proofs.ToySpend
import Connection.Proofs.Execution
import Connection.Proofs.StepComplete
import Connection.Proofs.ToyG3
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Connection theorems

REVIEW SURFACE, with `Connection/Mapping.lean` (how code values and executions map to the
spec), `Connection/Hypotheses.lean` (the hypotheses) and `Connection/Findings.lean` (the
differences found). Everything here is proved by one line pointing into `Connection/Proofs/`,
which is not for review.

1. **The two connection theorems.** `transact_connection`: every `transact` the code accepts
   satisfies the spec's `transact` (all preconditions, exact effects). `run_connection`: code
   executions are spec runs, up to the mapping. Every conclusion below rests on them.
2. **The security goals hold for the code.** Each goal is a named property of the spec,
   defined and proved in `Spec/Statements.lean` (`LeanSpec.Goals`); here the same
   property is stated of the code. Goals about runs (G1a–G1d, G5a, G5b) hold of the execution's
   run; goals about one transaction (G2a, G4a, G4b) hold of every transaction the code
   accepts. That the code checks every accepted transaction's proof is part of
   `transact_connection` (the spec's `transact` requires `validZKP`). G2b is about circuit
   witnesses only (no code involved). G3a and G3b (liveness) are proved separately: if the
   transaction gets past Anchor (`ReachesProgram`), the code accepts it.
3. **Non-vacuity**: the hypotheses can all hold together.

Scope: safety, except G3a and G3b, which say the code accepts a transaction assuming it gets past
Anchor's account checks (see `Findings.lean` for handler completeness).

Every code-level statement starts with the same three `letI` lines. They only fix which
cryptography the spec uses: its groups and pairing are the `alt_bn128` syscalls'
(`syscallGroups`, `syscallPairing`) and its verifying key is the program's (`programKey`). -/

namespace Connection

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-! ## 1. The two connection theorems -/

/-- **Every `transact` the code accepts satisfies the spec's `transact`.** In any execution of
    the code model from genesis, if `step` accepts a `transact`, then between the worlds before
    and after (mapped by `toWorld`) the spec's `transact` holds for the mapped transaction
    (`toInputs`): every spec precondition held, the proof check included, and the new world is
    exactly the spec's `transactEffects`. The spec's nullifier set is the one the execution
    spent before. -/
theorem transact_connection
    {d : Deployment} {rent : Nat → U64} {s₀ s s' : State} {evs : List Event} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hgen : Genesis d.programId s₀)                        -- [premise] an execution from genesis
    (hrun : Run d s₀ evs s)                                --   ...that reached `s`
    (hpid : d.programId ≠ systemProgram)                   -- [assumed] not the system program
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
                                                           -- [premise] the code accepts a transact
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)     -- [assumed] the syscall contracts
    (laws : PairingLaws C.e)                               -- [assumed] the pairing laws
    (hashes : HashesAgree d.crypto)                        -- [assumed] the hashes are the spec's
    (solana : SolanaFacts d rent tx out1 out2)             -- [assumed] Solana runtime facts
    (crypto : CryptoFacts d proof)                         -- [assumed] circuit and SHA-256 facts
    (outside : OutsideSpecDetail d rent s tx a proof) :    -- [by design] details the spec omits
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    LeanSpec.transact inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside

/-- **Every execution of the code model is a run of the spec.** Either the pool has not been
    initialized (and no transaction was accepted), or the final state is the end of a spec run
    (`IsSpecRun`): the run this execution went through (`IsRunOf`): from the start world
    `initialize` set, with the execution's transactions (`runTxs`) and their results, and the
    admin instructions with the signers of their transactions, up to what happened after the last
    transaction. `initialize` gives the start world; each accepted `transact` is a spec
    transaction; outside actions and the admin instructions are changes the spec allows between
    transactions. No by-design exclusion: a pre-funded nullifier
    address, or a payee that is a nullifier account, is such an allowed change before or after
    the spec transaction. -/
theorem run_connection {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    {states : List State}
    (hgen : Genesis d.programId s₀)                        -- [premise] an execution from genesis
    (hrun : ExecutionPath d s₀ evs states s)               --   ...that reached `s` through `states`
    (hpid : d.programId ≠ systemProgram)                   -- [assumed] not the system program
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)     -- [assumed] the syscall contracts
    (laws : PairingLaws C.e)                               -- [assumed] the pairing laws
    (hashes : HashesAgree d.crypto)                        -- [assumed] the hashes are the spec's
    (assume : ExecutionAssumptions d rent s₀ evs) :        -- [assumed] every step's rent,
                                                           --   `SolanaFacts`, `CryptoFacts`;
                                                           --   the fixed addresses differ
    (NoProgramAccounts d s ∧ runTxs evs = []) ∨
      (letI : LeanSpec.Groups := syscallGroups C
       letI : LeanSpec.Pairing := syscallPairing C laws
       letI : LeanSpec.Deployment := ⟨programKey C⟩
       IsSpecRun d rent s₀ evs states s) :=
  execution_is_spec_run_pf hgen hrun hpid C laws hashes assume

end

/-! ## 2. The security goals hold for the code

### Goals about runs: they hold of the execution's run

For an execution `evs` from a genesis state `s₀` to `s` that initialized the pool, under the
hypotheses of `run_connection`: the execution's run (`IsRunOf`) satisfies the goal, for any
witnesses of its proofs (T1) where the goal needs them. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event} {states : List State}
  (hgen : Genesis d.programId s₀)                          -- [premise] an execution from genesis
  (hrun : ExecutionPath d s₀ evs states s)                 --   ...that reached `s` through `states`
  (hpid : d.programId ≠ systemProgram)                     -- [assumed] not the system program
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)       -- [assumed] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumed] the pairing laws
  (hashes : HashesAgree d.crypto)                          -- [assumed] the hashes are the spec's
  (assume : ExecutionAssumptions d rent s₀ evs)            -- [assumed] as in `run_connection`
  (hi : Initialized d s)                                   -- [premise] the pool is initialized
include hgen hrun hpid C laws hashes assume hi

/-- **G1a for the code**: every spend in the execution is of a real note
    (`SpendsAreGenuine`). -/
theorem spendsAreGenuine_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.SpendsAreGenuine r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.spends_are_genuine params r

/-- **G1b for the code**: no note is spent twice in the execution (`NoDoubleSpend`). -/
theorem noDoubleSpend_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.NoDoubleSpend r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.no_double_spend params r

/-- **G1c for the code**: at the end of the execution, the pool's SOL exactly backs the
    unspent notes (`PoolBacksNotes`). -/
theorem poolBacksNotes_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.PoolBacksNotes params r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.balance params r

/-- **G1d for the code**: every spend in the execution uses the owner's secret key
    (`OnlyOwnerSpends`). -/
theorem onlyOwnerSpends_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.OnlyOwnerSpends r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _
    fun params r => LeanSpec.Goals.honest_note_spent_only_with_owner_key params r

/-- **G5a for the code**: the execution's run satisfies `OnlyAuthoritiesChangeConfig`: its admin
    changes are the code's, each signed by whoever initialized the pool, and they alone produced
    the config (with `IsRunOf`: the initializer is the deployment's admin key, when it has one). -/
theorem onlyAuthoritiesChangeConfig_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      LeanSpec.Goals.OnlyAuthoritiesChangeConfig params r :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _
    fun params r => LeanSpec.Goals.only_authorities_change_config params r

/-- **G5b for the code**: the execution's run satisfies `AdminPowersLimited`: the authorities stay
    whoever initialized the pool, and the fee rates and fee error margin stay at most 100%. -/
theorem adminPowersLimited_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      LeanSpec.Goals.AdminPowersLimited params r :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _
    fun params r => LeanSpec.Goals.admin_powers_limited params r

/-- **G5a on the execution's events**: only the authorities change the config.

    What `initialize` set up (`i`) satisfies:
    - **the initializer signed:** its authority is among the signers of its transaction;
    - **the admin key:** the initializer is the deployment's admin key, when it has one;
    - **the authorities:** both are the initializer;
    - **every admin instruction:** each `update_deposit_limit` and `update_global_config` in the
      execution, also after its last transaction, has the initializer among its signers.

    Follows from G5a, G5b and `IsRunOf`, which records these instructions. -/
theorem adminInstructionsSigned_code :
    ∃ i : InitRecord, (executionView d rent s₀ evs states).init = some i ∧
      i.initializer ∈ i.signers ∧
      (∀ a, d.adminPubkey.map toPubkey = some a → i.initializer = a) ∧
      i.world.state.config.authority = i.initializer ∧
      i.world.state.config.limitAuthority = i.initializer ∧
      ∀ tx ∈ adminTxs evs, i.initializer ∈ tx.signers.map toPubkey :=
  admin_instructions_signed_pf hgen hrun hpid C laws hashes assume hi

end

/-! ### Goals about one transaction: they hold of every transaction the code accepts

For a `transact` that `step` accepts in an execution from genesis, under the hypotheses of
`transact_connection`, between the mapped worlds before and after. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s s' : State} {evs : List Event} {tx : TxEnv}
  {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
  {out1 out2 : Slice U8} {events : List CommitmentData}
  (hgen : Genesis d.programId s₀)                          -- [premise] an execution from genesis
  (hrun : Run d s₀ evs s)                                  --   ...that reached `s`
  (hpid : d.programId ≠ systemProgram)                     -- [assumed] not the system program
  (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
                                                           -- [premise] the code accepts a transact
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)       -- [assumed] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumed] the pairing laws
  (hashes : HashesAgree d.crypto)                          -- [assumed] the hashes are the spec's
  (solana : SolanaFacts d rent tx out1 out2)               -- [assumed] Solana runtime facts
  (crypto : CryptoFacts d proof)                           -- [assumed] circuit and SHA-256 facts
  (outside : OutsideSpecDetail d rent s tx a proof)        -- [by design] details the spec omits
include hgen hrun hpid hstep C laws hashes solana crypto outside

/-- **G2a for the code**: if the accepted transaction has the public inputs of a
    well-formed honest transaction `T`, the two pay out the same (`SamePayout`). -/
theorem samePayout_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∀ T, LeanSpec.Goals.ExtDataWellFormed T
      ∧ T.pubInputs = (toInputs tx.signers a proof extAmount fee out1 out2).pubInputs →
      LeanSpec.Goals.SamePayout T (toInputs tx.signers a proof extAmount fee out1 out2) :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  fun T ⟨hT, hSame⟩ => LeanSpec.Goals.same_public_inputs_same_external_data T hT _ _ _ hSame
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G4a for the code**: in the accepted transaction, only accounts that signed pay, and at most
    what they agreed to (`OnlySignersPay`). Like `transact_connection`, it excludes what
    `OutsideSpecDetail` rules out: a pre-funded nullifier address, or a payee that is a nullifier
    account. -/
theorem onlySignersPay_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    LeanSpec.Goals.OnlySignersPay inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.only_signers_pay _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G4b for the code**: in the accepted transaction, every account changes by exactly what
    it should receive minus what it should pay (`ExactPayouts`). Like `transact_connection`, it
    excludes what `OutsideSpecDetail` rules out: a pre-funded nullifier address, or a payee that is
    a nullifier account. -/
theorem exactPayouts_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    LeanSpec.Goals.ExactPayouts inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.exact_payouts _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

end

/-! ### Liveness: G3a and G3b

**These assume the transaction gets past Anchor's account checks** (`ReachesProgram`): they cover
Anchor's `init`s, the handler and the runtime's lamport check, not the account constraints. They
also take nothing to have changed since the run's last transaction (`hfinal`), so a transfer or an
admin change in that gap isn't covered. "Accepted" means by the code model's `step`, which leaves
out some of Solana's rejections (`core-model/README.md`: writable flags, rent exemption, compute
and size limits).

`r` is any spec run ending at the code's world, so in particular the execution's own (`IsRunOf`). -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
  (hgen : Genesis d.programId s₀)                          -- [premise] an execution from genesis
  (hrun : Run d s₀ evs s)                                  --   ...that reached `s`
  (hpid : d.programId ≠ systemProgram)                     -- [assumed] not the system program
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)       -- [assumed] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumed] the pairing laws
  (assume : CompletenessAssumptions d.crypto C)            -- [assumed] the primitives answer
include hgen hrun hpid C laws assume

/-- **G3a for the code.** An honest spend with no limit hit is accepted by `step`, or a hash break
    occurs. Assumes it gets past Anchor (`ReachesProgram`).

    Excluded by name, because the code rejects them: L1 (an internal transfer) and A0
    (`Findings.lean`). -/
theorem honestSpendIsAccepted_code
    {tx : TxEnv} {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (reach : ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config) -- see the structure
    (notL1 : ext.val ≠ 0)                                  -- [finding L1] excluded
    (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) : -- [finding A0] excluded
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof ext fee out1 out2
    ∀ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
      (wit : ℕ → LeanSpec.Witness) (witness : LeanSpec.Witness) (k : ℕ),
      toWorld d rent (runSpent evs) s = r.final →          -- [by design] G3 speaks about `r.final`
      r.WitnessesFor wit →                                 -- [assumption T1]
      LeanSpec.HonestSpend r wit inputs witness k →        -- [owner]
      LeanSpec.LimitsNotHit r.final inputs →               -- [limit]
      (∃ s' events, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events))
        ∨ LeanSpec.SpendBlockedByBreak r wit witness k :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  fun params r wit witness k hfinal hwit hH hL =>
    (LeanSpec.Goals.honest_spend_is_accepted params r wit hwit _ witness k hH hL).imp_left
      (step_accepts_of_spec C laws assume (wf_reachable hgen hrun hpid assume.hashesAgree) reach notL1 notA0 _ hfinal)

/-- **G3b for the code.** A way to withdraw notes worth `spentAmt` lamports exists, at least half
    of `spentAmt` reaches the recipient, and an honest transaction using that way is accepted by `step`, or a
    hash break occurs. Assumes it gets past Anchor (`ReachesProgram`).

    L1 can't arise: a withdrawal's amount isn't zero. A0 is excluded by name (`Findings.lean`). -/
theorem adminsCannotLockWithdrawals_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∀ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
      (wit : ℕ → LeanSpec.Witness) (spentAmt : ℕ),
      toWorld d rent (runSpent evs) s = r.final →          -- [by design] G3 speaks about `r.final`
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
          ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config → -- see the structure
          proof.proof_a.val ≠ List.replicate 64 0#u8 →     -- [finding A0] excluded
          let inputs := toInputs tx.signers a proof ext fee out1 out2
          LeanSpec.HonestSpend r wit inputs witness k →    -- [owner] everything the owner controls
          witness.inAmt 0 + witness.inAmt 1 = (spentAmt : LeanSpec.F) → -- [owner] it spends `spentAmt`
          inputs.extAmt = -(payout : ℤ) → inputs.f = feeAmount → -- [owner] it uses this split
          inputs.R ∈ Set.range r.final.state.tree.history → -- [limit] the root is in the history
          LeanSpec.treeHasRoom r.final.state.tree →        -- [limit] the tree is not full
          LeanSpec.balancesFit inputs r.final →            -- [limit] no credited balance overflows
          (∃ s' events, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events))
            ∨ LeanSpec.SpendBlockedByBreak r wit witness k :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  fun params r wit spentAmt hfinal hwit hSpentAmt =>
    let ⟨payout, feeAmount, hway, hhalf, haccept⟩ :=
      LeanSpec.Goals.admins_cannot_lock_withdrawals params r wit hwit spentAmt hSpentAmt
    ⟨payout, feeAmount, hway, hhalf, fun _ _ _ ext _ _ _ _ _ _ witness k reach notA0 hH hV hA hF hW hR hB =>
      (haccept _ witness k hH hV hA hF hW hR hB).imp_left
        (step_accepts_of_spec C laws assume (wf_reachable hgen hrun hpid assume.hashesAgree) reach
          (fun h0 => by
            have h1 := hway.1
            have h2 : (ext.val : ℤ) = -(payout : ℤ) := hA
            omega) notA0 _ hfinal)⟩

end

/-! ## 3. Non-vacuity

One toy execution satisfies every hypothesis of the connection theorems: genesis,
`initialize`, a deposit of 2 lamports, then a withdrawal of 1 lamport with a fee of 1 that spends the note the
deposit created.
- **`connection_nonvacuous`:** it satisfies every hypothesis of `run_connection` and of the
  goals about runs, with a real spend.
- **`admin_connection_nonvacuous`:** a second execution, `initialize` then `update_deposit_limit`,
  satisfies them with an admin instruction.
- **`transact_connection_nonvacuous`:** its deposit and its withdrawal each satisfy every
  hypothesis of `transact_connection`.

The toy deployment is deliberately broken (`Proofs/Toy.lean`: `G1 = G2 = GT = Unit`, every
pairing 1, Poseidon always 1, SHA-256 always zero; the G1 decoding is the real one; a toy PDA
derivation). It shows the hypotheses can hold together, not that real cryptography reaches
the outcome.

The circuit's hashes `H1`, `H3`, `H4` are never computed by the code; the toy takes `H1` the
identity and `H3`, `H4` the sums of their arguments, so that the toy transactions have circuit
witnesses. In this section the spec's hashes are the toy's. -/

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **The connection theorems are not vacuous, with a real spend**: an execution with two
    transactions, a deposit and then a withdrawal.

    - **`run_connection`'s hypotheses** all hold for it;
    - **the hypotheses of the goals about runs** hold too: the pool is initialized, and
      `wit` are circuit witnesses for both transactions (so for every spec run of the
      execution: `IsRunOf` fixes its transactions to `runTxs evs`);
    - **a real spend:** in `wit` the withdrawal (transaction 1) spends a non-zero note, the
      one at leaf 0, which the deposit created.
    So the goals G1a–G1d are not vacuous on a spend. -/
theorem connection_nonvacuous :
    ∃ (d : Deployment) (s₀ s : State) (evs : List Event) (states : List State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- every hypothesis of `run_connection`
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ ExecutionPath d s₀ evs states s ∧ d.programId ≠ systemProgram
      ∧ HashesAgree d.crypto ∧ ExecutionAssumptions d Toy.toyRent s₀ evs
      -- the pool is initialized, and the execution has two transactions
      ∧ Initialized d s ∧ (runTxs evs).length = 2
      -- with circuit witnesses for both transactions
      ∧ ∃ wit : ℕ → LeanSpec.Witness,
        (∀ j (h : j < (runTxs evs).length), LeanSpec.RelationS (runTxs evs)[j].pubInputs (wit j))
        -- in which transaction 1 spends a real note, the one the deposit put at leaf 0
        ∧ (wit 1).inAmt 0 ≠ 0 ∧ LeanSpec.openedPos wit 1 0 = 0
        ∧ (wit 1).inNote 0 = LeanSpec.leafNote wit 0 :=
  Toy.toy_spend_nonvacuous

/-- **`adminInstructionsSigned_code` is not vacuous**: an execution with an accepted admin
    instruction, `update_deposit_limit` signed by the authority, satisfies every hypothesis of
    `run_connection` and initializes the pool. -/
theorem admin_connection_nonvacuous :
    ∃ (d : Deployment) (s₀ s : State) (evs : List Event) (states : List State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ ExecutionPath d s₀ evs states s ∧
      d.programId ≠ systemProgram ∧ HashesAgree d.crypto ∧
      ExecutionAssumptions d Toy.toyRent s₀ evs ∧ Initialized d s ∧ adminTxs evs ≠ [] :=
  Toy.toy_admin_nonvacuous

/-- **`transact_connection` is not vacuous, for a deposit and for a withdrawal**: in one
    deployment satisfying the deployment-level hypotheses (`PairingLaws`, genesis, the program
    is not the system program, `HashesAgree`), the code accepts a deposit (`extAmount > 0`) and
    a withdrawal (`extAmount < 0`), each in an execution from genesis and each satisfying the
    per-transaction hypotheses (`SolanaFacts`, `CryptoFacts`, `OutsideSpecDetail`). The two
    cover both payment paths: the signer pays the pool, and the pool pays the recipient. -/
theorem transact_connection_nonvacuous :
    ∃ (d : Deployment) (rent : Nat → U64) (s₀ : State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- the deployment-level hypotheses of `transact_connection`
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ d.programId ≠ systemProgram ∧ HashesAgree d.crypto
      -- a deposit the code accepts, with the per-transaction hypotheses
      ∧ (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
          (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8)
          (events : List CommitmentData),
        Run d s₀ evs s ∧ step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events)
        ∧ extAmount.val > 0
        ∧ SolanaFacts d rent tx out1 out2 ∧ CryptoFacts d proof ∧ OutsideSpecDetail d rent s tx a proof)
      -- and a withdrawal the code accepts, with the per-transaction hypotheses
      ∧ (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
          (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8)
          (events : List CommitmentData),
        Run d s₀ evs s ∧ step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events)
        ∧ extAmount.val < 0
        ∧ SolanaFacts d rent tx out1 out2 ∧ CryptoFacts d proof ∧ OutsideSpecDetail d rent s tx a proof) :=
  Toy.toy_transact_nonvacuous

end

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **G3a and G3b for the code are not vacuous, with a real spend**: after `initialize` and a deposit
    of 2 lamports, with nothing changed since, the withdrawal spending the deposit's note, as a
    payout of 1 and a fee of 1, satisfies every hypothesis of `honestSpendIsAccepted_code` and of
    `adminsCannotLockWithdrawals_code`. -/
theorem liveness_code_nonvacuous :
    ∃ (s₀ s : State) (evs : List Event) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
      (tt : zkcash_core.admin.TreeTokenAccount) (config : zkcash_core.admin.GlobalConfig),
      -- the hypotheses before the run
      Genesis Toy.toyD.programId s₀ ∧ Run Toy.toyD s₀ evs s ∧ Toy.toyD.programId ≠ systemProgram
      ∧ PairingLaws Toy.toyC.e ∧ CompletenessAssumptions Toy.toyD.crypto Toy.toyC
      ∧ ReachesProgram Toy.toyD Toy.toyRent s Toy.toyTx Toy.spendA Toy.spendProof Toy.wdExt 1#u64
          Toy.emptySlice Toy.emptySlice tree tt config
      ∧ Toy.wdExt.val ≠ 0 ∧ Toy.spendProof.proof_a.val ≠ List.replicate 64 0#u8
      -- the run, and the hypotheses about it
      ∧ letI : LeanSpec.Groups := syscallGroups Toy.toyC
        letI : AddCommGroup LeanSpec.G1 := inferInstanceAs (AddCommGroup Unit)
        letI : Module LeanSpec.F LeanSpec.G1 := inferInstanceAs (Module LeanSpec.F Unit)
        letI : AddCommGroup LeanSpec.G2 := inferInstanceAs (AddCommGroup Unit)
        letI : Module LeanSpec.F LeanSpec.G2 := inferInstanceAs (Module LeanSpec.F Unit)
        letI : CommGroup LeanSpec.GT := inferInstanceAs (CommGroup Unit)
        letI : LeanSpec.Pairing := syscallPairing Toy.toyC Toy.toyLaws
        letI : LeanSpec.Deployment := ⟨programKey Toy.toyC⟩
        let inputs := toInputs Toy.toyTx.signers Toy.spendA Toy.spendProof Toy.wdExt 1#u64
          Toy.emptySlice Toy.emptySlice
        ∃ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
          (wit : ℕ → LeanSpec.Witness) (witness : LeanSpec.Witness) (k : ℕ),
          toWorld Toy.toyD Toy.toyRent (runSpent evs) s = r.final ∧
          r.WitnessesFor wit ∧
          LeanSpec.HonestSpend r wit inputs witness k ∧
          LeanSpec.LimitsNotHit r.final inputs ∧
          witness.inAmt 0 ≠ 0 ∧
          -- it spends 2 lamports as a payout of 1 and a fee of 1, a way to withdraw (G3b)
          witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : LeanSpec.F) ∧
          inputs.extAmt = -((1 : ℕ) : ℤ) ∧ inputs.f = 1 ∧
          LeanSpec.Goals.WithdrawalWay r.final.state.config 2 1 1 :=
  Toy.toy_G3_code_nonvacuous

end

end Connection
