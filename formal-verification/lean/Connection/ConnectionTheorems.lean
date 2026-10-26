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
   property is stated of the code. Goals about runs (G1a–G1d, G3c, G5) hold of the execution's
   run; goals about one transaction (G2a, G4a, G4b) hold of every transaction the code
   accepts. That the code checks every accepted transaction's proof is part of
   `transact_connection` (the spec's `transact` requires `validZKP`). G2b is about circuit
   witnesses only (no code involved); G3a and G3b (liveness) need completeness, which these
   safety theorems don't give.
3. **Non-vacuity**: the hypotheses can all hold together.

Scope: safety. Nothing is claimed about transactions the code rejects (see `Findings.lean` for
handler completeness).

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
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.transact inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside

/-- **Every execution of the code model is a run of the spec.** Either the pool has not been
    initialized (and no transaction was accepted), or the final state is the end of a spec run
    (`IsSpecRun`): from the start world `initialize` set, with the execution's transactions
    (`runTxs`), up to what happened after the last one. `initialize` gives the start world; each
    accepted `transact` is a spec transaction; outside actions and the admin instructions are
    changes the spec allows between transactions. No by-design exclusion: a pre-funded nullifier
    address, or a payee that is a nullifier account, is such an allowed change before or after
    the spec transaction. -/
theorem run_connection {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀)                        -- [premise] an execution from genesis
    (hrun : Run d s₀ evs s)                                --   ...that reached `s`
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
       IsSpecRun d rent (runSpent evs) (runTxs evs) s) :=
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
variable {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
  (hgen : Genesis d.programId s₀)                          -- [premise] an execution from genesis
  (hrun : Run d s₀ evs s)                                  --   ...that reached `s`
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
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.SpendsAreGenuine r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.spends_are_genuine params r

/-- **G1b for the code**: no note is spent twice in the execution (`NoDoubleSpend`). -/
theorem noDoubleSpend_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.NoDoubleSpend r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.no_double_spend params r

/-- **G1c for the code**: at the end of the execution, the pool's SOL exactly backs the
    unspent notes (`PoolBacksNotes`). -/
theorem poolBacksNotes_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.PoolBacksNotes params r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.balance params r

/-- **G1d for the code**: every spend in the execution uses the owner's secret key
    (`OnlyOwnerSpends`). -/
theorem onlyOwnerSpends_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.Goals.OnlyOwnerSpends r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _
    fun params r => LeanSpec.Goals.honest_note_spent_only_with_owner_key params r

/-- **G3c for the code**: once the tree is full, no further transaction is accepted
    (`FullTreeFreezes`). -/
theorem fullTreeFreezes_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧ LeanSpec.Goals.FullTreeFreezes r :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.full_tree_freezes_pool params r

/-- **G5 for the code**: only the authorities change the config, and they are whoever
    initialized the pool (`ConfigOnlyByAuthority`; with `IsRunOf`: the deployment's admin
    key, when it has one). -/
theorem configOnlyByAuthority_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      LeanSpec.Goals.ConfigOnlyByAuthority params r :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _
    fun params r => LeanSpec.Goals.config_changes_only_by_authority params r

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
      ∧ T.pubInputs = (toInputs a proof extAmount fee out1 out2).pubInputs →
      LeanSpec.Goals.SamePayout T (toInputs a proof extAmount fee out1 out2) :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  fun T ⟨hT, hSame⟩ => LeanSpec.Goals.same_public_inputs_same_external_data T hT _ _ _ hSame
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G4a for the code**: the accepted transaction creates and loses no SOL, except the
    nullifier rent (`NoSolCreated`). -/
theorem noSolCreated_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.Goals.NoSolCreated inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.no_sol_created _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G4b for the code**: in the accepted transaction, every account changes by exactly what
    it is owed or owes (`ExactPayouts`). -/
theorem exactPayouts_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.Goals.ExactPayouts inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.balance_changes_exact _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

end

/-! ## 3. Non-vacuity

One toy execution satisfies every hypothesis of the connection theorems: genesis,
`initialize`, a deposit of 1 lamport, then a withdrawal of 1 lamport that spends the note the
deposit created.
- **`connection_nonvacuous`:** it satisfies every hypothesis of `run_connection` and of the
  goals about runs, with a real spend.
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
    ∃ (d : Deployment) (s₀ s : State) (evs : List Event)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- every hypothesis of `run_connection`
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ Run d s₀ evs s ∧ d.programId ≠ systemProgram
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

end Connection
