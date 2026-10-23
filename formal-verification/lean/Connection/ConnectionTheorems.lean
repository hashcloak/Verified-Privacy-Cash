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
2. **The security goals hold for the code.** Each goal is a named property of the spec
   (`Spec/Vocabulary.lean`, end), proved for the spec in `Spec/Statements.lean`; here the same
   property is stated of the code. Goals about runs (G1a–G1d, G3c, G5) hold of the execution's
   run; goals about one transaction (G1e, G2a, G4a, G4b) hold of every transaction the code
   accepts. G2b is about circuit witnesses only (no code involved); G3a and G3b (liveness) need
   completeness, which these safety theorems don't give.
3. **Non-vacuity**: the hypotheses can all hold together.

Scope: safety. Nothing is claimed about transactions the code rejects (see `Findings.lean` for
handler completeness). -/

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
    spent before.

    Hypotheses: the execution and the step (premise); the program is not the system program,
    `HashesAgree`, `SolanaFacts`, `CryptoFacts`, the syscall contracts `C`, `PairingLaws`
    (asm); `OutsideSpecDetail` (design). -/
theorem transact_connection
    {d : Deployment} {rent : Nat → U64} {s₀ s s' : State} {evs : List Event} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto) (solana : SolanaFacts d rent tx out1 out2)
    (crypto : CryptoFacts d proof) (outside : OutsideSpecDetail d rent s tx a proof) :
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
    the spec transaction.

    Hypotheses: the execution (premise); the program is not the system program, `HashesAgree`,
    the syscall contracts `C`, `PairingLaws` (asm); `ExecutionAssumptions` (asm: every step's
    rent, `SolanaFacts` and `CryptoFacts`, and the program's three fixed addresses differ). -/
theorem run_connection {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto) (assume : ExecutionAssumptions d rent s₀ evs) :
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
  (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
  (hashes : HashesAgree d.crypto) (assume : ExecutionAssumptions d rent s₀ evs)
  (hi : Initialized d s)
include hgen hrun hpid C laws hashes assume hi

/-- **G1a for the code**: `SpendsAreGenuine`. -/
theorem spendsAreGenuine_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.SpendsAreGenuine r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.spends_are_genuine params r

/-- **G1b for the code**: `NoDoubleSpend`. -/
theorem noDoubleSpend_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.NoDoubleSpend r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.no_double_spend params r

/-- **G1c for the code**: `PoolBacksNotes`. -/
theorem poolBacksNotes_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.PoolBacksNotes params r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.balance params r

/-- **G1d for the code**: `OnlyOwnerSpends`. -/
theorem onlyOwnerSpends_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      ∀ wit, r.WitnessesFor wit → LeanSpec.OnlyOwnerSpends r wit :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _
    fun params r => LeanSpec.Goals.honest_note_spent_only_with_owner_key params r

/-- **G3c for the code**: `FullTreeFreezes`. -/
theorem fullTreeFreezes_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧ LeanSpec.FullTreeFreezes r :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume hi _ fun params r => LeanSpec.Goals.full_tree_freezes_pool params r

/-- **G5 for the code**: `ConfigOnlyByAuthority` (with `IsRunOf`: the initializer is the
    deployment's admin key, when it has one). -/
theorem configOnlyByAuthority_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent (runSpent evs) (runTxs evs) s params r ∧
      LeanSpec.ConfigOnlyByAuthority params r :=
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
  (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
  (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
  (hashes : HashesAgree d.crypto) (solana : SolanaFacts d rent tx out1 out2)
  (crypto : CryptoFacts d proof) (outside : OutsideSpecDetail d rent s tx a proof)
include hgen hrun hpid hstep C laws hashes solana crypto outside

/-- **G1e for the code**: the accepted transaction's proof is valid (`proofValid`). -/
theorem proofValid_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.proofValid (toInputs a proof extAmount fee out1 out2) :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.transact_requires_valid_proof _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G2a for the code**: `CopiedProofSamePayout`, against any honest transaction `T`. -/
theorem copiedProofSamePayout_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    ∀ T, LeanSpec.CopiedProofSamePayout T (toInputs a proof extAmount fee out1 out2) :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.same_public_inputs_same_external_data _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G4a for the code**: `NoSolCreated`. -/
theorem noSolCreated_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.NoSolCreated inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.no_sol_created _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

/-- **G4b for the code**: `ExactPayouts`. -/
theorem exactPayouts_code :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.ExactPayouts inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  letI := syscallGroups C; letI := syscallPairing C laws; letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.Goals.balance_changes_exact _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto outside)

end

/-! ## 3. Non-vacuity

In a deliberately broken toy deployment (`Proofs/Toy.lean`: `G1 = G2 = GT = Unit`, every pairing
1, Poseidon always 1, SHA-256 always zero; the G1 decoding is the real one) and a toy PDA
derivation, one execution (genesis, `initialize`, a deposit of 1 lamport, then a withdrawal of
1 lamport that spends the note the deposit created) satisfies every hypothesis of
`run_connection` and of the goals about runs, with a real spend (`connection_nonvacuous`). Its
deposit and its withdrawal each satisfy every hypothesis of `transact_connection`
(`transact_connection_nonvacuous`). It shows the hypotheses can hold together, not that real
cryptography reaches the outcome.

The circuit's hashes `H1`, `H3`, `H4` are never computed by the code; the toy takes `H1` the
identity and `H3`, `H4` the sums of their arguments, so that the toy transactions have circuit
witnesses. In this section the spec's hashes are the toy's. -/

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **The connection theorems are not vacuous, with a real spend**: an execution with two
    transactions, a deposit and then a withdrawal, for which every hypothesis of
    `run_connection` holds, and every hypothesis of the goals about runs: the pool is
    initialized, and `wit` are circuit witnesses for both transactions (so for every spec run
    of the execution: `IsRunOf` fixes its transactions to `runTxs evs`). In `wit` the
    withdrawal (transaction 1) spends a non-zero note, and that note is the one at leaf 0,
    which the deposit created. So the goals G1a–G1d are not vacuous on a spend. -/
theorem connection_nonvacuous :
    ∃ (d : Deployment) (s₀ s : State) (evs : List Event)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ Run d s₀ evs s ∧ d.programId ≠ systemProgram ∧
      HashesAgree d.crypto ∧ ExecutionAssumptions d Toy.toyRent s₀ evs ∧ Initialized d s ∧
      (runTxs evs).length = 2 ∧
      ∃ wit : ℕ → LeanSpec.Witness,
        (∀ j (h : j < (runTxs evs).length), LeanSpec.RelationS (runTxs evs)[j].pubInputs (wit j)) ∧
        (wit 1).inAmt 0 ≠ 0 ∧ LeanSpec.spentLeaf wit 1 0 = 0 ∧
        (wit 1).inNote 0 = LeanSpec.leafNote wit 0 :=
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
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ d.programId ≠ systemProgram ∧ HashesAgree d.crypto ∧
      (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
          (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8)
          (events : List CommitmentData),
        Run d s₀ evs s ∧ step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events) ∧
        extAmount.val > 0 ∧ SolanaFacts d rent tx out1 out2 ∧ CryptoFacts d proof ∧
        OutsideSpecDetail d rent s tx a proof) ∧
      (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
          (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8)
          (events : List CommitmentData),
        Run d s₀ evs s ∧ step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events) ∧
        extAmount.val < 0 ∧ SolanaFacts d rent tx out1 out2 ∧ CryptoFacts d proof ∧
        OutsideSpecDetail d rent s tx a proof) :=
  Toy.toy_transact_nonvacuous

end

end Connection
