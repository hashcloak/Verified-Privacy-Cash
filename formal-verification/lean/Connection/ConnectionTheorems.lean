import Connection.Proofs.ToySpend
import Connection.Proofs.ToyDonate
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Connection theorems

REVIEW SURFACE, with `Connection/Mapping.lean` (how code values and executions map to the
spec), `Connection/Hypotheses.lean` (the hypotheses) and `Connection/Findings.lean` (the
differences found). Every proof here is one line pointing into `Connection/Proofs/`, which is
not for review.

## What we show: the code is sound and complete with respect to the spec

The code and the spec are compared step by step. `toWorld` maps a code state to a spec world
(it forgets what the spec does not model, e.g. rent); the code's step and the spec's step must
then agree:

    code state  s ──── code transact ────▶ s'
         │                                 │
      toWorld                           toWorld
         ▼                                 ▼
    spec world  w ──── spec transact ────▶ w'

- **Soundness (code ⟹ spec):** whenever the code accepts, the spec's `transact` holds between
  `toWorld s` and `toWorld s'` (all preconditions, exact effects). `transact_connection`.
- **Completeness (spec ⟹ code):** whenever the spec allows a transaction, the code accepts it
  and ends in a state that maps to the spec's `w'`. `handler_complete_except_L1_A0`.
- **Runs:** the square holds for every kind of step (`initialize`, `transact`, admin
  instructions, outside actions), so by induction from genesis every code execution is a spec
  run, with the same transactions and the same admin changes and signers. The goals about runs
  (G1, G5) need this: they are about the execution's history, not only its final world.
  `run_connection`.

The aim is agreement wherever the code and the spec are compared. Where they differ, the
theorem that should hold fails, and `Findings.lean` proves it fails with a counterexample.

## Results

The **handler** is the extracted `zkcash_core::transact::transact`: the program's own logic.
`step` runs Anchor's account checks and `init`s, then the handler, then the runtime's lamport
check.

- **Soundness holds.** For the whole `step` (Anchor, handler, runtime) and every execution,
  everything the code accepts, the spec allows. No differences found. `transact_connection`,
  `run_connection`.
- **Completeness fails: findings L1 and A0.** The code rejects two kinds of transaction the
  spec allows; `Findings.lean` gives a counterexample for each.
  - **L1:** an internal transfer (external amount zero).
  - **A0:** a proof whose `proof_a` is the 64 zero bytes (the identity point).
- **Completeness holds for everything else**, proved
  - for the handler: `handler_complete_except_L1_A0`;
  - for `step`, for honest withdrawals, once past Anchor's account checks (`ReachesProgram`):
    G3a, G3b (`Connection/CodeModelStatements.lean`).

Not proved: that a transaction gets past Anchor's account checks (out of scopes).

The spec's security goals stated of the code, which follow from these theorems, are in
`Connection/CodeModelStatements.lean`.

## Contents

1. **The connection theorems:** soundness (1a), then completeness (1b).
2. **Non-vacuity**: the hypotheses can all hold together.

Every code-level statement starts with the same three `letI` lines. They only fix which
cryptography the spec uses: its groups and pairing are the `alt_bn128` syscalls'
(`syscallGroups`, `syscallPairing`) and its verifying key is the program's (`programKey`). -/

namespace Connection

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-! ## 1. The connection theorems

### 1a. Soundness: what the code accepts, the spec allows -/

/-- **Every `transact` the code accepts satisfies the spec's `transact`.** In any execution of
    the code model from genesis, if the execution's next step is an accepted `transact` (a
    one-step `Run`: `step` accepts it, with core-model's positive rent), then between the worlds before
    and after (mapped by `toWorld`) the spec's `transact` holds for the mapped transaction
    (`toInputs`): every spec precondition held, the proof check included, and the new world is
    exactly the spec's `transactEffects`. The spec's nullifier set is taken from the
    execution: before, the nullifiers it has spent so far (`runSpent evs`); after, those
    plus this transaction's two (`inputs.k0`, `inputs.k1`). -/
theorem transact_connection
    {d : Deployment} {rent : Nat → U64} {sGenesis s s' : State} {evs : List Event} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (deploy : DeploymentFacts d)                           -- [assumed] see Hypotheses.lean
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)     -- [assumed] the syscall contracts
    (laws : PairingLaws C.e)                               -- [assumed] the pairing laws
    (hashes : HashesAgree d.crypto)                        -- [assumed] the hashes are the spec's
    (solana : SolanaFacts d tx)                            -- [assumed] Solana runtime facts
    (crypto : CryptoFacts d proof)                         -- [assumed] SHA-256 facts
    (circuit : CircuitFacts d {proof})                     -- [assumed] the circuit keeps the nullifiers distinct (I1)
    (outside : OutsideSpecDetail d rent s tx a proof)      -- [by design] details the spec omits
    (hgen : Genesis d.programId sGenesis)                  -- [premise] an execution from genesis
    (hrun : Run d sGenesis evs s)                          --   ...that reached `s`
    (hstep : Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s') :
                                                           -- [premise] ...then accepted a transact (one more step)
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    LeanSpec.transact inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  transact_connection_pf hgen hrun deploy.programNotSystem hstep C laws hashes solana crypto circuit outside

/-- **An execution path is core-model's execution, with its states.** `ExecutionPath`
    (`Mapping.lean`), which `run_connection` takes, has exactly the executions of core-model's
    `Run`. -/
theorem execution_path_iff_run {d : Deployment} {s s' : State} {evs : List Event} :
    (∃ states, ExecutionPath d s evs states s') ↔ Run d s evs s' :=
  ⟨fun ⟨_, h⟩ => h.toRun, Run.toExecutionPath⟩

/-- **Every execution of the code model is a run of the spec.** Either the pool has not been
    initialized (and no transaction was accepted), or the final state is the end of a spec run
    (`IsSpecRun`): the run this execution went through (`IsRunOf`): from the start world
    `initialize` set, with the execution's transactions (`runTxs`) and their results, and the
    admin instructions with the signers of their transactions, up to what happened after the last
    transaction. `initialize` gives the start world; each accepted `transact` is a spec
    transaction; outside actions and the admin instructions are changes the spec allows between
    transactions. By design, the rent is fixed (`ExecutionOutsideSpecDetail`, as
    `OutsideSpecDetail.rentFixed` for `transact_connection`). The other details `OutsideSpecDetail`
    rules out need no exclusion here: a pre-funded nullifier address, or a payee that is a
    nullifier account, is an allowed change before or after the spec transaction. -/
theorem run_connection {d : Deployment} {rent : Nat → U64} {sGenesis s : State} {evs : List Event}
    {states : List State}
    (deploy : DeploymentFacts d)                           -- [assumed] see the structure
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)     -- [assumed] the syscall contracts
    (laws : PairingLaws C.e)                               -- [assumed] the pairing laws
    (hashes : HashesAgree d.crypto)                        -- [assumed] the hashes are the spec's
    (assume : ExecutionAssumptions d sGenesis evs)    -- [assumed] every `transact`'s
                                                           --   `SolanaFacts`, `CryptoFacts`;
                                                           --   the fixed addresses differ
    (outside : ExecutionOutsideSpecDetail d rent sGenesis evs)
                                                           -- [by design] the rent is fixed
    (hgen : Genesis d.programId sGenesis)                  -- [premise] an execution from genesis
    (hrun : ExecutionPath d sGenesis evs states s) :       --   ...that reached `s` through `states`
    (NoProgramAccounts d s ∧ runTxs evs = []) ∨
      (letI : LeanSpec.Groups := syscallGroups C
       letI : LeanSpec.Pairing := syscallPairing C
       letI : LeanSpec.Deployment := ⟨programKey C⟩
       IsSpecRun d rent sGenesis evs states s) :=
  execution_is_spec_run_pf hgen hrun deploy.programNotSystem C laws hashes assume outside

/-! ### 1b. Completeness: what the spec allows, the handler accepts

Stated of the handler only: the spec world is the one the handler sees (`handlerWorld`: after
Anchor's `init`s, so no nullifier rent), on the environment `execTransact` builds
(`handlerEnv`). It fails in exactly the two cases of findings L1 and A0; the counterexamples
are in `Findings.lean`. -/

section
variable {signers : List Pubkey}

/-- `HandlerSpecAllows …`: the spec allows the transaction: every spec precondition holds
    for the mapped inputs in the world the handler sees. -/
def HandlerSpecAllows (signers : List Pubkey) (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
    (config : zkcash_core.admin.GlobalConfig) (spent : Finset LeanSpec.F)
    (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.transactPreconditions (toInputs signers a proof ext fee out1 out2) (handlerWorld a s₁ v tree config spent)

/-- `HandlerMatchesSpec …`: the handler accepts, with exactly the spec's effects: it returns
    `Ok`, every account's balance is the spec's (`transactEffects`, on code addresses), and
    the new tree is the spec's. -/
def HandlerMatchesSpec (signers : List Pubkey) (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
    (config : zkcash_core.admin.GlobalConfig) (spent : Finset LeanSpec.F)
    (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  let effects := LeanSpec.transactEffects (toInputs signers a proof ext fee out1 out2)
    (handlerWorld a s₁ v tree config spent)
  ∃ ap env' tree', zkcash_core.transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime
      (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2
      = ok (.Ok ap, env', tree') ∧
    (∀ k, (env'.balances k).val = effects.balances (toPubkey k)) ∧ toTree tree' = effects.state.tree

/-- **Every transaction the spec allows, the handler accepts with the spec's effects, except
    in the cases of findings L1 and A0.** If the spec allows a transaction in the world the
    handler sees, the handler accepts it, and every balance and the new tree are the spec's.
    The two excluded cases are where it fails (`Findings.lean`):
    - **L1:** a zero amount (an internal transfer);
    - **A0:** `proof_a` is the 64 zero bytes.
    So these are the only differences at the handler. It covers the handler only, not
    Anchor's checks or the runtime; for those, see `honestSpendIsAccepted_code`. -/
theorem handler_complete_except_L1_A0 (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) {a : TransactAccounts} {s₁ : State} {v : U64}
    {tree : zkcash_core.merkle_tree.MerkleTreeAccount} {config : zkcash_core.admin.GlobalConfig}
    {spent : Finset LeanSpec.F} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8}
    (hashes : HashesAgree c)                               -- [assumed] the hashes are the spec's
    (assume : CompletenessAssumptions c C)                 -- [assumed] see the structure
    (ctx : HandlerContext a s₁ tree config)      -- [invariant], [premise]: see the structure
    (notL1 : ext.val ≠ 0)                                  -- [finding L1] excluded
    (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8)   -- [finding A0] excluded
    (allows : HandlerSpecAllows signers c C a s₁ v tree config spent proof ext fee out1 out2) :
                                                           -- [premise] the spec allows it
    HandlerMatchesSpec signers c C a s₁ v tree config spent proof ext fee out1 out2 :=
  handler_complete_exact' c C laws hashes assume.1 assume.2 assume.3 a s₁ v tree config spent proof ext
    fee out1 out2 ctx.1 ctx.2 ctx.3 ctx.4 ctx.5 ctx.6 ctx.7 assume.usize64 notL1 notA0 allows

end

end

/-! ## 2. Non-vacuity

Toy executions satisfy every hypothesis of the theorems above, in one toy deployment:
- **`connection_nonvacuous`:** genesis, `initialize`, a deposit of 2 lamports, then a withdrawal
  of 1 lamport with a fee of 1 that spends the note the deposit created. It satisfies every
  hypothesis of `run_connection` and of the goals about runs (`CodeModelStatements.lean`), with
  a real spend.
- **`donation_nonvacuous`:** genesis, `initialize`, an outside action sending 1 lamport to the
  pool, then the deposit. It satisfies every hypothesis of `run_connection`, and every spec run
  of it counts the lamport as donated.
- **`transact_connection_nonvacuous`:** the deposit and the withdrawal each satisfy every
  hypothesis of `transact_connection`, so also of G2a, G4a and G4b for the code.
- **`handler_complete_nonvacuous`:** a deposit of 1 lamport whose `proof_a` is not the 64 zero
  bytes satisfies every hypothesis of `handler_complete_except_L1_A0`.

The non-vacuity of G3a, G3b for the code is in
`CodeModelStatements.lean`.

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
    ∃ (d : Deployment) (sGenesis s : State) (evs : List Event) (states : List State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- every hypothesis of `run_connection`
      PairingLaws C.e ∧ Genesis d.programId sGenesis ∧ ExecutionPath d sGenesis evs states s
      ∧ DeploymentFacts d ∧ HashesAgree d.crypto ∧ ExecutionAssumptions d sGenesis evs
      ∧ ExecutionOutsideSpecDetail d Toy.toyRent sGenesis evs
      -- the pool is initialized, and the execution has two transactions
      ∧ Initialized d s ∧ (runTxs evs).length = 2
      -- with circuit witnesses for both transactions
      ∧ ∃ wit : ℕ → LeanSpec.Witness,
        (∀ j (h : j < (runTxs evs).length), LeanSpec.RelationS (runTxs evs)[j].pubInputs (wit j))
        -- in which transaction 1 spends a real note, the one the deposit put at leaf 0
        ∧ (wit 1).inAmt 0 ≠ 0 ∧ LeanSpec.openedPos wit 1 0 = 0
        ∧ (wit 1).inNote 0 = LeanSpec.leafNote wit 0 :=
  Toy.toy_spend_nonvacuous

section
-- The spec's groups, pairing and key are the toy deployment's, as `run_connection` fixes them
-- (`syscallGroups`, `syscallPairing`, `programKey`).
attribute [local instance] Toy.toySpecGroups Toy.toySpecG1Group Toy.toySpecG2Group
  Toy.toySpecG1Module Toy.toySpecG2Module Toy.toySpecGTGroup Toy.toySpecPairing Toy.toySpecDeployment

/-- **`run_connection` is not vacuous on an outside action**: the toy execution `initialize`, an
    outside action (`EnvStep`) sending 1 lamport to the pool, then a deposit of 2 lamports.

    - **`run_connection`'s hypotheses** all hold for it;
    - **the outside action reaches the spec:** every spec run of the execution (`IsRunOf`)
      counts that lamport as donated (`r.donated = 1`). -/
theorem donation_nonvacuous :
    ∃ (sGenesis s : State) (evs : List Event) (states : List State),
      -- every hypothesis of `run_connection`, for the toy deployment
      Genesis Toy.toyD.programId sGenesis ∧ ExecutionPath Toy.toyD sGenesis evs states s
      ∧ DeploymentFacts Toy.toyD ∧ PairingLaws Toy.toyC.e ∧ HashesAgree Toy.toyD.crypto
      ∧ ExecutionAssumptions Toy.toyD sGenesis evs
      ∧ ExecutionOutsideSpecDetail Toy.toyD Toy.toyRent sGenesis evs
      -- the execution contains an outside action
      ∧ Event.env ∈ evs
      -- and every spec run of it counts 1 lamport as donated
      ∧ ∀ params r, IsRunOf Toy.toyD Toy.toyRent sGenesis evs states s params r → r.donated = 1 :=
  Toy.toy_donation_nonvacuous

end

/-- **`transact_connection` is not vacuous, for a deposit and for a withdrawal**: in one
    deployment satisfying the deployment-level hypotheses (`PairingLaws`, genesis,
    `DeploymentFacts`, `HashesAgree`), the code accepts a deposit (`extAmount > 0`) and
    a withdrawal (`extAmount < 0`), each in an execution from genesis and each satisfying the
    per-transaction hypotheses (`SolanaFacts`, `CryptoFacts`, `CircuitFacts`, `OutsideSpecDetail`). The two
    cover both payment paths: the signer pays the pool, and the pool pays the recipient. -/
theorem transact_connection_nonvacuous :
    ∃ (d : Deployment) (rent : Nat → U64) (sGenesis : State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      -- the deployment-level hypotheses of `transact_connection`
      PairingLaws C.e ∧ Genesis d.programId sGenesis ∧ DeploymentFacts d ∧ HashesAgree d.crypto
      -- a deposit the code accepts, with the per-transaction hypotheses
      ∧ (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
          (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8)
          (events : List CommitmentData),
        Run d sGenesis evs s ∧ Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s'
        ∧ extAmount.val > 0
        ∧ SolanaFacts d tx ∧ CryptoFacts d proof ∧ CircuitFacts d {proof} ∧ OutsideSpecDetail d rent s tx a proof)
      -- and a withdrawal the code accepts, with the per-transaction hypotheses
      ∧ (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts)
          (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) (out1 out2 : Slice U8)
          (events : List CommitmentData),
        Run d sGenesis evs s ∧ Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s'
        ∧ extAmount.val < 0
        ∧ SolanaFacts d tx ∧ CryptoFacts d proof ∧ CircuitFacts d {proof} ∧ OutsideSpecDetail d rent s tx a proof) :=
  Toy.toy_transact_nonvacuous

/-- **`handler_complete_except_L1_A0` is not vacuous**: in the toy deployment, a deposit of 1
    lamport (so not L1) whose `proof_a` is the verifying key's `alpha` (so not A0) satisfies
    every hypothesis: the completeness assumptions, the handler's context, and the spec allows
    it. -/
theorem handler_complete_nonvacuous
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    ∃ (c : Crypto) (C : AltBn128Contracts c.altBn128 Unit Unit Unit) (laws : PairingLaws C.e)
      (signers : List Pubkey) (a : TransactAccounts) (s₁ : State) (v : U64)
      (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (config : zkcash_core.admin.GlobalConfig)
      (spent : Finset LeanSpec.F) (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64)
      (out1 out2 : Slice U8),
      -- every hypothesis of `handler_complete_except_L1_A0`
      HashesAgree c ∧ CompletenessAssumptions c C ∧ HandlerContext a s₁ tree config
      ∧ ext.val ≠ 0 ∧ proof.proof_a.val ≠ List.replicate 64 0#u8
      ∧ HandlerSpecAllows signers c C a s₁ v tree config spent proof ext fee out1 out2 :=
  ⟨_, _, Toy.toyLaws, _, _, _, _, _, _, _, _, _, _, _, _, Toy.toyHashesAgree, Toy.toyAssumptions h64, Toy.toyContext 1#u64, by simp,
    Toy.okProof_notA0, Toy.toy_pre_ok⟩

end

end Connection
