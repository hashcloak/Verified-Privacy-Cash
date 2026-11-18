import Connection.Proofs.Execution
import Connection.Proofs.StepComplete
import Connection.Proofs.RunComplete
open Aeneas Aeneas.Std Result

/-! # Connection theorems

REVIEW SURFACE, with `Connection/Mapping.lean` (how code values and executions map to the
spec), `Connection/Hypotheses.lean` (the hypotheses) and `Connection/Findings.lean` (the
differences found). Every proof here is one line pointing into `Connection/Proofs/`, which is
not for review.

## What we show: the code is sound and complete with respect to the spec

`toWorld` maps a code state to a spec world (it forgets what the spec does not model, e.g.
rent). The code's step and the spec's step must then agree:

    code state  s ──── code transact ────▶ s'
         │                                 │
      toWorld                           toWorld
         ▼                                 ▼
    spec world  w ──── spec transact ────▶ w'

- **Soundness (code ⟹ spec):** whenever `step` accepts, the spec's `transact` holds between
  `toWorld s` and `toWorld s'` (all preconditions, exact effects). `transact_connection`; over
  runs, every code execution is a spec run, `run_connection`.
- **Completeness (spec ⟹ code):** whenever the spec allows a transaction, `step` accepts it
  and ends in a state that maps to the spec's `w'`. `transact_complete_except_L1_A0`; over
  runs, every spec run is a code execution, `run_complete_except_L1_A0`.

**How this finds errors.** Each direction catches one kind of bug. Soundness fails if the code
accepts what the spec forbids (a missing check: double spends, stolen funds). Completeness
fails if the code rejects what the spec allows (an extra check: stuck funds, blocked users).
Where the code and the spec differ, the theorem that should hold fails, and `Findings.lean`
proves so with a counterexample.

**Why two theorems.** The directions need different hypotheses: completeness needs more (e.g.
the right accounts listed, the crypto returning values) and excludes findings L1 and A0. One
theorem would carry both sets, and soundness would then hold only under completeness's
hypotheses and exclusions. Kept apart, soundness holds for every transaction the code accepts.

### Reading the theorems

- **Breaks:** collision resistance of derived addresses is not assumed: theorems end in "… or
  an address collision occurs" (`AddressCollision.lean`).
- **Inputs** (marked `[input]` in each theorem; the theorems hold for all of them):
  - `d : Deployment`: the deployed program (its id, addresses, crypto, admin key).
  - `rent`: the rent-exempt minimum by account size that the spec uses (`toWorld`).
  - `tx : TransactTx` (`Mapping.lean`): the transaction as the sender sends it, everything the
    sender chooses: `tx.ctx` the signers (core-model's `TxContext`), `tx.accounts` the accounts
    listed, `tx.args` the instruction data.
  - `sysvarRent`: the `Rent` sysvar as the runtime gives it; the sender does not choose it.
    `tx.env sysvarRent` is what the code receives besides accounts and data (`TxEnv`).
  - `oldState`: the chain state before a `transact`, reached by an execution (core-model's
    `Reachable`); `newState`: the state `step` returns.
  - Over runs: `sGenesis` a state where the program owns no account, `evs` the events from it
    to `s` (program instructions and outside actions), `states` the states between.
  A hypothesis restricts an input only if it mentions it; none bounds `tx`'s values.
- **Non-vacuity** is in `NonVacuityStatements.lean`.

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

The spec's security goals stated of the code, which follow from these theorems, are in
`Connection/CodeModelStatements.lean`.-/

namespace Connection

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]

/-! ## The connection theorems

Every theorem below assumes the following about the deployment `d` (they are its first
arguments):
-/

variable {d : CodeModel.Deployment}                        -- [input] the deployed program
  {rent : Nat → U64}                                       -- [input] the spec's rent
  (notSystem : ProgramNotSystem d)                         -- [assumption] see the definition
  (C : CodeModel.AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
                                                           -- [assumption] the syscall contracts
  (laws : PairingLaws C.e)                                 -- [assumption] the pairing laws
  (hashes : HashesAgree d)                                 -- [assumption] the hashes are the spec's
include notSystem laws hashes

/-! ### 1a. Soundness of `transact`: what the code accepts, the spec allows -/

/-- **Every `transact` the code accepts satisfies the spec's `transact`.** If an execution from
    genesis reaches `oldState` and `step` then accepts a `transact`, with new state `newState`,
    the spec's `transact` holds for the mapped inputs (`toInputs`) between `toWorld oldState`
    and `toWorld newState`: every precondition, the proof check included, and exactly the spec's
    effects. Or an address collision occurs (`AddressCollision`). -/
theorem transact_connection
    {tx : TransactTx}                                      -- [input] the transaction as sent: signers, accounts, data
    {sysvarRent : Option (Nat → U64)}                      -- [input] the `Rent` sysvar the runtime gives it
                                                           --   (core-model's `TxEnv.minimumBalance`: an `Option`
                                                           --   because `Rent::get()` can fail)
    {oldState : CodeModel.State}                           -- [input] the state before the `transact`
    (runtime : RuntimeFacts rent)                          -- [assumption] 64-bit `usize`, positive rent
    (pdasDoNotSign : PdasDoNotSign d tx.ctx)               -- [assumption] no PDA signs
    (circuit : CircuitFacts d {tx.args.proof})             -- [assumption] the circuit keeps the nullifiers distinct (I1)
    (sameRent : SameRent rent sysvarRent)                  -- [assumption] same rent as the spec
    (reachable : CodeModel.Reachable d oldState) :         -- [premise] an execution reached `oldState`, starting
                                                           --   where the program owns no account
    -- If the code accepts a transaction and executes `transact`, the Spec `transact` also holds,
    --    OR an address collision occurred (which we assume is infeasible).
    -- If it's rejected, we don't check anything.
    withSyscallSpec C in
    (match CodeModel.step d oldState (tx.env sysvarRent) tx.instruction with
      | .ok (newState, _logs) =>                          -- `step` accepts, with new state `newState`:
          Spec.transact (toInputs tx)                     --   the spec's `transact` holds
            (toWorld d rent oldState) (toWorld d rent newState)
      | .error _ => True)                                 -- `step` rejects: no claim; soundness is only about
                                                          --   what is accepted. Rejecting what the spec allows
                                                          --   is ruled out by completeness (§2a)
      ∨ AddressCollision d {tx.args.proof} :=              -- or a break: an address collision
  transact_connection_of notSystem C laws hashes runtime pdasDoNotSign circuit sameRent reachable

/-! ### 1b. Soundness over runs: every code execution is a spec run -/

omit notSystem laws hashes [Spec.PoseidonHashes] [Spec.Sha] in
/-- **An execution path is core-model's execution, with its states.** `ExecutionPath`
    (`Mapping.lean`), which `run_connection` takes, has exactly the executions of `Run`. -/
theorem execution_path_iff_run
    {s s' : CodeModel.State}                               -- [input] the first and last state
    {evs : List CodeModel.Event} :                         -- [input] the events in between
    (∃ states, ExecutionPath d s evs states s') ↔ CodeModel.Run d s evs s' :=
  ⟨fun ⟨_, h⟩ => h.toRun, Run.toExecutionPath⟩

/-- **Every execution of the code model is a run of the spec.** For an execution from genesis,
    either the pool is not initialized and no transaction was accepted, or the execution has a
    spec run (`IsSpecRun`, `IsRunOf`):
    - its start world is the one `initialize` set;
    - its transactions are the accepted `transact`s (`runTxs`), with their results;
    - between transactions, the outside actions and admin instructions (with their signers)
      are changes the spec allows.
    Or an address collision occurs (`AddressCollision`, over the execution's proofs). -/
theorem run_connection
    {sGenesis s : CodeModel.State}                         -- [input] genesis and the state reached
    {evs : List CodeModel.Event}                           -- [input] the events from genesis to `s`
    {states : List CodeModel.State}                        -- [input] the states between them
    (assume : ExecutionAssumptions d evs)                  -- [assumption] every `transact`'s
                                                           --   `PdasDoNotSign`, `CircuitFacts`
    (sameRent : ∀ txEnv ix em, .program txEnv ix em ∈ evs → SameRent rent txEnv.minimumBalance)
                                                           -- [assumption] same rent as the spec
    (hgen : CodeModel.Genesis d.programId sGenesis)        -- [premise] an execution from genesis
    (hrun : ExecutionPath d sGenesis evs states s) :       --   ...that reached `s` through `states`
    ((NoProgramAccounts d s ∧ runTxs evs = []) ∨
      (withSyscallSpec C in
       IsSpecRun d rent sGenesis evs states s))
      ∨ AddressCollision d (proofsIn evs) :=               -- or a break: an address collision
  run_connection_of notSystem C laws hashes assume sameRent hgen hrun

/-! ## The completeness theorems -/

/-! ### 2a. Completeness of `transact`: what the spec allows, the code does

If the spec allows a `transact` in the current state, the code accepts it and ends in the
spec's world: run `step`, map its new state into the spec (`toWorld`), and the result is the
spec's `transactEffects`. This is completeness: the code blocks no transaction the spec allows,
so users' funds cannot get stuck because of the code. Accepting means the whole on-chain `step`
succeeds, not only the handler: Anchor's account checks and `init`s, the handler, and the
runtime's lamport check.

It fails in exactly the cases of findings L1 and A0 (`Findings.lean`). -/


/-- **Every `transact` the spec allows, the code accepts, with the spec's result, except in the
    cases of findings L1 and A0.** If an execution from genesis has initialized the pool and
    reached `oldState`, and the spec allows the transaction in `toWorld oldState`
    (`SpecAllows`), then `step` accepts it, and its new state `newState` maps to the spec's
    world after the transaction (`toWorld newState = Spec.transactEffects …`). Or an address
    collision occurs (`AddressCollision`). Excluded, as it fails there:
    - **L1:** a zero external amount (an internal transfer);
    - **A0:** `proof_a` is the 64 zero bytes. -/
theorem transact_complete_except_L1_A0
    {tx : TransactTx}                                      -- [input] the transaction as sent: signers, accounts, data
    {sysvarRent : Option (Nat → U64)}                      -- [input] the `Rent` sysvar the runtime gives it
                                                           --   (core-model's `TxEnv.minimumBalance`: an `Option`
                                                           --   because `Rent::get()` can fail)
    {oldState : CodeModel.State}                           -- [input] the state before the `transact`
    (crypto : CryptoSucceeds d.crypto C)                   -- [assumption] the hash and syscalls return values
    (runtime : RuntimeFacts rent)                          -- [assumption] 64-bit `usize`, positive rent
    (pdas : PdasOnlyByProgram d oldState)                  -- [assumption] only the program creates
                                                           --   accounts at its addresses
    (sameRent : SameRent rent sysvarRent)                  -- [assumption] same rent as the spec
    (signerPlain : SignerIsPlain oldState tx.accounts)     -- [design: not modelled] the signer is a plain
                                                           --   system account, so it can pay
    (initialized : Initialized d oldState)                 -- [premise] the pool is initialized
    (reachable : CodeModel.Reachable d oldState)           -- [premise] an execution reached `oldState`, starting
                                                           --   where the program owns no account
    (accounts : AccountsListed d tx.accounts tx.args.proof) -- [premise] the right accounts are listed in the
                                                           --   transaction's account slots
    (notL1 : tx.args.extAmount.val ≠ 0)                    -- [finding L1] excluded
    (notA0 : tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8) : -- [finding A0] excluded
    SpecAllows C rent oldState tx →
      withSyscallSpec C in
      (match CodeModel.step d oldState (tx.env sysvarRent) tx.instruction with
        | .ok (newState, _logs) =>                        -- `step` accepts, with new state `newState`,
            toWorld d rent newState                       --   which maps to the spec's world after `tx`
              = Spec.transactEffects (toInputs tx) (toWorld d rent oldState)
        | .error _ => False)                              -- `step` rejects: never
      ∨ AddressCollision d {tx.args.proof} :=              -- or a break: an address collision
  transact_complete_of notSystem C laws hashes crypto runtime pdas sameRent signerPlain
    initialized reachable accounts notL1 notA0

/-! ### 2b. Completeness over runs: every spec run is a code execution

A spec run is rebuilt step by step as a code execution:
`initialize` sets up the start world, each change between transactions is an outside action or
an admin instruction, and each transaction is accepted by `step` (2a). The execution is
built so that every signer is plain and only the program creates accounts at its addresses, so
`SignerIsPlain` and `PdasOnlyByProgram` are not needed.

`SpecRun C params`: a spec run from `initWorld params`, with the syscalls' groups and pairing
and the program's key (`Mapping.lean`). -/


/-- **Every spec run is a run of the code, except for transactions of findings L1 and A0.** For
    every spec run `r` of this deployment's pool (`RunOfDeployment`), some code execution from
    genesis has spec run `r` (`IsRunOf`: the same start, transactions and results, admin changes
    and signers, and pool balance before each transaction). Or an address collision occurs
    (`AddressCollision`, within one of `r`'s transactions: across transactions, the spec already
    rejects a new nullifier account at an existing address, as Anchor's `init` does). Excluded,
    as it fails there (`Findings.lean`):
    - **L1:** a zero external amount (an internal transfer);
    - **A0:** `proof_a` is the 64 zero bytes. -/
theorem run_complete_except_L1_A0
    {params : Spec.InitParams}                         -- [input] the spec's start (`initWorld params`)
    (crypto : CryptoSucceeds d.crypto C)                   -- [assumption] the hash and syscalls return values
    (runtime : RuntimeFacts rent)                          -- [assumption] 64-bit `usize`, positive rent
    (r : SpecRun C params)                                 -- a spec run...
    (deployment : RunOfDeployment d rent params)           -- [premise] ...of this deployment's pool
    (notL1 : ∀ tx ∈ r.txs, tx.extAmt ≠ 0)                  -- [finding L1] excluded
    (notA0 : ∀ tx ∈ r.txs, tx.π.A ≠ List.replicate 64 0) : -- [finding A0] excluded
    withSyscallSpec C in
    (∃ sGenesis evs states s,
      CodeModel.Genesis d.programId sGenesis ∧ ExecutionPath d sGenesis evs states s ∧
      IsRunOf d rent sGenesis evs states s params r)
      ∨ AddressCollision d (fromSpecProof '' {tx | tx ∈ r.txs}) := -- or a break: an address collision
  or_collision (run_complete_of notSystem C laws hashes crypto runtime r deployment notL1 notA0)

end

end Connection
