import Connection.Proofs.Run
import Connection.Proofs.StepComplete
import Connection.Proofs.RunComplete
open Aeneas Aeneas.Std Result

/-! # Connection theorems

REVIEW SURFACE, with `Connection/Mapping.lean` (how code values and code runs map to the
spec), `Connection/Hypotheses.lean` (the hypotheses) and `Connection/Findings.lean` (the
differences found). Every proof here is one line pointing into `Connection/Proofs/`, which is
not for review.

## What we show: the code is sound and complete with respect to the spec

`toWorld` maps a chain state to a spec world (it forgets what the spec does not model, e.g.
rent). The code's `step` on a `transact` instruction and the spec's `transact` must then agree:

    chain state s ── step (transact instruction) ──▶ s'
         │                                           │
      toWorld                                     toWorld
         ▼                                           ▼
    spec world  w ──────────── spec's transact ────▶ w'

- **Soundness (code ⟹ spec):** whenever `step` accepts a `transact` instruction, the spec's
  `transact` holds between `toWorld s` and `toWorld s'` (all preconditions, exact effects).
  `transact_connection`; over runs, every code run is a spec run, `run_connection`.
- **Completeness (spec ⟹ code):** whenever the spec allows a spec transaction, `step` accepts
  its `transact` instruction and ends in a chain state that maps to the spec's `w'`.
  `transact_complete_except_L1_A0`; over runs, every spec run is a code run,
  `run_complete_except_L1_A0`.

**How this finds errors.** Each direction catches one kind of bug. Soundness fails if the code
accepts what the spec forbids (a missing check: double spends, stolen funds). Completeness
fails if the code rejects what the spec allows (an extra check: stuck funds, blocked users).
Where the code and the spec differ, the theorem that should hold fails, and `Findings.lean`
proves so with a counterexample.

**Why two sets of theorems.** The directions need different hypotheses: completeness needs more (e.g. the
right accounts listed, the crypto returning values) and excludes findings L1 and A0. One theorem
would carry both sets, and soundness would then hold only under completeness's hypotheses and
exclusions. Kept apart, soundness holds for every `transact` instruction the code accepts.

### Reading the theorems

- **Breaks:** collision resistance of derived addresses is not assumed: theorems end in "… or
  an address collision occurs" (`AddressCollision.lean`).
- **Inputs** (marked `[input]` in each theorem; the theorems hold for all of them):
  - `d : Deployment`: the deployed program (its id, addresses, crypto, admin key).
  - `rent`: the rent-exempt minimum by account size that the spec uses (`toWorld`).
  - `tx : TransactTx` (`Mapping.lean`): the `transact` instruction as the sender sends it,
    everything the sender chooses: `tx.ctx` the Solana transaction's signers (core-model's
    `TxContext`), `tx.accounts` the accounts listed, `tx.args` the instruction data.
  - `sysvarRent`: the `Rent` sysvar as the runtime gives it; the sender does not choose it.
    `tx.env sysvarRent` is what the code receives besides accounts and data (`TxEnv`).
  - `oldState`: the chain state before a `transact` instruction, reached by a code run
    (core-model's `Reachable`); `newState`: the chain state `step` returns.
  - Over runs: a code run is the Code Model's `Run` with the chain states around each event
    kept (`CodeRun`): `s₀` a chain state where the program owns no account, `steps` the steps
    from it to `sₙ`, each an event (a program instruction or an outside action) with the chain
    states just before and just after it.
  A hypothesis restricts an input only if it mentions it; none bounds `tx`'s values.
- **Non-vacuity** is in `NonVacuityStatements.lean`.

## Results

The **handler** (the Code Model's term) is the program's function for a `transact` instruction:
the extracted `zkcash_core::transact::transact`, which `step` calls. `step` runs Anchor's
account checks and `init`s, then the handler, then the runtime's lamport check.

- **Soundness holds.** For the whole `step` (Anchor, handler, runtime) and every code run,
  everything the code accepts, the spec allows. No differences found. `transact_connection`,
  `run_connection`.
- **Completeness fails: findings L1 and A0.** `step` rejects two kinds of `transact` instruction
  whose spec transaction the spec allows; `Findings.lean` gives a counterexample for each.
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

/-! ### 1a. Soundness of the `transact` instruction: what the code accepts, the spec allows -/

/-- **Every `transact` instruction the code accepts satisfies the spec's `transact`.** If a code run
    from genesis reaches `oldState` and `step` then accepts a `transact` instruction, with new chain
    state `newState`, the spec's `transact` holds for the mapped spec transaction (`toInputs`)
    between `toWorld oldState` and `toWorld newState`: every precondition, the proof check included,
    and exactly the spec's effects. Or an address collision occurs (`AddressCollision`). -/
theorem transact_connection
    {tx : TransactTx}                                      -- [input] the `transact` instruction as sent: signers, accounts, data
    {sysvarRent : Option (Nat → U64)}                      -- [input] the `Rent` sysvar the runtime gives it
                                                           --   (core-model's `TxEnv.minimumBalance`: an `Option`
                                                           --   because `Rent::get()` can fail)
    {oldState : CodeModel.State}                           -- [input] the chain state before the instruction
    (runtime : RuntimeFacts rent)                          -- [assumption] 64-bit `usize`, positive rent
    (txAssumptions : TransactAssumptions d tx.ctx tx.args.proof)
                                                           -- [assumption] no PDA signs; the circuit keeps
                                                           --   the nullifiers distinct (I1)
    (sameRent : SameRent rent sysvarRent)                  -- [assumption] same rent as the spec
    (reachable : CodeModel.Reachable d oldState) :         -- [premise] a code run reached `oldState`, starting
                                                           --   where the program owns no account
    -- If `step` accepts the `transact` instruction, the spec's `transact` also holds,
    --    OR an address collision occurred (which we assume is infeasible).
    -- If `step` rejects it, we don't check anything.
    withSyscallSpec C in
    (match CodeModel.step d oldState (tx.env sysvarRent) tx.instruction with
      | .ok (newState, _logs) =>                          -- `step` accepts, with new state `newState`:
          Spec.transact (toInputs tx)                     --   the spec's `transact` holds
            (toWorld d rent oldState) (toWorld d rent newState)
      | .error _ => True)                                 -- `step` rejects: no claim; soundness is only about
                                                          --   what is accepted. Rejecting what the spec allows
                                                          --   is ruled out by completeness (§2a)
      ∨ AddressCollision d {tx.args.proof} :=              -- or a break: an address collision
  transact_connection_of notSystem C laws hashes runtime txAssumptions sameRent reachable

/-! ### 1b. Soundness over runs: every code run is a spec run

To relate a code run to a spec run (`IsSpecRun`), we need the chain states around each event of
the code run: the two runs are compared state by state. The Code Model's `Run` does not record
these states: it is a `Prop`, so it cannot hand them back. This is why we use `CodeRun`
(`Mapping.lean`), which is `Run` with each event recorded as a step together with the chain states
just before and just after it. `codeRun_iff_run` shows that `CodeRun` and `Run` have the same code
runs, so a theorem over `CodeRun`, such as `run_connection` below, still covers every code run. -/

omit notSystem laws hashes [Spec.PoseidonHashes] [Spec.Sha] in
/-- **`CodeRun` is the Code Model's `Run`, with its states.** The events of every `CodeRun` form a
    `Run`, and every `Run` can be recorded as a `CodeRun` with the same events. A `Run` can have
    several recordings, because an outside action (`EnvStep`) may lead to several states;
    `run_connection` holds for all of them.

    It is about the Code Model alone, so it is stated without this section's shared assumptions
    (`notSystem`, `laws`, `hashes`) and the spec's hash instances; the `omit … in` line above
    removes them, as Lean would otherwise add them to every theorem in the section. -/
theorem codeRun_iff_run
    {s₀ sₙ : CodeModel.State}                              -- [input] the first and last chain state
    {events : List CodeModel.Event} :                      -- [input] the events in between
    (∃ steps, CodeRun d s₀ steps sₙ ∧ eventsOf steps = events) ↔
      CodeModel.Run d s₀ events sₙ :=
  ⟨fun ⟨_, h, he⟩ => he ▸ h.toRun, Run.toCodeRun⟩

/-- **Every code run is a spec run.** For a code run from genesis, either the program is not
    initialized (it holds no accounts) and no `transact` instruction was accepted, or a spec run
    describes the code run, so the code did only what the spec allows:
    - it starts from the world that the code run's only `initialize` instruction set up;
    - its spec transactions are the code run's accepted `transact` instructions, in order, and
      after each one the spec's world equals the chain's;
    - everything else the code run does (outside actions, and admin instructions with their
      signers) is a change the spec allows between spec transactions, up to the last chain state.
    Or an address collision occurs among the addresses derived for the code run's proofs. -/
theorem run_connection
    {s₀ sₙ : CodeModel.State}                              -- [input] genesis and the chain state reached
    {steps : List RunStep}                                 -- [input] the steps to `sₙ`
    (everyTxAssumptions : TransactAssumptionsInRun d (eventsOf steps))
                                                           -- [assumption] as in `transact_connection`,
                                                           --   for every `transact` instruction of the code run
    (sameRent : ∀ txEnv ix em, .program txEnv ix em ∈ (eventsOf steps) →
      SameRent rent txEnv.minimumBalance)                  -- [assumption] for all instructions, we assume
                                                           --   same rent as the spec
    (hgen : CodeModel.Genesis d.programId s₀)              -- [premise] a code run from genesis
    (hrun : CodeRun d s₀ steps sₙ) :                       --   ...through `steps` to `sₙ`
    ((NoProgramAccounts d sₙ ∧ runTxs (eventsOf steps) = []) ∨
                                                           -- the program was never initialized: it holds no
                                                           --   accounts and accepted no `transact` instruction,
      (withSyscallSpec C in
       IsSpecRun d rent steps sₙ))                         -- or a spec run describes the code run,
      ∨ AddressCollision d (proofsIn (eventsOf steps)) :=  -- or a break: an address collision
  run_connection_of notSystem C laws hashes everyTxAssumptions sameRent hgen hrun

/-! ## The completeness theorems -/

/-! ### 2a. Completeness of the `transact` instruction: what the spec allows, the code does

If the spec allows a spec transaction in the current spec world, `step` accepts its `transact`
instruction and ends in the spec's world: run `step`, map its new chain state into the spec
(`toWorld`), and the result is the spec's `transactEffects`. This is completeness: the code blocks
no spec transaction the spec allows, so users' funds cannot get stuck because of the code. Accepting
means the whole on-chain `step` succeeds, not only the handler: Anchor's account checks and `init`s,
the handler, and the runtime's lamport check.

It fails in exactly the cases of findings L1 and A0 (`Findings.lean`). -/


/-- **Every spec transaction the spec allows, the code accepts as a `transact` instruction, with the
    spec's result, except in the cases of findings L1 and A0.** If a code run from genesis has
    initialized the program and reached `oldState`, and the spec allows the spec transaction in
    `toWorld oldState` (`SpecAllows`), then `step` accepts the `transact` instruction, and its new
    chain state `newState` maps to the spec's world after the spec transaction
    (`toWorld newState = Spec.transactEffects …`). Or an address collision occurs
    (`AddressCollision`). Excluded, as it fails there:
    - **L1:** a zero external amount (an internal transfer);
    - **A0:** `proof_a` is the 64 zero bytes. -/
theorem transact_complete_except_L1_A0
    {tx : TransactTx}                                      -- [input] the `transact` instruction as sent: signers, accounts, data
    {sysvarRent : Option (Nat → U64)}                      -- [input] the `Rent` sysvar the runtime gives it
                                                           --   (core-model's `TxEnv.minimumBalance`: an `Option`
                                                           --   because `Rent::get()` can fail)
    {oldState : CodeModel.State}                           -- [input] the chain state before the instruction
    (crypto : CryptoSucceeds d.crypto C)                   -- [assumption] the hash and syscalls return values
    (runtime : RuntimeFacts rent)                          -- [assumption] 64-bit `usize`, positive rent
    (pdas : PdasOnlyByProgram d oldState)                  -- [assumption] only the program creates
                                                           --   accounts at its addresses
    (sameRent : SameRent rent sysvarRent)                  -- [assumption] same rent as the spec
    (signerPlain : SignerIsPlain oldState tx.accounts)     -- [design: not modelled] the signer is a plain
                                                           --   system account, so it can pay
    (initialized : Initialized d oldState)                 -- [premise] the program is initialized
    (reachable : CodeModel.Reachable d oldState)           -- [premise] a code run reached `oldState`, starting
                                                           --   where the program owns no account
    (accounts : AccountsListed d tx.accounts tx.args.proof) -- [premise] the right accounts are listed in the
                                                           --   instruction's account slots
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

/-! ### 2b. Completeness over runs: every spec run is a code run

A spec run is rebuilt one spec transaction at a time as a code run: `initialize` sets up the
start world, each change between spec transactions is an outside action or an admin
instruction, and `step` accepts each spec transaction's `transact` instruction (2a). The code run is
built so that every signer is plain and only the program creates accounts at its addresses, so
`SignerIsPlain` and `PdasOnlyByProgram` are not needed.

`SpecRun C params`: a spec run from `initWorld params`, with the syscalls' groups and pairing
and the program's key (`Mapping.lean`). -/


/-- **Every spec run is a code run, except for spec transactions of findings L1 and A0.** For every
    spec run `r` of this deployment (`RunOfDeployment`), some code run from genesis has spec run `r`
    (`IsRunOf`: the same start, spec transactions and the worlds after them, admin changes and
    signers, and pool account balance before each spec transaction). Or an address collision occurs
    (`AddressCollision`, within one of `r`'s spec transactions: across spec transactions, the spec
    already rejects a new nullifier account at an existing address, as Anchor's `init` does).
    Excluded, as it fails there (`Findings.lean`):
    - **L1:** a zero external amount (an internal transfer);
    - **A0:** `proof_a` is the 64 zero bytes. -/
theorem run_complete_except_L1_A0
    {params : Spec.InitParams}                         -- [input] the spec's start (`initWorld params`)
    (crypto : CryptoSucceeds d.crypto C)                   -- [assumption] the hash and syscalls return values
    (runtime : RuntimeFacts rent)                          -- [assumption] 64-bit `usize`, positive rent
    (r : SpecRun C params)                                 -- a spec run...
    (deployment : RunOfDeployment d rent params)           -- [premise] ...of this deployment
    (notL1 : ∀ tx ∈ r.txs, tx.extAmt ≠ 0)                  -- [finding L1] excluded
    (notA0 : ∀ tx ∈ r.txs, tx.π.A ≠ List.replicate 64 0) : -- [finding A0] excluded
    withSyscallSpec C in
    (∃ s₀ steps sₙ,
      CodeModel.Genesis d.programId s₀ ∧ CodeRun d s₀ steps sₙ ∧
      IsRunOf d rent steps sₙ params r)
      ∨ AddressCollision d (fromSpecProof '' {tx | tx ∈ r.txs}) := -- or a break: an address collision
  or_collision (run_complete_of notSystem C laws hashes crypto runtime r deployment notL1 notA0)

end

end Connection
