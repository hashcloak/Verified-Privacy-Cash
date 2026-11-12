import Connection.CodeModelAssumptions
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The hypotheses that link the code to the spec

REVIEW SURFACE. Besides "the code model accepted the transaction", the connection theorems
(`Connection/ConnectionTheorems.lean`) take hypotheses of three sources, each in its own place:
- about the spec: its trusted assumptions T0–T3 (`Spec/Statements.lean`);
- about the code alone: `CodeModelAssumptions.lean`, and core-model's own (`core-model/README.md`);
- linking the two, or leaving a detail out by design: this file.

1. `HashesAgree` (ASSUMED, links the models): the spec's abstract `H2` and `sha256` are the code's
   Poseidon and SHA-256 wherever the code returns a hash; the code's zero hashes are the spec's
   `Z` (computed from `H2`); Poseidon's outputs and the zero hashes are canonical bytes (below
   the field modulus).
2. `OutsideSpecDetail` (BY DESIGN): Solana details the spec deliberately does not model, as
   it is written at the level of the documentation. Each field rules one out;
   `transact_connection` does not cover transactions where such a detail matters. Not a
   defect of the code or the spec. `run_connection` takes only its rent part
   (`ExecutionOutsideSpecDetail`): there the other details are changes the spec allows between
   transactions.
3. For handler completeness only: `CompletenessAssumptions` (`HashesAgree` with the code-model
   assumptions that the primitives answer at all, `CodeModelAssumptions.lean`), and
   `HandlerContext` (invariants and a premise at the handler's start).
4. For G3a and G3b for the code only: `ReachesProgram`, bundling `AccountsCorrect` (the owner's
   choice), the code-model assumptions `ProgramAccountsInPlace`, `NullifierAddressesFree`,
   positive rent and `SolanaFacts`, the rent being fixed (by design), and `SignerCreditFits`
   (a limit).

No code/spec difference is currently excluded by `transact_connection` or `run_connection`. G3a
for the code excludes L1 and A0 by name, and G3b A0: see `Findings.lean`.

Not a hypothesis here, but relied on: core-model's `EnvStep` (outside actions cannot change the
owner or data of an account the program owns, and the program never closes one). The
double-spend protection rests on it: a nullifier account, once created, stays. Check it in
core-model (`PrivacyCash/Model/Execution.lean`).
-/

namespace Connection

variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- `HashesAgree c` (assumed): the spec's hash functions are the program's. The spec leaves `H2`
    and `sha256` abstract (its goals hold for any hash, unless a hash break occurs); this ties them
    to the code's: whenever the code's hash returns `h`, the spec's hash of the same inputs is `h`.
    Inputs the code rejects are left unconstrained. The program's zero hashes must then be the
    spec's empty-subtree roots `Z`, which the spec computes from `H2`. -/
structure HashesAgree (c : Crypto) : Prop where
  /-- Poseidon of two tree nodes is the spec's `H2`. -/
  poseidon : ∀ a b h, c.hasher.hash_pair a b = ok h → toF h = LeanSpec.PoseidonHashes.H2 (toF a) (toF b)
  /-- The program's zero hashes are the spec's empty-subtree roots `Z 0, …, Z 26`. -/
  zeroBytes : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = LeanSpec.Z i
  /-- SHA-256 is the spec's `sha256` (used for the external data hash). -/
  sha256 : ∀ x h, c.sha256.hash x = ok h → toBytes h.val = LeanSpec.Sha.sha256 (toBytes x.val)
  /-- Poseidon's outputs are canonical: their big-endian value is below the field modulus.
      True of the program's hasher: `light-poseidon` computes in `ark_bn254::Fr` and writes
      the result with `into_bigint().to_bytes_be()`, which is always below the field's modulus,
      and that modulus is the spec's `p` (`p_eq`, `Connection/Mapping.lean`). -/
  poseidonCanonical : ∀ a b h, c.hasher.hash_pair a b = ok h → Canonical h
  /-- The program's zero hashes `0, …, 26` are canonical. True: they are Poseidon outputs
      (checked by the fork's `zero_bytes_are_empty_subtree_roots` test), and entry 0 is zero. -/
  zeroBytesCanonical : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → Canonical (z.val[i]!)

/-- `OutsideSpecDetail d rent s tx a proof` (by design): Solana details the spec deliberately
    does not model. Each field rules one out; transactions where it matters are not covered. -/
structure OutsideSpecDetail (d : Deployment) (rent : Nat → U64) (s : State) (tx : TxEnv)
    (a : TransactAccounts) (proof : zkcash_core.transact.Proof) : Prop where
  /-- The rent is fixed. The spec fixes the two rent amounts; the code reads Solana's `Rent`
      sysvar each time. Ruled out: the transaction sees a different rent rate. -/
  rentFixed : tx.minimumBalance = some rent
  /-- Pre-funded nullifier addresses. Anyone can send lamports to the address of a nullifier
      account before it exists; Anchor then only tops it up, so the signer pays less than the
      spec's `2 * nullifierRent`. Ruled out: both addresses hold nothing beforehand. -/
  nullifierAddressesEmpty :
    (s (d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!))).lamports.val = 0 ∧
    (s (d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!))).lamports.val = 0
  /-- Payees that are nullifier accounts. The spec does not count nullifier accounts as public
      accounts; a payment to one (an existing one, or one this transaction creates) is locked
      there. Ruled out: neither payee is a nullifier account. -/
  payeesNotNullifierAccounts :
    (∀ b, (s a.recipient).data ≠ .nullifier b) ∧ (∀ b, (s a.feeRecipientAccount).data ≠ .nullifier b) ∧
    a.recipient ≠ d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) ∧
    a.recipient ≠ d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!) ∧
    a.feeRecipientAccount ≠ d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) ∧
    a.feeRecipientAccount ≠ d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!)

/-- `StepRentFixed rent tx ix` (by design): `initialize` and `transact` see the rent `rent`, as
    `OutsideSpecDetail.rentFixed`. -/
def StepRentFixed (rent : Nat → U64) (tx : TxEnv) : Instruction → Prop
  | .initialize _ => tx.minimumBalance = some rent
  | .transact .. => tx.minimumBalance = some rent
  | _ => True

/-- `ExecutionOutsideSpecDetail d rent sGenesis evs` (by design, used by `run_connection`): the Solana
    detail the spec deliberately does not model, for a whole execution. -/
structure ExecutionOutsideSpecDetail (d : Deployment) (rent : Nat → U64) (sGenesis : State)
    (evs : List Event) : Prop where
  /-- The rent is fixed, as `OutsideSpecDetail.rentFixed`: every `initialize` and `transact` of
      the execution sees the rent `rent`. Ruled out: an execution in which the rent changes. -/
  rentFixed : ∀ pre post s tx ix em, evs = pre ++ .program tx ix em :: post → Run d sGenesis pre s →
    StepRentFixed rent tx ix

/-! ## For handler completeness only -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : AltBn128}

/-- `CompletenessAssumptions c C` (assumed, handler completeness and G3 for the code): the deployment's
    hashes are the spec's (`HashesAgree`), its hash and syscall calls return a value on valid
    input (`HashesSucceed`, `SyscallsSucceed`), the key's G2 points decode (`KeyG2Decodes`),
    and `usize` is 64 bits. -/
structure CompletenessAssumptions (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) : Prop where
  hashesAgree : HashesAgree c
  hashesSucceed : HashesSucceed c
  syscallsSucceed : SyscallsSucceed C
  keyDecodes : KeyG2Decodes C
  /-- `usize` is 64 bits. SOLANA FACT: the program runs on 64-bit SBF. In Aeneas, `Usize.max`
      depends on the platform running Lean, so this cannot be proved; it ties the model to the
      target. -/
  usize64 : Usize.max = 2^64 - 1

end

/-- `HandlerContext a s₁ tree config` (handler completeness only): what holds when
    the handler starts, in the state `s₁` after Anchor's checks and `init`s, for the tree and
    config the handler is given. -/
structure HandlerContext (a : TransactAccounts) (s₁ : State)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (config : zkcash_core.admin.GlobalConfig) : Prop where
  /-- Invariant (`WellFormed.tree`): height 26, a history of 100 roots, a root index below 100. -/
  treeShape : TreeShape tree
  /-- Invariant (`WellFormed.storedRoots`): every stored root is canonical. -/
  rootsCanonical : ∀ j : Fin 100, Canonical tree.root_history.val[j.val]!
  /-- Invariant (`WellFormed.storedSubtrees`): every stored subtree is canonical. -/
  subtreesCanonical : ∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!
  /-- Invariant (`WellFormed.config`): the deposit fee rate is at most 10000. -/
  depositRate : config.deposit_fee_rate.val ≤ 10000
  /-- Invariant (`WellFormed.config`): the withdrawal fee rate is at most 10000. -/
  withdrawalRate : config.withdrawal_fee_rate.val ≤ 10000
  /-- Invariant (`WellFormed.config`): the fee error margin is at most 10000. -/
  feeErrorMargin : config.fee_error_margin.val ≤ 10000
  /-- Premise: the signer is a plain system account. Guaranteed by Anchor whenever creating the
      two nullifier accounts takes lamports from the signer (a system transfer requires a plain
      system account as source); that is always the case unless both nullifier addresses
      already hold their rent. -/
  signerIsSystemAccount : (s₁ a.signer).owner = systemProgram ∧ (s₁ a.signer).data.isEmpty

/-! ## For G3a and G3b for the code: the transaction gets past Anchor -/

/-- `AccountsCorrect d s a proof` (the owner's choice): the sender lists the right accounts.

    Fixes the addresses Anchor checks: the tree, the pool, the config, the four nullifier addresses
    of the proof's nullifiers and the system program. Then the owner's own accounts: the signer
    and the payees. Nothing here is a claim about the program. -/
structure AccountsCorrect (d : Deployment) (s : State) (a : TransactAccounts)
    (proof : zkcash_core.transact.Proof) : Prop where
  tree : a.treeAccount = treeAddr d
  pool : a.treeTokenAccount = poolAddr d
  config : a.globalConfig = configAddr d
  nullifier0 : a.nullifier0 = d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!)
  nullifier1 : a.nullifier1 = d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!)
  nullifier2 : a.nullifier2 = d.pda (nullifier0Seeds proof.input_nullifiers.val[1]!)
  nullifier3 : a.nullifier3 = d.pda (nullifier1Seeds proof.input_nullifiers.val[0]!)
  systemProg : a.systemProgram = systemProgram
  /-- The signer is a plain system account, as a wallet is. -/
  signerPlain : (s a.signer).owner = systemProgram ∧ (s a.signer).data.isEmpty
  /-- The recipient isn't a nullifier account (as `OutsideSpecDetail.payeesNotNullifierAccounts`). -/
  recipient : (∀ b, (s a.recipient).data ≠ .nullifier b) ∧
    a.recipient ≠ a.nullifier0 ∧ a.recipient ≠ a.nullifier1
  /-- The fee recipient isn't a nullifier account (likewise). -/
  feeRecipient : (∀ b, (s a.feeRecipientAccount).data ≠ .nullifier b) ∧
    a.feeRecipientAccount ≠ a.nullifier0 ∧ a.feeRecipientAccount ≠ a.nullifier1

/-- `SignerCreditFits d s a inputs` (a limit): what the signer gets from the transaction doesn't
    overflow a `u64`, measured from its balance before it pays rent (unreachable in practice:
    2^64 lamports exceeds the total SOL supply). Separate from the spec's `balancesFit`, which
    counts the rent, because a pre-funded nullifier address can make the signer pay less. -/
def SignerCreditFits (d : Deployment) (s : State) (a : TransactAccounts) (inputs : LeanSpec.TxInputs) : Prop :=
  ((s a.signer).lamports.val : ℤ) + LeanSpec.balanceDelta inputs (toPubkey (poolAddr d)) 0
    (toPubkey a.signer) < 2^64

/-- `ReachesProgram …`: everything G3a and G3b for the code take about getting a `transact` past
    Anchor and into the program. -/
structure ReachesProgram (d : Deployment) (rent : Nat → U64) (s : State) (tx : TxEnv)
    (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64)
    (out1 out2 : Slice U8) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
    (tt : zkcash_core.admin.TreeTokenAccount) (config : zkcash_core.admin.GlobalConfig) : Prop where
  /-- [owner] The sender lists the right accounts. -/
  accounts : AccountsCorrect d s a proof
  /-- [assumed] The program's accounts are in place. -/
  program : ProgramAccountsInPlace d s tree tt config
  /-- [assumed] Anchor's constraints on the nullifier addresses hold. -/
  nullifiers : NullifierAddressesFree d s proof
  /-- [by design] The transaction sees the rent (as `OutsideSpecDetail.rentFixed`). -/
  rentFixed : tx.minimumBalance = some rent
  /-- [assumed] The rent is positive, as core-model's `Run` requires of every program step
      (`TxEnv.RentPositive`). Taken here because the step is the conclusion, not part of a run. -/
  rentPositive : tx.RentPositive
  /-- [assumed] The Solana facts. -/
  solana : SolanaFacts d tx
  /-- [limit] The signer's credit fits. -/
  signerCredit : SignerCreditFits d s a (toInputs tx.signers a proof ext fee out1 out2)

end Connection
