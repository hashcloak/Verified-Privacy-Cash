import Connection.CodeModelAssumptions
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The hypotheses that link the code to the spec

REVIEW SURFACE. Besides "the code model accepted the transaction", the connection theorems
(`Connection/ConnectionTheorems.lean`) take hypotheses of three sources, each in its own place:
- about the spec: its trusted assumptions T0–T3 (`Spec/Statements.lean`);
- about the code alone: `CodeModelAssumptions.lean`, and core-model's own (`core-model/README.md`);
- linking the two: this file.

1. `HashesAgree` (ASSUMED, links the models): the spec's abstract `H2` and `sha256` are the code's
   Poseidon and SHA-256 wherever the code returns a hash; the code's zero hashes are the spec's
   `Z` (computed from `H2`); Poseidon's outputs and the zero hashes are canonical bytes (below
   the field modulus).
2. `SameRent` (ASSUMED, links the models): the code and the spec use the same rent.
   `transact_connection` takes it for its transaction, `run_connection` for every program
   instruction of the execution.
3. For handler completeness only: `HandlerContext` (invariants and a premise at the handler's
   start).
4. For G3a and G3b for the code only: `ReachesProgram`, bundling `AccountsCorrect` (the owner's
   choice), the code-model assumptions `ProgramAccountsInPlace`, `NullifierAddressesFree`,
   positive rent and `SolanaFacts`, and the same rent on both sides (`SameRent`, assumed).

No code/spec difference and no Solana detail is excluded by `transact_connection` or
`run_connection`. G3a for the code excludes L1 and A0 by name, and G3b A0: see `Findings.lean`.

Not a hypothesis here, but relied on: core-model's `EnvStep` (outside actions cannot change the
owner or data of an account the program owns, and the program never closes one). The
double-spend protection rests on it: a nullifier account, once created, stays. Check it in
core-model (`PrivacyCash/Model/Execution.lean`).
-/

namespace Connection

variable [Spec.PoseidonHashes] [Spec.Sha]

/-- `HashesAgree c` (assumed): the spec's hash functions are the program's. The spec leaves `H2`
    and `sha256` abstract (its goals hold for any hash, unless a hash break occurs); this ties them
    to the code's: whenever the code's hash returns `h`, the spec's hash of the same inputs is `h`.
    Inputs the code rejects are left unconstrained. The program's zero hashes must then be the
    spec's empty-subtree roots `Z`, which the spec computes from `H2`. -/
structure HashesAgree (c : Crypto) : Prop where
  /-- Poseidon of two tree nodes is the spec's `H2`. -/
  poseidon : ∀ a b h, c.hasher.hash_pair a b = ok h → toF h = Spec.PoseidonHashes.H2 (toF a) (toF b)
  /-- The program's zero hashes are the spec's empty-subtree roots `Z 0, …, Z 26`. -/
  zeroBytes : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = Spec.Z i
  /-- SHA-256 is the spec's `sha256` (used for the external data hash). -/
  sha256 : ∀ x h, c.sha256.hash x = ok h → toBytes h.val = Spec.Sha.sha256 (toBytes x.val)
  /-- Poseidon's outputs are canonical: their big-endian value is below the field modulus.
      True of the program's hasher: `light-poseidon` computes in `ark_bn254::Fr` and writes
      the result with `into_bigint().to_bytes_be()`, which is always below the field's modulus,
      and that modulus is the spec's `p` (`p_eq`, `Connection/Mapping.lean`). -/
  poseidonCanonical : ∀ a b h, c.hasher.hash_pair a b = ok h → Canonical h
  /-- The program's zero hashes `0, …, 26` are canonical. True: they are Poseidon outputs
      (checked by the fork's `zero_bytes_are_empty_subtree_roots` test), and entry 0 is zero. -/
  zeroBytesCanonical : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → Canonical (z.val[i]!)

/-- `SameRent rent tx` (assumed): the code and the spec use the same rent. The spec takes its
    two rent amounts as given (`toWorld` reads them from `rent`); the code reads them from
    Solana's `Rent` sysvar (`tx.minimumBalance`). Assumed equal. Ruled out: a transaction that
    sees a different rent, or none. -/
def SameRent (rent : Nat → U64) (tx : TxEnv) : Prop := tx.minimumBalance = some rent

/-! ## For handler completeness only -/

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
    of the proof's nullifiers and the system program. Then the owner's own account: the signer
    of the transaction. Nothing here is a claim about the program. -/
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
  /-- [assumed] The code and the spec use the same rent (`SameRent`). -/
  sameRent : SameRent rent tx
  /-- [assumed] The rent is positive, as core-model's `Run` requires of every program step
      (`TxEnv.RentPositive`). Taken here because the step is the conclusion, not part of a run. -/
  rentPositive : tx.RentPositive
  /-- [assumed] The Solana facts. -/
  solana : SolanaFacts d tx

end Connection
