/-
What Anchor checks about each instruction's accounts before the handler runs
(the `#[derive(Accounts)]` structs in lib.rs, Anchor 0.31.1).

Anchor's generated `try_accounts` works in two passes:
  1. in field order, every non-`init` field is loaded and type-checked
     (`Account<T>` / `AccountLoader<T>`: owned by this program with T's
     discriminator; `SystemAccount`: owned by the system program;
     `Signer`: signed the transaction; `Program<System>`: the system program);
  2. in field order, the constraints run: `seeds`/`bump` address checks, and
     `init`, which creates the account.
So pass-1 checks see the state before any `init`. Anchor 0.31.1 does not
reject the same account passed in two fields (no duplicate-account check).

Soundness rule for this file: the model may check LESS than Anchor (that only
lets it accept more transactions, so safety proofs still cover every real
one), never MORE. Checks left out on purpose are listed at each structure.
-/
import PrivacyCash.Model.Pda
open Aeneas Aeneas.Std

namespace PrivacyCash.Model

/-- What the transaction itself provides. -/
structure TxContext where
  /-- The keys that signed the transaction. -/
  signers : List Pubkey

/-- `init` can create an account at `key` only if nothing has been created
    there yet: still owned by the system program, with no data. (Lamports may
    already be there; Anchor tops them up. The system program's `allocate` and
    `assign` fail otherwise.) -/
def Initializable (s : State) (key : Pubkey) : Prop :=
  (s key).owner = systemProgram ∧ (s key).data = .empty

/-- `SystemAccount<'info>`: owned by the system program. -/
def IsSystemAccount (s : State) (key : Pubkey) : Prop :=
  (s key).owner = systemProgram

/-- `AccountLoader<MerkleTreeAccount>` at `key` holding `tree`. -/
def HoldsTree (programId : Pubkey) (s : State) (key : Pubkey) (tree : zkcash_core.merkle_tree.MerkleTreeAccount) : Prop :=
  (s key).owner = programId ∧ (s key).data = .treeAccount tree

/-- `Account<TreeTokenAccount>` at `key` holding `t`. -/
def HoldsTreeToken (programId : Pubkey) (s : State) (key : Pubkey) (t : zkcash_core.admin.TreeTokenAccount) : Prop :=
  (s key).owner = programId ∧ (s key).data = .treeToken t

/-- `Account<GlobalConfig>` at `key` holding `c`. -/
def HoldsGlobalConfig (programId : Pubkey) (s : State) (key : Pubkey) (c : zkcash_core.admin.GlobalConfig) : Prop :=
  (s key).owner = programId ∧ (s key).data = .globalConfig c

/-! ## `transact` -/

/-- The accounts passed to `transact`, in the order of `struct Transact` (lib.rs). -/
structure TransactAccounts where
  treeAccount : Pubkey
  nullifier0 : Pubkey
  nullifier1 : Pubkey
  nullifier2 : Pubkey
  nullifier3 : Pubkey
  treeTokenAccount : Pubkey
  globalConfig : Pubkey
  recipient : Pubkey
  feeRecipientAccount : Pubkey
  signer : Pubkey
  systemProgram : Pubkey

/-- Everything Anchor checks about `transact`'s accounts, for the proof's input
    nullifiers `n₀ n₁` (`proof.input_nullifiers`), on the state `s` before the
    instruction. The loaded tree, pool and config are named so the handler
    model can use them.

    Left out (each only makes real transactions fail, never succeed):
    `mut` accounts being writable, the signer being able to pay the nullifier
    accounts' rent (modeled when `init` is executed), rent exemption.
    `recipient` and `fee_recipient_account` are `UncheckedAccount`s: any
    account at all, possibly one of the others. -/
structure TransactAccountsValid (A : Addresses) (s : State) (tx : TxContext) (a : TransactAccounts)
    (n₀ n₁ : Pubkey) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
    (treeToken : zkcash_core.admin.TreeTokenAccount)
    (globalConfig : zkcash_core.admin.GlobalConfig) : Prop where
  /-- `tree_account: AccountLoader<MerkleTreeAccount>`,
      `seeds = [b"merkle_tree"], bump = tree_account.load()?.bump`. -/
  treeAccount : HoldsTree A.programId s a.treeAccount tree ∧
    a.treeAccount = A.createProgramAddress (merkleTreeSeeds ++ [tree.bump])
  /-- `nullifier0: init, seeds = [b"nullifier0", proof.input_nullifiers[0]], bump`. -/
  nullifier0 : a.nullifier0 = A.pda (nullifier0Seeds n₀) ∧ Initializable s a.nullifier0
  /-- `nullifier1: init, seeds = [b"nullifier1", proof.input_nullifiers[1]], bump`. -/
  nullifier1 : a.nullifier1 = A.pda (nullifier1Seeds n₁) ∧ Initializable s a.nullifier1
  /-- `nullifier2: SystemAccount, seeds = [b"nullifier0", proof.input_nullifiers[1]], bump`:
      nullifier 1 was never spent in slot 0. -/
  nullifier2 : a.nullifier2 = A.pda (nullifier0Seeds n₁) ∧ IsSystemAccount s a.nullifier2
  /-- `nullifier3: SystemAccount, seeds = [b"nullifier1", proof.input_nullifiers[0]], bump`:
      nullifier 0 was never spent in slot 1. -/
  nullifier3 : a.nullifier3 = A.pda (nullifier1Seeds n₀) ∧ IsSystemAccount s a.nullifier3
  /-- `tree_token_account: Account<TreeTokenAccount>`,
      `seeds = [b"tree_token"], bump = tree_token_account.bump`. -/
  treeTokenAccount : HoldsTreeToken A.programId s a.treeTokenAccount treeToken ∧
    a.treeTokenAccount = A.createProgramAddress (treeTokenSeeds ++ [treeToken.bump])
  /-- `global_config: Account<GlobalConfig>`,
      `seeds = [b"global_config"], bump = global_config.bump`. -/
  globalConfig : HoldsGlobalConfig A.programId s a.globalConfig globalConfig ∧
    a.globalConfig = A.createProgramAddress (globalConfigSeeds ++ [globalConfig.bump])
  /-- `signer: Signer`. -/
  signer : a.signer ∈ tx.signers
  /-- `system_program: Program<System>`. -/
  systemProgram : a.systemProgram = systemProgram

/-! ## `initialize` -/

/-- The accounts passed to `initialize`, in the order of `struct Initialize`. -/
structure InitializeAccounts where
  treeAccount : Pubkey
  treeTokenAccount : Pubkey
  globalConfig : Pubkey
  authority : Pubkey
  systemProgram : Pubkey

/-- Everything Anchor checks about `initialize`'s accounts. All three program
    accounts are `init` at their canonical PDAs, so `initialize` can succeed
    only once. Who may call it is checked by the handler (`ADMIN_PUBKEY`),
    not here.

    Left out: writable flags, the authority affording the three accounts'
    rent (modeled when `init` is executed). -/
structure InitializeAccountsValid (A : Addresses) (s : State) (tx : TxContext) (a : InitializeAccounts) : Prop where
  /-- `tree_account: AccountLoader<MerkleTreeAccount>, init, seeds = [b"merkle_tree"], bump`. -/
  treeAccount : a.treeAccount = A.pda merkleTreeSeeds ∧ Initializable s a.treeAccount
  /-- `tree_token_account: Account<TreeTokenAccount>, init, seeds = [b"tree_token"], bump`. -/
  treeTokenAccount : a.treeTokenAccount = A.pda treeTokenSeeds ∧ Initializable s a.treeTokenAccount
  /-- `global_config: Account<GlobalConfig>, init, seeds = [b"global_config"], bump`. -/
  globalConfig : a.globalConfig = A.pda globalConfigSeeds ∧ Initializable s a.globalConfig
  /-- `authority: Signer` (and the payer of all three accounts). -/
  authority : a.authority ∈ tx.signers
  /-- `system_program: Program<System>`. -/
  systemProgram : a.systemProgram = systemProgram

/-! ## `update_deposit_limit` -/

/-- The accounts passed to `update_deposit_limit`, in the order of `struct UpdateDepositLimit`. -/
structure UpdateDepositLimitAccounts where
  treeAccount : Pubkey
  authority : Pubkey

/-- Everything Anchor checks about `update_deposit_limit`'s accounts: the
    signer must be the authority recorded in the SOL tree. -/
structure UpdateDepositLimitAccountsValid (A : Addresses) (s : State) (tx : TxContext) (a : UpdateDepositLimitAccounts)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) : Prop where
  /-- `tree_account: AccountLoader<MerkleTreeAccount>`,
      `seeds = [b"merkle_tree"], bump = tree_account.load()?.bump`,
      `has_one = authority @ ErrorCode::Unauthorized`. -/
  treeAccount : HoldsTree A.programId s a.treeAccount tree ∧
    a.treeAccount = A.createProgramAddress (merkleTreeSeeds ++ [tree.bump]) ∧
    tree.authority = a.authority
  /-- `authority: Signer`. -/
  authority : a.authority ∈ tx.signers

/-! ## `update_global_config` -/

/-- The accounts passed to `update_global_config`, in the order of `struct UpdateGlobalConfig`. -/
structure UpdateGlobalConfigAccounts where
  globalConfig : Pubkey
  authority : Pubkey

/-- Everything Anchor checks about `update_global_config`'s accounts: the
    signer must be the authority recorded in the config. -/
structure UpdateGlobalConfigAccountsValid (A : Addresses) (s : State) (tx : TxContext) (a : UpdateGlobalConfigAccounts)
    (globalConfig : zkcash_core.admin.GlobalConfig) : Prop where
  /-- `global_config: Account<GlobalConfig>`,
      `seeds = [b"global_config"], bump = global_config.bump`,
      `has_one = authority @ ErrorCode::Unauthorized`. -/
  globalConfig : HoldsGlobalConfig A.programId s a.globalConfig globalConfig ∧
    a.globalConfig = A.createProgramAddress (globalConfigSeeds ++ [globalConfig.bump]) ∧
    globalConfig.authority = a.authority
  /-- `authority: Signer`. -/
  authority : a.authority ∈ tx.signers

/-! ## The checks are decidable (so the model can be run on concrete inputs) -/

instance (s : State) (key : Pubkey) : Decidable (Initializable s key) := by
  unfold Initializable; infer_instance
instance (s : State) (key : Pubkey) : Decidable (IsSystemAccount s key) := by
  unfold IsSystemAccount; infer_instance
instance (pid : Pubkey) (s : State) (key : Pubkey) (t : zkcash_core.merkle_tree.MerkleTreeAccount) :
    Decidable (HoldsTree pid s key t) := by
  unfold HoldsTree; infer_instance
instance (pid : Pubkey) (s : State) (key : Pubkey) (t : zkcash_core.admin.TreeTokenAccount) :
    Decidable (HoldsTreeToken pid s key t) := by
  unfold HoldsTreeToken; infer_instance
instance (pid : Pubkey) (s : State) (key : Pubkey) (c : zkcash_core.admin.GlobalConfig) :
    Decidable (HoldsGlobalConfig pid s key c) := by
  unfold HoldsGlobalConfig; infer_instance

instance (A : Addresses) (s : State) (tx : TxContext) (a : TransactAccounts) (n₀ n₁ : Pubkey)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (treeToken : zkcash_core.admin.TreeTokenAccount)
    (globalConfig : zkcash_core.admin.GlobalConfig) :
    Decidable (TransactAccountsValid A s tx a n₀ n₁ tree treeToken globalConfig) :=
  decidable_of_iff
    ((HoldsTree A.programId s a.treeAccount tree ∧
        a.treeAccount = A.createProgramAddress (merkleTreeSeeds ++ [tree.bump])) ∧
      (a.nullifier0 = A.pda (nullifier0Seeds n₀) ∧ Initializable s a.nullifier0) ∧
      (a.nullifier1 = A.pda (nullifier1Seeds n₁) ∧ Initializable s a.nullifier1) ∧
      (a.nullifier2 = A.pda (nullifier0Seeds n₁) ∧ IsSystemAccount s a.nullifier2) ∧
      (a.nullifier3 = A.pda (nullifier1Seeds n₀) ∧ IsSystemAccount s a.nullifier3) ∧
      (HoldsTreeToken A.programId s a.treeTokenAccount treeToken ∧
        a.treeTokenAccount = A.createProgramAddress (treeTokenSeeds ++ [treeToken.bump])) ∧
      (HoldsGlobalConfig A.programId s a.globalConfig globalConfig ∧
        a.globalConfig = A.createProgramAddress (globalConfigSeeds ++ [globalConfig.bump])) ∧
      a.signer ∈ tx.signers ∧ a.systemProgram = systemProgram)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩,
     fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩⟩

instance (A : Addresses) (s : State) (tx : TxContext) (a : InitializeAccounts) :
    Decidable (InitializeAccountsValid A s tx a) :=
  decidable_of_iff
    ((a.treeAccount = A.pda merkleTreeSeeds ∧ Initializable s a.treeAccount) ∧
      (a.treeTokenAccount = A.pda treeTokenSeeds ∧ Initializable s a.treeTokenAccount) ∧
      (a.globalConfig = A.pda globalConfigSeeds ∧ Initializable s a.globalConfig) ∧
      a.authority ∈ tx.signers ∧ a.systemProgram = systemProgram)
    ⟨fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

instance (A : Addresses) (s : State) (tx : TxContext) (a : UpdateDepositLimitAccounts)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) :
    Decidable (UpdateDepositLimitAccountsValid A s tx a tree) :=
  decidable_of_iff
    ((HoldsTree A.programId s a.treeAccount tree ∧
        a.treeAccount = A.createProgramAddress (merkleTreeSeeds ++ [tree.bump]) ∧
        tree.authority = a.authority) ∧ a.authority ∈ tx.signers)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.1, h.2⟩⟩

instance (A : Addresses) (s : State) (tx : TxContext) (a : UpdateGlobalConfigAccounts)
    (globalConfig : zkcash_core.admin.GlobalConfig) :
    Decidable (UpdateGlobalConfigAccountsValid A s tx a globalConfig) :=
  decidable_of_iff
    ((HoldsGlobalConfig A.programId s a.globalConfig globalConfig ∧
        a.globalConfig = A.createProgramAddress (globalConfigSeeds ++ [globalConfig.bump]) ∧
        globalConfig.authority = a.authority) ∧ a.authority ∈ tx.signers)
    ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.1, h.2⟩⟩

end PrivacyCash.Model
