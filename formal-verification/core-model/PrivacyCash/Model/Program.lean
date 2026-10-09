/-
The zkcash program (SOL instructions) as one function on the chain state:

  step d s tx ix = .ok s'   -- the instruction succeeds and the chain becomes s'
  step d s tx ix = .error e -- it fails; the transaction reverts and s is kept

Each instruction runs like on-chain:
  1. Anchor loads and checks the accounts (`Accounts.lean`), then creates the
     `init` accounts (the payer funds them through the system program);
  2. the handler runs: the EXTRACTED `zkcash_core` function, with the model
     runtime (`Runtime.lean`) and the deployment's crypto (`Crypto.lean`);
  3. the handler's account data is written back;
  4. the runtime's end-of-instruction check: total lamports of the
     instruction's accounts are unchanged.

What is checked but not distinguished: WHICH error a failing instruction
returns when Anchor or the runtime rejects it (the program's own error codes
are kept). Checks left out (writable flags, rent exemption, the runtime's
"only the owner debits" rule, compute limits) only make real instructions
fail, so leaving them out keeps the model at least as permissive as Solana.
-/
import PrivacyCash.Model.Accounts
import PrivacyCash.Model.Runtime
import PrivacyCash.Model.Crypto
import Mathlib.Data.List.Dedup
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Model

/-- What differs between deployments of the same program: where it lives and
    how its addresses derive (`Addresses`), the crypto, and the admin key. -/
structure Deployment extends Addresses where
  crypto : Crypto
  /-- `ADMIN_PUBKEY`: `none` on localnet (anyone may initialize), the admin key otherwise. -/
  adminPubkey : Option Pubkey

/-- What the transaction provides besides its accounts. -/
structure TxEnv extends TxContext where
  /-- `Rent::get()?.minimum_balance(space)`, or `none` if reading the `Rent`
      sysvar fails. -/
  minimumBalance : Option (Nat → U64)

/-- The SOL instructions, with their accounts and arguments. -/
inductive Instruction where
  | initialize (accounts : InitializeAccounts)
  | updateDepositLimit (accounts : UpdateDepositLimitAccounts) (newLimit : U64)
  | updateGlobalConfig (accounts : UpdateGlobalConfigAccounts)
      (depositFeeRate withdrawalFeeRate feeErrorMargin : Option U16)
  | transact (accounts : TransactAccounts) (proof : zkcash_core.transact.Proof)
      (extAmount : I64) (fee : U64) (encryptedOutput1 encryptedOutput2 : Slice U8)

/-- Why an instruction failed. -/
inductive Error where
  /-- Anchor rejected the accounts, or creating an `init` account failed. -/
  | accounts
  /-- The handler returned one of the program's error codes. -/
  | program (code : zkcash_core.error.ErrorCode)
  /-- `transact` failed in the runtime (CPI, sysvar) or in serialization. -/
  | transact (e : zkcash_core.transact.Error)
  /-- The Rust code panicked. -/
  | panic
  /-- The runtime's end-of-instruction check failed (lamports not conserved). -/
  | unbalanced

/-! ## Account sizes (`space = 8 + size_of::<T>()`)

Checked against the program's `size_of` by `Tests/AccountSpaces.lean`. -/

def treeAccountSpace : Nat := 8 + 4128        -- MerkleTreeAccount
def treeTokenAccountSpace : Nat := 8 + 33     -- TreeTokenAccount
def globalConfigSpace : Nat := 8 + 40         -- GlobalConfig (39 bytes, aligned to 2)
def nullifierAccountSpace : Nat := 8 + 1      -- NullifierAccount

/-! ## Runtime helpers -/

/-- Anchor's `init`, paid by `payer` (Anchor 0.31.1 `generate_create_account`):
    if the address holds no lamports, `create_account` funds it with the
    rent-exempt minimum; otherwise the payer (which must be a different
    account) tops it up to that minimum. Either way the account becomes owned
    by this program and holds `data`. `none` if a transfer fails. The
    "nothing created here yet" precondition is part of the account checks. -/
def State.initAccount (programId : Pubkey) (s : State) (minimumBalance : Nat → U64) (payer key : Pubkey)
    (space : Nat) (data : AccountData) : Option State :=
  let required := minimumBalance space
  let funded :=
    if (s key).lamports.val = 0 then s.systemTransfer payer key required
    else if payer = key then none
    else
      let topUp := (max required.val 1) - (s key).lamports.val
      if topUp = 0 then some s
      else s.systemTransfer payer key ⟨BitVec.ofNat 64 topUp⟩
  funded.map fun s' => s'.set key { s' key with owner := programId, data := data }

/-- Total lamports of the distinct accounts in `keys`. -/
def State.totalLamports (s : State) (keys : List Pubkey) : Nat :=
  (keys.dedup.map fun k => (s k).lamports.val).sum

/-- The runtime's end-of-instruction check over the instruction's accounts. -/
def checkBalanced (s s' : State) (keys : List Pubkey) : Except Error State :=
  if s'.totalLamports keys = s.totalLamports keys then .ok s' else .error .unbalanced

/-- The outcome of extracted code: its value, or a panic. -/
def ofResult {α : Type} (r : Result α) : Except Error α :=
  match Option.ofResult r with
  | some a => .ok a
  | none => .error .panic

/-- The zero-filled `MerkleTreeAccount` that `load_init` starts from. -/
def zeroTree : zkcash_core.merkle_tree.MerkleTreeAccount where
  authority := Std.Array.repeat 32#usize 0#u8
  next_index := 0#u64
  subtrees := Std.Array.repeat 26#usize (Std.Array.repeat 32#usize 0#u8)
  root := Std.Array.repeat 32#usize 0#u8
  root_history := Std.Array.repeat 100#usize (Std.Array.repeat 32#usize 0#u8)
  root_index := 0#u64
  max_deposit_amount := 0#u64
  height := 0#u8
  root_history_size := 0#u8
  bump := 0#u8
  _padding := Std.Array.repeat 5#usize 0#u8

/-! ## The instructions -/

/-- `initialize`. -/
def execInitialize (d : Deployment) (s : State) (tx : TxEnv)
    (a : InitializeAccounts) : Except Error State :=
  if ¬ InitializeAccountsValid d.toAddresses s tx.toTxContext a then .error .accounts else
  match tx.minimumBalance with
  | none => .error .accounts
  | some mb =>
  -- Anchor creates the three accounts, paid by the authority.
  match (s.initAccount d.programId mb a.authority a.treeAccount treeAccountSpace (.treeAccount zeroTree)).bind
      (·.initAccount d.programId mb a.authority a.treeTokenAccount treeTokenAccountSpace
        (.treeToken ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩)) |>.bind
      (·.initAccount d.programId mb a.authority a.globalConfig globalConfigSpace
        (.globalConfig ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩)) with
  | none => .error .accounts
  | some s₁ => do
    -- The handler: the admin check, then the field writes.
    match ← ofResult (zkcash_core.admin.check_admin a.authority d.adminPubkey) with
    | .Err e => .error (.program e)
    | .Ok () =>
      let (r, tree, token, config) ← ofResult (zkcash_core.admin.initialize d.crypto.hasher
        zeroTree ⟨Std.Array.repeat 32#usize 0#u8, 0#u8⟩
        ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩ a.authority
        (d.canonicalBump merkleTreeSeeds) (d.canonicalBump treeTokenSeeds)
        (d.canonicalBump globalConfigSeeds))
      match r with
      | .Err e => .error (.program e)
      | .Ok () =>
        let s₂ := s₁.set a.treeAccount { s₁ a.treeAccount with data := .treeAccount tree }
        let s₃ := s₂.set a.treeTokenAccount { s₂ a.treeTokenAccount with data := .treeToken token }
        let s₄ := s₃.set a.globalConfig { s₃ a.globalConfig with data := .globalConfig config }
        checkBalanced s s₄ [a.treeAccount, a.treeTokenAccount, a.globalConfig, a.authority, a.systemProgram]

/-- `update_deposit_limit`. -/
def execUpdateDepositLimit (d : Deployment) (s : State) (tx : TxEnv)
    (a : UpdateDepositLimitAccounts) (newLimit : U64) : Except Error State :=
  match (s a.treeAccount).data with
  | .treeAccount tree =>
    if ¬ UpdateDepositLimitAccountsValid d.toAddresses s tx.toTxContext a tree then .error .accounts else do
    let tree' ← ofResult (zkcash_core.admin.update_deposit_limit tree newLimit)
    .ok (s.set a.treeAccount { s a.treeAccount with data := .treeAccount tree' })
  | _ => .error .accounts

/-- `update_global_config`. -/
def execUpdateGlobalConfig (d : Deployment) (s : State) (tx : TxEnv)
    (a : UpdateGlobalConfigAccounts) (dep wd margin : Option U16) : Except Error State :=
  match (s a.globalConfig).data with
  | .globalConfig config =>
    if ¬ UpdateGlobalConfigAccountsValid d.toAddresses s tx.toTxContext a config then .error .accounts else do
    let (r, config') ← ofResult (zkcash_core.admin.update_global_config config dep wd margin)
    match r with
    | .Err e => .error (.program e)
    | .Ok () => .ok (s.set a.globalConfig { s a.globalConfig with data := .globalConfig config' })
  | _ => .error .accounts

/-- `transact`. -/
def execTransact (d : Deployment) (s : State) (tx : TxEnv) (a : TransactAccounts)
    (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64)
    (out1 out2 : Slice U8) : Except Error State :=
  let n₀ := proof.input_nullifiers.val[0]!
  let n₁ := proof.input_nullifiers.val[1]!
  match (s a.treeAccount).data, (s a.treeTokenAccount).data, (s a.globalConfig).data with
  | .treeAccount tree, .treeToken treeToken, .globalConfig config =>
    if ¬ TransactAccountsValid d.toAddresses s tx.toTxContext a n₀ n₁ tree treeToken config then .error .accounts else
    match tx.minimumBalance with
    | none => .error .accounts
    | some mb =>
    -- Anchor creates the two nullifier accounts, paid by the signer.
    match (s.initAccount d.programId mb a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
        (·.initAccount d.programId mb a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) with
    | none => .error .accounts
    | some s₁ => do
      -- The handler: the extracted `transact` with the model runtime.
      let env : SolEnv :=
        { accounts := s₁, balances := s₁.balances, signer := a.signer,
          treeToken := a.treeTokenAccount, recipient := a.recipient,
          feeRecipient := a.feeRecipientAccount,
          rentExemptMinimum := some (mb treeTokenAccountSpace) }
      let (r, env', tree') ← ofResult (zkcash_core.transact.transact d.crypto.hasher
        arkFr d.crypto.sha256 d.crypto.proofVerifier solRuntime env tree config proof
        extAmount fee a.recipient a.feeRecipientAccount out1 out2)
      match r with
      | .Err e => .error (.transact e)
      | .Ok _ =>
        -- The runtime only changed balances: owners and data are those after `init`.
        let s₂ := s₁.withBalances env'.balances
        let s₃ := s₂.set a.treeAccount { s₂ a.treeAccount with data := .treeAccount tree' }
        checkBalanced s s₃ [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3,
          a.treeTokenAccount, a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer,
          a.systemProgram]
  | _, _, _ => .error .accounts

/-- **The program**: one instruction on the chain. -/
def step (d : Deployment) (s : State) (tx : TxEnv) : Instruction → Except Error State
  | .initialize a => execInitialize d s tx a
  | .updateDepositLimit a newLimit => execUpdateDepositLimit d s tx a newLimit
  | .updateGlobalConfig a dep wd margin => execUpdateGlobalConfig d s tx a dep wd margin
  | .transact a proof extAmount fee out1 out2 => execTransact d s tx a proof extAmount fee out1 out2

/-! ## Sanity checks: the model enforces access control -/

/-- If the authority did not sign, `update_deposit_limit` fails. -/
theorem updateDepositLimit_requires_signature (d : Deployment) (s : State) (tx : TxEnv)
    (a : UpdateDepositLimitAccounts) (newLimit : U64) (h : a.authority ∉ tx.signers) :
    execUpdateDepositLimit d s tx a newLimit = .error .accounts := by
  unfold execUpdateDepositLimit
  split
  · rw [if_pos (fun hv => h hv.authority)]
  · rfl

/-- `update_deposit_limit` succeeds only if the signing authority is the one
    recorded in the tree it changes. -/
theorem updateDepositLimit_only_by_tree_authority (d : Deployment) (s s' : State) (tx : TxEnv)
    (a : UpdateDepositLimitAccounts) (newLimit : U64)
    (h : execUpdateDepositLimit d s tx a newLimit = .ok s') :
    a.authority ∈ tx.signers ∧
      ∃ tree, (s a.treeAccount).data = .treeAccount tree ∧ tree.authority = a.authority := by
  unfold execUpdateDepositLimit at h
  split at h
  · rename_i tree htree
    by_cases hv : UpdateDepositLimitAccountsValid d.toAddresses s tx.toTxContext a tree
    · exact ⟨hv.authority, tree, htree, hv.treeAccount.2.2⟩
    · simp [hv] at h
  · cases h

end PrivacyCash.Model
