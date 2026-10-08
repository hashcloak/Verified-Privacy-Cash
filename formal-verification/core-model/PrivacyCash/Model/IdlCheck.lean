/-
The hand-written account model agrees with the program's IDL.

Each `model...` list below is what Accounts.lean / Pda.lean / Program.lean say
about an instruction's accounts, written in the IDL's terms and built from the
model's own definitions (`merkleTreeSeeds`, `systemProgram`, ...). Each
theorem proves it equal to the list generated from the IDL (Idl.lean). If the
program's `#[derive(Accounts)]` changes, regenerating Idl.lean makes these
theorems fail until the model is updated.

What the IDL cannot check, and is kept right by hand (see the comments):
which model field each IDL account is, and which instruction argument feeds
an `arg` seed.
-/
import PrivacyCash.Model.Idl
import PrivacyCash.Model.Program
open Aeneas Aeneas.Std

namespace PrivacyCash.Model.IdlCheck
open PrivacyCash.Model PrivacyCash.Model.Idl

/-- Bytes as the IDL writes them. -/
def bytes (l : List U8) : List Nat := l.map (·.val)

/-- A constant seed, from the model's seed bytes. -/
def const (l : List U8) : Seed := .const (bytes l)

/-- One account, with the IDL's defaults (not a signer, no fixed address, no
    PDA, no relations). (`name` is a keyword once Aeneas is imported.) -/
def acct (accountName : String) (isSigner : Bool := false) (address : Option (List Nat) := none)
    (seeds : Option (List Seed) := none) (relations : List String := []) : AccountSpec :=
  AccountSpec.mk accountName isSigner address seeds relations

/-- `system_program: Program<System>` is checked against `systemProgram`. -/
def systemProgramAddress : Option (List Nat) := some (bytes systemProgram.val)

/-- `initialize`: `InitializeAccounts` / `InitializeAccountsValid`. -/
def modelInitialize : List AccountSpec := [
  acct "tree_account" (seeds := some [const merkleTreeSeeds]),          -- treeAccount
  acct "tree_token_account" (seeds := some [const treeTokenSeeds]),     -- treeTokenAccount
  acct "global_config" (seeds := some [const globalConfigSeeds]),       -- globalConfig
  acct "authority" (isSigner := true),                                    -- authority
  acct "system_program" (address := systemProgramAddress)]              -- systemProgram

/-- `update_deposit_limit`: `UpdateDepositLimitAccounts` / `...Valid`
    (the relation is `tree.authority = a.authority`). -/
def modelUpdateDepositLimit : List AccountSpec := [
  acct "tree_account" (seeds := some [const merkleTreeSeeds]),          -- treeAccount
  acct "authority" (isSigner := true) (relations := ["tree_account"])]    -- authority

/-- `update_global_config`: `UpdateGlobalConfigAccounts` / `...Valid`
    (the relation is `globalConfig.authority = a.authority`). -/
def modelUpdateGlobalConfig : List AccountSpec := [
  acct "global_config" (seeds := some [const globalConfigSeeds]),       -- globalConfig
  acct "authority" (isSigner := true) (relations := ["global_config"])]   -- authority

/-- `transact`: `TransactAccounts` / `TransactAccountsValid`. The nullifier
    seeds are `nullifier0Seeds n = ascii "nullifier0" ++ n` (and likewise for
    slot 1), with `n₀ = proof.input_nullifiers[0]`, `n₁ = ...[1]` in `execTransact`. -/
def modelTransact : List AccountSpec := [
  acct "tree_account" (seeds := some [const merkleTreeSeeds]),          -- treeAccount
  acct "nullifier0"                                                     -- nullifier0: n₀
    (seeds := some [const (ascii "nullifier0"), .arg "proof.input_nullifiers [0]"]),
  acct "nullifier1"                                                     -- nullifier1: n₁
    (seeds := some [const (ascii "nullifier1"), .arg "proof.input_nullifiers [1]"]),
  acct "nullifier2"                                                     -- nullifier2: slot 0, n₁
    (seeds := some [const (ascii "nullifier0"), .arg "proof.input_nullifiers [1]"]),
  acct "nullifier3"                                                     -- nullifier3: slot 1, n₀
    (seeds := some [const (ascii "nullifier1"), .arg "proof.input_nullifiers [0]"]),
  acct "tree_token_account" (seeds := some [const treeTokenSeeds]),     -- treeTokenAccount
  acct "global_config" (seeds := some [const globalConfigSeeds]),       -- globalConfig
  acct "recipient",                                                     -- recipient
  acct "fee_recipient_account",                                         -- feeRecipientAccount
  acct "signer" (isSigner := true),                                       -- signer
  acct "system_program" (address := systemProgramAddress)]              -- systemProgram

/-- The nullifier seeds used above are the model's. -/
theorem nullifierSeeds_eq (n : Pubkey) :
    nullifier0Seeds n = ascii "nullifier0" ++ n.val ∧
    nullifier1Seeds n = ascii "nullifier1" ++ n.val := ⟨rfl, rfl⟩

theorem initialize_matches_idl : modelInitialize = Idl.ixInitialize := by decide
theorem updateDepositLimit_matches_idl : modelUpdateDepositLimit = Idl.ixUpdateDepositLimit := by decide
theorem updateGlobalConfig_matches_idl : modelUpdateGlobalConfig = Idl.ixUpdateGlobalConfig := by decide
theorem transact_matches_idl : modelTransact = Idl.ixTransact := by decide

end PrivacyCash.Model.IdlCheck
