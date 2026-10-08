/-
The Solana state the Privacy Cash model runs on: addresses, accounts and
the chain. Account contents are modeled after Anchor has decoded them (the
Borsh / zero-copy byte encodings are trusted, not modeled).
-/
import PrivacyCash.Extracted.Funs
open Aeneas Aeneas.Std

namespace PrivacyCash.Model

/-- A 32-byte address, the same type the extracted code uses for keys. -/
abbrev Pubkey := Std.Array U8 32#usize

/-- The system program's address (all zero bytes). -/
def systemProgram : Pubkey := Std.Array.repeat 32#usize 0#u8

/-- The address the zkcash program is deployed at. Left abstract: every
    theorem holds for any deployment (localnet, devnet, mainnet). -/
opaque programId : Pubkey

/-- An account's data, as the program sees it once Anchor has decoded it. -/
inductive AccountData where
  /-- No data: a wallet, or an address nothing has been created at. -/
  | empty
  /-- `#[account(zero_copy)] MerkleTreeAccount` (the SOL tree or an SPL tree). -/
  | treeAccount (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
  /-- `#[account] TreeTokenAccount`: the SOL pool. -/
  | treeToken (account : zkcash_core.admin.TreeTokenAccount)
  /-- `#[account] GlobalConfig`. -/
  | globalConfig (config : zkcash_core.admin.GlobalConfig)
  /-- `#[account] NullifierAccount`: marks a note as spent. -/
  | nullifier (bump : U8)
  /-- Data this program does not interpret (owned by another program). -/
  | foreign

structure Account where
  lamports : U64
  owner : Pubkey
  data : AccountData

/-- What an address holds before anything is created there: nothing, owned
    by the system program. -/
def Account.default : Account :=
  { lamports := 0#u64, owner := systemProgram, data := .empty }

/-- The chain: every address holds an account (possibly the default one). -/
abbrev State := Pubkey → Account

/-- `s` with the account at `key` replaced. -/
def State.set (s : State) (key : Pubkey) (a : Account) : State :=
  fun k => if k = key then a else s k

@[simp] theorem State.set_same (s : State) (k : Pubkey) (a : Account) :
    s.set k a k = a := by simp [State.set]

@[simp] theorem State.set_other (s : State) {k k' : Pubkey} (a : Account) (h : k' ≠ k) :
    s.set k a k' = s k' := by simp [State.set, h]

end PrivacyCash.Model
