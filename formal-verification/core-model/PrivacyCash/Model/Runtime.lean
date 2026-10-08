/-
The Solana runtime, as the extracted `transact` sees it: a Lean
implementation of the extracted `zkcash_core::transact::SolRuntime` trait.

The trait only reads and writes lamports (and makes a system transfer, which
also only moves lamports). The model makes that structural: the runtime holds
every account's owner and data read-only (`accounts`) and keeps balances in a
separate map (`lamports`), the only thing its methods update. So whatever the
extracted code does with the runtime, it cannot change an owner or account
data, and no proof about the extracted code is needed for that.

Balances are read and written by address, so when two roles are the same
account (e.g. recipient = fee recipient) a write through one role is seen
through the other, exactly as with the shared `AccountInfo` on-chain.

The runtime's end-of-instruction check (total lamports unchanged) applies to
the whole instruction and is modeled where instructions are executed.
-/
import PrivacyCash.Model.Basic
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Model

/-- Whether an account holds no data. -/
def AccountData.isEmpty : AccountData → Bool
  | .empty => true
  | _ => false

/-- `balances` with the one at `key` replaced. -/
def setBalance (balances : Pubkey → U64) (key : Pubkey) (v : U64) : Pubkey → U64 :=
  fun k => if k = key then v else balances k

/-- A system-program `Transfer` of `amount` lamports from `src` to `dst`
    (`src` signed), on the balances `balances` of the accounts `accounts`.
    The system program requires `src` to hold no data and to be owned by it
    (only an account's owner may debit it), and enough lamports; crediting
    `dst` must not overflow a u64. `none` if it fails. With `src = dst` the
    balance is unchanged, as on-chain. -/
def systemTransferBalances (accounts : State) (balances : Pubkey → U64)
    (src dst : Pubkey) (amount : U64) : Option (Pubkey → U64) :=
  if (accounts src).owner = systemProgram ∧ (accounts src).data.isEmpty ∧
      amount.val ≤ (balances src).val then
    let b₁ := setBalance balances src ⟨(balances src).bv - amount.bv⟩
    if (b₁ dst).val + amount.val ≤ U64.max then
      some (setBalance b₁ dst ⟨(b₁ dst).bv + amount.bv⟩)
    else none
  else none

/-- `s`'s balances. -/
def State.balances (s : State) : Pubkey → U64 := fun k => (s k).lamports

/-- `s` with every balance replaced by `balances` (owners and data kept). -/
def State.withBalances (s : State) (balances : Pubkey → U64) : State :=
  fun k => { s k with lamports := balances k }

/-- A system-program transfer on the chain. -/
def State.systemTransfer (s : State) (src dst : Pubkey) (amount : U64) : Option State :=
  (systemTransferBalances s s.balances src dst amount).map s.withBalances

/-- What `transact`'s runtime calls can see and change. -/
structure SolEnv where
  /-- Every account's owner and data, read-only for the runtime (its
      `lamports` field is not used: balances live in `balances`). -/
  accounts : State
  /-- Every account's balance; the only thing the runtime's methods change. -/
  balances : Pubkey → U64
  /-- `ctx.accounts.signer`. -/
  signer : Pubkey
  /-- `ctx.accounts.tree_token_account` (the SOL pool). -/
  treeToken : Pubkey
  /-- `ctx.accounts.recipient`. -/
  recipient : Pubkey
  /-- `ctx.accounts.fee_recipient_account`. -/
  feeRecipient : Pubkey
  /-- `Rent::get()?.minimum_balance(tree_token_account.data_len())`, or `none`
      if reading the `Rent` sysvar fails. -/
  rentExemptMinimum : Option U64

namespace SolEnv

/-- `**account.try_borrow_mut_lamports()? = v`. -/
def setLamports (e : SolEnv) (key : Pubkey) (v : U64) : SolEnv :=
  { e with balances := setBalance e.balances key v }

/-- A system-program transfer between two of the accounts. -/
def systemTransfer (e : SolEnv) (src dst : Pubkey) (amount : U64) : Option SolEnv :=
  (systemTransferBalances e.accounts e.balances src dst amount).map
    fun b => { e with balances := b }

end SolEnv

/-- The extracted `SolRuntime` trait, implemented over the chain.
    (The outer `Result` is "did the Rust code panic"; these calls never do.
    The inner `core.result.Result _ Unit` is the trait's `Result<_, ()>`.) -/
def solRuntime : zkcash_core.transact.SolRuntime SolEnv where
  rent_exempt_minimum e :=
    ok (match e.rentExemptMinimum with
      | some r => (.Ok r, e)
      | none => (.Err (), e))
  transfer_from_signer_to_tree_token e amount :=
    ok (match e.systemTransfer e.signer e.treeToken amount with
      | some e' => (.Ok (), e')
      | none => (.Err (), e))
  tree_token_lamports e := ok (e.balances e.treeToken)
  recipient_lamports e := ok (e.balances e.recipient)
  fee_recipient_lamports e := ok (e.balances e.feeRecipient)
  set_tree_token_lamports e v := ok (.Ok (), e.setLamports e.treeToken v)
  set_recipient_lamports e v := ok (.Ok (), e.setLamports e.recipient v)
  set_fee_recipient_lamports e v := ok (.Ok (), e.setLamports e.feeRecipient v)

/-! ## Facts -/

@[simp] theorem setBalance_same (b : Pubkey → U64) (k : Pubkey) (v : U64) :
    setBalance b k v k = v := by simp [setBalance]

@[simp] theorem setBalance_other (b : Pubkey → U64) {k k' : Pubkey} (v : U64) (h : k' ≠ k) :
    setBalance b k v k' = b k' := by simp [setBalance, h]

/-- Replacing balances keeps every owner. -/
@[simp] theorem State.withBalances_owner (s : State) (b : Pubkey → U64) (k : Pubkey) :
    (s.withBalances b k).owner = (s k).owner := rfl

/-- Replacing balances keeps all account data. -/
@[simp] theorem State.withBalances_data (s : State) (b : Pubkey → U64) (k : Pubkey) :
    (s.withBalances b k).data = (s k).data := rfl

/-- A system transfer keeps every owner and all account data. -/
theorem State.systemTransfer_owner_data {s s' : State} {src dst : Pubkey} {amount : U64}
    (h : s.systemTransfer src dst amount = some s') (k : Pubkey) :
    (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := by
  unfold State.systemTransfer at h
  cases hb : systemTransferBalances s s.balances src dst amount with
  | none => simp [hb] at h
  | some b => simp only [hb, Option.map_some, Option.some.injEq] at h; subst h; simp

end PrivacyCash.Model
