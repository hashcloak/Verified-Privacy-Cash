/-!
# A simplified model of Solana, for zkcash's `transact`

Hand-written and standalone: core Lean only, no imports, not generated, and not yet connected
to the extracted model in `code_model/`. Each section is one step of the walkthrough:

1. Accounts      — where all state lives
2. Ownership     — the validator's rules about who may change an account
3. Instructions  — how a program changes accounts: signers, writable accounts, the
                   validator's setters, and the System Program's `transfer`
4. PDAs          — addresses a program computes from seeds
5. Anchor        — the account checks that run before `transact`'s own code
6. `transact`    — putting it together, and the first theorem: no double spending

Simplifications, all deliberate:
* Lamports are `Nat`. u64 overflow is not modelled; the real code's `checked_*` errors can
  only make it fail more often, which no safety theorem below cares about.
* Account data is typed (`Data`), not bytes, so Anchor's discriminator and borsh are skipped.
* The pure checks inside `transact` (known root, ext-data hash, public amount, fee rule,
  Groth16) are one opaque yes/no answer, `checksPass`. In the real model they are the
  extracted Rust, three of which `proofs/Transact/` already characterises.
* Only `transact` is modelled. Events, logs and compute limits are left out.
* The validator's rent check after each transaction is left out (Agave `verify_changes`,
  `transition_allowed` in `svm/src/rent_calculator.rs`): an account that started at 0 lamports,
  or at or above its rent-exempt minimum, must end at 0 or at or above that minimum, or the
  transaction fails with `InsufficientFundsForRent`. It moves no lamports, so `balanced` is
  unaffected, but it can make a real `transact` fail where the model succeeds: for example a
  withdrawal below the rent minimum to an address that holds nothing yet. Liveness only.
* PDA bumps are left out: `pda` is `find_program_address`, which picks the canonical bump.
  Where lib.rs checks a bump stored in the account instead, that bump is the canonical one:
  each is written once at init from `ctx.bumps` (lib.rs:81, 90, 98, 173) and never changed.
  An instruction that took a bump from its caller or rewrote one would break this.
-/

set_option autoImplicit false

namespace Solana

/-! ## Step 1: Accounts -/

/-- Raw bytes. -/
abbrev Bytes := List UInt8

/-- An address. On chain it is 32 bytes; here any byte list, since only equality matters. -/
structure Pubkey where
  bytes : Bytes
  deriving DecidableEq, Inhabited

/-- The System Program's address: 32 zero bytes. It owns every ordinary wallet, and every
    address nobody has created an account at. -/
def SYSTEM_PROGRAM : Pubkey := ⟨List.replicate 32 0⟩

/-- The part of zkcash's Merkle tree account (`MerkleTreeAccount`, lib.rs:1087) the model
    keeps. -/
structure Tree where
  /-- The commitments appended so far. The real account stores subtrees and a root history
      instead. -/
  leaves     : List Bytes
  /-- `max_deposit_amount`. -/
  maxDeposit : Nat
  deriving DecidableEq

/-- zkcash's fee configuration (`GlobalConfig`, lib.rs:1071), without authority and bump. -/
structure Config where
  depositFeeRate    : Nat
  withdrawalFeeRate : Nat
  feeErrorMargin    : Nat
  deriving DecidableEq

/-- What an account holds, typed by zkcash's account kinds. `empty` is what a fresh address
    holds, and also the all-zeros data of an account just created. -/
inductive Data where
  | empty
  | tree (t : Tree)
  | treeToken
  | config (c : Config)
  | nullifier
  deriving DecidableEq

/-- The tree, if this is a tree account's data. -/
def Data.tree? : Data → Option Tree
  | .tree t => some t
  | _ => none

/-- The config, if this is a config account's data. -/
def Data.config? : Data → Option Config
  | .config c => some c
  | _ => none

/-- An account: its balance, the program that owns it, and its data. -/
structure Account where
  lamports : Nat
  owner    : Pubkey
  data     : Data

/-- What every address holds until an account is created there. -/
def Account.empty : Account :=
  { lamports := 0, owner := SYSTEM_PROGRAM, data := .empty }

/-- The whole chain: every address has an account. -/
abbrev Store := Pubkey → Account

/-- Replace the account at one address. -/
def Store.set (σ : Store) (a : Pubkey) (acc : Account) : Store :=
  fun b => if b = a then acc else σ b

@[simp] theorem Store.set_same (σ : Store) (a : Pubkey) (acc : Account) :
    σ.set a acc a = acc := by
  simp [Store.set]

theorem Store.set_other (σ : Store) {a b : Pubkey} (acc : Account) (h : b ≠ a) :
    σ.set a acc b = σ b := by
  simp [Store.set, h]

/-- An account is in use when a program owns it or it holds data. This is what makes
    Anchor's `init` fail (step 5). Lamports alone don't count. -/
def Account.InUse (acc : Account) : Prop :=
  acc.owner ≠ SYSTEM_PROGRAM ∨ acc.data ≠ .empty

instance (acc : Account) : Decidable acc.InUse := by
  unfold Account.InUse; infer_instance

/-- A fresh address is not in use. -/
theorem Account.empty_not_inUse : ¬ Account.empty.InUse := by
  simp [Account.InUse, Account.empty]

/-- An account not in use is owned by the System Program. -/
theorem Account.owner_of_not_inUse {acc : Account} (h : ¬ acc.InUse) :
    acc.owner = SYSTEM_PROGRAM :=
  Classical.byContradiction fun hne => h (.inl hne)

/-! ## Step 2: Ownership -/

/-- What the validator lets the running program `Q` do to one account.
    Each field is one check in Agave's `transaction-context/src/instruction_accounts.rs`. -/
structure AllowedChange (Q : Pubkey) (before after : Account) : Prop where
  /-- `can_data_be_changed` → `ExternalAccountDataModified` -/
  data     : after.data ≠ before.data → before.owner = Q
  /-- `set_lamports` → `ExternalAccountLamportSpend` -/
  lamports : after.lamports < before.lamports → before.owner = Q
  /-- `set_owner` → `ModifiedProgramId`. Its extra condition, that the data is all zeros,
      is left out here: it only makes the rule stricter. -/
  owner    : after.owner ≠ before.owner → before.owner = Q

/-- Leaving an account as it was is always allowed. -/
theorem AllowedChange.refl (Q : Pubkey) (acc : Account) : AllowedChange Q acc acc :=
  ⟨fun h => absurd rfl h, fun h => absurd h (Nat.lt_irrefl _), fun h => absurd rfl h⟩

/-- Sum of the balances of the accounts `accs`. -/
def total (σ : Store) (accs : List Pubkey) : Nat :=
  (accs.map fun a => (σ a).lamports).sum

/-- One run of program `Q` over the accounts `accs`, as the validator accepts it.
    A run that breaks any of this is rejected and changes nothing, so only accepted runs
    ever appear in the chain's history. -/
structure RunAccepted (Q : Pubkey) (accs : List Pubkey) (σ σ' : Store) : Prop where
  /-- The validator merges an account passed twice into one entry. -/
  nodup     : accs.Nodup
  /-- A program only touches the accounts passed to it (step 3). -/
  untouched : ∀ a, a ∉ accs → σ' a = σ a
  /-- The three ownership rules, for every account. -/
  rules     : ∀ a, AllowedChange Q (σ a) (σ' a)
  /-- `push`/`pop` → `UnbalancedInstruction`: while programs run, lamports move but none
      appear or disappear. Fees don't contradict this: they are taken before any instruction
      runs (`FeeCharged`), outside this check. -/
  balanced  : total σ' accs = total σ accs

/-- Charging a transaction fee, before any instruction runs. The payer must be owned by the
    System Program (`validate_fee_payer` → `InvalidAccountForFee`). The fee is burned or paid
    to the validator, so the total goes down: there is no `balanced` here. -/
def FeeCharged (σ σ' : Store) : Prop :=
  ∃ payer fee, (σ payer).owner = SYSTEM_PROGRAM ∧ fee ≤ (σ payer).lamports ∧
    σ' = σ.set payer { σ payer with lamports := (σ payer).lamports - fee }

/-- What anything other than zkcash can do to zkcash's accounts: add lamports, nothing else. -/
def ZkcashUntouched (P : Pubkey) (σ σ' : Store) : Prop :=
  ∀ a, (σ a).owner = P →
    (σ' a).owner = P ∧ (σ' a).data = (σ a).data ∧ (σ a).lamports ≤ (σ' a).lamports

/-- A run of any program `Q` other than zkcash leaves zkcash's accounts alone.
    Proved from the rules, not assumed. -/
theorem zkcashUntouched_of_rules {P Q : Pubkey} {σ σ' : Store} (hQ : Q ≠ P)
    (h : ∀ a, AllowedChange Q (σ a) (σ' a)) : ZkcashUntouched P σ σ' := by
  intro a ha
  have hne : (σ a).owner ≠ Q := fun h' => hQ (h'.symm.trans ha)
  refine ⟨?_, ?_, ?_⟩
  · exact Classical.byContradiction fun hc => hne ((h a).owner fun e => hc (e.trans ha))
  · exact Classical.byContradiction fun hc => hne ((h a).data hc)
  · exact Nat.not_lt.mp fun hlt => hne ((h a).lamports hlt)

/-- Charging a fee leaves zkcash's accounts alone: the payer is a System Program account. -/
theorem zkcashUntouched_of_fee {P : Pubkey} {σ σ' : Store} (hP : P ≠ SYSTEM_PROGRAM)
    (h : FeeCharged σ σ') : ZkcashUntouched P σ σ' := by
  obtain ⟨payer, fee, hsys, _, rfl⟩ := h
  intro a ha
  by_cases hap : a = payer
  · subst hap
    exact absurd (ha.symm.trans hsys) hP
  · simp [Store.set_other _ _ hap, ha]

/-- One step of the chain, split by which program is running.

    * `ours`: zkcash runs. `Run` is its code plus Anchor's checks (step 6). Every write it
      makes goes through the validator's setters (step 3), so the ownership rules hold by
      construction, and the lamport total is checked at its end.
    * `other`: any other program runs. We know nothing about its code, only the rules.
    * `fee`: the validator charges a transaction fee.

    TRUSTED, and not statable in Lean because the real chain is not in Lean: every change the
    real chain makes is a sequence of these steps. -/
inductive Step (P : Pubkey) (Run : Store → Store → Prop) : Store → Store → Prop
  | ours  {σ σ' : Store} : Run σ σ' → Step P Run σ σ'
  | other {Q : Pubkey} {accs : List Pubkey} {σ σ' : Store} :
      Q ≠ P → RunAccepted Q accs σ σ' → Step P Run σ σ'
  | fee   {σ σ' : Store} : FeeCharged σ σ' → Step P Run σ σ'

/-- Zero or more steps. -/
inductive Reachable (P : Pubkey) (Run : Store → Store → Prop) : Store → Store → Prop
  | refl (σ : Store) : Reachable P Run σ σ
  | step {σ σ' σ'' : Store} : Step P Run σ σ' → Reachable P Run σ' σ'' → Reachable P Run σ σ''

/-- In every step, either zkcash ran or zkcash's accounts were left alone. -/
theorem Step.ours_or_untouched {P : Pubkey} {Run : Store → Store → Prop} {σ σ' : Store}
    (hP : P ≠ SYSTEM_PROGRAM) : Step P Run σ σ' → Run σ σ' ∨ ZkcashUntouched P σ σ'
  | .ours hrun => .inl hrun
  | .other hQ hacc => .inr (zkcashUntouched_of_rules hQ hacc.rules)
  | .fee hfee => .inr (zkcashUntouched_of_fee hP hfee)

/-! ## Step 3: Instructions -/

/-- How an instruction lists one account (`AccountMeta` in `solana-instruction`). -/
structure AccountMeta where
  key        : Pubkey
  isSigner   : Bool
  isWritable : Bool

/-- A call to a program: which program, which accounts, and its arguments. -/
structure Instruction where
  program  : Pubkey
  accounts : List AccountMeta
  data     : Bytes

/-- What a program run may use. -/
structure Ctx where
  /-- The program whose code is running. -/
  program  : Pubkey
  /-- The accounts whose signature this run carries. -/
  signers  : List Pubkey
  /-- The accounts this run may change. -/
  writable : List Pubkey
  /-- `Rent::minimum_balance`: the lamports an account with `n` data bytes must hold. -/
  rent     : Nat → Nat

/-- The context of a top-level instruction. The validator rejects the transaction before
    running anything if an account marked `isSigner` did not sign, so every account listed
    here really signed. -/
def Ctx.ofInstruction (ix : Instruction) (rent : Nat → Nat) : Ctx where
  program  := ix.program
  signers  := ix.accounts.filterMap fun m => if m.isSigner then some m.key else none
  writable := ix.accounts.filterMap fun m => if m.isWritable then some m.key else none
  rent     := rent

/-- Why a run failed. Any failure undoes the whole transaction. -/
inductive Error where
  /-- validator: lowered the balance of an account the running program doesn't own -/
  | externalAccountLamportSpend
  /-- validator: changed the data of an account the running program doesn't own -/
  | externalAccountDataModified
  /-- validator: an owner change that isn't allowed -/
  | modifiedProgramId
  /-- validator: changed an account the instruction didn't mark writable -/
  | readonlyModified
  /-- validator: the lamport total changed -/
  | unbalancedInstruction
  /-- System Program: the account paying didn't sign -/
  | missingSignature
  /-- System Program: the account paying holds data, so it isn't an ordinary wallet -/
  | notSystemAccount
  /-- System Program: not enough lamports -/
  | insufficientFunds
  /-- System Program: creating an account at an address already in use -/
  | accountInUse
  /-- one of Anchor's account checks failed -/
  | anchor (check : String)
  /-- one of zkcash's own `require!`s failed -/
  | program (check : String)

/-- Fail with `e` unless `c` holds. -/
def require (c : Prop) [Decidable c] (e : Error) : Except Error Unit :=
  if c then .ok () else .error e

/-- The validator's `set_lamports` (`instruction_accounts.rs:120`). -/
def setLamports (ctx : Ctx) (a : Pubkey) (n : Nat) (σ : Store) : Except Error Store :=
  if n = (σ a).lamports then .ok σ
  else if n < (σ a).lamports ∧ (σ a).owner ≠ ctx.program then .error .externalAccountLamportSpend
  else if a ∉ ctx.writable then .error .readonlyModified
  else .ok (σ.set a { σ a with lamports := n })

/-- The validator's `can_data_be_changed` (`instruction_accounts.rs:338`), then the write. -/
def setData (ctx : Ctx) (a : Pubkey) (d : Data) (σ : Store) : Except Error Store :=
  if a ∉ ctx.writable then .error .readonlyModified
  else if (σ a).owner ≠ ctx.program then .error .externalAccountDataModified
  else .ok (σ.set a { σ a with data := d })

/-- The validator's `set_owner` (`instruction_accounts.rs:91`): only the owner, only a writable
    account, and only while its data is all zeros. -/
def setOwner (ctx : Ctx) (a o : Pubkey) (σ : Store) : Except Error Store :=
  if (σ a).owner ≠ ctx.program ∨ a ∉ ctx.writable ∨ (σ a).data ≠ .empty then
    .error .modifiedProgramId
  else .ok (σ.set a { σ a with owner := o })

/-- The System Program's `transfer`. It runs *as the System Program*, so the setters check its
    writes against the System Program's ownership: it can take lamports only from accounts it
    owns. Its own extra rules: `src` signed, and holds no data. -/
def systemTransfer (ctx : Ctx) (src dst : Pubkey) (amount : Nat) (σ : Store) :
    Except Error Store := do
  let sys := { ctx with program := SYSTEM_PROGRAM }
  require (src ∈ ctx.signers) .missingSignature
  require ((σ src).data = .empty) .notSystemAccount
  require (amount ≤ (σ src).lamports) .insufficientFunds
  let σ ← setLamports sys src ((σ src).lamports - amount) σ
  setLamports sys dst ((σ dst).lamports + amount) σ

/-! ### Reasoning about `Except`

Three facts that let `simp` take apart a run that succeeded. -/

theorem bind_ok {α β : Type} {m : Except Error α} {f : α → Except Error β} {b : β} :
    (m >>= f) = .ok b ↔ ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m <;> simp [bind, Except.bind]

theorem require_ok {c : Prop} [Decidable c] {e : Error} {u : Unit} :
    require c e = .ok u ↔ c := by
  unfold require; by_cases hc : c <;> simp [hc]

theorem pure_ok {α : Type} {a b : α} : (pure a : Except Error α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem unit_exists {p : Unit → Prop} : (∃ u, p u) ↔ p () :=
  ⟨fun ⟨(), h⟩ => h, fun h => ⟨(), h⟩⟩

/-! ### What the setters guarantee -/

section Setters
variable {ctx : Ctx} {a o : Pubkey} {n : Nat} {d : Data} {σ σ' : Store}

/-- `setLamports` obeys step 2's rules for the running program. -/
theorem setLamports_allowed (h : setLamports ctx a n σ = .ok σ') (b : Pubkey) :
    AllowedChange ctx.program (σ b) (σ' b) := by
  unfold setLamports at h
  split at h
  · cases h; exact .refl _ _
  · split at h
    · cases h
    · rename_i hspend
      split at h
      · cases h
      · cases h
        by_cases hb : b = a
        · subst hb
          simp only [Store.set_same]
          refine ⟨fun hd => absurd rfl hd, fun hl => ?_, fun ho => absurd rfl ho⟩
          exact Classical.byContradiction fun hne => hspend ⟨hl, hne⟩
        · rw [Store.set_other _ _ hb]; exact .refl _ _

/-- `setData` obeys step 2's rules for the running program. -/
theorem setData_allowed (h : setData ctx a d σ = .ok σ') (b : Pubkey) :
    AllowedChange ctx.program (σ b) (σ' b) := by
  unfold setData at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i howner
      cases h
      by_cases hb : b = a
      · subst hb
        have hown : (σ b).owner = ctx.program := Classical.byContradiction howner
        exact ⟨fun _ => hown, fun _ => hown, fun _ => hown⟩
      · rw [Store.set_other _ _ hb]; exact .refl _ _

/-- `setOwner` obeys step 2's rules for the running program. -/
theorem setOwner_allowed (h : setOwner ctx a o σ = .ok σ') (b : Pubkey) :
    AllowedChange ctx.program (σ b) (σ' b) := by
  unfold setOwner at h
  split at h
  · cases h
  · rename_i hok
    cases h
    by_cases hb : b = a
    · subst hb
      have hown : (σ b).owner = ctx.program :=
        Classical.byContradiction fun hne => hok (.inl hne)
      exact ⟨fun _ => hown, fun _ => hown, fun _ => hown⟩
    · rw [Store.set_other _ _ hb]; exact .refl _ _

theorem setLamports_owner (h : setLamports ctx a n σ = .ok σ') (b : Pubkey) :
    (σ' b).owner = (σ b).owner := by
  unfold setLamports at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; by_cases hb : b = a <;> simp [Store.set, hb]

theorem setData_owner (h : setData ctx a d σ = .ok σ') (b : Pubkey) :
    (σ' b).owner = (σ b).owner := by
  unfold setData at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; by_cases hb : b = a <;> simp [Store.set, hb]

/-- `setOwner` changes the owner of `a` only. -/
theorem setOwner_owner (h : setOwner ctx a o σ = .ok σ') :
    (σ' a).owner = o ∧ ∀ b, b ≠ a → (σ' b).owner = (σ b).owner := by
  unfold setOwner at h
  split at h
  · cases h
  · cases h
    exact ⟨by simp, fun b hb => by rw [Store.set_other _ _ hb]⟩

end Setters

section SystemTransfer
variable {ctx : Ctx} {src dst : Pubkey} {amount : Nat} {σ σ' : Store}

/-- The System Program moves lamports out of an account only if that account signed. -/
theorem systemTransfer_needs_signature (h : systemTransfer ctx src dst amount σ = .ok σ') :
    src ∈ ctx.signers := by
  simp only [systemTransfer, bind_ok, require_ok, unit_exists] at h
  exact h.1

/-- A transfer never changes an owner. -/
theorem systemTransfer_owner (h : systemTransfer ctx src dst amount σ = .ok σ') (b : Pubkey) :
    (σ' b).owner = (σ b).owner := by
  simp only [systemTransfer, bind_ok, require_ok, unit_exists] at h
  obtain ⟨_, _, _, σ₁, h₁, h₂⟩ := h
  rw [setLamports_owner h₂, setLamports_owner h₁]

end SystemTransfer

/-! ## Step 4: PDAs -/

/-- `Pubkey::find_program_address(seeds, program)`: an address computed from a program and some
    seeds. SHA-256 underneath, so it stays abstract, like the hash functions elsewhere in the
    model. A PDA is not a point on the signing curve, so no private key exists for it. -/
opaque pda (program : Pubkey) (seeds : List Bytes) : Pubkey

/-- What we assume about `pda`, stated on the *concatenated* seeds: Solana hashes the seeds
    back to back, so `["ab", "c"]` and `["a", "bc"]` give the same address. It follows from
    SHA-256's collision resistance. Only liveness theorems need it; the safety theorems in
    step 6 don't. -/
class PdaInjective : Prop where
  inj : ∀ {p p' : Pubkey} {s s' : List Bytes},
    pda p s = pda p' s' → p = p' ∧ s.flatten = s'.flatten

/-- A program signing for one of its own PDAs (`invoke_signed`). Only the running program's
    PDAs can be added this way, and no transaction signature can stand in for one, since no
    private key exists. So only zkcash can create an account at a zkcash PDA. -/
def Ctx.signedWith (ctx : Ctx) (seeds : List Bytes) : Ctx :=
  { ctx with signers := pda ctx.program seeds :: ctx.signers }

/-- `b"merkle_tree"` -/
def seedMerkleTree : Bytes := [109, 101, 114, 107, 108, 101, 95, 116, 114, 101, 101]
/-- `b"tree_token"` -/
def seedTreeToken : Bytes := [116, 114, 101, 101, 95, 116, 111, 107, 101, 110]
/-- `b"global_config"` -/
def seedGlobalConfig : Bytes := [103, 108, 111, 98, 97, 108, 95, 99, 111, 110, 102, 105, 103]
/-- `b"nullifier0"` -/
def seedNullifier0 : Bytes := [110, 117, 108, 108, 105, 102, 105, 101, 114, 48]
/-- `b"nullifier1"` -/
def seedNullifier1 : Bytes := [110, 117, 108, 108, 105, 102, 105, 101, 114, 49]

-- The byte lists above are the strings in lib.rs. Checked when this file is built.
#guard seedMerkleTree = "merkle_tree".toUTF8.toList
#guard seedTreeToken = "tree_token".toUTF8.toList
#guard seedGlobalConfig = "global_config".toUTF8.toList
#guard seedNullifier0 = "nullifier0".toUTF8.toList
#guard seedNullifier1 = "nullifier1".toUTF8.toList

/-- zkcash's PDAs, as the `seeds = [...]` constraints in lib.rs define them. -/
def treeAddr (P : Pubkey) : Pubkey := pda P [seedMerkleTree]
def treeTokenAddr (P : Pubkey) : Pubkey := pda P [seedTreeToken]
def configAddr (P : Pubkey) : Pubkey := pda P [seedGlobalConfig]
def nullifier0Addr (P : Pubkey) (k : Bytes) : Pubkey := pda P [seedNullifier0, k]
def nullifier1Addr (P : Pubkey) (k : Bytes) : Pubkey := pda P [seedNullifier1, k]

/-- Nullifier `k` is spent once zkcash owns an account at either of its two addresses.
    This is the model's version of the spec's `nullifiers : Finset F`. It looks at the owner,
    not just "does an account exist", because the cross-checks in step 5 do. -/
def Spent (P : Pubkey) (σ : Store) (k : Bytes) : Prop :=
  (σ (nullifier0Addr P k)).owner = P ∨ (σ (nullifier1Addr P k)).owner = P

/-- A nullifier address never coincides with the tree account's address. The lengths differ:
    10 + 32 bytes against 11. -/
theorem nullifier0Addr_ne_treeAddr [PdaInjective] {P : Pubkey} {k : Bytes}
    (hk : k.length = 32) : nullifier0Addr P k ≠ treeAddr P := by
  intro h
  have hlen := congrArg List.length (PdaInjective.inj h).2
  simp [seedNullifier0, seedMerkleTree, hk] at hlen

/-! ## Step 5: Anchor -/

/-- The accounts a `transact` instruction passes, one per field of `Transact` (lib.rs:780). -/
structure TransactAccounts where
  tree          : Pubkey
  nullifier0    : Pubkey
  nullifier1    : Pubkey
  nullifier2    : Pubkey
  nullifier3    : Pubkey
  treeToken     : Pubkey
  config        : Pubkey
  recipient     : Pubkey
  feeRecipient  : Pubkey
  signer        : Pubkey
  systemProgram : Pubkey

/-- All of them, in field order. -/
def TransactAccounts.keys (acc : TransactAccounts) : List Pubkey :=
  [acc.tree, acc.nullifier0, acc.nullifier1, acc.nullifier2, acc.nullifier3, acc.treeToken,
   acc.config, acc.recipient, acc.feeRecipient, acc.signer, acc.systemProgram]

/-- `transact`'s arguments (lib.rs:217), cut down to what the model reads. -/
structure TransactArgs where
  /-- `proof.input_nullifiers` -/
  k0        : Bytes
  k1        : Bytes
  /-- `proof.output_commitments` -/
  out0      : Bytes
  out1      : Bytes
  /-- `ext_data_minified.ext_amount`: positive for a deposit, negative for a withdrawal. -/
  extAmount : Int
  /-- `ext_data_minified.fee` -/
  fee       : Nat
  /-- Everything else: the rest of `Proof` and the encrypted outputs. Only `checksPass`
      reads it. -/
  proof     : Bytes

/-- Data size of a nullifier account (lib.rs:795): 8-byte discriminator plus the bump. -/
def nullifierSpace : Nat := 8 + 1

/-- Anchor's `init` with `seeds` and `payer` (lib.rs:792-799, anchor-syn
    `generate_create_account`). The System Program funds the account up to the rent minimum
    and hands it to zkcash; then zkcash, now the owner, writes its data. Fails if the address
    is already in use. -/
def anchorInit (ctx : Ctx) (payer addr : Pubkey) (seeds : List Bytes) (space : Nat)
    (data : Data) (σ : Store) : Except Error Store := do
  require (addr = pda ctx.program seeds) (.anchor "ConstraintSeeds")
  require (¬ (σ addr).InUse) .accountInUse
  -- The System Program runs, and the new account signs through `invoke_signed`.
  let sys := { ctx.signedWith seeds with program := SYSTEM_PROGRAM }
  let σ ← systemTransfer sys payer addr (ctx.rent space - (σ addr).lamports) σ
  let σ ← setOwner sys addr ctx.program σ
  setData ctx addr data σ

/-- Everything Anchor does before `transact`'s own code runs, in the order anchor-syn 0.31.1
    generates it (`codegen/accounts/try_accounts.rs`): first the type check of every field
    without `init`, then every `init`, then the remaining constraints. -/
def anchorTransact (ctx : Ctx) (acc : TransactAccounts) (args : TransactArgs) (σ : Store) :
    Except Error Store := do
  let P := ctx.program
  -- Phase 1: the type of each field without `init`, in field order.
  require ((σ acc.tree).owner = P ∧ (σ acc.tree).data.tree?.isSome) (.anchor "tree_account")
  require ((σ acc.nullifier2).owner = SYSTEM_PROGRAM) (.anchor "nullifier2")  -- SystemAccount
  require ((σ acc.nullifier3).owner = SYSTEM_PROGRAM) (.anchor "nullifier3")  -- SystemAccount
  require ((σ acc.treeToken).owner = P ∧ (σ acc.treeToken).data = .treeToken)
    (.anchor "tree_token_account")
  require ((σ acc.config).owner = P ∧ (σ acc.config).data.config?.isSome)
    (.anchor "global_config")
  require (acc.signer ∈ ctx.signers) (.anchor "signer")                        -- Signer
  require (acc.systemProgram = SYSTEM_PROGRAM) (.anchor "system_program")      -- Program<System>
  -- Phase 2: the `init` fields, in field order.
  let σ ← anchorInit ctx acc.signer acc.nullifier0 [seedNullifier0, args.k0] nullifierSpace
    .nullifier σ
  let σ ← anchorInit ctx acc.signer acc.nullifier1 [seedNullifier1, args.k1] nullifierSpace
    .nullifier σ
  -- Phase 3: the other fields' constraints. Grouped by kind rather than by field, which only
  -- changes which error is reported, not whether one is.
  require (acc.tree = treeAddr P) (.anchor "tree_account seeds")
  require (acc.nullifier2 = nullifier0Addr P args.k1) (.anchor "nullifier2 seeds")
  require (acc.nullifier3 = nullifier1Addr P args.k0) (.anchor "nullifier3 seeds")
  require (acc.treeToken = treeTokenAddr P) (.anchor "tree_token_account seeds")
  require (acc.config = configAddr P) (.anchor "global_config seeds")
  require (∀ a ∈ [acc.tree, acc.treeToken, acc.recipient, acc.feeRecipient, acc.signer],
    a ∈ ctx.writable) (.anchor "mut")
  pure σ

section Anchor
variable {ctx : Ctx} {payer addr : Pubkey} {seeds : List Bytes} {space : Nat} {data : Data}
  {acc : TransactAccounts} {args : TransactArgs} {σ σ' : Store}

/-- A successful `init`: the address is the PDA, was owned by the System Program, and now
    belongs to zkcash. No other account changes owner. -/
theorem anchorInit_spec (h : anchorInit ctx payer addr seeds space data σ = .ok σ') :
    addr = pda ctx.program seeds ∧ (σ addr).owner = SYSTEM_PROGRAM ∧
      (σ' addr).owner = ctx.program ∧ ∀ b, b ≠ addr → (σ' b).owner = (σ b).owner := by
  simp only [anchorInit, bind_ok, require_ok, unit_exists] at h
  obtain ⟨haddr, hfree, σ₁, h₁, σ₂, h₂, h₃⟩ := h
  have ⟨howner₂, hframe₂⟩ := setOwner_owner h₂
  refine ⟨haddr, Account.owner_of_not_inUse hfree, ?_, fun b hb => ?_⟩
  · rw [setData_owner h₃, howner₂]
  · rw [setData_owner h₃, hframe₂ b hb, systemTransfer_owner h₁]

/-- What Anchor's checks alone guarantee about the two input nullifiers: neither was spent
    before, both are spent after, and nothing zkcash owned stops being zkcash's. -/
theorem anchorTransact_spec (hP : ctx.program ≠ SYSTEM_PROGRAM)
    (h : anchorTransact ctx acc args σ = .ok σ') :
    ¬ Spent ctx.program σ args.k0 ∧ ¬ Spent ctx.program σ args.k1 ∧
      Spent ctx.program σ' args.k0 ∧ Spent ctx.program σ' args.k1 ∧
      ∀ a, (σ a).owner = ctx.program → (σ' a).owner = ctx.program := by
  -- Take the accounts apart, so each one is a variable `subst` can replace.
  obtain ⟨_, n0, n1, n2, n3, _, _, _, _, _, _⟩ := acc
  simp only [anchorTransact, bind_ok, require_ok, unit_exists, pure_ok] at h
  obtain ⟨_, hn2, hn3, _, _, _, _, σ₁, hi₀, σ₂, hi₁, _, hs2, hs3, _, _, _, rfl⟩ := h
  have ⟨ha₀, hfree₀, hown₀, hframe₀⟩ := anchorInit_spec hi₀
  have ⟨ha₁, hfree₁, hown₁, hframe₁⟩ := anchorInit_spec hi₁
  -- Name the two addresses that were initialised.
  have e₀ : n0 = nullifier0Addr ctx.program args.k0 := ha₀
  have e₁ : n1 = nullifier1Addr ctx.program args.k1 := ha₁
  subst e₀ e₁ hs2 hs3
  -- The second `init` saw its address still owned by the System Program, so it is not the
  -- address the first `init` had just given to zkcash.
  have hne : nullifier1Addr ctx.program args.k1 ≠ nullifier0Addr ctx.program args.k0 := by
    intro heq
    rw [heq, hown₀] at hfree₁
    exact hP hfree₁
  have hfree₁' : (σ (nullifier1Addr ctx.program args.k1)).owner = SYSTEM_PROGRAM := by
    rw [← hframe₀ _ hne]; exact hfree₁
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- k0 unspent: its nullifier0 address was free for `init`, its nullifier1 address passed
    -- the `nullifier3` SystemAccount check.
    rintro (h | h)
    · exact hP (h.symm.trans hfree₀)
    · exact hP (h.symm.trans hn3)
  · -- k1 unspent: the `nullifier2` check, and the second `init`.
    rintro (h | h)
    · exact hP (h.symm.trans hn2)
    · exact hP (h.symm.trans hfree₁')
  · exact .inl (by rw [hframe₁ _ (Ne.symm hne)]; exact hown₀)
  · exact .inr hown₁
  · intro a ha
    have h₀ : a ≠ nullifier0Addr ctx.program args.k0 := by
      intro heq; subst heq; exact hP (ha.symm.trans hfree₀)
    have h₁ : a ≠ nullifier1Addr ctx.program args.k1 := by
      intro heq; subst heq; exact hP (ha.symm.trans hfree₁')
    rw [hframe₁ _ h₁, hframe₀ _ h₀]; exact ha

end Anchor

/-! ## Step 6: `transact` -/

/-- The pure checks inside `transact` (lib.rs:225-264): the root is known, the ext-data hash
    matches, the public amount is right, the fee rule holds, and the Groth16 proof verifies.
    In the real model these are the extracted Rust; here, one yes/no answer about which the
    model assumes nothing. -/
opaque checksPass : Tree → Config → TransactArgs → Bool

/-- Data size of the tree token account: discriminator, authority, bump. -/
def treeTokenSpace : Nat := 8 + 32 + 1

/-- The deposit or the withdrawal (lib.rs:270-320). A deposit takes lamports from the signer's
    wallet, which the System Program owns, so zkcash has to ask it. A withdrawal takes them
    from the tree token account, which zkcash owns, so zkcash writes both balances itself.
    Both balances are read before either is written, as in lib.rs:310-319. -/
def moveFunds (ctx : Ctx) (acc : TransactAccounts) (args : TransactArgs) (t : Tree)
    (σ : Store) : Except Error Store :=
  if args.extAmount > 0 then do
    require (args.extAmount.toNat ≤ t.maxDeposit) (.program "DepositLimitExceeded")
    systemTransfer ctx acc.signer acc.treeToken args.extAmount.toNat σ
  else if args.extAmount < 0 then do
    let amt := args.extAmount.natAbs
    require (amt + args.fee + ctx.rent treeTokenSpace ≤ (σ acc.treeToken).lamports)
      (.program "InsufficientFundsForWithdrawal")
    let treeBalance := (σ acc.treeToken).lamports
    let recipientBalance := (σ acc.recipient).lamports
    let σ ← setLamports ctx acc.treeToken (treeBalance - amt) σ
    setLamports ctx acc.recipient (recipientBalance + amt) σ
  else pure σ

/-- The fee payment (lib.rs:322-346). -/
def payFee (ctx : Ctx) (acc : TransactAccounts) (args : TransactArgs) (σ : Store) :
    Except Error Store :=
  if args.fee > 0 then do
    require (args.extAmount < 0 ∨ args.fee + ctx.rent treeTokenSpace ≤ (σ acc.treeToken).lamports)
      (.program "InsufficientFundsForFee")
    let treeBalance := (σ acc.treeToken).lamports
    let feeBalance := (σ acc.feeRecipient).lamports
    let σ ← setLamports ctx acc.treeToken (treeBalance - args.fee) σ
    setLamports ctx acc.feeRecipient (feeBalance + args.fee) σ
  else pure σ

/-- `transact`'s own code (lib.rs:217-368), run after Anchor's checks. -/
def transactHandler (ctx : Ctx) (acc : TransactAccounts) (args : TransactArgs) (σ : Store) :
    Except Error Store :=
  match (σ acc.tree).data, (σ acc.config).data with
  | .tree t, .config c => do
    require (checksPass t c args) (.program "checks")
    let σ ← moveFunds ctx acc args t σ
    let σ ← payFee ctx acc args σ
    require (t.leaves.length + 2 ≤ 2 ^ 26) (.program "MerkleTreeFull")
    setData ctx acc.tree (.tree { t with leaves := t.leaves ++ [args.out0, args.out1] }) σ
  | _, _ => .error (.program "account data")

/-- One `transact` instruction: Anchor's checks, `transact`'s code, then the validator's
    lamport-total check over the instruction's accounts, each counted once. -/
def execTransact (ctx : Ctx) (acc : TransactAccounts) (args : TransactArgs) (σ : Store) :
    Except Error Store := do
  let σ' ← anchorTransact ctx acc args σ
  let σ' ← transactHandler ctx acc args σ'
  let accs := acc.keys.eraseDups
  require (total σ' accs = total σ accs) .unbalancedInstruction
  pure σ'

/-- "zkcash ran `transact`", as a step of the chain's history. -/
def TransactRun (P : Pubkey) (σ σ' : Store) : Prop :=
  ∃ ctx acc args, ctx.program = P ∧ execTransact ctx acc args σ = .ok σ'

section Transact
variable {ctx : Ctx} {acc : TransactAccounts} {args : TransactArgs} {t : Tree} {σ σ' : Store}

theorem moveFunds_owner (h : moveFunds ctx acc args t σ = .ok σ') (b : Pubkey) :
    (σ' b).owner = (σ b).owner := by
  unfold moveFunds at h
  split at h
  · simp only [bind_ok, require_ok, unit_exists] at h
    exact systemTransfer_owner h.2 b
  · split at h
    · simp only [bind_ok, require_ok, unit_exists] at h
      obtain ⟨_, σ₁, h₁, h₂⟩ := h
      rw [setLamports_owner h₂, setLamports_owner h₁]
    · cases h; rfl

theorem payFee_owner (h : payFee ctx acc args σ = .ok σ') (b : Pubkey) :
    (σ' b).owner = (σ b).owner := by
  unfold payFee at h
  split at h
  · simp only [bind_ok, require_ok, unit_exists] at h
    obtain ⟨_, σ₁, h₁, h₂⟩ := h
    rw [setLamports_owner h₂, setLamports_owner h₁]
  · cases h; rfl

/-- `transact`'s own code never changes an owner. -/
theorem transactHandler_owner (h : transactHandler ctx acc args σ = .ok σ') (b : Pubkey) :
    (σ' b).owner = (σ b).owner := by
  unfold transactHandler at h
  split at h
  · simp only [bind_ok, require_ok, unit_exists] at h
    obtain ⟨_, σ₁, h₁, σ₂, h₂, _, h₃⟩ := h
    rw [setData_owner h₃, payFee_owner h₂, moveFunds_owner h₁]
  · cases h

theorem execTransact_parts (h : execTransact ctx acc args σ = .ok σ') :
    ∃ σ₁, anchorTransact ctx acc args σ = .ok σ₁ ∧ transactHandler ctx acc args σ₁ = .ok σ' := by
  simp only [execTransact, bind_ok, require_ok, unit_exists, pure_ok] at h
  obtain ⟨σ₁, h₁, σ₂, h₂, _, rfl⟩ := h
  exact ⟨σ₁, h₁, h₂⟩

/-- Before a successful `transact`, neither input nullifier was spent; after it, both are; and
    nothing zkcash owned stops being zkcash's. -/
theorem execTransact_spec (hP : ctx.program ≠ SYSTEM_PROGRAM)
    (h : execTransact ctx acc args σ = .ok σ') :
    ¬ Spent ctx.program σ args.k0 ∧ ¬ Spent ctx.program σ args.k1 ∧
      Spent ctx.program σ' args.k0 ∧ Spent ctx.program σ' args.k1 ∧
      ∀ a, (σ a).owner = ctx.program → (σ' a).owner = ctx.program := by
  obtain ⟨σ₁, hanchor, hhandler⟩ := execTransact_parts h
  have ⟨hu₀, hu₁, hs₀, hs₁, hkeep⟩ := anchorTransact_spec hP hanchor
  have hsame := transactHandler_owner hhandler
  refine ⟨hu₀, hu₁, ?_, ?_, fun a ha => by rw [hsame]; exact hkeep a ha⟩
  · unfold Spent at hs₀ ⊢; rw [hsame, hsame]; exact hs₀
  · unfold Spent at hs₁ ⊢; rw [hsame, hsame]; exact hs₁

end Transact

/-! ### No double spending -/

/-- A spent nullifier stays spent, whatever runs: zkcash, another program, or a fee. -/
theorem Step.spent {P : Pubkey} {σ σ' : Store} {k : Bytes} (hP : P ≠ SYSTEM_PROGRAM)
    (hstep : Step P (TransactRun P) σ σ') (hk : Spent P σ k) : Spent P σ' k := by
  have keep : ∀ a, (σ a).owner = P → (σ' a).owner = P := by
    rcases hstep.ours_or_untouched hP with ⟨ctx, acc, args, hctx, h⟩ | hun
    · subst hctx; exact (execTransact_spec hP h).2.2.2.2
    · exact fun a ha => (hun a ha).1
  rcases hk with h | h
  · exact .inl (keep _ h)
  · exact .inr (keep _ h)

/-- ... and so along any history. -/
theorem Reachable.spent {P : Pubkey} {σ σ' : Store} {k : Bytes} (hP : P ≠ SYSTEM_PROGRAM)
    (hreach : Reachable P (TransactRun P) σ σ') (hk : Spent P σ k) : Spent P σ' k := by
  induction hreach with
  | refl => exact hk
  | step hstep _ ih => exact ih (hstep.spent hP hk)

/-- **No double spending.** Once nullifier `k` is spent, no later successful `transact` uses
    it as an input, whatever happened on the chain in between. Nothing is assumed about
    `checksPass`: this comes from the account model and Anchor's checks alone. -/
theorem no_double_spend {P : Pubkey} {σ₀ σ σ' : Store} {k : Bytes} {ctx : Ctx}
    {acc : TransactAccounts} {args : TransactArgs} (hP : P ≠ SYSTEM_PROGRAM)
    (hreach : Reachable P (TransactRun P) σ₀ σ) (hk : Spent P σ₀ k)
    (hctx : ctx.program = P) (h : execTransact ctx acc args σ = .ok σ') :
    args.k0 ≠ k ∧ args.k1 ≠ k := by
  subst hctx
  have hσ := hreach.spent hP hk
  have ⟨hu₀, hu₁, _⟩ := execTransact_spec hP h
  exact ⟨fun e => hu₀ (e ▸ hσ), fun e => hu₁ (e ▸ hσ)⟩

end Solana
