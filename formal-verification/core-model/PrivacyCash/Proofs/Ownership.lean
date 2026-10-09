/-
Lemma L1 of no-double-spend: once this program owns an account, it owns it
forever: through every instruction of the program and everything the rest of
the world can do.
-/
import PrivacyCash.Model.Execution
open Aeneas Aeneas.Std

namespace PrivacyCash.Model

variable {programId : Pubkey}

/-- Every account this program owns in `s`, it still owns in `s'`. -/
def KeepsOwned (programId : Pubkey) (s s' : State) : Prop :=
  ∀ k, (s k).owner = programId → (s' k).owner = programId

theorem KeepsOwned.refl (s : State) : KeepsOwned programId s s := fun _ h => h

theorem KeepsOwned.trans {s₁ s₂ s₃ : State} (h₁ : KeepsOwned programId s₁ s₂) (h₂ : KeepsOwned programId s₂ s₃) :
    KeepsOwned programId s₁ s₃ := fun k hk => h₂ k (h₁ k hk)

/-- Replacing one account keeps ownership if the new account is owned by this
    program whenever the old one was. -/
theorem KeepsOwned.set (s : State) (key : Pubkey) (a : Account)
    (h : (s key).owner = programId → a.owner = programId) : KeepsOwned programId s (s.set key a) := by
  intro k hk
  by_cases hkey : k = key
  · subst hkey; simp [h hk]
  · simp [State.set_other _ _ hkey, hk]

/-- Changing an account's data or lamports (but not its owner) keeps ownership. -/
theorem KeepsOwned.set_same_owner (s : State) (key : Pubkey) (a : Account)
    (h : a.owner = (s key).owner) : KeepsOwned programId s (s.set key a) :=
  KeepsOwned.set s key a (fun hk => h.trans hk)

/-- Rewriting one account's data keeps ownership. -/
theorem KeepsOwned.setData (s : State) (key : Pubkey) (data : AccountData) :
    KeepsOwned programId s (s.set key { s key with data := data }) :=
  KeepsOwned.set_same_owner s key _ rfl

theorem KeepsOwned.withBalances (s : State) (b : Pubkey → U64) : KeepsOwned programId s (s.withBalances b) :=
  fun k hk => by simpa using hk

theorem KeepsOwned.systemTransfer {s s' : State} {src dst : Pubkey} {amount : U64}
    (h : s.systemTransfer src dst amount = some s') : KeepsOwned programId s s' :=
  fun k hk => (State.systemTransfer_owner_data h k).1.trans hk

/-- `init` keeps ownership: funding only moves lamports, and the created
    account becomes owned by this program. -/
theorem KeepsOwned.initAccount {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData}
    (h : s.initAccount programId mb payer key space data = some s') : KeepsOwned programId s s' := by
  unfold State.initAccount at h
  -- `funded` is `s` or a system transfer from `s`; then `key` is set to this program.
  have hfunded : ∀ s₁, (if (s key).lamports.val = 0 then s.systemTransfer payer key (mb space)
      else if payer = key then none
      else if max (mb space).val 1 - (s key).lamports.val = 0 then some s
      else s.systemTransfer payer key ⟨BitVec.ofNat 64 (max (mb space).val 1 - (s key).lamports.val)⟩)
      = some s₁ → KeepsOwned programId s s₁ := by
    intro s₁ hs₁
    split at hs₁
    · exact KeepsOwned.systemTransfer hs₁
    · split at hs₁
      · cases hs₁
      · split at hs₁
        · cases hs₁; exact KeepsOwned.refl s
        · exact KeepsOwned.systemTransfer hs₁
  obtain ⟨s₁, hs₁, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (hfunded s₁ hs₁).trans (KeepsOwned.set s₁ key _ (fun _ => rfl))

/-! ## Each instruction keeps ownership -/

/-- If `x >>= f` succeeded, `x` succeeded with some `a` and `f a` gave the result. -/
theorem Except.bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem checkBalanced_ok {s s₂ s' : State} {keys : List Pubkey}
    (h : checkBalanced s s₂ keys = .ok s') : s' = s₂ := by
  unfold checkBalanced at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

theorem execUpdateDepositLimit_keepsOwned {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : UpdateDepositLimitAccounts} {newLimit : U64}
    (h : execUpdateDepositLimit d s tx a newLimit = .ok s') : KeepsOwned d.programId s s' := by
  unfold execUpdateDepositLimit at h
  split at h
  · split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Except.bind_ok h
      cases h
      exact KeepsOwned.set_same_owner _ _ _ rfl
  · cases h

theorem execUpdateGlobalConfig_keepsOwned {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : UpdateGlobalConfigAccounts} {dep wd margin : Option U16}
    (h : execUpdateGlobalConfig d s tx a dep wd margin = .ok s') : KeepsOwned d.programId s s' := by
  unfold execUpdateGlobalConfig at h
  split at h
  · split at h
    · cases h
    · obtain ⟨⟨r, _⟩, -, h⟩ := Except.bind_ok h
      cases r with
      | Err e => cases h
      | Ok _ => cases h; exact KeepsOwned.set_same_owner _ _ _ rfl
  · cases h

theorem execInitialize_keepsOwned {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : InitializeAccounts} (h : execInitialize d s tx a = .ok s') : KeepsOwned d.programId s s' := by
  unfold execInitialize at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i s₁ hs₁
  -- Anchor's three `init`s keep ownership.
  obtain ⟨s₀₂, h₀₂, h₃⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨s₀₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h₀₂
  have hinit : KeepsOwned d.programId s s₁ :=
    ((KeepsOwned.initAccount h₁).trans (KeepsOwned.initAccount h₂)).trans (KeepsOwned.initAccount h₃)
  -- The handler only rewrites the data of those accounts.
  obtain ⟨r₀, -, h⟩ := Except.bind_ok h
  cases r₀ with
  | Err e => cases h
  | Ok _ =>
    obtain ⟨⟨r, tree, token, config⟩, -, h⟩ := Except.bind_ok h
    cases r with
    | Err e => cases h
    | Ok _ =>
      rw [checkBalanced_ok h]
      exact hinit.trans ((KeepsOwned.setData _ _ _).trans
        ((KeepsOwned.setData _ _ _).trans (KeepsOwned.setData _ _ _)))

theorem execTransact_keepsOwned {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8}
    (h : execTransact d s tx a proof extAmount fee out1 out2 = .ok s') : KeepsOwned d.programId s s' := by
  unfold execTransact at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    rename_i s₁ hs₁
    -- Anchor's two nullifier `init`s keep ownership.
    obtain ⟨s₀₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp hs₁
    have hinit : KeepsOwned d.programId s s₁ := (KeepsOwned.initAccount h₁).trans (KeepsOwned.initAccount h₂)
    -- The handler: the runtime changes only balances (by construction of
    -- `SolEnv`), then the tree's data is written back.
    obtain ⟨⟨r, env', tree'⟩, -, h⟩ := Except.bind_ok h
    cases r with
    | Err e => cases h
    | Ok _ =>
      rw [checkBalanced_ok h]
      exact hinit.trans ((KeepsOwned.withBalances _ _).trans (KeepsOwned.setData _ _ _))
  · cases h

/-! ## L1: ownership is permanent -/

/-- Every instruction of the program keeps ownership. -/
theorem step_keepsOwned {d : Deployment} {s s' : State} {tx : TxEnv} {ix : Instruction}
    (h : step d s tx ix = .ok s') : KeepsOwned d.programId s s' := by
  cases ix with
  | «initialize» a => exact execInitialize_keepsOwned h
  | updateDepositLimit a l => exact execUpdateDepositLimit_keepsOwned h
  | updateGlobalConfig a dep wd margin => exact execUpdateGlobalConfig_keepsOwned h
  | transact a proof e f o₁ o₂ => exact execTransact_keepsOwned h

/-- Nothing the rest of the world does can take an account from this program. -/
theorem EnvStep.keepsOwned {s s' : State} (h : EnvStep programId s s') : KeepsOwned programId s s' :=
  fun _ hk => (h.data_of_owned hk).1

/-- **L1.** Along any run, an account this program owns stays owned by it. -/
theorem Run.keepsOwned {d : Deployment} {s s' : State} {events : List Event}
    (h : Run d s events s') : KeepsOwned d.programId s s' := by
  induction h with
  | nil s => exact KeepsOwned.refl s
  | program hstep _ ih => exact (step_keepsOwned hstep).trans ih
  | env henv _ ih => exact henv.keepsOwned.trans ih

end PrivacyCash.Model
