import Connection.Proofs.Transact
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: every reachable state is `WellFormed`

NOT FOR REVIEW: the statements are restated in `Connection/Statements.lean`. -/

namespace Connection

variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- Anchor `init`, on either funding path: the account at `key` becomes the program's with
    `data`; every other account keeps its owner and data. -/
theorem initAccount_ownerData {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (h : s.initAccount pid mb payer key space data = some s') :
    (s' key).owner = pid ∧ (s' key).data = data ∧
      ∀ k, k ≠ key → (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := by
  unfold State.initAccount at h
  obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp h
  have keep : ∀ k, (s₀ k).owner = (s k).owner ∧ (s₀ k).data = (s k).data := by
    intro k
    by_cases h1 : (s key).lamports.val = 0
    · rw [if_pos h1] at hs₀; exact State.systemTransfer_owner_data hs₀ k
    rw [if_neg h1] at hs₀
    by_cases h2 : payer = key
    · rw [if_pos h2] at hs₀; cases hs₀
    rw [if_neg h2] at hs₀
    dsimp only at hs₀
    split at hs₀
    · cases hs₀; exact ⟨rfl, rfl⟩
    · exact State.systemTransfer_owner_data hs₀ k
  refine ⟨by simp, by simp, fun k hk => ?_⟩
  simp only [State.set, hk, if_false]; exact keep k

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
theorem ugc_rates (c c' : zkcash_core.admin.GlobalConfig) (dep wd m : Option U16)
    (h : zkcash_core.admin.update_global_config c dep wd m = ok (.Ok (), c'))
    (hd : c.deposit_fee_rate.val ≤ 10000) (hw : c.withdrawal_fee_rate.val ≤ 10000)
    (hm : c.fee_error_margin.val ≤ 10000) :
    c'.deposit_fee_rate.val ≤ 10000 ∧ c'.withdrawal_fee_rate.val ≤ 10000 ∧
      c'.fee_error_margin.val ≤ 10000 ∧ c'.bump = c.bump ∧ c'.authority = c.authority := by
  have hmax : (zkcash_core.admin.MAX_BASIS_POINTS).val = 10000 := by
    simp [zkcash_core.admin.MAX_BASIS_POINTS]
  unfold zkcash_core.admin.update_global_config at h
  rcases dep with _ | dr <;> rcases wd with _ | wr <;> rcases m with _ | mr <;>
    simp only at h <;> (try split_ifs at h) <;>
    (have e := Result.ok_injective h; simp only [Prod.mk.injEq] at e; obtain ⟨e1, rfl⟩ := e) <;>
    (try cases e1) <;>
    simp_all [UScalar.le_equiv]

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- Outside actions keep `WellFormed`: accounts the program owns keep their owner and data, and
    no other account can come to hold the program's account types. -/
theorem wf_envStep {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State}
    (wf : WellFormed d spent s) (h : EnvStep d.programId s s') : WellFormed d spent s' := by
  have own : ∀ k, (s' k).owner = d.programId → (∃ x, (s' k).data = x ∧ x.isProgramData = true) →
      (s k).owner = d.programId ∧ (s' k).data = (s k).data := by
    intro k _ ⟨x, hx, hpx⟩
    by_cases hk : (s k).owner = d.programId
    · exact ⟨hk, ((h k).1 hk).2.1⟩
    · have := (h k).2 hk; rw [hx] at this; simp [hpx] at this
  refine ⟨wf.programNotSystem, ?_, ?_, ?_, ?_⟩
  · intro k t ⟨ho, hd⟩
    obtain ⟨ho', hd'⟩ := own k ho ⟨_, hd, rfl⟩
    exact wf.tree k t ⟨ho', hd' ▸ hd⟩
  · intro k p ⟨ho, hd⟩
    obtain ⟨ho', hd'⟩ := own k ho ⟨_, hd, rfl⟩
    exact wf.pool k p ⟨ho', hd' ▸ hd⟩
  · intro k c ⟨ho, hd⟩
    obtain ⟨ho', hd'⟩ := own k ho ⟨_, hd, rfl⟩
    exact wf.config k c ⟨ho', hd' ▸ hd⟩
  · intro x hx
    obtain ⟨n, hn, hnx, hown⟩ := wf.spentRecorded x hx
    exact ⟨n, hn, hnx, hown.imp (EnvStep.keepsOwned h _) (EnvStep.keepsOwned h _)⟩

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- Changing one account's data to a value of a given kind, at an address that already held
    that kind: a helper for the admin instructions. -/
theorem set_data_other {s : State} {key k : Pubkey} {acc : Account} (hk : k ≠ key) :
    (s.set key acc k) = s k := by simp [State.set, hk]

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
theorem wf_updateDepositLimit {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : UpdateDepositLimitAccounts} {newLimit : U64}
    (wf : WellFormed d spent s) (h : execUpdateDepositLimit d s tx a newLimit = .ok s') :
    WellFormed d spent s' := by
  unfold execUpdateDepositLimit at h
  split at h
  swap; · cases h
  rename_i tree htree
  split at h
  · cases h
  rename_i hv
  obtain ⟨tree', htree', h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases h
  have ht' : tree' = { tree with max_deposit_amount := newLimit } := by
    have := ofResult_ok htree'
    simp only [zkcash_core.admin.update_deposit_limit] at this
    exact (Result.ok_injective this).symm
  have hval := not_not.mp hv
  obtain ⟨hka, hshape⟩ := wf.tree _ _ hval.treeAccount.1
  have hk : ∀ k, k ≠ a.treeAccount → (s.set a.treeAccount { s a.treeAccount with data := .treeAccount tree' }) k = s k :=
    fun k hk => set_data_other hk
  have hkey : (s.set a.treeAccount { s a.treeAccount with data := .treeAccount tree' }) a.treeAccount
      = { s a.treeAccount with data := .treeAccount tree' } := by simp
  refine ⟨wf.programNotSystem, ?_, ?_, ?_, ?_⟩
  · intro k t ⟨ho, hd⟩
    by_cases hka' : k = a.treeAccount
    · subst hka'; rw [hkey] at hd; cases hd
      refine ⟨hka, ?_⟩; rw [ht']; exact hshape
    · rw [hk k hka'] at ho hd; exact wf.tree k t ⟨ho, hd⟩
  · intro k p ⟨ho, hd⟩
    by_cases hka' : k = a.treeAccount
    · subst hka'; rw [hkey] at hd; cases hd
    · rw [hk k hka'] at ho hd; exact wf.pool k p ⟨ho, hd⟩
  · intro k c ⟨ho, hd⟩
    by_cases hka' : k = a.treeAccount
    · subst hka'; rw [hkey] at hd; cases hd
    · rw [hk k hka'] at ho hd; exact wf.config k c ⟨ho, hd⟩
  · intro x hx
    obtain ⟨n, hn, hnx, hown⟩ := wf.spentRecorded x hx
    have keep : ∀ k, (s k).owner = d.programId →
        ((s.set a.treeAccount { s a.treeAccount with data := .treeAccount tree' }) k).owner = d.programId := by
      intro k ho
      by_cases hka' : k = a.treeAccount
      · subst hka'; rw [hkey]; exact ho
      · rw [hk k hka']; exact ho
    exact ⟨n, hn, hnx, hown.imp (keep _) (keep _)⟩

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
theorem wf_updateGlobalConfig {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : UpdateGlobalConfigAccounts} {dep wd m : Option U16}
    (wf : WellFormed d spent s) (h : execUpdateGlobalConfig d s tx a dep wd m = .ok s') :
    WellFormed d spent s' := by
  unfold execUpdateGlobalConfig at h
  split at h
  swap; · cases h
  rename_i config hconfig
  split at h
  · cases h
  rename_i hv
  obtain ⟨⟨r, config'⟩, hres, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r with
  | Err e => cases h
  | Ok u =>
  cases h
  have hval := not_not.mp hv
  obtain ⟨hka, hd0, hw0, hm0⟩ := wf.config _ _ hval.globalConfig.1
  obtain ⟨hd1, hw1, hm1, -, -⟩ := ugc_rates config config' dep wd m (ofResult_ok hres) hd0 hw0 hm0
  have hk : ∀ k, k ≠ a.globalConfig → (s.set a.globalConfig { s a.globalConfig with data := .globalConfig config' }) k = s k :=
    fun k hk => set_data_other hk
  have hkey : (s.set a.globalConfig { s a.globalConfig with data := .globalConfig config' }) a.globalConfig
      = { s a.globalConfig with data := .globalConfig config' } := by simp
  refine ⟨wf.programNotSystem, ?_, ?_, ?_, ?_⟩
  · intro k t ⟨ho, hd⟩
    by_cases hka' : k = a.globalConfig
    · subst hka'; rw [hkey] at hd; cases hd
    · rw [hk k hka'] at ho hd; exact wf.tree k t ⟨ho, hd⟩
  · intro k p ⟨ho, hd⟩
    by_cases hka' : k = a.globalConfig
    · subst hka'; rw [hkey] at hd; cases hd
    · rw [hk k hka'] at ho hd; exact wf.pool k p ⟨ho, hd⟩
  · intro k c ⟨ho, hd⟩
    by_cases hka' : k = a.globalConfig
    · subst hka'; rw [hkey] at hd; cases hd
      exact ⟨hka, hd1, hw1, hm1⟩
    · rw [hk k hka'] at ho hd; exact wf.config k c ⟨ho, hd⟩
  · intro x hx
    obtain ⟨n, hn, hnx, hown⟩ := wf.spentRecorded x hx
    have keep : ∀ k, (s k).owner = d.programId →
        ((s.set a.globalConfig { s a.globalConfig with data := .globalConfig config' }) k).owner = d.programId := by
      intro k ho
      by_cases hka' : k = a.globalConfig
      · subst hka'; rw [hkey]; exact ho
      · rw [hk k hka']; exact ho
    exact ⟨n, hn, hnx, hown.imp (keep _) (keep _)⟩


omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- Every successful `transact` keeps `WellFormed`, and its two input nullifiers become spent.
    No hypothesis beyond `WellFormed` itself. -/
theorem wf_transact {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {evs : List CommitmentData}
    (wf : WellFormed d spent s) (hx : execTransact d s tx a proof ext fee out1 out2 = .ok (s', evs)) :
    WellFormed d (spent ∪ {toF proof.input_nullifiers.val[0]!, toF proof.input_nullifiers.val[1]!}) s' := by
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, hmb, hs₁, hhandler, hs', -⟩ := execTransact_ok hx
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨o0, d0, k0⟩ := initAccount_ownerData hA1
  obtain ⟨o1, d1, k1⟩ := initAccount_ownerData hA2
  have hnf : ∀ k, (k = a.nullifier0 ∨ k = a.nullifier1) →
      (s₁ k).owner = d.programId ∧ ∃ b, (s₁ k).data = .nullifier b := by
    rintro k (rfl | rfl)
    · by_cases he : a.nullifier0 = a.nullifier1
      · rw [he]; exact ⟨o1, _, d1⟩
      · obtain ⟨e1, e2⟩ := k1 _ he; exact ⟨e1.trans o0, _, e2.trans d0⟩
    · exact ⟨o1, _, d1⟩
  have hoth : ∀ k, k ≠ a.nullifier0 → k ≠ a.nullifier1 →
      (s₁ k).owner = (s k).owner ∧ (s₁ k).data = (s k).data := by
    intro k h0 h1
    obtain ⟨e1, e2⟩ := k1 k h1; obtain ⟨e3, e4⟩ := k0 k h0
    exact ⟨e1.trans e3, e2.trans e4⟩
  have hok := handler_ok d.crypto _ tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2
    ap env' tree' hhandler
  have hcan := verifyProof_canonical _ proof _ hok.verify
  have hcan0 : Canonical proof.input_nullifiers.val[0]! := by simpa [publicInputs] using hcan 3 (by decide)
  have hcan1 : Canonical proof.input_nullifiers.val[1]! := by simpa [publicInputs] using hcan 4 (by decide)
  obtain ⟨htreeAddr, hshape⟩ := wf.tree _ _ hvalid.treeAccount.1
  obtain ⟨p1, p2, t1, hap1, hap2⟩ := hok.appends
  have hsh1 := (append_shape _ _ tree t1 p1 hshape hap1).1
  have hsh2 := (append_shape _ _ t1 tree' p2 hsh1 hap2).1
  have hs'k : ∀ k, (s' k).owner = (s₁ k).owner ∧
      (s' k).data = (if k = a.treeAccount then .treeAccount tree' else (s₁ k).data) := by
    intro k; rw [hs']
    by_cases hk : k = a.treeAccount
    · subst hk; simp [State.set, State.withBalances]
    · simp [State.set, hk, State.withBalances]
  have htree_nf : ∀ k, (k = a.nullifier0 ∨ k = a.nullifier1) → k ≠ a.treeAccount := by
    rintro k hk rfl
    have hsys : (s a.treeAccount).owner = systemProgram := by
      rcases hk with h | h
      · rw [h]; exact hvalid.nullifier0.2.1
      · rw [h]; exact hvalid.nullifier1.2.1
    exact wf.programNotSystem (hvalid.treeAccount.1.1.symm.trans hsys)
  -- an account of the program's in `s'` that is not the tree and not a new nullifier account is
  -- unchanged from `s`
  have back : ∀ k, k ≠ a.treeAccount → ¬ (k = a.nullifier0 ∨ k = a.nullifier1) →
      (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := by
    intro k ht hn
    push_neg at hn
    obtain ⟨e1, e2⟩ := hs'k k
    obtain ⟨e3, e4⟩ := hoth k hn.1 hn.2
    rw [e1, e2, if_neg ht]; exact ⟨e3, e4⟩
  have notNull : ∀ k, (k = a.nullifier0 ∨ k = a.nullifier1) → ∃ b, (s' k).data = .nullifier b := by
    intro k hk
    obtain ⟨-, b, hb⟩ := hnf k hk
    exact ⟨b, by rw [(hs'k k).2, if_neg (htree_nf k hk), hb]⟩
  refine ⟨wf.programNotSystem, ?_, ?_, ?_, ?_⟩
  · intro k t ⟨ho, hd⟩
    by_cases ht : k = a.treeAccount
    · subst ht; rw [(hs'k _).2, if_pos rfl] at hd; cases hd; exact ⟨htreeAddr, hsh2⟩
    by_cases hn : k = a.nullifier0 ∨ k = a.nullifier1
    · obtain ⟨b, hb⟩ := notNull k hn; rw [hb] at hd; cases hd
    obtain ⟨e1, e2⟩ := back k ht hn
    exact wf.tree k t ⟨e1 ▸ ho, e2 ▸ hd⟩
  · intro k p ⟨ho, hd⟩
    by_cases ht : k = a.treeAccount
    · subst ht; rw [(hs'k _).2, if_pos rfl] at hd; cases hd
    by_cases hn : k = a.nullifier0 ∨ k = a.nullifier1
    · obtain ⟨b, hb⟩ := notNull k hn; rw [hb] at hd; cases hd
    obtain ⟨e1, e2⟩ := back k ht hn
    exact wf.pool k p ⟨e1 ▸ ho, e2 ▸ hd⟩
  · intro k c ⟨ho, hd⟩
    by_cases ht : k = a.treeAccount
    · subst ht; rw [(hs'k _).2, if_pos rfl] at hd; cases hd
    by_cases hn : k = a.nullifier0 ∨ k = a.nullifier1
    · obtain ⟨b, hb⟩ := notNull k hn; rw [hb] at hd; cases hd
    obtain ⟨e1, e2⟩ := back k ht hn
    exact wf.config k c ⟨e1 ▸ ho, e2 ▸ hd⟩
  · intro x hx'
    have hkeep := PrivacyCash.Model.execTransact_keepsOwned hx
    rcases Finset.mem_union.mp hx' with hold | hnew
    · obtain ⟨n, hn, hnx, hown⟩ := wf.spentRecorded x hold
      exact ⟨n, hn, hnx, hown.imp (hkeep _) (hkeep _)⟩
    · rcases Finset.mem_insert.mp hnew with h | h
      · refine ⟨_, hcan0, h.symm, Or.inl ?_⟩
        rw [← hvalid.nullifier0.1, (hs'k _).1]; exact (hnf _ (Or.inl rfl)).1
      · rw [Finset.mem_singleton] at h
        refine ⟨_, hcan1, h.symm, Or.inr ?_⟩
        rw [← hvalid.nullifier1.1, (hs'k _).1]; exact (hnf _ (Or.inr rfl)).1


omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- What the extracted `admin::initialize` produces when it succeeds: a tree of the fixed shape
    (height 26, a history of 100 roots, current index 0) and a config with rates 0, 25, 500. -/
theorem adminInitialize_ok {H : zkcash_core.merkle_tree.Hasher Unit}
    {t0 t : zkcash_core.merkle_tree.MerkleTreeAccount} {tk0 tk : zkcash_core.admin.TreeTokenAccount}
    {c0 c : zkcash_core.admin.GlobalConfig} {auth : Pubkey} {b1 b2 b3 : U8}
    (h : zkcash_core.admin.initialize H t0 tk0 c0 auth b1 b2 b3 = ok (.Ok (), t, tk, c)) :
    TreeShape t ∧ c.deposit_fee_rate.val = 0 ∧ c.withdrawal_fee_rate.val = 25 ∧
      c.fee_error_margin.val = 500 := by
  unfold zkcash_core.admin.initialize at h
  obtain ⟨⟨r, t1⟩, hit, h⟩ := bindOk h
  obtain ⟨cf, hcf, h⟩ := bindOk h
  cases r with
  | Err e =>
    have : cf = .Break (.Err e) := by
      simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok_injective hcf).symm
    subst this
    obtain ⟨r1, hr1, h⟩ := bindOk h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame, Result.ok.injEq] at hr1
    subst hr1
    have := Result.ok_injective h; simp at this
  | Ok u =>
  have : cf = .Continue u := by
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok_injective hcf).symm
  subst this
  have e := Result.ok_injective h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl, -, rfl⟩ := e
  refine ⟨?_, by simp, by simp, by simp⟩
  -- init_tree sets the shape fields, `merkle_tree::initialize` keeps them
  unfold zkcash_core.admin.init_tree zkcash_core.merkle_tree.initialize at hit
  obtain ⟨_, -, hit⟩ := bindOk hit
  obtain ⟨_, -, hit⟩ := bindOk hit
  obtain ⟨_, -, hit⟩ := bindOk hit
  obtain ⟨_, -, hit⟩ := bindOk hit
  obtain ⟨_, -, hit⟩ := bindOk hit
  have e := Result.ok_injective hit
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  refine ⟨?_, ?_, ?_⟩ <;> simp [zkcash_core.admin.MERKLE_TREE_HEIGHT, zkcash_core.admin.ROOT_HISTORY_SIZE]


omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- `initialize` keeps `WellFormed` (it creates the tree, pool and config at their canonical
    addresses, with the fixed tree shape and rates 0, 25, 500). -/
theorem wf_initialize {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : InitializeAccounts} (wf : WellFormed d spent s) (h : execInitialize d s tx a = .ok s') :
    WellFormed d spent s' := by
  have hkeep := PrivacyCash.Model.execInitialize_keepsOwned h
  unfold execInitialize at h
  split at h
  · cases h
  rename_i hv
  have hvalid := not_not.mp hv
  split at h
  · cases h
  rename_i mb hmb
  split at h
  · cases h
  rename_i s₁ hs₁
  obtain ⟨r₀, -, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r₀ with
  | Err e => cases h
  | Ok _ =>
  obtain ⟨⟨r, tree, token, config⟩, hres, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r with
  | Err e => cases h
  | Ok u =>
  obtain ⟨hshape, hdr, hwr, hmr⟩ := adminInitialize_ok (ofResult_ok hres)
  have hs' := PrivacyCash.Model.checkBalanced_ok h
  -- the three inits: only the three new accounts change owner or data
  obtain ⟨s₀₂, h₀₂, h₃⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨s₀₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h₀₂
  have hoth : ∀ k, k ≠ a.treeAccount → k ≠ a.treeTokenAccount → k ≠ a.globalConfig →
      (s₁ k).owner = (s k).owner ∧ (s₁ k).data = (s k).data := by
    intro k ht hp hc
    obtain ⟨-, -, k3⟩ := initAccount_ownerData h₃
    obtain ⟨-, -, k2⟩ := initAccount_ownerData h₂
    obtain ⟨-, -, k1⟩ := initAccount_ownerData h₁
    obtain ⟨e1, e2⟩ := k3 k hc; obtain ⟨e3, e4⟩ := k2 k hp; obtain ⟨e5, e6⟩ := k1 k ht
    exact ⟨e1.trans (e3.trans e5), e2.trans (e4.trans e6)⟩
  -- the final writes
  have hs'k : ∀ k, (s' k).owner = (s₁ k).owner ∧ (s' k).data =
      (if k = a.globalConfig then .globalConfig config else if k = a.treeTokenAccount then .treeToken token
       else if k = a.treeAccount then .treeAccount tree else (s₁ k).data) := by
    intro k; rw [hs']
    simp only [State.set]
    split_ifs <;> simp_all
  have htA : a.treeAccount = treeAddr d := hvalid.treeAccount.1
  have hpA : a.treeTokenAccount = poolAddr d := hvalid.treeTokenAccount.1
  have hcA : a.globalConfig = configAddr d := hvalid.globalConfig.1
  have back : ∀ k, k ≠ a.treeAccount → k ≠ a.treeTokenAccount → k ≠ a.globalConfig →
      (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := by
    intro k ht hp hc
    obtain ⟨e1, e2⟩ := hs'k k; obtain ⟨e3, e4⟩ := hoth k ht hp hc
    rw [e1, e2, if_neg hc, if_neg hp, if_neg ht]; exact ⟨e3, e4⟩
  refine ⟨wf.programNotSystem, ?_, ?_, ?_, ?_⟩
  · intro k t ⟨ho, hd⟩
    rw [(hs'k k).2] at hd
    by_cases hc : k = a.globalConfig
    · rw [if_pos hc] at hd; cases hd
    rw [if_neg hc] at hd
    by_cases hp : k = a.treeTokenAccount
    · rw [if_pos hp] at hd; cases hd
    rw [if_neg hp] at hd
    by_cases ht : k = a.treeAccount
    · rw [if_pos ht] at hd; cases hd; exact ⟨ht.trans htA, hshape⟩
    rw [if_neg ht] at hd
    obtain ⟨e1, e2⟩ := back k ht hp hc
    exact wf.tree k t ⟨e1 ▸ ho, by rw [← (hoth k ht hp hc).2]; exact hd⟩
  · intro k p ⟨ho, hd⟩
    rw [(hs'k k).2] at hd
    by_cases hc : k = a.globalConfig
    · rw [if_pos hc] at hd; cases hd
    rw [if_neg hc] at hd
    by_cases hp : k = a.treeTokenAccount
    · exact hp.trans hpA
    rw [if_neg hp] at hd
    by_cases ht : k = a.treeAccount
    · rw [if_pos ht] at hd; cases hd
    rw [if_neg ht] at hd
    obtain ⟨e1, e2⟩ := back k ht hp hc
    exact wf.pool k p ⟨e1 ▸ ho, by rw [← (hoth k ht hp hc).2]; exact hd⟩
  · intro k c ⟨ho, hd⟩
    rw [(hs'k k).2] at hd
    by_cases hc : k = a.globalConfig
    · rw [if_pos hc] at hd; cases hd
      exact ⟨hc.trans hcA, by omega, by omega, by omega⟩
    rw [if_neg hc] at hd
    by_cases hp : k = a.treeTokenAccount
    · rw [if_pos hp] at hd; cases hd
    rw [if_neg hp] at hd
    by_cases ht : k = a.treeAccount
    · rw [if_pos ht] at hd; cases hd
    rw [if_neg ht] at hd
    obtain ⟨e1, e2⟩ := back k ht hp hc
    exact wf.config k c ⟨e1 ▸ ho, by rw [← (hoth k ht hp hc).2]; exact hd⟩
  · intro x hx
    obtain ⟨n, hn, hnx, hown⟩ := wf.spentRecorded x hx
    exact ⟨n, hn, hnx, hown.imp (hkeep _) (hkeep _)⟩


/-- The nullifiers one instruction spends (only `transact` spends any). -/
def stepSpent : Instruction → Finset LeanSpec.F
  | .transact _ proof _ _ _ _ => {toF proof.input_nullifiers.val[0]!, toF proof.input_nullifiers.val[1]!}
  | _ => ∅

/-- The nullifiers an execution spends: those of its `transact` instructions. -/
def runSpent : List Event → Finset LeanSpec.F
  | [] => ∅
  | .program _ ix _ :: es => stepSpent ix ∪ runSpent es
  | .env :: es => runSpent es

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
theorem wf_step {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {ix : Instruction} {evs : List CommitmentData}
    (wf : WellFormed d spent s) (h : step d s tx ix = .ok (s', evs)) :
    WellFormed d (spent ∪ stepSpent ix) s' := by
  cases ix with
  | «initialize» a =>
    obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
    cases h2; simpa [stepSpent] using wf_initialize wf h1
  | updateDepositLimit a l =>
    obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
    cases h2; simpa [stepSpent] using wf_updateDepositLimit wf h1
  | updateGlobalConfig a dep wd m =>
    obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
    cases h2; simpa [stepSpent] using wf_updateGlobalConfig wf h1
  | transact a proof ext fee out1 out2 =>
    exact wf_transact wf h

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
theorem wf_run {d : Deployment} {spent : Finset LeanSpec.F} {s s' : State} {evs : List Event}
    (hrun : Run d s evs s') (wf : WellFormed d spent s) : WellFormed d (spent ∪ runSpent evs) s' := by
  induction hrun generalizing spent with
  | nil => simpa [runSpent] using wf
  | program hstep _ ih =>
    have := ih (wf_step wf hstep)
    simpa [runSpent, Finset.union_assoc] using this
  | env henv _ ih =>
    simpa [runSpent] using ih (wf_envStep wf henv)

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
theorem wf_genesis {d : Deployment} {s : State} (hgen : Genesis d.programId s)
    (hpid : d.programId ≠ systemProgram) : WellFormed d ∅ s :=
  ⟨hpid, fun k _ h => absurd h.1 (hgen k), fun k _ h => absurd h.1 (hgen k),
   fun k _ h => absurd h.1 (hgen k), fun _ hx => absurd hx (Finset.notMem_empty _)⟩

omit [LeanSpec.PoseidonHashes] [LeanSpec.Sha] in
/-- **Every state an execution reaches from genesis is `WellFormed`**, for the nullifiers the
    execution spent. -/
theorem wf_reachable {d : Deployment} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram) :
    WellFormed d (runSpent evs) s := by
  simpa using wf_run hrun (wf_genesis hgen hpid)

end Connection
