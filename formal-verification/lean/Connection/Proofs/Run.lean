import Connection.Proofs.WellFormed
import Connection.Proofs.RunView
import Connection.Proofs.Bridge
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: every code run is a spec run

NOT FOR REVIEW: the statements are in `Connection/ConnectionTheorems.lean`. The bridge walks over an
code run from genesis one event at a time, keeping a spec run that matches it so far. Before
`initialize` no program step can succeed. `initialize` starts the spec run at `initWorld`.
Each `transact` extends it by one transaction (the main per-step theorem). Admin instructions
and outside actions are changes allowed between transactions
(`Spec.UpdatedValuesBetweenTransacts.Allowed`).
-/

namespace Connection

/-! ## Whether the pool has been initialized -/

theorem genesis_noProgramAccounts {d : Deployment} {s : State} (h : Genesis d.programId s) :
    NoProgramAccounts d s :=
  ⟨fun k _ hk => h k hk.1, fun k _ hk => h k hk.1, fun k _ hk => h k hk.1, fun k hk => h k hk.1⟩

/-! ## Outside actions -/

/-- Outside actions never make an account the program's tree, pool, config or nullifier account. -/
theorem env_noProgramAccounts {d : Deployment} {s s' : State} (h : EnvStep d.programId s s')
    (hn : NoProgramAccounts d s) : NoProgramAccounts d s' := by
  have back : ∀ k x, (s' k).owner = d.programId → (s' k).data = x → x.isProgramData = true →
      (s k).owner = d.programId ∧ (s k).data = x := by
    intro k x ho hd hx
    by_cases hk : (s k).owner = d.programId
    · exact ⟨hk, ((h k).1 hk).2.1 ▸ hd⟩
    · have := (h k).2 hk; rw [hd] at this; simp [hx] at this
  refine ⟨fun k t ht => ?_, fun k p hp => ?_, fun k c hc => ?_, fun k ⟨ho, b, hd⟩ => ?_⟩
  · exact hn.1 k t (back k _ ht.1 ht.2 rfl)
  · exact hn.2.1 k p (back k _ hp.1 hp.2 rfl)
  · exact hn.2.2.1 k c (back k _ hc.1 hc.2 rfl)
  · obtain ⟨o, dd⟩ := back k _ ho hd rfl; exact hn.2.2.2 k ⟨o, b, dd⟩

/-- Outside actions keep the program's tree, pool and config. -/
theorem env_initialized {d : Deployment} {s s' : State} (h : EnvStep d.programId s s')
    (hi : Initialized d s) : Initialized d s' := by
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨c, hc⟩⟩ := hi
  refine ⟨⟨t, ?_⟩, ⟨p, ?_⟩, ⟨c, ?_⟩⟩
  · obtain ⟨o, dd, -⟩ := (h _).1 ht.1; exact ⟨o, dd.trans ht.2⟩
  · obtain ⟨o, dd, -⟩ := (h _).1 hp.1; exact ⟨o, dd.trans hp.2⟩
  · obtain ⟨o, dd, -⟩ := (h _).1 hc.1; exact ⟨o, dd.trans hc.2⟩

/-- Two states with the same spec tree and the same nullifier accounts map to worlds that
    differ only in their balances and config. -/
theorem toWorld_withUpdatedValues_of_same_tree {d : Deployment} {rent : Nat → U64}
    {s s' : State} (ht : toTree (s'.treeAccount d.treeAddress) = toTree (s.treeAccount d.treeAddress))
    (hn : nullifierAccountsOf d s' = nullifierAccountsOf d s) :
    toWorld d rent s' = (toWorld d rent s).withUpdatedValues
      (Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s')) := by
  simp only [toWorld, Spec.World.withUpdatedValues,
    Spec.UpdatedValuesBetweenTransacts.unchanged, ht, hn]

/-- Outside actions keep the program's nullifier accounts: they keep the owner and data of every
    account the program owns, and give no other account the program's data. -/
theorem env_nullifierAccounts {d : Deployment} {s s' : State} (h : EnvStep d.programId s s') :
    nullifierAccountsOf d s' = nullifierAccountsOf d s := by
  ext x
  rw [mem_nullifierAccountsOf, mem_nullifierAccountsOf]
  constructor
  · rintro ⟨ho, b, hd⟩
    by_cases hk : (s (fromPubkey x)).owner = d.programId
    · obtain ⟨-, dd, -⟩ := (h _).1 hk
      exact ⟨hk, b, dd ▸ hd⟩
    · have := (h _).2 hk; rw [hd] at this; simp [AccountData.isProgramData] at this
  · rintro ⟨ho, b, hd⟩
    obtain ⟨o, dd, -⟩ := (h _).1 ho
    exact ⟨o, b, dd.trans hd⟩

/-- Writing one account's data keeps the nullifier accounts, if neither the old nor the new data
    is a nullifier account's. -/
theorem set_data_nullifierAccounts {d : Deployment} {s : State} {key : Pubkey} {dt : AccountData}
    (hold : ∀ b, (s key).data ≠ .nullifier b) (hnew : ∀ b, dt ≠ .nullifier b) :
    nullifierAccountsOf d (s.set key { s key with data := dt }) = nullifierAccountsOf d s := by
  ext x
  rw [mem_nullifierAccountsOf, mem_nullifierAccountsOf]
  by_cases hk : fromPubkey x = key
  · rw [hk]
    simp only [PrivacyCash.Model.Deployment.IsNullifierAccount, State.set]
    constructor
    · rintro ⟨-, b, hb⟩; exact absurd hb (hnew b)
    · rintro ⟨-, b, hb⟩; exact absurd hb (hold b)
  · simp only [PrivacyCash.Model.Deployment.IsNullifierAccount, State.set, if_neg hk]

/-- **Outside actions are changes allowed between transactions.** The program's data is
    untouched, and the pool only gains lamports. -/
theorem env_between {d : Deployment} {rent : Nat → U64} {s s' : State}
    (h : EnvStep d.programId s s') (hi : Initialized d s) :
    toWorld d rent s' = (toWorld d rent s).withUpdatedValues
        (Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s')) ∧
      (Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s')).Allowed
        (toWorld d rent s) := by
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨c, hc⟩⟩ := hi
  have dt := ((h _).1 ht.1).2.1
  have dc := ((h _).1 hc.1).2.1
  have hw := toWorld_withUpdatedValues_of_same_tree (d := d) (rent := rent)
    (s := s) (s' := s')
    (by simp only [PrivacyCash.Model.State.treeAccount, dt]) (env_nullifierAccounts h)
  refine ⟨hw, ⟨?_, toWorld_fit d rent s', ?_⟩⟩
  · -- the program owns its accounts, so they only gain
    intro x hx
    show s.lamports (fromPubkey x) ≤ s'.lamports (fromPubkey x)
    have hown : (s (fromPubkey x)).owner = d.programId := by
      rcases hx with rfl | hx | rfl | rfl
      · show (s (fromPubkey (toPubkey d.poolAddress))).owner = _
        rw [fromPubkey_toPubkey]; exact hp.1
      · exact (mem_nullifierAccountsOf.mp hx).1
      · show (s (fromPubkey (toPubkey d.treeAddress))).owner = _
        rw [fromPubkey_toPubkey]; exact ht.1
      · show (s (fromPubkey (toPubkey d.configAddress))).owner = _
        rw [fromPubkey_toPubkey]; exact hc.1
    exact ((h _).1 hown).2.2
  · have : (toWorld d rent s').state.config = (toWorld d rent s).state.config := by
      simp only [toWorld, PrivacyCash.Model.State.treeAccount, PrivacyCash.Model.State.configAccount, dt, dc]
    show Spec.ReachableByAdminChanges [] _ (toWorld d rent s').state.config
    rw [this]; exact .noChange _

/-! ## Admin instructions -/

/-- The values `w` already has, reached by the admin changes `chs`. -/
def recordChanges (w : Spec.World) (chs : List Spec.AdminChange) :
    Spec.UpdatedValuesBetweenTransacts :=
  { Spec.UpdatedValuesBetweenTransacts.unchanged w with adminChanges := chs }

/-- What `update_global_config` computes: each given setting replaces the old one, and the
    fee error margin, when given, is at most 10000. -/
theorem ugc_spec (c c' : zkcash_core.admin.GlobalConfig) (dep wd m : Option U16)
    (h : zkcash_core.admin.update_global_config c dep wd m = ok (.Ok (), c')) :
    c' = { c with deposit_fee_rate := dep.getD c.deposit_fee_rate,
                  withdrawal_fee_rate := wd.getD c.withdrawal_fee_rate,
                  fee_error_margin := m.getD c.fee_error_margin } ∧
      ∀ v, m = some v → v.val ≤ 10000 := by
  have hmax : (zkcash_core.admin.MAX_BASIS_POINTS).val = 10000 := by
    simp [zkcash_core.admin.MAX_BASIS_POINTS]
  unfold zkcash_core.admin.update_global_config at h
  rcases dep with _ | dr <;> rcases wd with _ | wr <;> rcases m with _ | mr <;>
    simp only at h <;> (try split_ifs at h) <;>
    (have e := Result.ok_injective h; simp only [Prod.mk.injEq] at e; obtain ⟨e1, rfl⟩ := e) <;>
    (try cases e1) <;>
    simp_all [UScalar.le_equiv]

/-- Writing one account's data keeps every account's lamports. -/
theorem set_data_lamports {s : State} {key : Pubkey} {dt : AccountData} (k : Pubkey) :
    ((s.set key { s key with data := dt }) k).lamports = (s k).lamports := by
  by_cases hk : k = key
  · subst hk; simp [State.set]
  · simp [State.set, hk]

/-- **`update_global_config` is an allowed admin change.** It sets the fee settings, signed by
    the config's authority, with a fee error margin of at most 10000; nothing else changes. -/
theorem ugc_between {d : Deployment} {rent : Nat → U64} {s s' : State}
    {tx : TxEnv} {a : UpdateGlobalConfigAccounts} {dep wd m : Option U16}
    (wf : WellFormed d s) (hi : Initialized d s)
    (h : execUpdateGlobalConfig d s tx a dep wd m = .ok s') :
    Initialized d s' ∧
      toWorld d rent s' = (toWorld d rent s).withUpdatedValues
        (recordChanges (toWorld d rent s') (toAdminChange d s tx (.updateGlobalConfig a dep wd m)).toList) ∧
      (recordChanges (toWorld d rent s') (toAdminChange d s tx (.updateGlobalConfig a dep wd m)).toList).Allowed
        (toWorld d rent s) := by
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
  obtain ⟨hka, hd0, hw0, hm0, -⟩ := wf.config _ _ hval.globalConfig.1
  obtain ⟨hc', hmv⟩ := ugc_spec config config' dep wd m (ofResult_ok hres)
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, -⟩ := hi
  have hne : d.treeAddress ≠ a.globalConfig := fun e => by
    have h1 := ht.2; rw [e, hval.globalConfig.1.2] at h1; cases h1
  have hpne : d.poolAddress ≠ a.globalConfig := fun e => by
    have h1 := hp.2; rw [e, hval.globalConfig.1.2] at h1; cases h1
  set s' := s.set a.globalConfig { s a.globalConfig with data := .globalConfig config' } with hs'
  have keep : ∀ k, k ≠ a.globalConfig → s' k = s k := fun k hk => set_data_other hk
  have hkey : s' a.globalConfig = { s a.globalConfig with data := .globalConfig config' } := by simp [hs']
  have htree : s'.treeAccount d.treeAddress = s.treeAccount d.treeAddress := by
    simp only [PrivacyCash.Model.State.treeAccount, keep _ hne]
  refine ⟨⟨⟨t, by unfold HoldsTree; rw [keep _ hne]; exact ht⟩, ⟨p, by unfold HoldsTreeToken; rw [keep _ hpne]; exact hp⟩,
    ⟨config', ?_⟩⟩, toWorld_withUpdatedValues_of_same_tree (by rw [htree])
      (set_data_nullifierAccounts (by rw [hval.globalConfig.1.2]; intro b h; cases h)
        (by intro b h; cases h)), ⟨?_, toWorld_fit d rent _, ?_⟩⟩
  · unfold HoldsGlobalConfig; rw [← hka, hkey]; exact ⟨hval.globalConfig.1.1, rfl⟩
  · -- balances: unchanged
    intro x _
    show s.lamports (fromPubkey x) ≤ s'.lamports (fromPubkey x)
    by_cases hx : fromPubkey x = a.globalConfig
    · rw [PrivacyCash.Model.State.lamports, PrivacyCash.Model.State.lamports, hx, hkey]
    · rw [PrivacyCash.Model.State.lamports, PrivacyCash.Model.State.lamports, keep _ hx]
  · -- config: one allowed admin change
    have hcfg : s.configAccount d.configAddress = config := by
      simp only [PrivacyCash.Model.State.configAccount, ← hka, hval.globalConfig.1.2]
    have hcfg' : s'.configAccount d.configAddress = config' := by
      simp only [PrivacyCash.Model.State.configAccount, ← hka, hkey]
    show Spec.ReachableByAdminChanges
      [⟨tx.signers.map toPubkey,
        .feeSettings (dep.getD (s.configAccount d.configAddress).deposit_fee_rate).val
          (wd.getD (s.configAccount d.configAddress).withdrawal_fee_rate).val
          (m.getD (s.configAccount d.configAddress).fee_error_margin).val⟩]
      (toConfig (s.configAccount d.configAddress) (s.treeAccount d.treeAddress))
      (toConfig (s'.configAccount d.configAddress) (s'.treeAccount d.treeAddress))
    rw [hcfg, hcfg', htree]
    refine .extend (chs := []) ⟨tx.signers.map toPubkey,
      .feeSettings (dep.getD config.deposit_fee_rate).val (wd.getD config.withdrawal_fee_rate).val
        (m.getD config.fee_error_margin).val⟩ (.noChange _) ?_
    have hsig : toPubkey config.authority ∈ tx.signers.map toPubkey := by
      rw [hval.globalConfig.2.2]; exact List.mem_map_of_mem hval.authority
    have hErrorMargin : (m.getD config.fee_error_margin).val ≤ 10000 := by
      rcases m with _ | v
      · exact hm0
      · exact hmv v rfl
    obtain ⟨hd1, hw1, -⟩ := ugc_rates config config' dep wd m (ofResult_ok hres) hd0 hw0 hm0
    rw [hc'] at hd1 hw1
    simp only [Spec.AdminChange.apply, toConfig, if_pos (And.intro hsig (And.intro hd1 (And.intro hw1 hErrorMargin))), hc']

/-- **`update_deposit_limit` is an allowed admin change.** It sets the deposit limit, signed by
    the tree's authority; the spec's tree and everything else are unchanged. -/
theorem udl_between {d : Deployment} {rent : Nat → U64} {s s' : State}
    {tx : TxEnv} {a : UpdateDepositLimitAccounts} {newLimit : U64}
    (wf : WellFormed d s) (hi : Initialized d s)
    (h : execUpdateDepositLimit d s tx a newLimit = .ok s') :
    Initialized d s' ∧
      toWorld d rent s' = (toWorld d rent s).withUpdatedValues
        (recordChanges (toWorld d rent s') (toAdminChange d s tx (.updateDepositLimit a newLimit)).toList) ∧
      (recordChanges (toWorld d rent s') (toAdminChange d s tx (.updateDepositLimit a newLimit)).toList).Allowed
        (toWorld d rent s) := by
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
  obtain ⟨hka, -⟩ := wf.tree _ _ hval.treeAccount.1
  obtain ⟨-, ⟨p, hp⟩, ⟨c, hc⟩⟩ := hi
  have hpne : d.poolAddress ≠ a.treeAccount := fun e => by
    have h1 := hp.2; rw [e, hval.treeAccount.1.2] at h1; cases h1
  have hcne : d.configAddress ≠ a.treeAccount := fun e => by
    have h1 := hc.2; rw [e, hval.treeAccount.1.2] at h1; cases h1
  set s' := s.set a.treeAccount { s a.treeAccount with data := .treeAccount tree' } with hs'
  have keep : ∀ k, k ≠ a.treeAccount → s' k = s k := fun k hk => set_data_other hk
  have hkey : s' a.treeAccount = { s a.treeAccount with data := .treeAccount tree' } := by simp [hs']
  have hT : s.treeAccount d.treeAddress = tree := by simp only [PrivacyCash.Model.State.treeAccount, ← hka, hval.treeAccount.1.2]
  have hT' : s'.treeAccount d.treeAddress = tree' := by simp only [PrivacyCash.Model.State.treeAccount, ← hka, hkey]
  have hC : s'.configAccount d.configAddress = s.configAccount d.configAddress := by
    simp only [PrivacyCash.Model.State.configAccount, keep _ hcne]
  refine ⟨⟨⟨tree', ?_⟩, ⟨p, by unfold HoldsTreeToken; rw [keep _ hpne]; exact hp⟩, ⟨c, by unfold HoldsGlobalConfig; rw [keep _ hcne]; exact hc⟩⟩,
    toWorld_withUpdatedValues_of_same_tree (by rw [hT, hT', ht']; rfl)
      (set_data_nullifierAccounts (by rw [hval.treeAccount.1.2]; intro b h; cases h)
        (by intro b h; cases h)), ⟨?_, toWorld_fit d rent _, ?_⟩⟩
  · unfold HoldsTree; rw [← hka, hkey]; exact ⟨hval.treeAccount.1.1, rfl⟩
  · intro x _
    show s.lamports (fromPubkey x) ≤ s'.lamports (fromPubkey x)
    by_cases hx : fromPubkey x = a.treeAccount
    · rw [PrivacyCash.Model.State.lamports, PrivacyCash.Model.State.lamports, hx, hkey]
    · rw [PrivacyCash.Model.State.lamports, PrivacyCash.Model.State.lamports, keep _ hx]
  · show Spec.ReachableByAdminChanges [⟨tx.signers.map toPubkey, .depositLimit newLimit.val⟩]
      (toConfig (s.configAccount d.configAddress) (s.treeAccount d.treeAddress))
      (toConfig (s'.configAccount d.configAddress) (s'.treeAccount d.treeAddress))
    rw [hC, hT, hT', ht']
    refine .extend (chs := []) ⟨tx.signers.map toPubkey, .depositLimit newLimit.val⟩ (.noChange _) ?_
    have hsig : toPubkey tree.authority ∈ tx.signers.map toPubkey := by
      rw [hval.treeAccount.2.2]; exact List.mem_map_of_mem hval.authority
    have hlt : newLimit.val < 2 ^ 64 := newLimit.hBounds
    simp only [Spec.AdminChange.apply, toConfig, if_pos (And.intro hsig hlt)]

/-! ## `transact` -/

/-- `transact` keeps the program's tree, pool and config (it rewrites the tree's data and creates
    two nullifier accounts elsewhere). -/
theorem transact_initialized {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (wf : WellFormed d s) (hi : Initialized d s)
    (h : step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events)) :
    Initialized d s' := by
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, -, hs₁, -, hs', -⟩ := execTransact_ok h
  obtain ⟨⟨t, ht⟩, ⟨p, hp⟩, ⟨c, hc⟩⟩ := hi
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨-, -, k1⟩ := initAccount_ownerData hA1
  obtain ⟨-, -, k2⟩ := initAccount_ownerData hA2
  have hnot : ∀ k, (s k).owner = d.programId → k ≠ a.nullifier0 ∧ k ≠ a.nullifier1 := by
    intro k hk
    refine ⟨fun e => wf.programNotSystem ?_, fun e => wf.programNotSystem ?_⟩
    · rw [← hk, e]; exact hvalid.nullifier0.2.1
    · rw [← hk, e]; exact hvalid.nullifier1.2.1
  have s₁_keep : ∀ k, (s k).owner = d.programId → (s₁ k).owner = (s k).owner ∧ (s₁ k).data = (s k).data := by
    intro k hk
    obtain ⟨n0, n1⟩ := hnot k hk
    obtain ⟨o2, d2⟩ := k2 k n1
    obtain ⟨o1, d1⟩ := k1 k n0
    exact ⟨o2.trans o1, d2.trans d1⟩
  have htA : a.treeAccount = d.treeAddress := (wf.tree _ _ hvalid.treeAccount.1).1
  have s'_other : ∀ k, k ≠ a.treeAccount → (s' k).owner = (s₁ k).owner ∧ (s' k).data = (s₁ k).data := by
    intro k hk; rw [hs']; simp [State.set, hk, State.withBalances]
  have hpt : d.poolAddress ≠ a.treeAccount := fun e => by
    have h1 := hp.2; rw [e, hvalid.treeAccount.1.2] at h1; cases h1
  have hct : d.configAddress ≠ a.treeAccount := fun e => by
    have h1 := hc.2; rw [e, hvalid.treeAccount.1.2] at h1; cases h1
  refine ⟨⟨tree', ?_⟩, ⟨p, ?_⟩, ⟨c, ?_⟩⟩
  · unfold HoldsTree
    rw [← htA, hs']
    obtain ⟨o, -⟩ := s₁_keep _ hvalid.treeAccount.1.1
    simp [State.set, State.withBalances]
    rw [o]; exact hvalid.treeAccount.1.1
  · obtain ⟨o, dd⟩ := s'_other _ hpt
    obtain ⟨o', dd'⟩ := s₁_keep _ hp.1
    exact ⟨o.trans (o'.trans hp.1), dd.trans (dd'.trans hp.2)⟩
  · obtain ⟨o, dd⟩ := s'_other _ hct
    obtain ⟨o', dd'⟩ := s₁_keep _ hc.1
    exact ⟨o.trans (o'.trans hc.1), dd.trans (dd'.trans hc.2)⟩

/-! ## `initialize`: the tree it writes is the spec's empty tree -/

private theorem okOfE {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ x, m = ok x ∧ P x :=
  (WP.spec_equiv_exists _ _).mp h

private theorem cloneUsizeE : ∀ x : Usize, core.clone.CloneUsize.clone x = ok x := by
  intro x; simp

private theorem ltUsizeE : ∀ a b : Usize,
    core.cmp.PartialOrdUsize.lt a b = ok (decide (a.val < b.val)) := by
  intro a b; simp [core.cmp.impls.PartialOrdUsize.lt]; try rfl

/-- `initialize`'s loop writes the zero hashes `0 … 25` into the subtrees. -/
theorem initLoop_values (iter : core.ops.range.Range Usize)
    (a : Std.Array (Std.Array U8 32#usize) 26#usize) (z : Std.Array (Std.Array U8 32#usize) 41#usize)
    (r : Std.Array (Std.Array U8 32#usize) 26#usize)
    (hstart : iter.start.val = 0) (hend : iter.end.val = 26)
    (h : zkcash_core.merkle_tree.initialize_loop iter a z = ok r) :
    ∀ j : ℕ, j < 26 → r.val[j]! = z.val[j]! := by
  unfold zkcash_core.merkle_tree.initialize_loop at h
  have hinv : iter.end.val = 26 ∧ iter.start.val ≤ 26 ∧
      ∀ j : ℕ, j < iter.start.val → a.val[j]! = z.val[j]! :=
    ⟨hend, by omega, fun j hj => absurd hj (by omega)⟩
  refine loop_ok_induction _
    (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize) =>
      26 - x.1.start.val)
    (fun x => x.1.end.val = 26 ∧ x.1.start.val ≤ 26 ∧ ∀ j : ℕ, j < x.1.start.val → x.2.val[j]! = z.val[j]!)
    (fun r => ∀ j : ℕ, j < 26 → r.val[j]! = z.val[j]!)
    ?_ (iter, a) r hinv h
  rintro ⟨it, a⟩ rr ⟨hend, hle, ha⟩ hr
  simp only at hend hle ha
  unfold zkcash_core.merkle_tree.initialize_loop.body at hr
  simp only [core.iter.range.StepUsize] at hr
  by_cases hlt : it.start.val < 26
  · obtain ⟨⟨o, it1⟩, hn, ho, hs1, he1⟩ := okOfE
      (core.iter.range.IteratorRange.next_UScalar_some_spec cloneUsizeE ltUsizeE it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    obtain ⟨zb, hzi, hr⟩ := bindOk hr
    obtain ⟨zb', hzi', hzbv⟩ := okOfE (Std.Array.index_usize_spec z it.start (by simp; omega))
    rw [hzi'] at hzi; obtain rfl := Result.ok_injective hzi
    obtain ⟨a2, ha2, hr⟩ := bindOk hr
    obtain ⟨a2', ha2', ha2v⟩ := okOfE (Std.Array.update_spec a it.start zb' (by simp; omega))
    rw [ha2'] at ha2; obtain rfl := Result.ok_injective ha2
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show it1.end.val = 26; rw [he1]; exact hend
    · show it1.start.val ≤ 26; omega
    · show ∀ j : ℕ, j < it1.start.val → a2'.val[j]! = z.val[j]!
      intro j hj
      rw [ha2v]
      simp only [Std.Array.set_val_eq]
      by_cases hji : j = it.start.val
      · rw [getElem!_pos _ _ (by simp; omega)]; simp only [hji, List.getElem_set_self]
        rw [hzbv, getElem!_pos _ _ (by simp; omega)]
      · rw [getElem!_pos _ _ (by simp; omega)]
        have := ha j (by omega)
        rw [getElem!_pos _ _ (by simp; omega)] at this
        have hne : it.start.val ≠ j := Ne.symm hji
        simpa [hne] using this
    · show 26 - it1.start.val < 26 - it.start.val; omega
  · obtain ⟨⟨o, it1⟩, hn, ho, hit⟩ := okOfE
      (core.iter.range.IteratorRange.next_UScalar_none_spec ltUsizeE it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    intro j hj; exact ha j (by omega)

/-- What `init_tree` writes: the zero hashes `0 … 25` as subtrees, the zero hash of height 26
    as root and in history slot 0, the other history slots as they were, index 0, and the given
    authority and deposit limit. -/
theorem initTree_values {H : zkcash_core.merkle_tree.Hasher Unit}
    {t0 t : zkcash_core.merkle_tree.MerkleTreeAccount} {auth : Pubkey} {b : U8} {m : U64}
    {r : core.result.Result Unit zkcash_core.error.ErrorCode}
    {z : Std.Array (Std.Array U8 32#usize) 41#usize} (hzb : H.zero_bytes = ok z)
    (h : zkcash_core.admin.init_tree H t0 auth b m = ok (r, t)) :
    (∀ j : ℕ, j < 26 → t.subtrees.val[j]! = z.val[j]!) ∧ t.root = z.val[26]! ∧
      (∀ j : Fin 100, t.root_history.val[j.val]! =
        if j.val = 0 then z.val[26]! else t0.root_history.val[j.val]!) ∧
      t.next_index.val = 0 ∧ t.root_index.val = 0 ∧ t.authority = auth ∧ t.max_deposit_amount = m := by
  unfold zkcash_core.admin.init_tree zkcash_core.merkle_tree.initialize at h
  obtain ⟨hgt, hhgt, h⟩ := bindOk h
  obtain ⟨z', hz', h⟩ := bindOk h
  rw [hzb] at hz'
  have hzz := Result.ok_injective hz'
  subst z'
  obtain ⟨sub, hsub, h⟩ := bindOk h
  obtain ⟨ir, hir, h⟩ := bindOk h
  obtain ⟨a1, ha1, h⟩ := bindOk h
  have e := Result.ok_injective h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl⟩ := e
  have hgv : hgt.val = 26 := by
    have := (Result.ok_injective hhgt).symm
    rw [this]; simp [zkcash_core.admin.MERKLE_TREE_HEIGHT]
  obtain ⟨ir', hir', hirv⟩ := okOfE (Std.Array.index_usize_spec z hgt (by simp; omega))
  rw [hir'] at hir; obtain rfl := Result.ok_injective hir
  obtain ⟨a1', ha1', ha1v⟩ := okOfE (Std.Array.update_spec t0.root_history 0#usize ir' (by simp))
  rw [ha1'] at ha1; obtain rfl := Result.ok_injective ha1
  have hir26 : ir' = z.val[26]! := by
    simp [hirv, hgv]
  refine ⟨initLoop_values _ _ _ _ rfl (by simpa using hgv) hsub, hir26, ?_, by simp, by simp, rfl, rfl⟩
  intro j
  show a1'.val[j.val]! = _
  rw [ha1v]
  have hlen : t0.root_history.val.length = 100 := by simp
  simp only [Std.Array.set_val_eq]
  by_cases hj : j.val = 0
  · rw [getElem!_pos _ _ (by simp [hlen]), if_pos hj]; simp [hj, hir26]
  · rw [getElem!_pos _ _ (by simp [hlen]), if_neg hj, getElem!_pos _ _ (by simp [hlen])]
    have hj' : (0 : ℕ) ≠ j.val := Ne.symm hj
    simp [hj']

/-- Zero bytes are the field element 0. -/
theorem toF_zeroBytes32 : toF (Std.Array.repeat 32#usize 0#u8) = 0 := by
  have hb : beNat (Std.Array.repeat 32#usize 0#u8) = 0 := by rfl
  simp only [toF_def, hb, Nat.cast_zero]

/-- **The tree `initialize` writes is the spec's empty tree** (`Spec.initTree`), when the
    code's zero hashes are the spec's (`HashesAgree.zeroBytes`). -/
theorem initialize_toTree [Spec.PoseidonHashes] {H : zkcash_core.merkle_tree.Hasher Unit}
    {t : zkcash_core.merkle_tree.MerkleTreeAccount} {auth : Pubkey} {b : U8} {m : U64}
    {r : core.result.Result Unit zkcash_core.error.ErrorCode}
    (hz : ∃ z, H.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = Spec.Z i)
    (h : zkcash_core.admin.init_tree H zeroTree auth b m = ok (r, t)) :
    toTree t = Spec.initTree := by
  obtain ⟨z, hzb, hzv⟩ := hz
  obtain ⟨hsub, hroot, hhist, hni, hri, -, -⟩ := initTree_values hzb h
  have hzero : ∀ j : ℕ, j < 100 → zeroTree.root_history.val[j]! = Std.Array.repeat 32#usize 0#u8 := by
    intro j hj
    rw [getElem!_pos _ _ (by simp; omega)]
    simp only [zeroTree, Std.Array.repeat_val, List.getElem_replicate]
  simp only [toTree, Spec.initTree, Spec.Tree.mk.injEq]
  refine ⟨hni, ?_, by rw [hroot, hzv 26 le_rfl], ?_, ?_⟩
  · funext i; rw [hsub i.val i.isLt, hzv i.val (by omega)]
  · funext i
    rw [hhist i]
    by_cases h0 : i.val = 0
    · have hi : i = 0 := Fin.ext h0
      rw [if_pos h0, if_pos hi, hzv 26 le_rfl]
    · have hi : i ≠ 0 := fun e => h0 (by rw [e]; rfl)
      rw [if_neg h0, if_neg hi, hzero i.val i.isLt, toF_zeroBytes32]
  · apply Fin.ext; simp [hri]

/-! ## `initialize`: the admin check and the pool's lamports -/

/-- `check_admin` accepts only the admin, when there is one. -/
theorem checkAdmin_ok {auth : Pubkey} {adm : Option Pubkey}
    (h : zkcash_core.admin.check_admin auth adm = ok (.Ok ())) : ∀ k, adm = some k → auth = k := by
  intro k hk
  subst hk
  unfold zkcash_core.admin.check_admin at h
  simp only at h
  obtain ⟨b, hb, hiff⟩ := (WP.spec_equiv_exists _ _).mp (arrayEqU8Spec auth k)
  rw [hb, bind_tc_ok] at h
  cases b with
  | true => exact hiff.mp rfl
  | false => simp at h

/-- A system transfer's destination ends with at least the amount, and accounts other than the
    two involved keep their balance. -/
theorem moveN_dst_ge (b : Pubkey → ℕ) (src dst : Pubkey) (x : ℕ) : x ≤ moveN b src dst x dst := by
  simp [moveN]

/-- Anchor `init`: the new account holds at least the rent-exempt minimum, and an account the
    system program does not own, other than the new one, keeps its lamports (it cannot pay). -/
theorem initAccount_lamports {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (h : s.initAccount pid mb payer key space data = some s') :
    (mb space).val ≤ (s' key).lamports.val ∧
      ∀ k, k ≠ key → (s k).owner ≠ systemProgram → (s' k).lamports = (s k).lamports := by
  unfold State.initAccount at h
  obtain ⟨s₀, hs₀, rfl⟩ := Option.map_eq_some_iff.mp h
  have hset : ∀ k, ((s₀.set key { s₀ key with owner := pid, data := data }) k).lamports = (s₀ k).lamports := by
    intro k; by_cases hk : k = key
    · subst hk; simp [State.set]
    · simp [State.set, hk]
  simp only [hset]
  -- a transfer from `payer` to `key`
  have transfer : ∀ (amt : U64) (s₀ : State), s.systemTransfer payer key amt = some s₀ →
      (fun k => (s₀ k).lamports.val) = moveN (fun k => (s k).lamports.val) payer key amt.val ∧
      (s payer).owner = systemProgram := by
    intro amt s₀ hs
    unfold State.systemTransfer at hs
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨ho, -, -, hm⟩ := stb_spec hb
    exact ⟨by funext k; simpa [State.withBalances, State.balances] using congrFun hm k, ho⟩
  have other : ∀ (amt : U64) (s₀ : State), s.systemTransfer payer key amt = some s₀ →
      ∀ k, k ≠ key → (s k).owner ≠ systemProgram → (s₀ k).lamports = (s k).lamports := by
    intro amt s₀ hs k hk hko
    obtain ⟨hm, ho⟩ := transfer amt s₀ hs
    have hkp : k ≠ payer := fun e => hko (e ▸ ho)
    apply UScalar.eq_of_val_eq
    rw [show (s₀ k).lamports.val = _ from congrFun hm k, moveN_other _ _ hkp hk]
  by_cases h0 : (s key).lamports.val = 0
  · rw [if_pos h0] at hs₀
    refine ⟨?_, other _ _ hs₀⟩
    have := congrFun (transfer _ _ hs₀).1 key
    rw [show (s₀ key).lamports.val = _ from this]; exact moveN_dst_ge _ _ _ _
  rw [if_neg h0] at hs₀
  by_cases hpk : payer = key
  · rw [if_pos hpk] at hs₀; cases hs₀
  rw [if_neg hpk] at hs₀
  dsimp only at hs₀
  split at hs₀
  · rename_i htop
    cases hs₀
    refine ⟨by omega, fun k _ _ => rfl⟩
  · rename_i htop
    refine ⟨?_, other _ _ hs₀⟩
    have := congrFun (transfer _ _ hs₀).1 key
    rw [show (s₀ key).lamports.val = _ from this]
    have hv : (⟨BitVec.ofNat 64 (max (mb space).val 1 - (s key).lamports.val)⟩ : U64).val
        = max (mb space).val 1 - (s key).lamports.val := by
      show (BitVec.ofNat 64 _).toNat = _
      rw [BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have := (mb space).hBounds
      have : (mb space).val < 2 ^ 64 := by scalar_tac
      omega
    rw [hv]
    simp only [moveN, Function.update_self, Function.update_of_ne (Ne.symm hpk)]
    omega

/-- Anchor `init` with a positive rent fails if the payer is the new account: an empty address
    can't pay its own rent, and Anchor refuses a funded one paying for itself. -/
theorem initAccount_payer_ne {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (h : s.initAccount pid mb payer key space data = some s')
    (hpos : 0 < (mb space).val) : payer ≠ key := by
  intro hpk; subst hpk
  unfold State.initAccount at h
  obtain ⟨s₀, hs₀, -⟩ := Option.map_eq_some_iff.mp h
  by_cases h0 : (s payer).lamports.val = 0
  · rw [if_pos h0] at hs₀
    unfold State.systemTransfer at hs₀
    obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.mp hs₀
    unfold systemTransferBalances at hb
    split at hb
    · rename_i hc
      have := hc.2.2
      simp only [State.balances] at this
      omega
    · cases hb
  · rw [if_neg h0, if_pos rfl] at hs₀; cases hs₀

/-- What `admin::initialize` returns when it succeeds: the tree `init_tree` wrote, a pool and a
    config whose authority is the caller, with fee rates 0 and 25 and fee error margin 500. -/
theorem adminInitialize_values {H : zkcash_core.merkle_tree.Hasher Unit}
    {t0 t : zkcash_core.merkle_tree.MerkleTreeAccount} {tk0 tk : zkcash_core.admin.TreeTokenAccount}
    {c0 c : zkcash_core.admin.GlobalConfig} {auth : Pubkey} {b1 b2 b3 : U8}
    (h : zkcash_core.admin.initialize H t0 tk0 c0 auth b1 b2 b3 = ok (.Ok (), t, tk, c)) :
    (∃ r, zkcash_core.admin.init_tree H t0 auth b1 zkcash_core.admin.DEFAULT_MAX_DEPOSIT_AMOUNT
      = ok (r, t)) ∧ tk = { authority := auth, bump := b2 } ∧
      c = { authority := auth, deposit_fee_rate := 0#u16, withdrawal_fee_rate := 25#u16,
            fee_error_margin := 500#u16, bump := b3 } := by
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
      Result.ok.injEq] at hr1
    subst hr1
    have := Result.ok_injective h; simp at this
  | Ok u =>
  have : cf = .Continue u := by
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using (Result.ok_injective hcf).symm
  subst this
  have e := Result.ok_injective h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl, rfl, rfl⟩ := e
  exact ⟨⟨_, hit⟩, rfl, rfl⟩

/-- **`initialize` starts the spec's run.** The state right after it is the spec's start world
    `initWorld`, for the parameters it set: both authorities are the caller, who is the admin
    when the deployment has one, the settings are the documented defaults, the tree is the spec's empty tree. SOL
    already at the pool's address counts as sent to it before the first transaction (allowed). -/
theorem init_between [Spec.PoseidonHashes] {d : Deployment} {rent : Nat → U64} {s s' : State}
    {tx : TxEnv} {a : InitializeAccounts}
    (hdist : d.treeAddress ≠ d.poolAddress ∧ d.treeAddress ≠ d.configAddress ∧ d.poolAddress ≠ d.configAddress)
    (hpid : d.programId ≠ systemProgram) (hrent : tx.minimumBalance = some rent)
    (hpos : ∀ n, 0 < (rent n).val)
    (hnoNull : ∀ k, ¬ d.IsNullifierAccount s k)
    (hz : ∃ z, d.crypto.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = Spec.Z i)
    (h : execInitialize d s tx a = .ok s') :
    Initialized d s' ∧ ∃ params : Spec.InitParams, RunOfDeployment d rent params ∧
      params.initializer = toPubkey a.authority ∧ params.signers = tx.signers.map toPubkey ∧
      params.cfg = (toWorld d rent s').state.config ∧
      params.balances = (toWorld d rent s').balances ∧
      toWorld d rent s' = (Spec.initWorld params).withUpdatedValues
        (Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s')) ∧
      (Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s')).Allowed
        (Spec.initWorld params) := by
  unfold execInitialize at h
  split at h
  · cases h
  rename_i hv
  have hvalid := not_not.mp hv
  split at h
  · cases h
  rename_i mb hmb
  have hmr : mb = rent := Option.some.inj (hmb.symm.trans hrent)
  subst mb
  split at h
  · cases h
  rename_i s₁ hs₁
  obtain ⟨r₀, hr₀, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r₀ with
  | Err e => cases h
  | Ok u₀ =>
  obtain ⟨⟨r, tree, token, config⟩, hres, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r with
  | Err e => cases h
  | Ok u =>
  have hs' := PrivacyCash.Model.checkBalanced_ok h
  have hadmin := checkAdmin_ok (ofResult_ok hr₀)
  obtain ⟨⟨r', hit⟩, -, hc⟩ := adminInitialize_values (ofResult_ok hres)
  have htree := initialize_toTree hz hit
  obtain ⟨z, hzb, -⟩ := hz
  have hauth : tree.authority = a.authority := (initTree_values hzb hit).2.2.2.2.2.1
  -- the three accounts and their addresses
  have htA : a.treeAccount = d.treeAddress := hvalid.treeAccount.1
  have hpA : a.treeTokenAccount = d.poolAddress := hvalid.treeTokenAccount.1
  have hcA : a.globalConfig = d.configAddress := hvalid.globalConfig.1
  obtain ⟨dtp, dtc, dpc⟩ := hdist
  rw [← htA, ← hpA] at dtp
  rw [← htA, ← hcA] at dtc
  rw [← hpA, ← hcA] at dpc
  -- the three inits
  obtain ⟨s₀₂, h₀₂, h₃⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨s₀₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h₀₂
  obtain ⟨o1, -, k1⟩ := initAccount_ownerData h₁
  obtain ⟨o2, -, k2⟩ := initAccount_ownerData h₂
  obtain ⟨o3, -, k3⟩ := initAccount_ownerData h₃
  have own1 : (s₁ a.treeAccount).owner = d.programId := by
    rw [(k3 _ dtc).1, (k2 _ dtp).1]; exact o1
  have own2 : (s₁ a.treeTokenAccount).owner = d.programId := by
    rw [(k3 _ dpc).1]; exact o2
  have own3 : (s₁ a.globalConfig).owner = d.programId := o3
  -- the pool's lamports: at least the rent-exempt minimum
  have hpl : (rent treeTokenAccountSpace).val ≤ (s₁ a.treeTokenAccount).lamports.val := by
    rw [(initAccount_lamports h₃).2 _ dpc (by rw [o2]; exact hpid)]
    exact (initAccount_lamports h₂).1
  -- the final writes
  have hs'k : ∀ k, (s' k).owner = (s₁ k).owner ∧ (s' k).lamports = (s₁ k).lamports ∧ (s' k).data =
      (if k = a.globalConfig then .globalConfig config else if k = a.treeTokenAccount then .treeToken token
       else if k = a.treeAccount then .treeAccount tree else (s₁ k).data) := by
    intro k; rw [hs']
    simp only [State.set]
    split_ifs <;> simp_all
  have dT : (s' d.treeAddress).data = .treeAccount tree := by
    rw [← htA, (hs'k _).2.2, if_neg dtc, if_neg dtp, if_pos rfl]
  have dP : (s' d.poolAddress).data = .treeToken token := by
    rw [← hpA, (hs'k _).2.2, if_neg dpc, if_pos rfl]
  have dC : (s' d.configAddress).data = .globalConfig config := by
    rw [← hcA, (hs'k _).2.2, if_pos rfl]
  have hT : s'.treeAccount d.treeAddress = tree := by simp only [PrivacyCash.Model.State.treeAccount, dT]
  have hC : s'.configAccount d.configAddress = config := by simp only [PrivacyCash.Model.State.configAccount, dC]
  have hinit : Initialized d s' := by
    refine ⟨⟨tree, ?_, dT⟩, ⟨token, ?_, dP⟩, ⟨config, ?_, dC⟩⟩
    · rw [← htA, (hs'k _).1]; exact own1
    · rw [← hpA, (hs'k _).1]; exact own2
    · rw [← hcA, (hs'k _).1]; exact own3
  -- no nullifier account yet
  have hnull' : nullifierAccountsOf d s' = ∅ := by
    ext x
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_nullifierAccountsOf]
    rintro ⟨ho, b, hd⟩
    rw [(hs'k _).2.2] at hd
    split_ifs at hd with e1 e2 e3
    rw [(hs'k _).1, (k3 _ e1).1, (k2 _ e2).1, (k1 _ e3).1] at ho
    rw [(k3 _ e1).2, (k2 _ e2).2, (k1 _ e3).2] at hd
    exact hnoNull _ ⟨ho, b, hd⟩
  have hcfg : (toWorld d rent s').state.config = toConfig config tree := by
    simp only [toWorld, hT, hC]
  have pa : (toConfig config tree).authority = toPubkey a.authority := by simp [toConfig, hc]
  have pl : (toConfig config tree).limitAuthority = toPubkey a.authority := by simp [toConfig, hauth]
  have pad : ∀ x, d.adminPubkey.map toPubkey = some x → toPubkey a.authority = x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hx
    rw [hadmin k hk]
  have pdr : (toConfig config tree).depositFeeRate = 0 := by simp [toConfig, hc]
  have pwr : (toConfig config tree).withdrawalFeeRate = 25 := by simp [toConfig, hc]
  have pm : (toConfig config tree).feeErrorMargin = 500 := by simp [toConfig, hc]
  have plim : (toConfig config tree).maxDepositLimit = 1_000_000_000_000 := by
    simp [toConfig, (initTree_values hzb hit).2.2.2.2.2.2,
      zkcash_core.admin.DEFAULT_MAX_DEPOSIT_AMOUNT]
  have psg : toPubkey a.authority ∈ tx.signers.map toPubkey :=
    List.mem_map_of_mem hvalid.authority
  -- the initializer pays for the three accounts, so it is none of them
  have na1 := initAccount_payer_ne h₁ (hpos _)
  have na2 := initAccount_payer_ne h₂ (hpos _)
  have na3 := initAccount_payer_ne h₃ (hpos _)
  have pnc : toPubkey a.authority ≠ toPubkey d.poolAddress ∧
      toPubkey a.authority ≠ toPubkey d.treeAddress ∧ toPubkey a.authority ≠ toPubkey d.configAddress :=
    ⟨fun e => na2 (by rw [hpA]; exact toPubkey_inj e), fun e => na1 (by rw [htA]; exact toPubkey_inj e),
      fun e => na3 (by rw [hcA]; exact toPubkey_inj e)⟩
  -- the tree's and the config's accounts hold at least their rent
  have htl : (rent treeAccountSpace).val ≤ (s₁ a.treeAccount).lamports.val := by
    rw [(initAccount_lamports h₃).2 _ dtc (by rw [(k2 _ dtp).1, o1]; exact hpid),
      (initAccount_lamports h₂).2 _ dtp (by rw [o1]; exact hpid)]
    exact (initAccount_lamports h₁).1
  have hcl : (rent globalConfigSpace).val ≤ (s₁ a.globalConfig).lamports.val :=
    (initAccount_lamports h₃).1
  have tP : toPubkey d.treeAddress ≠ toPubkey d.poolAddress := fun e => dtp (by rw [htA, hpA]; exact toPubkey_inj e)
  have tC : toPubkey d.treeAddress ≠ toPubkey d.configAddress := fun e => dtc (by rw [htA, hcA]; exact toPubkey_inj e)
  have cP : toPubkey d.configAddress ≠ toPubkey d.poolAddress := fun e => dpc (by rw [hpA, hcA]; exact (toPubkey_inj e).symm)
  refine ⟨hinit, ⟨toConfig config tree, (toWorld d rent s').balances, (rent treeTokenAccountSpace).val,
    (rent nullifierAccountSpace).val, toPubkey d.poolAddress, nullifierAddrOf d, toPubkey d.treeAddress,
    toPubkey d.configAddress, (rent treeAccountSpace).val, (rent globalConfigSpace).val,
    toWorld_fit d rent s', toPubkey a.authority, pnc,
    tx.signers.map toPubkey, psg, d.adminPubkey.map toPubkey, pa, pl, pad, pdr, pwr, pm, plim⟩,
    ⟨rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, hcfg.symm, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [toWorld, Spec.initWorld, Spec.World.withUpdatedValues,
      Spec.UpdatedValuesBetweenTransacts.unchanged, hT, hnull',
      htree]; rfl
  · -- the program's accounts gained at least nothing; there are no nullifier accounts yet
    rintro x (rfl | hx | rfl | rfl)
    · show (Spec.initWorld _).poolBalance ≤ s'.lamports (fromPubkey (toPubkey d.poolAddress))
      simp only [Spec.World.poolBalance, Spec.initWorld, Function.update_self,
        fromPubkey_toPubkey, PrivacyCash.Model.State.lamports]
      rw [← hpA, (hs'k _).2.1]; exact hpl
    · simp [Spec.initWorld] at hx
    · show (Spec.initWorld _).balances (toPubkey d.treeAddress) ≤
        s'.lamports (fromPubkey (toPubkey d.treeAddress))
      simp only [Spec.initWorld, Function.update_of_ne tP, Function.update_of_ne tC,
        Function.update_self, fromPubkey_toPubkey, PrivacyCash.Model.State.lamports]
      rw [← htA, (hs'k _).2.1]; exact htl
    · show (Spec.initWorld _).balances (toPubkey d.configAddress) ≤
        s'.lamports (fromPubkey (toPubkey d.configAddress))
      simp only [Spec.initWorld, Function.update_of_ne cP, Function.update_self,
        fromPubkey_toPubkey, PrivacyCash.Model.State.lamports]
      rw [← hcA, (hs'k _).2.1]; exact hcl
  · exact toWorld_fit d rent s'
  · show Spec.ReachableByAdminChanges [] (toConfig config tree)
      (toWorld d rent s').state.config
    rw [hcfg]; exact .noChange _

/-! ## Before and after `initialize` -/

/-- Before initialization, only `initialize` can succeed: every other instruction needs the
    program's tree or config. -/
theorem noProgram_step {d : Deployment} {s s' : State} {tx : TxEnv} {ix : Instruction}
    {em : List CommitmentData} (hn : NoProgramAccounts d s) (h : step d s tx ix = .ok (s', em)) :
    ∃ a, ix = .initialize a := by
  cases ix with
  | «initialize» a => exact ⟨a, rfl⟩
  | updateDepositLimit a l =>
    exfalso
    obtain ⟨s₁, h1, -⟩ := PrivacyCash.Model.Except.bind_ok h
    unfold execUpdateDepositLimit at h1
    split at h1
    swap; · cases h1
    split at h1
    · cases h1
    rename_i hv
    exact hn.1 _ _ (not_not.mp hv).treeAccount.1
  | updateGlobalConfig a dep wd m =>
    exfalso
    obtain ⟨s₁, h1, -⟩ := PrivacyCash.Model.Except.bind_ok h
    unfold execUpdateGlobalConfig at h1
    split at h1
    swap; · cases h1
    split at h1
    · cases h1
    rename_i hv
    exact hn.2.2.1 _ _ (not_not.mp hv).globalConfig.1
  | transact a proof ext fee out1 out2 =>
    exfalso
    have hx : execTransact d s tx a proof ext fee out1 out2 = .ok (s', em) := h
    obtain ⟨_, _, _, _, _, _, _, _, hvalid, -⟩ := execTransact_ok hx
    exact hn.1 _ _ hvalid.treeAccount.1

/-- After initialization, `initialize` cannot run again: the tree's address is taken. -/
theorem initialized_no_initialize {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : InitializeAccounts} {em : List CommitmentData} (hpid : d.programId ≠ systemProgram)
    (hi : Initialized d s) (h : step d s tx (.initialize a) = .ok (s', em)) : False := by
  obtain ⟨s₁, h1, -⟩ := PrivacyCash.Model.Except.bind_ok h
  unfold execInitialize at h1
  split at h1
  · cases h1
  rename_i hv
  have hvalid := not_not.mp hv
  obtain ⟨⟨t, ht⟩, -, -⟩ := hi
  apply hpid
  rw [← ht.1, show d.treeAddress = a.treeAccount from hvalid.treeAccount.1.symm]
  exact hvalid.treeAccount.2.1

/-! ## The bridge, one event at a time -/

section
variable [Spec.PoseidonHashes] [Spec.Sha] {G1 G2 GT : Type} [AddCommGroup G1] [Inhabited G2]
  [Module Spec.F G1] [CommGroup GT]

/-- What the bridge keeps along a code run. -/
def BridgeInv (d : Deployment) (rent : Nat → U64) (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
    (v : RunView)
    (txs : List Spec.TxInputs) (s : State) : Prop :=
  WellFormed d s ∧
    ((NoProgramAccounts d s ∧ txs = [] ∧ v = {}) ∨
      (Initialized d s ∧
        withSyscallSpec C in
        ∃ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)),
          RunMatchesView d rent v txs s params r))

/-- A change between transactions after the end of a spec run: the view's open gap gains the
    admin changes `chs`. -/
theorem RunMatchesView.between {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT}
    {v v' : RunView} {txs : List Spec.TxInputs} {s s' : State}
    {chs : List Spec.AdminChange}
    (hv : v' = { v with openGap := v.openGap ++ chs })
    (h : withSyscallSpec C in
      ∃ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)),
        RunMatchesView d rent v txs s params r)
    (hw : toWorld d rent s' = (toWorld d rent s).withUpdatedValues
      (recordChanges (toWorld d rent s') chs))
    (ha : (recordChanges (toWorld d rent s') chs).Allowed (toWorld d rent s)) :
    withSyscallSpec C in
    ∃ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)),
      RunMatchesView d rent v' txs s' params r := by
  withSyscallSpec C
  subst hv
  obtain ⟨params, r, hdep, hi, htx, hpl, hp, hal, ha', hgl, hg, b, hb, hgap, heq⟩ := h
  refine ⟨params, r, hdep, hi, htx, hpl, hp, hal, ha', hgl, hg,
    b.andThen (recordChanges (toWorld d rent s') chs), ?_, ?_, ?_⟩
  · rw [heq] at ha
    exact hb.trans ha
  · show b.adminChanges ++ chs = v.openGap ++ chs
    rw [hgap]
  · rw [hw, heq]; rfl

/-- **Outside actions keep the invariant.** -/
theorem bridge_env {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT}
    {v : RunView} {txs : List Spec.TxInputs} {s s' : State}
    (hinv : BridgeInv d rent C v txs s) (h : EnvStep d.programId s s') :
    BridgeInv d rent C v txs s' := by
  obtain ⟨wf, hn | ⟨hi, hr⟩⟩ := hinv
  · exact ⟨wf_envStep wf h, Or.inl ⟨env_noProgramAccounts h hn.1, hn.2⟩⟩
  · obtain ⟨hw, ha⟩ := env_between (rent := rent) h hi
    refine ⟨wf_envStep wf h, Or.inr ⟨env_initialized h hi, ?_⟩⟩
    exact RunMatchesView.between (chs := []) (by cases v; simp) hr hw ha

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- The program's three fixed accounts differ (from `RunFacts.fixedAddressesDiffer`). -/
theorem fixed_addresses_differ {d : Deployment} {events : List Event}
    (runFacts : RunFacts d events) :
    d.treeAddress ≠ d.poolAddress ∧ d.treeAddress ≠ d.configAddress ∧ d.poolAddress ≠ d.configAddress :=
  singleton_pdas_distinct_of _ _ _ runFacts.fixedAddressesDiffer

/-- **Each instruction keeps the invariant.** `initialize` starts the spec run; `transact`
    extends it by its transaction (the main per-step theorem); the admin instructions are
    allowed changes between transactions, recorded with their signers. -/
theorem bridge_step {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT} {laws : PairingLaws C.e}
    {v : RunView} {txs : List Spec.TxInputs} {s s' : State}
    {tx : TxEnv} {ix : Instruction} {em : List CommitmentData}
    (hinv : BridgeInv d rent C v txs s)
    (hpid : d.programId ≠ systemProgram) (hashes : HashesAgree d)
    (hdist : d.treeAddress ≠ d.poolAddress ∧ d.treeAddress ≠ d.configAddress ∧ d.poolAddress ≠ d.configAddress)
    (hstepA : StepFacts d tx ix) (hrentA : SameRent rent tx.minimumBalance)
    (h : step d s tx ix = .ok (s', em)) (hrentPos : tx.RentPositive) :
    BridgeInv d rent C (v.afterEvent d rent s (.program tx ix em) s') (txs ++ stepTxs tx ix) s' := by
  withSyscallSpec C
  obtain ⟨wf, hn | ⟨hi, hr⟩⟩ := hinv
  · -- before initialization: only `initialize` succeeds, and it starts the spec run
    have wf' := wf_step hashes.poseidon_canonical hashes.zeroBytes_canonical wf h
    obtain ⟨a, rfl⟩ := noProgram_step hn.1 h
    obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
    cases h2
    obtain ⟨hi', params, hdep, hp5, hp6, hp7, hp8, heq, ha⟩ := init_between hdist
      hpid hrentA (fun n => hrentPos rent hrentA n) hn.1.2.2.2 hashes.zeroBytes_agree h1
    obtain ⟨-, rfl, rfl⟩ := hn
    refine ⟨wf', Or.inr ⟨hi', ?_⟩⟩
    refine ⟨params, Spec.Run.empty _, hdep,
      ⟨_, rfl, hp5, hp6, hp7, fun x _ => by rw [hp8]⟩, by simp [stepTxs], rfl, ?_, rfl, ?_, rfl, ?_,
      Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s'), ha, rfl, ?_⟩
    · intro j hj; exact absurd hj (by simp [Spec.Run.empty])
    · intro j hj; exact absurd hj (by simp [Spec.Run.empty])
    · intro j hj; exact absurd hj (by simp [Spec.Run.empty])
    · exact heq
  · cases ix with
    | «initialize» a => exact (initialized_no_initialize hpid hi h).elim
    | updateDepositLimit a l =>
      have wf' := wf_step hashes.poseidon_canonical hashes.zeroBytes_canonical wf h
      obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
      cases h2
      obtain ⟨hi', hw, ha⟩ := udl_between (rent := rent) wf hi h1
      simp only [stepTxs, List.append_nil]
      exact ⟨wf', Or.inr ⟨hi', RunMatchesView.between rfl hr hw ha⟩⟩
    | updateGlobalConfig a dep wd m =>
      have wf' := wf_step hashes.poseidon_canonical hashes.zeroBytes_canonical wf h
      obtain ⟨s₁, h1, h2⟩ := PrivacyCash.Model.Except.bind_ok h
      cases h2
      obtain ⟨hi', hw, ha⟩ := ugc_between (rent := rent) wf hi h1
      simp only [stepTxs, List.append_nil]
      exact ⟨wf', Or.inr ⟨hi', RunMatchesView.between rfl hr hw ha⟩⟩
    | transact a proof ext fee out1 out2 =>
      obtain ⟨txAssumptions, newAddressesDiffer⟩ := hstepA
      have hrent : tx.minimumBalance = some rent := hrentA
      have wf' := wf_step hashes.poseidon_canonical hashes.zeroBytes_canonical wf h
      obtain ⟨b₁, hb₁, b₂, htx, hb₂, hb₁nil, hb₁pool, hb₂cfg, hb₂pool⟩ :=
        transact_refines_between_verified C laws h hashes wf txAssumptions hrentPos
          newAddressesDiffer hrent
      have hi' := transact_initialized wf hi h
      obtain ⟨params, r, hdep, hinit, htxs, hpl, hpb, hal, hafter, hgl, hgaps, b, hb, hgap, heq⟩ := hr
      rw [heq] at htx hb₁
      rw [Spec.World.withUpdatedValues_twice] at htx
      obtain ⟨r', hr'tx, hr'f, hws, hup, hlast⟩ := r.snoc _ (hb.trans hb₁) _ _ htx
      have hlen : r'.txs.length = r.txs.length + 1 := by rw [hr'tx]; simp
      have hfinal : r'.ws (r.txs.length + 1) = r'.final := by
        unfold Spec.Run.final; rw [hlen]
      refine ⟨wf', Or.inr ⟨hi', params, r', hdep, hinit, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        Spec.UpdatedValuesBetweenTransacts.unchanged
        (toWorld d rent s'), ?_, rfl, ?_⟩⟩
      · rw [hr'tx, htxs]; rfl
      · simp only [RunView.afterEvent, List.length_append, List.length_singleton]
        omega
      · intro j hj
        simp only [RunView.afterEvent]
        rcases Nat.lt_or_ge j r.txs.length with hlt | hge
        · rw [List.getElem?_append_left (by omega), hpb j hlt, hup j hlt]
        · have hj' : j = r.txs.length := by omega
          subst hj'
          rw [List.getElem?_append_right (by omega), hpl, Nat.sub_self, hlast]
          simp only [List.getElem?_cons_zero, Option.some.injEq]
          exact hb₁pool.symm
      · simp only [RunView.afterEvent, List.length_append, List.length_singleton]
        omega
      · intro j hj
        simp only [RunView.afterEvent]
        rcases Nat.lt_or_ge j r.txs.length with hlt | hge
        · rw [List.getElem?_append_left (by omega), hafter j hlt, hws (j+1) (by omega)]
        · have hj' : j = r.txs.length := by omega
          subst hj'
          rw [List.getElem?_append_right (by omega), hal, Nat.sub_self, hfinal, hr'f]
          simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq]
          refine ⟨?_, ?_⟩
          · show _ = { (toWorld d rent s').state with
              config := b₂.config }
            rw [hb₂cfg]
          · exact hb₂pool.symm
      · simp only [RunView.afterEvent, List.length_append, List.length_singleton]
        omega
      · intro j hj
        simp only [RunView.afterEvent]
        rcases Nat.lt_or_ge j r.txs.length with hlt | hge
        · rw [List.getElem?_append_left (by omega), hgaps j hlt, hup j hlt]
        · have hj' : j = r.txs.length := by omega
          subst hj'
          rw [List.getElem?_append_right (by omega), hgl, Nat.sub_self, hlast]
          simp only [List.getElem?_cons_zero, Option.some.injEq]
          show v.openGap = b.adminChanges ++ b₁.adminChanges
          rw [hb₁nil, hgap, List.append_nil]
      · rw [hr'f]; exact hb₂
      · rw [hr'f, Spec.World.withUpdatedValues_twice]
        exact (Spec.World.withUpdatedValues_self _).symm

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- A `CodeRun` is a `Run` over its events. -/
theorem CodeRun.toRun {d : Deployment} {s s' : State} {steps : List RunStep}
    (h : CodeRun d s steps s') : Run d s (eventsOf steps) s' := by
  induction h with
  | nil => exact .nil _
  | @cons _ _ _ e _ he _ ih =>
    cases e with
    | program => exact .program he.1 he.2 ih
    | env => exact .env he ih

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- A one-step code run is an accepted step with positive rent. -/
theorem Run.single_inv {d : Deployment} {s s' : State} {tx : TxEnv} {ix : Instruction}
    {em : List CommitmentData} (h : Run d s [.program tx ix em] s') :
    step d s tx ix = .ok (s', em) ∧ tx.RentPositive := by
  cases h with
  | program hs hr hnil => cases hnil; exact ⟨hs, hr⟩

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- A `Run` is a `CodeRun`, through some steps with its events. -/
theorem Run.toCodeRun {d : Deployment} {s s' : State} {events : List Event}
    (h : Run d s events s') : ∃ steps, CodeRun d s steps s' ∧ eventsOf steps = events := by
  induction h with
  | nil s => exact ⟨[], .nil s, rfl⟩
  | program hs hr _ ih =>
    obtain ⟨st, h, he⟩ := ih; exact ⟨_, .program hs hr h, by rw [← he]; rfl⟩
  | env he _ ih => obtain ⟨st, h, he'⟩ := ih; exact ⟨_, .env he h, by rw [← he']; rfl⟩

/-- **The invariant holds along any `CodeRun`**, from any state where it holds. -/
theorem bridge_run {d : Deployment} {rent : Nat → U64}
    {C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT} {laws : PairingLaws C.e} {s₀ : State}
    {all : List Event} (hpid : d.programId ≠ systemProgram)
    (hashes : HashesAgree d) (runFacts : RunFacts d all)
    (sameRent : ∀ tx ix em, .program tx ix em ∈ all → SameRent rent tx.minimumBalance) :
    ∀ {s s' : State} {steps : List RunStep} {pre : List Event} {v : RunView}
      {txs : List Spec.TxInputs},
      all = pre ++ eventsOf steps → Run d s₀ pre s → BridgeInv d rent C v txs s →
      CodeRun d s steps s' →
      BridgeInv d rent C (RunView.afterSteps d rent v steps) (txs ++ runTxs (eventsOf steps))
        s' := by
  intro s s' steps pre v txs hall hpre hinv hrun
  induction hrun generalizing pre v txs with
  | nil => simpa [runTxs, eventsOf, RunView.afterSteps] using hinv
  | @cons s₁ s₂ s₃ e steps hev hrest ih =>
    cases e with
    | program tx ix emitted =>
      obtain ⟨hstep, hrentPos⟩ := hev
      have hA := runFacts.eachStep tx ix emitted (by rw [hall]; simp [eventsOf])
      have hR := sameRent tx ix emitted (by rw [hall]; simp [eventsOf])
      have hinv' := bridge_step (laws := laws) hinv hpid hashes (fixed_addresses_differ runFacts)
        hA hR hstep hrentPos
      have := ih (pre := pre ++ [.program tx ix emitted]) (by rw [hall]; simp [eventsOf])
        (hpre.append (.program hstep hrentPos (.nil _))) hinv'
      simpa [runTxs, eventsOf, RunView.afterSteps, List.append_assoc] using this
    | env =>
      have := ih (pre := pre ++ [.env]) (by rw [hall]; simp [eventsOf])
        (hpre.append (.env hev (.nil _))) (bridge_env hinv hev)
      simpa [runTxs, eventsOf, RunView.afterSteps, RunView.afterEvent] using this

/-- **The bridge.** Every code run from genesis either has not initialized
    the pool, or is (read through `toWorld`, `runTxs` and `runView`) a run of the spec from
    the start world `initialize` set, up to what happened after its last transaction. -/
theorem code_run_is_spec_run_pf {d : Deployment} {rent : Nat → U64} {s₀ s : State}
    {steps : List RunStep}
    (hgen : Genesis d.programId s₀) (hrun : CodeRun d s₀ steps s)
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (runFacts : RunFacts d (eventsOf steps))
    (sameRent : ∀ tx ix em, .program tx ix em ∈ eventsOf steps →
      SameRent rent tx.minimumBalance) :
    (NoProgramAccounts d s ∧ runTxs (eventsOf steps) = []) ∨
      (withSyscallSpec C in
       IsSpecRun d rent steps s) := by
  have h0 : BridgeInv d rent C {} [] s₀ :=
    ⟨wf_genesis hgen hpid, Or.inl ⟨genesis_noProgramAccounts hgen, rfl, rfl⟩⟩
  have := bridge_run (C := C) (laws := laws) hpid hashes runFacts sameRent (pre := []) (by simp) (.nil _) h0 hrun
  simp only [List.nil_append] at this
  rcases this.2 with ⟨hn, ht, -⟩ | ⟨-, params, r, hr⟩
  · exact Or.inl ⟨hn, ht⟩
  · withSyscallSpec C
    exact Or.inr ⟨params, r, isRunOf_of_view hpid hrun hr⟩

omit [Spec.PoseidonHashes] [Spec.Sha] in
/-- Assumptions for a code run hold for any prefix of it. -/
theorem RunFacts.prefix {d : Deployment}
    {events more : List Event} (h : RunFacts d (events ++ more)) :
    RunFacts d events :=
  ⟨h.fixedAddressesDiffer, fun tx ix em hm => h.eachStep tx ix em (List.mem_append_left _ hm)⟩

/-- An initialized code run is a spec run (the bridge, without its "not initialized" case). -/
theorem code_spec_run {d : Deployment} {rent : Nat → U64} {s₀ s : State}
    {steps : List RunStep}
    (hgen : Genesis d.programId s₀) (hrun : CodeRun d s₀ steps s)
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (runFacts : RunFacts d (eventsOf steps))
    (sameRent : ∀ tx ix em, .program tx ix em ∈ eventsOf steps →
      SameRent rent tx.minimumBalance) (hi : Initialized d s) :
    withSyscallSpec C in
    IsSpecRun d rent steps s := by
  rcases code_run_is_spec_run_pf hgen hrun hpid C laws hashes runFacts sameRent with ⟨hn, -⟩ | hr
  · obtain ⟨⟨t, ht⟩, -, -⟩ := hi; exact (hn.1 _ _ ht).elim
  · exact hr

/-- **What the spec proves of all its runs holds of an initialized code run's spec run.** -/
theorem run_satisfies {d : Deployment} {rent : Nat → U64} {s₀ s : State}
    {steps : List RunStep}
    (hgen : Genesis d.programId s₀) (hrun : CodeRun d s₀ steps s)
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (runFacts : RunFacts d (eventsOf steps))
    (sameRent : ∀ tx ix em, .program tx ix em ∈ eventsOf steps →
      SameRent rent tx.minimumBalance) (hi : Initialized d s) :
    withSyscallSpec C in
    ∀ (P : ∀ params : Spec.InitParams, Spec.Run (Spec.initWorld params) → Prop),
      (∀ params r, P params r) →
      ∃ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)),
        IsRunOf d rent steps s params r ∧ P params r := by
  withSyscallSpec C
  intro P hP
  obtain ⟨params, r, h⟩ := code_spec_run hgen hrun hpid C laws hashes runFacts sameRent hi
  exact ⟨params, r, h, hP params r⟩

/-- The per-transaction connection, for a `transact` in a code run from genesis. -/
theorem transact_connection_pf {d : Deployment} {rent : Nat → U64} {s s' : State}
    {tx : TxEnv} {a : TransactAccounts} {proof : zkcash_core.transact.Proof}
    {extAmount : I64} {fee : U64} {out1 out2 : Slice U8} {events : List CommitmentData}
    (reachable : Reachable d s) (hpid : d.programId ≠ systemProgram)
    (hstep : Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s')
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (txAssumptions : TransactAssumptions d tx.toTxContext proof)
    (newAddressesDiffer : NewNullifierAddressesDiffer d proof)
    (sameRent : SameRent rent tx.minimumBalance) :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    Spec.transact inputs (toWorld d rent s) (toWorld d rent s') :=
  have ⟨hs, hrentPos⟩ := Run.single_inv hstep
  have ⟨_, _, hgen, hrun⟩ := reachable
  (transact_refines_verified C laws hs hashes (wf_reachable hgen hrun hpid hashes) txAssumptions
    hrentPos newAddressesDiffer sameRent)

/-- `transact_connection_pf` for `step` directly: if `step` accepts, the spec's `transact` holds. -/
theorem transact_connection_step_pf {d : Deployment} {rent : Nat → U64} {s : State}
    {tx : TxEnv} {a : TransactAccounts} {proof : zkcash_core.transact.Proof}
    {extAmount : I64} {fee : U64} {out1 out2 : Slice U8}
    (reachable : Reachable d s) (hpid : d.programId ≠ systemProgram) (rentPos : tx.RentPositive)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (txAssumptions : TransactAssumptions d tx.toTxContext proof)
    (newAddressesDiffer : NewNullifierAddressesDiffer d proof)
    (sameRent : SameRent rent tx.minimumBalance) :
    withSyscallSpec C in
    match step d s tx (.transact a proof extAmount fee out1 out2) with
      | .ok (s', _) =>
          Spec.transact (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩)
            (toWorld d rent s) (toWorld d rent s')
      | .error _ => True :=
  match hs : step d s tx (.transact a proof extAmount fee out1 out2) with
  | .ok (_, _) => transact_connection_pf reachable hpid (.program hs rentPos (.nil _)) C laws hashes
      txAssumptions newAddressesDiffer sameRent
  | .error _ => trivial

/-- `transact_connection_step_pf` as `transact_connection` states it, arguments in its order. -/
theorem transact_connection_of {d : Deployment} {rent : Nat → U64} {tx : TransactTx}
    {sysvarRent : Option (Nat → U64)} {s : State} (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d) (runtime : RuntimeFacts rent)
    (txAssumptions : TransactAssumptions d tx.ctx tx.args.proof)
    (sameRent : SameRent rent sysvarRent)
    (reachable : Reachable d s) :
    withSyscallSpec C in
    (match step d s (tx.env sysvarRent) tx.instruction with
      | .ok (s', _) => Spec.transact (toInputs tx) (toWorld d rent s) (toWorld d rent s')
      | .error _ => True)
      ∨ AddressCollision d {tx.args.proof} :=
  or_collision fun hc => transact_connection_step_pf reachable hpid
    (rentPositive_of_sameRent runtime sameRent) C laws hashes txAssumptions
    (newDiffer_of_noCollision (Set.mem_singleton _) hc) sameRent

/-- `code_run_is_spec_run_pf` as `run_connection` states it, arguments in its order. -/
theorem run_connection_of {d : Deployment} {rent : Nat → U64} {s₀ s : State}
    {steps : List RunStep}
    (hpid : d.programId ≠ systemProgram)
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d)
    (everyTxAssumptions : TransactAssumptionsInRun d (eventsOf steps))
    (sameRent : ∀ tx ix em, .program tx ix em ∈ eventsOf steps →
      SameRent rent tx.minimumBalance)
    (hgen : Genesis d.programId s₀) (hrun : CodeRun d s₀ steps s) :
    ((NoProgramAccounts d s ∧ runTxs (eventsOf steps) = []) ∨
      (withSyscallSpec C in IsSpecRun d rent steps s))
      ∨ AddressCollision d (proofsIn (eventsOf steps)) :=
  or_collision fun hc => code_run_is_spec_run_pf hgen hrun hpid C laws hashes
    (RunFacts.of_assumptions everyTxAssumptions hc) sameRent

end

end Connection
